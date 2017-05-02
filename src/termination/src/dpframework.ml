(* Copyright 2014, 2015 Cynthia Kop
 * GNU Lesser General Public License
 *
 * This file is part of CTRL.
 * 
 * CTRL is free software: you can redistribute it and/or modify it under
 * the terms of the GNU Lesser General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * CTRL is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
 * License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with CTRL. If not, see <http://www.gnu.org/licenses/>.
 *)

(*** OPENS *******************************************************************)

open Util;;
open Ctrs;;

(*** TYPES *******************************************************************)

type t = Alphabet.t * Environment.t * (Function.t -> Function.t) *
         (Sort.t -> bool) * (Dpproblem.t list)

(*** MODULES *****************************************************************)

(*** FUNCTIONS ***************************************************************)

(* creates a marked variation of the given function [f], and saves it
   in the alphabet [a]; the return value is the pair (f, f#)
*)
let create_marked a dpsort f =
  let sd = match Alphabet.find_sortdec f a with
    | Left s -> Sortdeclaration.create (Sortdeclaration.input_sorts s) dpsort
    | Right s -> failwith ("The termination module is not equipped " ^
        "to deal with polymorphic defined symbols.  Polymorphism " ^
        "(and variable input arity) is only intended to be used " ^
        "for logical symbols.")
  in
  let rec unused n =
    if Alphabet.mem_fun_name n a then unused (n ^ "'")
    else n
  in
  let name = unused ((Function.find_name f) ^ "#") in
  let g = Alphabet.create_fun sd name a in
  Alphabet.set_symbol_kind g Alphabet.Terms a ;
  (f, g)
;;

(* creates a (currently unused) sort to be the sort for dependency pairs;
   here, lst is the set of sort names currently in use
*)
let create_dpsort lst =
  let rec nonexisting str =
    if List.mem str lst then nonexisting (str ^ "'")
    else str
  in
  Sort.from_string (nonexisting "dpsort")
;;

(* creates an alphabet extended from the alphabet of [trs] with
   marked symbols, and returns both this alphabet and the function
   "up" which assigns a symbol to its marked version, or raises a
   Not_found error if the symbol is not defined
*)
let create_alphabet trs =
  let a = Alphabet.copy (Trs.get_alphabet trs) in
  let sorts = Alphabet.find_sorts a in
  let dpsort = create_dpsort (List.map Sort.to_string sorts) in
  let defs = Trs.def_symbols trs in
  let mapping = List.map (create_marked a dpsort) defs in
  (a, fun f -> List.assoc f mapping)
;;

(* returns all dependency pairs of the given set of rules [rules],
   assuming [defs] to be the set of defined symbols.  Here, [up]
   is a function which assigns f# to all defined symbols f, and
   which throws a Not_found error if given an argument for which
   no marked symbol is defined.
   Note: we may not assume that [up] always fails on constructor
   symbols!
*)
let get_dps rules defs up =
  let is_defined f = List.mem f defs in
  let rec candidates = function
    | Term.Var _ | Term.Forall _ | Term.Exists _ -> []
    | Term.InstanceFun (f, args, sd) -> List.flat_map candidates args
        (* function symbols without fixed declaration cannot be defined *)
    | Term.Fun (f, args) ->
      if is_defined f then (
        let fup = up f in
        (Term.make_fun fup args) ::
        List.flat_map candidates args
      )
      else List.flat_map candidates args
  in
  let dps_for_rule rule =
    let l = match Rule.lhs rule with
      | Term.Var _ | Term.InstanceFun _ | Term.Forall _ | Term.Exists _ ->
        failwith ("Error calculating dependency pairs: unexpected " ^
          "left-hand side starting with a variable, instance " ^
          "function or quantifier.")
      | Term.Fun (f, args) ->
        let fup = up f in
        Term.make_fun fup args
    in
    let rs = candidates (Rule.rhs rule) in
    let c = Rule.constraints rule in
    List.map (fun r -> Rule.create l r c) rs
  in
  try List.flat_map dps_for_rule rules
  with Not_found -> failwith
    "Encountered defined function symbol for which no marked version exists!"
;;

(* replaces the variables of [rule] by variables in [newenv] *)
let update_environment newenv alf (rule, oldenv) =
  try Rule.environment_transfer rule oldenv newenv (Alphabet.fun_names alf)
  with Failure msg ->
    failwith ("Variable error with rule " ^ (Rule.to_string rule) ^
              ": " ^ msg)
;;

(* generate the dependency pair framework for the given trs *)
let generate trs full : t =
  let (a, up) = create_alphabet trs in
  let e = Environment.empty 100 in
  let rules = Trs.get_rules trs in
  let rules = List.map (update_environment e a) rules in
  (* let rules = List.map (Rule.calculation_free a e) rules in *)
  let dps = get_dps rules (Trs.def_symbols trs) up in
  let problem = (
    if full then Dpproblem.full_problem a e dps rules
    else Dpproblem.innermost_problem a e dps rules
  ) in
  let lsorts = Alphabet.find_logical_sorts a in
  let isunsafe sort = not (Trs.test_safe_sort trs sort) in
  let unsafe = List.filter isunsafe lsorts in
  let valuesafe sort = not (List.mem sort unsafe) in
  (a, e, up, valuesafe, [problem])
;;

let get_alphabet (a, _, _, _, _) = a;;
let get_environment (_, e, _, _, _) = e;;
let solved (_, _, _, _, lst) = List.equal lst []
let values_assumed (_, _, _, v, _) prob sort =
  if Dpproblem.get_innermost prob then v sort
  else false
;;

let pop = function
  | (_, _, _, _, []) -> failwith "Can't pop from the empty framework!"
  | (a, e, u, v, hd::tl) -> (hd, (a, e, u, v, tl))
;;

let push (a, e, u, v, r) p = (a, e, u, v, p::r);;

let rec push_all w = function
  | [] -> w
  | head :: tail ->
    push_all (push w head) tail
;;

