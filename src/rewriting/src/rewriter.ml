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
open Smt;;

(*** TYPES *******************************************************************)
type t = Solver.t;;

(** STATE VARIABLES **********************************************************)
let current : t option ref = ref None;;

(*** FUNCTIONS ***************************************************************)

let create smt = smt;;
let smt_solver t = t;;

let set_current k = current := Some k;;
let has_current _ = !current <> None;;
let get_current _ = match !current with
  | None -> failwith "No current rewriter has been set!"
  | Some rewriter -> rewriter
;;

let solver _ = smt_solver (get_current ());;

(* interactions with the smt-solver *)

let smt_check formula = Solver.satisfiable_formulas [formula] (solver ());;
let smt_calc t = Solver.calculate t (solver ());;
let smt_val s = Solver.get_value s (solver ());;

(* Doing normal calculations *)

(* does a reduction at the root, if all the root's children are values *)
let rec top_calc_reduce term =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let not_a_value term = not (Term.is_value a term) in
  match term with
  | Term.Var _ -> None
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    if Alphabet.find_symbol_kind f a <> Alphabet.Logical then None
    else if List.filter not_a_value args <> [] then None
    else Some (smt_calc term)
  | Term.Forall (x, arg) ->
    calculate_quantifier x (Smtquantifiers.universal_range x a arg) true a
  | Term.Exists (x, arg) ->
    calculate_quantifier x (Smtquantifiers.existential_range x a arg) false a

(* reduces a quantifier to True or False, if its bounds are values *)
and calculate_quantifier x ((below, sb), (above, sa), claim) forall alf =
  (* basic conversion functions and necessary values *)
  let not_a_value term = not (Term.is_value alf term) in
  let to_int t = Function.integer_to_int (Option.the (Term.root t)) in
  let to_val n = Term.make_fun (Function.integer_symbol n) [] in
  let (bot, top) = 
    try (Alphabet.get_bot_symbol alf, Alphabet.get_top_symbol alf)
    with Not_found -> failwith ("When using quantifiers, both a " ^
               "top and bottom symbol must be set in the theory.")
  in
  (* there is no point in this if the term contains other variables *)
  let vs = Term.vars claim in
  if (vs <> []) && (vs <> [x]) then None else
  (* we need both a lower and upper bound, and they must be integers *)
  if not_a_value below then None else
  if not_a_value above then None else
  let (b, a) =
    try (to_int below, to_int above)
    with _ -> failwith ("Quantifier bounds are not integers, " ^
                        "this is unusual!")
  in
  (* get the actual bounds (taking strictness into account *)
  let b = if sb then b + 1 else b in
  let a = if sa then a - 1 else a in
  (* test each of the possible values in b..a! *)
  let testclaim value =
    let gamma = Substitution.of_list [(x,value)] in
    let updatedclaim = Substitution.apply_term gamma claim in
    let normalised = normalise_calculations alf updatedclaim in
    if not_a_value normalised then None
    else Some normalised
  in
  let rec checkfor lower upper =
    if lower > upper then
      Some (Term.make_fun (if forall then top else bot) []) else
    let v = testclaim (to_val lower) in
    match v with
      | None -> None
      | Some (Term.Fun (f, [])) | Some (Term.InstanceFun (f, [], _)) ->
        if (f = top) && (not forall) then v
        else if (f = bot) && forall then v
        else checkfor (lower + 1) upper
      | _ -> failwith "Child of forall does not return a boolean!"
  in
  checkfor b a

(* normalises all calculations in the given term in an innermost way *)
and normalise_calculations a term =
  let term_with_children args =
    let normalised_args = List.map (normalise_calculations a) args in
    let updatedterm = Term.replace_args term normalised_args in
    match top_calc_reduce updatedterm with
      | None -> updatedterm
      | Some value -> value
  in
  match term with
    | Term.Var _ -> term
    | Term.Fun (_, args) | Term.InstanceFun (_, args, _) ->
      term_with_children args
    | Term.Forall (_, arg) | Term.Exists (_, arg) ->
      term_with_children [arg]
;;

let calc_reduce term position =
  let sub = Term.subterm position term in
  match top_calc_reduce sub with
    | None -> None
    | Some newsub -> Some (Term.replace position newsub term)
;;

let calc_normalise term =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  normalise_calculations a term
;;

(* Single reduction steps with a rule *)

let top_applicable_with substitution term (rule, env) =
  let trs = Trs.get_current () in
  let a = Trs.get_alphabet trs in
  let test_value_substitute s domain =
    let rec test_values = function
      | [] -> true
      | x :: tail ->
        let xsub = (Substitution.find x !substitution) in
        if not (Term.is_value a xsub) then false
        else test_values tail
    in
    test_values (List.intersect (Term.vars s) domain)
  in
  let test_constraint s =
    let domain = Substitution.domain !substitution in
    if not (test_value_substitute s domain) then false
    else (
      let formula = Substitution.apply_term !substitution s in
      let (result, newsub) = smt_check formula env in
      if result <> Smtresults.SAT then false
      else (
        let rec add_to_substitution = function
          | [] -> ()
          | (x, term) :: tail ->
            substitution := Substitution.add x term !substitution ;
            add_to_substitution tail
        in
        add_to_substitution (Substitution.to_list newsub) ;
        true
      )
    )
  in
  let constraints = Rule.constraints rule in
  if not (List.for_all test_constraint constraints) then None
  else Some !substitution
;;

let top_applicable term (rule, env) =
  try
    let substitution = ref (Elogic.match_term term (Rule.lhs rule)) in
    top_applicable_with substitution term (rule, env)
  with Elogic.Not_matchable -> None
;;

let user_input sort name =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let e = Trs.get_main_environment (Trs.get_current ()) in
  Format.fprintf Format.std_formatter "Input to variable %s:\n> " name ;
  Format.print_flush () ;
  let line = read_line () in
  let term = Term.read_value line a "user input" in
  let foundsort = Term.get_sort a e term in
  if not (Sort.equal foundsort sort) then
    failwith ("Value from input does not have the right sort; " ^
      "sort should be " ^ (Sort.to_string sort) ^ ".") ;
  term
;;

let rec get_input_and_random term env =
  let handle_var x =
    try
      let name = Variable.find_name x in
      let sort = Environment.find_sort x env in
      let start = String.sub (name ^ "   ") 0 3 in
      if start = "inp" then user_input sort name
      else if start = "rnd" then smt_val sort
      else Term.make_var x
    with Not_found -> Term.make_var x
  in
  let makeargs args =
    List.map (fun t -> get_input_and_random t env) args
  in
  let handle_fun f args = Term.make_fun f (makeargs args) in
  let handle_instance f args sd = Term.make_instance f (makeargs args) sd in
  let handle_forall = Term.make_forall in
  let handle_exists = Term.make_forall in
  Term.recurse handle_var handle_fun handle_instance handle_forall
               handle_exists term
;;

let top_rule_reduce term (rule, env) calculate =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  match top_applicable term (rule, env) with
    | None -> None
    | Some gamma -> (
        let rhs = Rule.rhs rule in
        let q = Substitution.apply_term gamma rhs in
        let q = (if calculate then normalise_calculations a q else q) in
        let q = get_input_and_random q env in
        Some q
      )
;;

let shuffle d =
  let nd = List.map (fun c -> (Random.bits (), c)) d in
  let sond = List.sort compare nd in
  List.map snd sond
;;

let top_rule_reduce_choose term rules calculate =
  let realrules = (
    match rules with
      | None -> Trs.get_rules (Trs.get_current ())
      | Some lst -> lst
  ) in
  let rec attempt_reduction = function
    | [] -> None
    | rulepair :: tail -> (
      match top_rule_reduce term rulepair calculate with
        | Some newterm -> Some newterm
        | None -> attempt_reduction tail
      )
  in
  attempt_reduction (shuffle realrules)
;;

let rule_reduce term position rules calculate =
  (* subfun keeps track of whether the returned term is a value;
     this is a slight optimisation over having to check it
     yourself every time (always 0 if calculate is set to false)
  *)
  let rec subfun term position =
    if position = Position.root then (
      match top_rule_reduce_choose term rules calculate with
        | None -> (None, false)
        | Some reduct as t ->
          if not calculate then (t, false) else
          let a = Trs.get_alphabet (Trs.get_current ()) in
          if Term.is_value a reduct then (t, true)
          else (t, false)
    )
    else (
      let (head, tail) = Position.split_first position in
      let poshead = Position.make head in
      let sub = Term.subterm poshead term in
      match subfun sub tail with
        | (None, _) -> (None, true)
        | (Some newsub, isvalue) ->
          let replaced = Term.replace poshead newsub term in
          if isvalue then (
            match top_calc_reduce replaced with
              | None -> (Some replaced, false)
              | Some value -> (Some value, true)
          )
          else (Some replaced, false)
    )
  in
  fst (subfun term position)
;;

(* Normalising *)

let rec normalise_innermost rules term =
  let make_head_step s =
    match top_calc_reduce s with
      | Some value -> [value]
      | None -> (
        match top_rule_reduce_choose s rules false with
          | None -> []
          | Some q -> q :: normalise_innermost rules q
      )
  in
  let rec make_reduction i s = function
    | [] -> make_head_step s
    | [] :: tail -> make_reduction (i+1) s tail
    | (h :: t) :: tail ->
      let pos = Position.make i in
      let q = Term.replace pos h s in
      q :: make_reduction i q (t :: tail)
  in
  let normalise_function args =
    let args = List.map (normalise_innermost rules) args in
    make_reduction 0 term args
  in
  match term with
    | Term.Var _ -> []
    | Term.Fun (_, args) -> normalise_function args
    | Term.InstanceFun (_, args, _) -> normalise_function args
    | Term.Forall (_, arg) | Term.Exists (_, arg) -> normalise_function [arg]
;;

(* Main functionality *)

let reduce_to_normal t = t :: normalise_innermost None t;;

