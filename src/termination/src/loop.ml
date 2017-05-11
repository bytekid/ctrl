(* Copyright 2014 Cynthia Kop
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
open Ctrs;;

(*** MODULES ******************************************************************)
module L = Util.List
module LL = Util.LazyList
module Sub = Substitution
module P = Io.Printer
module Alph = Alphabet
module Rewriter = Rewriting.Rewriter
module Pos = Position

(*** TYPES ********************************************************************)
(* context *)
type t = {
  alph: Alph.t;
  env: Environment.t;
  max_length: int;
  max_size: int
}

(* loop candidate *)
type seq = Rule.t * (Rule.t * Pos.t * Term.t) list * Sub.t

(* Create a context record. *)
let mk_ctxt a e ml ms = { alph = a; env = e; max_length = ml; max_size = ms } 

(* Returns the SMT-solver we will use (just the default) *)
let smt () = Rewriter.smt_solver (Rewriter.get_current ());;

(* String representation of loop. *)
let sequence_to_string (st, rs,_) =
  let add_step (str,t) (rule,p, u) =
  try
    let str =
      str ^ " -> " ^ (P.to_string_term u) ^ " [" ^(P.to_string_rule rule) ^"]\n"
    in
    (str,u)
  with Elogic.Not_matchable -> failwith ((P.to_string_term t) ^ " with " ^
   (P.to_string_rule rule) ^ " causes match failure in sequence reconstruction")
  in
  let sstr = P.to_string_term (Rule.lhs st) in
  fst (List.fold_left add_step (sstr ^ " -> \n", Rule.lhs st) rs)
;;

(* String representation of constraints. *)
let constraints_to_string = function
    [] -> ""
  | [c] -> P.to_string_term c
  | c :: cs ->
    let add_constr str c = (P.to_string_term c) ^ " /\\ " ^ str in
    List.fold_left add_constr (P.to_string_term c) cs
;;

(* String representation of loop, with explanation. *)
let explanation ((rl,_,_) as loop) =
  let cs = Rule.constraints rl in
  "We use the loop processor to conclude nontermination.\n" ^
  "The loop is given by the sequence \n" ^ (sequence_to_string loop) ^
  (if cs = [] then "" else " if " ^ (constraints_to_string cs) ^ "\n" )
;;

let substr sigma =
  let xstr x = P.to_string_term (Term.make_var x) in
  let app x t s = " " ^ (xstr x) ^ " -> " ^ (P.to_string_term t) ^ "\n" ^ s in
  "{" ^ (Sub.fold app sigma "}")
;;

let conjunction ctxt =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let conj = Alph.get_and_symbol ctxt.alph in
  let top = mk_fun (Alph.get_top_symbol ctxt.alph) [] in
  function
    | [] -> top
    | c :: cs -> List.fold_left (fun a b -> mk_fun conj [a; b]) c cs
;;

let logical_check check ctxt f =
  let not_logical = Term.check_logical_term ctxt.alph f <> None in
  if not_logical then false
  else check [f] (smt ()) ctxt.env
;;

let logical_sat = logical_check Smt.Solver.satisfiable

let logical_valid = logical_check Smt.Solver.valid

(* Given constraints cs, check whether cs => cs sigma is valid. *)
let subst_constr_valid ctxt cs sigma =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let disj = Alph.get_or_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let c1 = conjunction ctxt cs in
  let c2 = Sub.apply_term sigma c1 in
  let c = mk_fun disj [mk_fun neg [c1]; c2] in
  let r = logical_valid ctxt c in
  r
;;


let refined_subst_constr_valid ctxt cs sigma =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let eq = Alph.get_equal_symbol ctxt.alph in
  let app x t cs = (mk_fun eq [Term.make_var x; t]) :: cs in
  let c = conjunction ctxt (Sub.fold app sigma cs) in
  (*let c_cap = Term.logical_cap ctxt.alph ctxt.env c in*)
  let not_logical = Term.check_logical_term ctxt.alph c <> None in
  if not_logical then None
  else (
    let r = Smt.Solver.satisfiable_formulas [c] (smt ()) ctxt.env in
    if fst r = SAT then Some (snd r) else None)
;;

(* Check whether constraints cs are satisfiable. *)
let constr_sat ctxt cs =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let conj = Alph.get_and_symbol ctxt.alph in
  let top = mk_fun (Alph.get_top_symbol ctxt.alph) [] in
  let conj_cs = List.fold_left (fun a b -> mk_fun conj [a; b]) top cs in
  logical_sat ctxt conj_cs
;;

(* Check whether the given rewrite sequence constitutes a loop; to that end
   it is checked whether the initial term unifies with (a subterm of) the final
   term, and constraint conditions are satisfied. *)
let check ctxt ((rule, rs, sigma) as seq) =
  let (s, t) = Rule.to_terms rule in
  let cs = Rule.constraints rule in
  let check' get_subst t' b =
    try
      let tau = get_subst t' s in
      let sigma' = Sub.compose Sub.apply_term sigma tau in
      let rule' = if b then Rule.apply_sub tau rule else rule in
      if subst_constr_valid ctxt cs sigma' then
        Some (rule', rs, sigma')
      else (
        match refined_subst_constr_valid ctxt cs sigma' with
          | None -> None
          | Some rho ->
            let rule'' = Rule.apply_sub rho rule' in
        (
         Some (rule'', rs, Sub.compose Sub.apply_term sigma' rho)))
    with Elogic.Not_unifiable | Elogic.Not_matchable -> None
  in
  if not (constr_sat ctxt cs) then LL.empty
  else
    let check t' =
      match check' Elogic.match_term t' false with
        | Some loop -> [loop]
        | None -> ( match check' Elogic.unify t' true with
          | Some loop -> [loop]
          | None -> [])
    in LL.of_list (L.flat_map check (Term.subterms t))
;;

(* Shorthand to rename a rule. *)
let rename_rule c rule =
  let fn = Alph.fun_names c.alph in
  let newenv = Environment.empty 10 in
  Rule.rename rule c.env
;;

(* Narrow last term in sequence using given rule at position p. *)
let narrow c ((st, rs,sigma) as seq) p rule =
  let rule' = rename_rule c rule in
  let l,r = Rule.lhs rule', Rule.rhs rule' in
  try
    let s,t = Rule.lhs st, Rule.rhs st in
    let mgu = Elogic.unify (Term.subterm p t) l in
    let constr = Rule.constraints st @ (Rule.constraints rule') in
    let st' = Rule.apply_sub mgu (Rule.create s (Term.replace p r t) constr) in
    let sigma' = Sub.compose Sub.apply_term sigma mgu in
    [st', rs @ [(rule, p, Rule.rhs st')], sigma']
  with Elogic.Not_unifiable -> []
;;

(* Do forward narrowing using rules in trs from last terms in sequence, trying
   possible rules and positions. For the rules to be applied at the root
   (typically dependency pairs) only consider rules which are smaller or equal
   to the first rule (with respect to some arbitrary order), to avoid redundant
   representations of same loop that start at different term. *)
let forward c (rules_root, rules_below) ((st,rs,_) as seq) =
  let r0,_,_ = L.nth rs 0 in
  let rsrt = L.filter (fun r -> Rule.compare r r0 <= 0) rules_root in
  let rlps_root = List.map (Util.Pair.make Pos.root) rsrt in
  let ps = L.remove Pos.root (Term.funs_pos (Rule.rhs st)) in
  let rlps = rlps_root @ (L.product ps rules_below) in
  (* do not process already found loops further *)
  if not (LL.null (check c seq)) then LL.empty
  else LL.of_list (L.flat_map (fun (p,rl) -> narrow c seq p rl) rlps)
;;

(* Checking whether the sequence does not exceed the maximal term size. *)
let small c (st,_,_) =
  Term.size (Rule.lhs st) <= c.max_size && Term.size (Rule.lhs st) <= c.max_size
;;

(* Checking whether the sequence does not exceed the maximal length. *)
let short c (_,rs,_) = List.length rs < c.max_length

(* Do forward narrowing from last terms in sequences, trying all possible
   rules and positions but eliminating sequences that exceed the bounds. *)
let all_forward c rules _ seqs =
  let cs (rl,_,tau) = L.map (Sub.apply_term tau) (Rule.constraints rl) in
  let useful seq = small c seq && short c seq && (constr_sat c (cs seq)) in
  let seqs' = LL.filter useful seqs in
  let seqs'' = LL.concat (LL.map (forward c rules) seqs') in
  if LL.null seqs'' then None else Some seqs''
;;

(* The initial sequence, starting from a rule. *)
let init_seq rule = (rule, [rule, Position.root, Rule.rhs rule], Sub.empty)

(* Generates loops, starting from rule set rules and using the step function
   to extend sequences.
*)
let generate_loops ctxt start_rules step =
  let init_seqs = LL.of_list (List.map init_seq start_rules) in
  let seqs = LL.concat (LL.of_function_with step init_seqs) in
  let loops = LL.concat (LL.map (check ctxt) (LL.append init_seqs seqs)) in
  loops
;;

(* Main functionality *)
let process verbose prob =
  let dps = Dpproblem.get_dps prob in
  let rules = Dpproblem.get_rules prob in
  let alph = Dpproblem.get_alphabet prob in
  let env = Dpproblem.get_environment prob in
  let ctxt = mk_ctxt alph env 4 25 in
  let loops = generate_loops ctxt dps (all_forward ctxt (dps, rules)) in
  if LL.null loops then None
  else (
    let rec print i xs =
      if not (LL.null xs) then
      let s = explanation (LL.hd xs) in
      Format.printf "%d. %s\n%!" i s;
      print (i+1) (LL.tl xs)
    in print 0 loops;
    Some ([ ],  explanation (LL.hd loops)))
;;

