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

(*** TYPES ********************************************************************)
(* context *)
type t = {
  alph: Alph.t;
  env: Environment.t;
  max_length: int;
  max_size: int
}

let mk_ctxt a e ml ms = { alph = a; env = e; max_length = ml; max_size = ms } 

(* returns the SMT-solver we will use (just the default) *)
let smt () = Rewriter.smt_solver (Rewriter.get_current ());;

let sequence_to_string (st, rs,_) =
  let add_step (str,t) (rule,p) =
    let u = Rule.rewrite t p rule in
    let str = str ^ " -> " ^ (P.to_string_term u) ^ "\n" in
    (str,u)
  in
  let sstr = P.to_string_term (Rule.lhs st) in
  fst (List.fold_left add_step (sstr ^ " -> \n", Rule.lhs st) rs)
;;

let constraints_to_string = function
    [] -> ""
  | [c] -> P.to_string_term c
  | c :: cs ->
    let add_constr str c = " /\\ " ^ (P.to_string_term c) in
    List.fold_left add_constr (P.to_string_term c) cs
;;

let explanation ((rl,_,_) as loop) =
  "We use the loop processor to conclude nontermination.\n" ^
  "The loop is given by the sequence \n" ^ (sequence_to_string loop) ^ "\n" ^
  "with constraints " ^ (constraints_to_string (Rule.constraints rl))
;;

let rename_rule c rule =
  let fn = Alph.fun_names c.alph in
  let newenv = Environment.empty 10 in
  Rule.rename rule c.env
;;

let narrow c ((st, rs,sigma) as seq) p rule =
  let rule' = rename_rule c rule in
  let l,r = Rule.lhs rule', Rule.rhs rule' in
  try
    let s,t = Rule.lhs st, Rule.rhs st in
    let mgu = Elogic.unify (Term.subterm p t) l in
    let constr = Rule.constraints st @ (Rule.constraints rule') in
    let st' = Rule.apply_sub mgu (Rule.create s (Term.replace p r t) constr) in
    let sigma' = Sub.compose Sub.apply_term sigma mgu in
    [st', rs @ [(rule, p)], sigma']
  with Elogic.Not_unifiable -> []
;;

let forward c trs ((st,rs,_) as seq) =
  let at_pos p = L.flat_map (narrow c seq p) trs in
  LL.of_list (L.flat_map at_pos (Term.funs_pos (Rule.rhs st)))
;;

let small c (st,_,_) =
  Term.size (Rule.lhs st) <= c.max_size && Term.size (Rule.lhs st) <= c.max_size
;;

let short c (_,rs,_) = List.length rs <= c.max_length

let all_forward c trs _ seqs =
  let seqs' = LL.filter (fun seq -> small c seq && short c seq) seqs in
  let seqs'' = LL.concat (LL.map (forward c trs) seqs') in
  if LL.null seqs'' then None else Some seqs''
;;

let constr_imp_valid ctxt cs sigma =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let conj = Alph.get_and_symbol ctxt.alph in
  let disj = Alph.get_or_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let top = mk_fun (Alph.get_top_symbol ctxt.alph) [] in 
  let conjunction = List.fold_left (fun a b -> mk_fun conj [a; b]) top in
  let c1 = conjunction cs in
  let c2 = Sub.apply_term sigma c1 in
  let c = mk_fun disj [mk_fun neg [c1]; c2] in
  (*Format.printf "checking %s\n%!" (P.to_string_term c);*)
  Smt.Solver.valid [c] (smt ()) ctxt.env
;;

let check ctxt ((rule, rs, sigma) as seq) =
  (*Format.printf "check %s\n%!" (sequence_to_string seq);*)
  let (s, t) = Rule.to_terms rule in
  let cs = Rule.constraints rule in
  let check t' =
    try
      let tau = Elogic.match_term t' s in
      let sigma' = Sub.compose Sub.apply_term sigma tau in
      if constr_imp_valid ctxt cs sigma' then [seq]
      else
        let tau =  Elogic.unify s t' in
        let sigma' = Sub.compose Sub.apply_term sigma tau in
        if not (constr_imp_valid ctxt cs sigma') then []
        else [ Rule.apply_sub tau rule, rs, sigma' ]
      with Elogic.Not_unifiable | Elogic.Not_matchable -> []
  in LL.of_list (L.flat_map check (Term.subterms t))
;;

let init_seq rule = (rule, [rule, Position.root], Sub.empty)

let generate_loops ctxt rules step =
  let init_seqs = LL.of_list (List.map init_seq rules) in
  let seqs = LL.concat (LL.of_function_with step init_seqs) in
  let loops = LL.concat (LL.map (check ctxt) (LL.append init_seqs seqs)) in
  loops
;;

(* main functionality *)
let process verbose prob =
  let rules = Dpproblem.get_dps prob in (* FIXME incorporate weak rules *)
  let alph = Dpproblem.get_alphabet prob in
  let env = Dpproblem.get_environment prob in
  let ctxt = mk_ctxt alph env 3 25 in
  let loops = generate_loops ctxt rules (all_forward ctxt rules) in
  if LL.null loops then 
    None
  else (
    let s = explanation ( LL.hd loops) in
    Format.printf "%s\n" s;
    Some ([ ], s))
;;

