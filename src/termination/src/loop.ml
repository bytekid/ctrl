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

(*** TYPES ********************************************************************)
(* context *)
type t = {
  alph: Alphabet.t;
  env: Environment.t;
  max_length: int;
  max_size: int
}

let mk_ctxt a e ml ms = { alph = a; env = e; max_length = ml; max_size = ms } 

let sequence_to_string (s, rs) =
  let add_step (str,t) (rule,p) =
    let u = Rule.rewrite t p rule in
    let str = str ^ " -> " ^ (P.to_string_term u) ^ "\n" in
    (str,u)
  in
  let sstr = P.to_string_term s in
  fst (List.fold_left add_step (sstr ^ " -> \n", s) rs)
;;

let rule_sequence_to_string (rl, rs) = sequence_to_string (Rule.lhs rl, rs)

let explanation loop =
  "We use the loop processor to conclude nontermination.\n" ^
  "The loop is given by the sequence \n" ^ (sequence_to_string loop) ^ "\n"
;;

let rename_rule c rule =
  let fn = Alphabet.fun_names c.alph in
  let newenv = Environment.empty 10 in
  (*Rule.fresh_renaming rule c.env newenv fn*)
  Rule.rename rule c.env
;;

let narrow c (st, rs) p rule =
  let rule' = rename_rule c rule in
  let l,r = Rule.lhs rule', Rule.rhs rule' in
  try
    let s,t = Rule.lhs st, Rule.rhs st in
    let mgu = Elogic.unify (Term.subterm p t) l in
    let constr = Rule.constraints st @ (Rule.constraints rule') in
    let st' = Rule.apply_sub mgu (Rule.create s (Term.replace p r t) constr) in
    [st', rs @ [(rule, p)]]
  with Elogic.Not_unifiable -> []
;;

let forward c trs ((st,rs) as seq) =
  let at_pos p = L.flat_map (narrow c seq p) trs in
  LL.of_list (L.flat_map at_pos (Term.funs_pos (Rule.rhs st)))
;;

let small c (st,_) =
  Term.size (Rule.lhs st) <= c.max_size && Term.size (Rule.lhs st) <= c.max_size
;;

let short c (_,rs) = List.length rs <= c.max_length

let all_forward c trs _ seqs =
  let seqs' = LL.filter (fun seq -> small c seq && short c seq) seqs in
  let seqs'' = LL.concat (LL.map (forward c trs) seqs') in
  if LL.null seqs'' then None else Some seqs''
;;

let check (rule, rs) =
  let (s, t) = Rule.to_terms rule in
  let check t' =
   try
     let mgu =  Elogic.unify s t' in
     [ Sub.apply_term mgu s, rs ]
   with Elogic.Not_unifiable -> []
  in LL.of_list (L.flat_map check (Term.subterms t))
;;

let init_seq rule = (rule , [(rule , Position.root)])

let generate_loops rules step =
  let init_seqs = LL.of_list (List.map init_seq rules) in
  let seqs = LL.concat (LL.of_function_with step init_seqs) in
  let loops = LL.concat (LL.map check seqs) in
  loops
;;

(* main functionality *)
let process verbose prob =
  let rules = Dpproblem.get_dps prob in (* FIXME incorporate weak rules *)
  let alph = Dpproblem.get_alphabet prob in
  let env = Dpproblem.get_environment prob in
  let ctxt = mk_ctxt alph env 5 25 in
  let loops = generate_loops rules (all_forward ctxt rules) in
  if LL.null loops then 
    None
  else (
    let s = explanation ( LL.hd loops) in
    Format.printf "%s\n" s;
    Some ([ ], s))
;;

