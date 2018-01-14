(* Copyright 2018 Sarah Winkler
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

open Util
open Ctrs
open Rewriting
open Termination

module Conf = Confluence.Confluencechecker
module P = Io.Printer

type result = (Ctrs.Rule.t * Ctrs.Environment.t) list

exception Fail


let conjunction (alph,env) =
  let mk_fun = Term.make_function alph env in
  let conj = Alphabet.get_and_symbol alph in
  let top = mk_fun (Alphabet.get_top_symbol alph) [] in
  function
    | [] -> top
    | c :: cs -> List.fold_left (fun a b -> mk_fun conj [a; b]) c cs
;;

let deduce rule rules =
  let n = List.length rules in
  let newenv = Environment.empty n in
  let alf = Trs.get_alphabet (Trs.get_current ()) in
  let funnames = Alphabet.fun_names alf in
  let info_rename i (rule, e) =
    (i, Rule.fresh_renaming rule e newenv funnames)
  in
  let irules = List.mapi info_rename rules in
  let combinations = List.product [info_rename n rule] irules in
  let make_pair ((i, rule1), (j, rule2)) =
    if i < j then (rule1, rule2, true)
    else if i > j then (rule1, rule2, false)
    else (
      let l = Rule.lhs rule1 in
      let r = Rule.rhs rule1 in
      let renamed = Rule.fresh_renaming rule2 newenv newenv funnames in
      (rule1, renamed, not (List.is_supset (Term.vars l) (Term.vars r)))
    )
  in
  let pairs = List.map make_pair combinations in
  let get_cp (rule1, rule2, allow_top) =
    Conf.all_critical_pairs rule1 rule2 alf newenv allow_top
  in
  let rulecps = List.flat_map get_cp pairs in
  let calccps, newenv = Conf.critical_pairs [rule] in
  let to_equation (l,r,phis) = Rule.create l r phis, newenv in
  List.map to_equation (rulecps @ (List.map fst calccps))
;;

let orient (alph,env) (e,e_env) rr =
  let l,r,phi = Rule.lhs e, Rule.rhs e, Rule.constraints e in
  let trs = Trs.create alph env in
  Trs.set_rules ((e,env)::rr) trs;
  let (ans, _) = Terminator.check false true trs in
  if ans = Terminator.TERMINATING then e
  else (
    let e' = Rule.reverse e in
    let trs = Trs.create alph env in
    Trs.set_rules ((e',env) :: rr) trs;
    let (ans, _) = Terminator.check false true trs in
    if ans = Terminator.TERMINATING then e'
    else raise Fail)
;;


let simplify (alph,env) (e,e_env) rr =
  let f = Alphabet.create_unsorted_fun 2 "_pair" alph in
  Alphabet.set_symbol_kind f Alphabet.Terms alph;
  let trs = Trs.create alph e_env in
  Trs.set_rules rr trs;
  let rec simplify e =
    Format.printf "  simplify iteration\n%!";
    let rewrite = Constrainedrewriter.rewrite_bounded false false true trs 1 in
    let l,r,phis = Rule.lhs e, Rule.rhs e, Rule.constraints e in
    let pair = Term.Fun(f,[l;r]) in
    match rewrite (pair,conjunction (alph,env) phis) with
      | [] ->  (Format.printf "  no reduct\n%!"; Some e)
      | ((Term.Fun (_,[l';r']),phi'), is_nf) :: _ ->
        if l' = r' then None
        else
          let e' = (Rule.create l' r' [phi']) in
          if is_nf then Some e' else simplify e'
      | _ -> failwith "simplify: unexpected result pattern"
  in simplify e
;;

let print i (ee,rr) =
  let print_all =
    List.iter (fun (e,_) -> Format.printf " %s\n" (P.to_string_rule e))
  in
  Format.printf "Iteration %i\n%!EE:\n" i;
  print_all ee;
  Format.printf "RR:\n";
  print_all rr;
  Format.printf "\n%!"
;;

let rec complete i ctxt (ee,rr) =
  print i (ee,rr);
  match ee with
   | [] -> rr
   | (e,env) :: ee ->
     Format.printf "pick equation %s\n" (Io.Printer.to_string_rule e);
     match simplify ctxt (e,env) rr with
     | None -> (Format.printf "simplify,delete\n"; complete (i+1) ctxt (ee,rr))
     | Some e' ->
       Format.printf "simplify %s to %s\n%!"
         (Io.Printer.to_string_rule e) (Io.Printer.to_string_rule e');
       let r = orient ctxt (e',env) rr in
       Format.printf "oriented\n%!";
       let cps = deduce (r,env) rr in
       complete (i+1) ctxt (cps @ ee, (r,env)::rr)
;;

let standard v trs keep_oriented =
  try
    let alph = Trs.get_alphabet trs in
    let env = Trs.get_main_environment trs in
    let ee = Trs.get_main_environment trs in
    Some (complete 0 (alph,env) (Trs.get_rules trs,[]))
  with Fail -> None
;;

let ordered v trs keep_oriented = None