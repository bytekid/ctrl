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
  let cps = List.map to_equation (rulecps @ (List.map fst calccps)) in

  Format.printf "deduce\n";
  let print_all =
    List.iter (fun (e,_) -> Format.printf " %s\n" (P.to_string_rule e))
  in
  print_all cps;
  cps
;;

let is_terminating (alph,env) rs =
  let trs = Trs.create alph env in
  Trs.set_rules rs trs;
  let (ans, _) = Terminator.check false true trs in
  ans = Terminator.TERMINATING
;;

let orient ((alph, _) as ctxt) keep_oriented (e,e_env) rr =
  let rl = 
  Format.printf "start orient\n%!";
  let l,r,phi = Rule.lhs e, Rule.rhs e, Rule.constraints e in
  let maybe_lhs l = not (Term.is_value alph l) && not (Term.is_var l) in
  if maybe_lhs l && is_terminating ctxt ((e,e_env)::rr) then e
  else (
    let e' = Rule.create r l phi in
    let rr' = (e',e_env) :: rr in
    if not keep_oriented && maybe_lhs r && is_terminating ctxt rr' then e'
    else raise Fail)
  in
  let rl' = Constrainedrewriter.equalities_into_rule (fst ctxt) e_env rl in
  Format.printf "ORIENTED %s, simp to %s\n%!"
    (Rule.to_string rl) (Rule.to_string rl');
  rl'
;;

let transfer_trs alph rs newenv =
  let fnames = Alphabet.fun_names alph in
  let move (rule, oldenv) =
    try Rule.environment_transfer rule oldenv newenv fnames, newenv
    with _ ->
      failwith ("Variable error with rule " ^ (Rule.to_string rule))
  in List.map move rs
;;

let simplify (alph,env) (e,e_env) rr =
  let f = Alphabet.create_unsorted_fun 2 "_pair" alph in
  Alphabet.set_symbol_kind f Alphabet.Terms alph;
  let trs = Trs.create alph e_env in
  Trs.set_rules (transfer_trs alph rr e_env) trs;
  let rec simplify e =
    Format.printf "  simplify iteration\n%!";
    Format.printf "  %s\n" (P.to_string_rule e);
    (*let e = Constrainedrewriter.equalities_into_rule alph e_env e in
    Format.printf " after equalities_into_rule  %s\n" (P.to_string_rule e);*)
    (* calc simp general *)
    let rewrite = Constrainedrewriter.rewrite_bounded true false false trs 1 in
    let l,r,phis = Rule.lhs e, Rule.rhs e, Rule.constraints e in
    if Constrainedrewriter.equivalent_cterms alph e_env l r phis then
      (Format.printf "DELETE\n%!"; None)
    else
      let cterm = Term.Fun(f,[l;r]), conjunction (alph,env) phis in
      match rewrite cterm with
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

let take_smallest e ee =
  let size ((r,_),_) = Term.size (Rule.lhs r) + Term.size (Rule.rhs r) in
  let m = List.fold_left (fun x y -> if size y < size x then y else x) e ee in
  m, List.remove m ee
;;

let complete ctxt (ee,rr) =
  let rec complete i (ee,rr) =
    print i (List.map fst ee,rr);
    match ee with
    | [] -> rr
    | e :: ee ->
      let ((e,env), keep_oriented), ee = take_smallest e ee in
      Format.printf "pick equation %s\n" (Io.Printer.to_string_rule e);
      (* do not simplify if this is an input rule to be maintained *)
      let e' = if keep_oriented then Some e else simplify ctxt (e,env) rr in
      match e' with
      | None -> complete (i+1) (ee,rr)
      | Some e' ->
        Format.printf "SIMPLIFIED %s to %s\n%!"
          (Io.Printer.to_string_rule e) (Io.Printer.to_string_rule e');
        let r = orient ctxt keep_oriented (e',env) rr in
        Format.printf "ORIENT %s\n%!" (Io.Printer.to_string_rule r);
        let cps = List.map (fun e -> e,false) (deduce (r,env) rr) in
        Format.printf "deduced\n%!";
        complete (i+1) (cps @ ee, (r,env)::rr)
  in complete 0 (ee,rr)
;;

let standard v trs keep_oriented =
  try
    let alph = Trs.get_alphabet trs in
    let env = Trs.get_main_environment trs in
    let ee = Trs.get_main_environment trs in
    let rs = Trs.get_rules trs in
    if keep_oriented && not (is_terminating (alph,env) rs) then (
      Format.printf "Termination using input orientation cannot be verified";
      raise Fail); 
    let rs_ko = List.map (fun r -> r,keep_oriented) rs in
    Some (complete (alph,env) (rs_ko,[]))
  with Fail -> None
;;

let ordered v trs keep_oriented = None