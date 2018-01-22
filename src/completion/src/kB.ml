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
module Crew = Constrainedrewriter

type result = (Ctrs.Rule.t * Ctrs.Environment.t) list

exception Fail


let to_string_rule = Io.Printer.to_string_rule

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
  let combinations = List.product [info_rename n rule] irules @
                     (List.product irules [info_rename n rule]) in
  let make_pair ((i, rule1), (j, rule2)) =
    let no_var = not (Rule.is_variant rule1 rule2) in
    if i < j && no_var then (rule1, rule2, true)
    else if i > j && no_var then (rule1, rule2, true)
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
  let cps = rulecps @ (List.map fst calccps) in
  let cps = List.filter (fun (l,r,_) -> l <> r) cps in
  let to_equation (l,r,phis) = 
    Crew.equalities_into_rule alf newenv (Rule.create l r phis), newenv
  in
  List.map to_equation cps
;;

let transfer_trs alph rs newenv =
  let fnames = Alphabet.fun_names alph in
  let move (rule, oldenv) =
    try Rule.environment_transfer rule oldenv newenv fnames, newenv
    with _ ->
      failwith ("Variable error with rule " ^ (to_string_rule rule))
  in List.map move rs
;;

let all_terminating (alph,env) prec rs =
  let trs = Trs.create alph env in
  Trs.set_rules rs trs;
  if prec <> [] then
    Crpo.orient prec trs
  else (
    let (ans, _) = Terminator.check false true trs in
    ans = Terminator.TERMINATING)
;;

let is_terminating (alph,env) prec rl rs =
  if prec <> [] then
    let trs = Trs.create alph env in
    Trs.set_rules [rl] trs;
    Crpo.orient prec trs
  else (
    let trs = Trs.create alph env in
    Trs.set_rules (rl::rs) trs;
    let (ans, _) = Terminator.check false true trs in
    ans = Terminator.TERMINATING)
;;

let orient ((alph, _) as ctxt) prec keep_oriented (e,e_env) rr =
  let rl = 
  let l,r,phi = Rule.lhs e, Rule.rhs e, Rule.constraints e in
  let maybe_lhs l = not (Term.is_value alph l) && not (Term.is_var l) in
  let rr = transfer_trs alph rr e_env in
  if maybe_lhs l && is_terminating (alph,e_env) prec (e,e_env) rr then e
  else (
    let e' = Rule.create r l phi in
    if not keep_oriented && maybe_lhs r &&
       is_terminating (alph,e_env) prec (e',e_env) rr then e'
    else raise Fail)
  in
  let rl' = Crew.equalities_into_rule (fst ctxt) e_env rl in
  rl'
;;

let simplify (alph,env) (e,e_env) rr =
  let f = Alphabet.create_unsorted_fun 2 "_pair" alph in
  Alphabet.set_symbol_kind f Alphabet.Terms alph;
  let trs = Trs.create alph e_env in
  Trs.set_rules (transfer_trs alph rr e_env) trs;
  let equiv e = 
    let l,r,phis = Rule.lhs e, Rule.rhs e, Rule.constraints e in
    Crew.equivalent_cterms alph e_env l r phis
  in
  let rec simplify e =
    (*Format.printf "  simplify iteration: %!";
    Format.printf "  %s\n" (P.to_string_rule e);*)
    let l,r,phis = Rule.lhs e, Rule.rhs e, Rule.constraints e in
    if equiv e then None
    else
      let rewrite = Crew.rewrite_bounded true false false trs 1 in
      let cterm = Term.Fun(f,[l;r]), conjunction (alph,env) phis in
      match rewrite cterm with
        | [] ->  Some e
        | ((Term.Fun (_,[l';r']),phi'), is_nf) :: _ ->
          if l' = r' then None
          else
            let e' = (Rule.create l' r' [phi']) in
            if is_nf then
              (if equiv e' then None else Some e')
            else simplify e'
        | _ -> failwith "simplify: unexpected result pattern"
  in 
  match simplify e with
      None -> None
    | Some e -> Some (Crew.equalities_into_rule alph e_env e)
;;

let print_all =
  List.iter (fun (e,_) -> Format.printf " %s\n" (P.to_string_rule e))
;;

let flip rl = Rule.create (Rule.rhs rl) (Rule.lhs rl) (Rule.constraints rl)

let print i (ee,rr) =
  Format.printf "Iteration %i\n%!EE:\n" i;
  print_all ee;
  Format.printf "RR:\n";
  print_all rr;
  Format.printf "\n%!"
;;

let take_smallest e ee =
  let size ((r,_),_) = Term.size (Rule.lhs r) + Term.size (Rule.rhs r) in
  let m = List.fold_left (fun x y -> if size y < size x then y else x) e ee in
  m, List.remove m (e::ee)
;;

let compose_collapse v (alph,_) (r,env) rr =
  let f = Alphabet.create_unsorted_fun 2 "_pair" alph in
  Alphabet.set_symbol_kind f Alphabet.Terms alph;
  let trs = Trs.create alph env in
  Trs.set_rules [r,env] trs;
  let rr = transfer_trs alph rr env in
  let rewrite (ee,rr) rl =
    let l,r,phis = Rule.lhs rl, Rule.rhs rl, Rule.constraints rl in
    let cterm = Term.Fun(f,[l;r]), conjunction (alph,env) phis in
    let rewrite = Crew.rewrite_bounded false false false trs 1 in
    match rewrite cterm with
      | [] -> (ee,(rl,env)::rr)
      | ((Term.Fun (_,[l';r']),phi'), is_nf) :: _ -> 
        if l' = l && r' = r then (ee,(rl,env)::rr)
        else if l' = l then (
          let rl' = Rule.create l' r' [phi'] in
          if v then
            Format.printf "COMPOSE %s to %s\n" (to_string_rule rl)
              (to_string_rule rl');
          (ee,(rl',env) :: rr))
        else (*
          Format.printf "collapse %s\n" (to_string_rule rl);
          ((Rule.create l' r' [phi'],env) :: ee,rr)*) (ee,(rl,env)::rr)
      | _ -> failwith "simplify: unexpected result pattern"
  in List.fold_left (fun er (rl,_) -> rewrite er rl) ([],[]) rr
;;

let no_variant_in ctxt ee rr ((e,_),_) =
  let all = List.map fst ee @ rr in
  not (List.exists (fun (e',_) -> Rule.is_variant e e') all)
;;


let all = ref []

let no_variant ee =
  let var_of e ((e',_),_) = Rule.is_variant e e' in
  let no_var ((e,_),_) = not (List.exists (var_of e) !all) in
  List.filter no_var ee
;;

let complete v ctxt prec (ee,rr) =
  let rec complete i (ee,rr) =
    if v then print i (List.map fst ee,rr);
    match ee with
    | [] -> rr
    | e :: ee ->
      let ((e,env), keep_oriented), ee = take_smallest e ee in
      if v then Format.printf "CHOOSE %s\n" (to_string_rule e);
      (* do not simplify if this is an input rule to be maintained *)
      let e' = if keep_oriented then Some e else simplify ctxt (e,env) rr in
      match e' with
      | None -> complete (i+1) (ee,rr)
      | Some e' ->
        if v then
          Format.printf "SIMPLIFIED %s to %s\n%!"
            (to_string_rule e) (to_string_rule e');
        let r = orient ctxt prec keep_oriented (e',env) rr in
        if v then
          Format.printf "ORIENT %s\n%!" (to_string_rule r);
        let cps = List.map (fun e -> e,false) (deduce (r,env) rr) in
        if v && cps <> [] then 
          Format.printf "DEDUCE\n%!"; print_all (List.map fst cps);
        let cps' = List.filter (no_variant_in ctxt ee rr) cps in
        let collapsed,rr' = compose_collapse v ctxt (r,env) rr in
        let ee' = no_variant ((List.map (fun e -> e,false) collapsed) @ cps') in
        all := ((r, env), true) :: ee' @ !all;
        let rr'' = if (List.exists (fun (r',_) -> Rule.is_variant r r') rr') then rr' else (r,env)::rr' in
        complete (i+1) (ee' @ ee, rr'')
  in complete 0 (ee,rr)
;;

let standard v trs prec keep_oriented =
  try
    let alph = Trs.get_alphabet trs in
    let env = Trs.get_main_environment trs in
    let ee = Trs.get_main_environment trs in
    let rs = Trs.get_rules trs in
    if keep_oriented && not (all_terminating (alph,env) prec rs) then (
      Format.printf "Termination using input orientation cannot be verified";
      raise Fail); 
    let rs_ko = List.map (fun r -> r,keep_oriented) rs in
    all := rs_ko;
    Some (complete v (alph,env) prec (rs_ko,[]))
  with Fail -> None
;;


let oprint i eeo (ee,rr) =
  Format.printf "Iteration %i\n%!EE open:\n" i;
  print_all eeo;
  Format.printf "EE closed:\n";
  print_all ee;
  Format.printf "RR:\n";
  print_all rr;
  Format.printf "\n%!"
;;

let orient ctxt prec keep_oriented (e',env) rr =
  try orient ctxt prec keep_oriented (e',env) rr, true with Fail -> e', false
;;

let odeduce (alph,env) prec rls_new rr =
  let check (rl, env) =
    let trs = Trs.create alph env in
    Trs.set_rules [flip rl,env] trs;
    if Crpo.orient prec trs then [] else deduce (rl,env) rr
  in
  match rls_new with
      [rl] -> deduce rl rr
    | [rl1; rl2] -> check rl1 @ (check rl2)
    | _ -> failwith "odeduce: unexpected rule set"
;;

let add_unless_variant (e,env) ee =
  if (List.exists (fun (e',_) -> Rule.is_variant e e') ee) then ee
  else (e,env) :: ee
;;

let ocomplete v ctxt prec ee =
  let rec ocomplete i ee_open (ee,rr) =
    if v then oprint i (List.map fst ee_open) (ee,rr);
    match ee_open with
    | [] -> (ee,rr)
    | e :: ee_open ->
      let ((e,env), keep_oriented), ee_open = take_smallest e ee_open in
      if v then Format.printf "CHOOSE %s\n" (to_string_rule e);
      (* do not simplify if this is an input rule to be maintained *)
      (* ordered? *)
      let e' = if keep_oriented then Some e else simplify ctxt (e,env) rr in
      match e' with
      | None -> ocomplete (i+1) ee_open (ee,rr)
      | Some e' ->
        if v then Format.printf "SIMPLIFIED %s to %s\n%!"
          (to_string_rule e) (to_string_rule e');
        let r, is_oriented = orient ctxt prec keep_oriented (e',env) rr in
        if v then Format.printf "ORIENT %s\n%!" (to_string_rule r);
        let ded_new = if is_oriented then [r,env] else [r,env;flip r, env] in
        let cps = List.map (fun e -> e,false) (odeduce ctxt prec ded_new rr) in
        if v && cps <> [] then 
          Format.printf "DEDUCE\n%!"; print_all (List.map fst cps);
        let cps' = List.filter (no_variant_in ctxt ee_open (ee@rr)) cps in
        let collapsed,rr' =
          if is_oriented then compose_collapse v ctxt (r,env) rr
          else [],rr
        in
        let eeo = no_variant ((List.map (fun e -> e,false) collapsed) @ cps') in
        all := ((r, env), true) :: eeo @ !all;
        let rr'' =
          if not is_oriented then rr' else add_unless_variant (r,env) rr'
        in
        let ee' = if not is_oriented then add_unless_variant (r,env) ee else ee in
        ocomplete (i+1) (eeo @ ee_open) (ee', rr'')
  in ocomplete 0 ee ([],[])
;;

let ordered v trs prec keep_oriented =
  try
    let alph = Trs.get_alphabet trs in
    let env = Trs.get_main_environment trs in
    let ee = Trs.get_main_environment trs in
    let rs = Trs.get_rules trs in
    let rs_ko = List.map (fun r -> r,keep_oriented) rs in
    all := rs_ko;
    Some (ocomplete v (alph,env) prec rs_ko)
  with Fail -> None
;;