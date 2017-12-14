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
open Ctrs;;
open Util;;
open Smt;;
open Rewriting;;
open Termination;;

(*** MODULES *****************************************************************)
module T = Terminator;;

(*** TYPES *******************************************************************)

type possible_results = CONFLUENT | NONCONFLUENT | UNKNOWN;;
type criticalpair = Term.t * Term.t * Term.t list;;

(*** FUNCTIONS ***************************************************************)

let smtsolver () = Rewriter.smt_solver (Rewriter.get_current ());;

(* for debugging purposes *)
let to_string_cp (l, r, phis) =
  let rule = Rule.create l r phis in
  Rule.to_string rule
;;

let print_cp cp = Printf.printf "  %s\n" (to_string_cp cp);;

let constructor_trs trs =
  let lefthandsides = Trs.lhs trs in
  let subterms = List.flat_map Term.args lefthandsides in
  let subfuns = List.flat_map Term.funs subterms in
  let defs = Trs.def_symbols trs in
  let bad f = List.mem f defs in
  List.filter bad subfuns = []
;;

let notvarorval alphabet term =
  not ((Term.is_var term) || (Term.is_value alphabet term))
;;

let critical_pair rule1 rule2 alphabet environment pos =
  let (l, r, phis) = (Rule.lhs rule1, Rule.rhs rule1, Rule.constraints rule1) in
  let (u, v, psis) = (Rule.lhs rule2, Rule.rhs rule2, Rule.constraints rule2) in
  let lsub = Term.subterm pos l in
  let phisvars = List.unique (List.flat_map Term.vars phis) in
  let psisvars = List.unique (List.flat_map Term.vars psis) in
  let cvars = List.union phisvars psisvars in
  try
    if not (Term.is_fun lsub) then raise Elogic.Not_unifiable ;
    let unifier = Elogic.unify lsub u in
    let dom = Substitution.domain unifier in
    let dangerousvars = List.intersect dom cvars in
    let getunivalue x = Substitution.find x unifier in
    let results = List.map getunivalue dangerousvars in
    if List.filter (notvarorval alphabet) results <> [] then []
    else (
      let phisgamma = List.map (Substitution.apply_term unifier) phis in
      let psisgamma = List.map (Substitution.apply_term unifier) psis in
      let together = List.union phisgamma psisgamma in
      if Solver.satisfiable together (smtsolver ()) environment then (
        let runi = Substitution.apply_term unifier r in
        let vuni = Substitution.apply_term unifier v in
        let cvuni = Term.replace pos vuni l in
        [(runi, cvuni, together)]
      )
      else []
    )
  with Elogic.Not_unifiable -> []
;;

let calculation_critical_pair rule alphabet environment pos =
  let (l, r, phis) = (Rule.lhs rule, Rule.rhs rule, Rule.constraints rule) in
  let lsub = Term.subterm pos l in
  let suitable args = List.filter (notvarorval alphabet) args = [] in
  let fresh_variable sort =
    let anames = Alphabet.fun_names alphabet in
    Term.make_var (Environment.create_sorted_var sort anames environment)
  in
  let create_equal a b =
    try
      let eq = Alphabet.get_equal_symbol alphabet in
      Term.make_function alphabet environment eq [a;b]
    with Not_found -> failwith ("Equality symbol should be set in " ^
      "alphabet in order to find critical pairs!")
  in
  match Term.root lsub with
    | None -> []
    | Some f ->
      let args = Term.args lsub in
      if Alphabet.find_symbol_kind f alphabet <> Alphabet.Logical then []
      else if not (suitable args) then []
      else (
        let xterm = fresh_variable (Term.get_sort alphabet environment lsub) in
        let lcalc = Term.replace pos xterm l in
        let newconstraint = create_equal xterm lsub in
        [(lcalc, r, newconstraint :: phis)]
      )
;;

let all_critical_pairs rule1 rule2 a e allow_top =
  let l = Rule.lhs rule1 in
  let f = Rule.left_root rule2 in
  let posses = Term.fun_pos f l in
  let ps =
    if allow_top then posses
    else List.diff posses [Position.root]
  in
  let pairs_at p = critical_pair rule1 rule2 a e p in
  List.flat_map pairs_at ps
;;

let all_calculation_critical_pairs rule a e =
  let l = Rule.lhs rule in
  let logicalhead term = match Term.root term with
    | None -> false
    | Some f -> Alphabet.find_symbol_kind f a = Alphabet.Logical
  in
  let posses = Term.req_pos logicalhead l in
  let pairs_at p = calculation_critical_pair rule a e p in
  List.flat_map pairs_at posses
;;

let critical_pairs rules =
  let rulelen = List.length rules in
  let newenv = Environment.empty rulelen in
  let alf = Trs.get_alphabet (Trs.get_current ()) in
  let funnames = Alphabet.fun_names alf in
  let info_rename i (rule, e) =
    (i, Rule.fresh_renaming rule e newenv funnames)
  in
  let irules = List.mapi info_rename rules in
  let combinations = List.product irules irules in
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
    all_critical_pairs rule1 rule2 alf newenv allow_top
  in
  let get_ccp (i, rule) =
    all_calculation_critical_pairs rule alf newenv
  in
  let rulecriticalpairs = List.flat_map get_cp pairs in
  let calccriticalpairs = List.flat_map get_ccp irules in
  let criticalpairs = List.append calccriticalpairs rulecriticalpairs in
  (criticalpairs, newenv)
;;

let orthogonal trs =
  if Trs.is_left_linear trs then (
    let (cps, newenv) = critical_pairs (Trs.get_rules trs) in
    let empty = (cps = []) in
    Environment.drop newenv ;
    empty
  )
  else false
;;

let equivalent_under_constraint s t phis a e acceptablevar =
  (* get the relevant function symbols from the alphabet *)
  let (eq, conj, neg) =
    try
      (Alphabet.get_equal_symbol a,
       Alphabet.get_and_symbol a,
       Alphabet.get_not_symbol a)
    with Not_found -> failwith ("The equality, conjunction or " ^
      "negation symbol is not set in the alphabet; these are all " ^
      "needed to test weak orthogonality.")
  in
  (* generates pairs of acceptable variables and values which must be
  equal for s and t to be equal *)
  let rec matchem s t =
    if s = t then []
    else match (s, t) with
      | (Term.Var x, Term.Var y) ->
        if not (acceptablevar x) then raise Elogic.Not_unifiable
        else if not (acceptablevar y) then raise Elogic.Not_unifiable
        else [(s, t)]
      | (Term.Var x, _ ) ->
        if not (acceptablevar x) then raise Elogic.Not_unifiable
        else if not (Term.is_value a t) then raise Elogic.Not_unifiable
        else [(s, t)]
      | (_, Term.Var y) ->
        if not (acceptablevar y) then raise Elogic.Not_unifiable
        else if not (Term.is_value a s) then raise Elogic.Not_unifiable
        else [(s, t)]
      | (Term.Fun (f, a), Term.Fun (g, b)) ->
        if f <> g then raise Elogic.Not_unifiable ;
        List.flat_map (uncurry matchem) (List.zip a b)
      | (Term.InstanceFun (f, a, d), Term.InstanceFun (g, b, e)) ->
        if f <> g then raise Elogic.Not_unifiable ;
        if d <> e then raise Elogic.Not_unifiable ;
        List.flat_map (uncurry matchem) (List.zip a b)
      | (Term.Forall _, Term.Forall _) | (Term.Exists _, Term.Exists _) ->
        failwith ("Quantifiers outside the constraint are not " ^
                  "currently supported in the confluence module.")
      | _ -> raise Elogic.Not_unifiable
  in
  (* turn a list of term pairs into a single conjunction of many equalities,
     and negate it! *)
  let make_equality (x, y) = Term.make_function a e eq [x;y] in
  let make_equalities lst = List.map make_equality lst in
  let rec make_conj nonemptylist =
    let f term1 term2 = Term.make_function a e conj [term1;term2] in
    List.fold_left f (List.hd nonemptylist) (List.tl nonemptylist)
  in
  let make_neg_conj nonemptylist =
    Term.make_function a e neg [make_conj nonemptylist]
  in

  (* main functionality: to have that s = t [phi], for every
  substitution that maps the acceptable variables of s and t to other
  acceptable variables and respects phi, and which does nothing else,
  we must have s gamma = t gamma.  We assume that "acceptable" means:
  this variable can only be filled in with a value in a respectful
  substitution.  We also assume that non-acceptable variables do not
  have this property, and may falsely conclude non-equivalence if this
  is violated.

  First, we get the equalities required for strong unification (as in
  matchem); if they don't unify strongly, they cannot be equivalent.
  To be equivalent, we require that phi => s = t is valid or,
  limiting interest to the logical symbols, that phi => <generated
  equality> is valid.  To be non-equivalent, phi \/ NOT equality must
  be satisfiable *)
  try
    let lst = make_equalities (matchem s t) in
    if lst = [] then true
    else (
      let constr = make_neg_conj lst in
      let cs = constr :: phis in
      let smt = smtsolver () in
      Solver.unsatisfiable cs smt e
    )
  with Elogic.Not_unifiable -> false
;;

let weak_orthogonal trs =
  let a = Trs.get_alphabet trs in
  if not (Trs.is_left_linear trs) then UNKNOWN
  else (
    let (cps, newenv) = critical_pairs (Trs.get_rules trs) in
    (*List.iter print_cp cps ;*)
    let equivalent (s, t, phis) =
      let vars = List.flat_map Term.vars phis in
      let acceptable x = List.mem x vars in
      equivalent_under_constraint s t phis a newenv acceptable
    in
    let answer = List.for_all equivalent cps in
    Environment.drop newenv ;
    if answer then CONFLUENT else UNKNOWN
  )
;;

(* loops when supplied with a nonterminating system *)
let knuth_bendix verbose trs =
  let verbose = false in
  if fst (T.check verbose true trs) <> T.TERMINATING then
  UNKNOWN, "Knuth-Bendix criterion not applicable due to nontermination.\n"
  else (
    let (cps, newenv) = critical_pairs (Trs.get_rules trs) in
    (*List.iter print_cp cps ;*)
    let bounded_joinable k ((s, t, phis) as cp) =
      let ss' = Rewriter.reduce_to_normal s in
      let ts' = Rewriter.reduce_to_normal t in
      Util.List.intersect ss' ts' <> []
    in
    let all_joinable = List.for_all (bounded_joinable 5) cps in
    let c =
      if all_joinable then
      "Knuth-Bendix: The system is terminating and all CPs are joinable."
      else
      "The system is terminating but joinability of CPs could not be verified."
    in
    Environment.drop newenv;
    (if all_joinable then CONFLUENT else UNKNOWN),c ^ "\n"
  )
;;

let all verbose trs =
  if weak_orthogonal trs = CONFLUENT then CONFLUENT,"Weak orthogonality applies"
  else knuth_bendix verbose trs
;;