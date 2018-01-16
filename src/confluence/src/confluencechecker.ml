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
module P = Io.Printer;;

(*** TYPES *******************************************************************)

type possible_results = CONFLUENT | NONCONFLUENT | UNKNOWN;;
type criticalpair = Term.t * Term.t * Term.t list;;

(* context *)
type t = {
  alph: Alphabet.t;
  env: Environment.t
}

type overlap = Calc of Rule.t | Rules of (Rule.t * Rule.t)

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
  let cvars = List.unique (List.flat_map Term.vars (phis @ psis)) in
  try
    if not (Term.is_fun lsub) then []
    else (
      let gamma = Elogic.unify lsub u in
      let dom = Substitution.domain gamma in
      let apply_gamma x = Substitution.find x gamma in
      let results = List.map apply_gamma (List.intersect dom cvars) in
      if List.filter (notvarorval alphabet) results <> [] then []
      else (
        let phisgamma = List.map (Substitution.apply_term gamma) phis in
        let psisgamma = List.map (Substitution.apply_term gamma) psis in
        let together = List.union phisgamma psisgamma in
        if Solver.satisfiable together (smtsolver ()) environment then (
          let r_gamma = Substitution.apply_term gamma r in
          let v_gamma = Substitution.apply_term gamma v in
          let lv_gamma = Substitution.apply_term gamma (Term.replace pos v l) in
          [(r_gamma, lv_gamma, together)]
        )
        else []
      ))
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

let critical_pairs' rules =
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
    let cps = all_critical_pairs rule1 rule2 alf newenv allow_top in
    List.map (fun cp -> cp, Rules (rule1,rule2)) cps
  in
  let get_ccp (i, rule) =
    let cps = all_calculation_critical_pairs rule alf newenv in
    List.map (fun cp -> cp, Calc rule) cps
  in
  let rulecriticalpairs = List.flat_map get_cp pairs in
  let calccriticalpairs = List.flat_map get_ccp irules in
  (rulecriticalpairs, calccriticalpairs, newenv)
;;

let critical_pairs rules =
  let (rcps,ccps,env) = critical_pairs' rules in rcps @ ccps,env
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
    let equivalent ((s, t, phis),_) =
      let vars = List.flat_map Term.vars phis in
      let acceptable x = List.mem x vars in
      equivalent_under_constraint s t phis a newenv acceptable
    in
    let answer = List.for_all equivalent cps in
    Environment.drop newenv ;
    if answer then CONFLUENT else UNKNOWN
  )
;;

let cp_string msg ((s, t, phis),overlap) =
  let o =
    match overlap with
      | Rules (rule1,rule2) -> 
        let r1,r2 = P.to_string_rule rule1, P.to_string_rule rule2 in
        "Rules\n  " ^ r1 ^ "\n  " ^ r2 ^ "\ngive rise to the CP\n  "
      | Calc rule ->
        let r = P.to_string_rule rule in
        "Rule\n" ^ r ^ "\ngives rise to the calculation CP\n  "
  in
  let s,t = P.to_string_term s, P.to_string_term t in
  let c = P.to_string_constraints phis in
  msg ^ o ^ s ^ " = " ^ t ^ " [" ^ c ^ "]\n"
;;


let knuth_bendix verbose trs =
  if fst (T.check verbose true trs) <> T.TERMINATING then
  let c = "Knuth-Bendix criterion not applicable as termination could not be" ^
   "verified\n" in
  UNKNOWN, if verbose then c else ""
  else (
    let (cps, newenv) = critical_pairs (Trs.get_rules trs) in
    (*List.iter print_cp cps ;*)
    let joinable ((s, t, phis),_) =
      let ss' = Rewriter.reduce_to_normal s in
      let ts' = Rewriter.reduce_to_normal t in
      List.intersect ss' ts' <> []
    in
    let non_joinables = List.filter (fun cp -> not (joinable cp)) cps in
    let msg =
      if not verbose then ""
      else
        let non_joinable_msg = List.fold_left cp_string "" non_joinables in
        if non_joinables <> [] then "Non-joinable CPs:\n" ^ non_joinable_msg
        else "The system is terminating and all CPs are joinable.\n"
    in
    Environment.drop newenv;
    (if non_joinables = [] then CONFLUENT else NONCONFLUENT), msg
  )
;;

let conjunction ctxt =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let conj = Alphabet.get_and_symbol ctxt.alph in
  let top = mk_fun (Alphabet.get_top_symbol ctxt.alph) [] in
  function
    | [] -> top
    | c :: cs -> List.fold_left (fun a b -> mk_fun conj [a; b]) c cs
;;

let sat ctxt form =
  (*Format.printf "... check %s\n" (P.to_string_term form);*)
  let solver = Rewriter.smt_solver (Rewriter.get_current ()) in
  fst (Solver.satisfiable_formulas [form] solver ctxt.env) = Smtresults.SAT
;;

let tcap ctxt trs (t,phi) =
  let unifies_with u (rl, _) =
      let l,psi = Rule.lhs rl, Rule.constraints rl in
      Elogic.are_unifiable u l && sat ctxt (conjunction ctxt (phi :: psi))
  in
  let unifiable u = List.exists (unifies_with u) (Trs.get_rules trs) in
  let var s = Term.make_var (Environment.create_sorted_var s [] ctxt.env) in
  let rec tcap t =
    let sort = Term.get_sort ctxt.alph ctxt.env t in
    match t with
      | Term.Var _ -> var sort
      | Term.Fun (f, ts) ->
        let u = Term.Fun (f, List.map tcap ts) in
        if unifiable u then var sort else u
      | Term.InstanceFun (f, ts, d) ->
        let u = Term.InstanceFun (f, List.map tcap ts, d) in
        if unifiable u then var sort else u
      | Term.Forall (x,t) -> Term.Forall (x, tcap t)
      | Term.Exists (x,t) -> Term.Exists (x, tcap t)
  in tcap t
;;

let hat ctxt t =
  let sym x =
    let sort = Term.get_sort ctxt.alph ctxt.env (Term.Var x) in
    let sd = Sortdeclaration.create [] sort in
    let n = Variable.find_name x in
    Term.make_fun (Alphabet.create_fun sd ("hat"^n) ctxt.alph) []
  in
  let rec hat t =
    match t with
      | Term.Var x -> sym x
      | Term.Fun (f, ts) -> Term.Fun (f, List.map hat ts)
      | Term.InstanceFun (f, ts, d) -> Term.InstanceFun (f, List.map hat ts, d)
      | Term.Forall (x,t) -> Term.Forall (x, hat t)
      | Term.Exists (x,t) -> Term.Exists (x, hat t)
  in hat t
;;

let non_canonical_nf ((t,phi), nf) = 
  if not nf then false
  else
    let rooted syms = function
      | Term.Fun (f,_) -> List.mem (Function.find_name f) syms
      | Term.InstanceFun (f,_,_) -> List.mem (Function.find_name f) syms
      | _ -> false
    in
    let rec has_nesting syms1 syms2 = function
      | Term.Fun (f,ts) ->
        let at_root = List.mem (Function.find_name f) syms1 in
        (at_root && List.exists (rooted syms2) ts) ||
        List.exists (has_nesting syms1 syms2) ts
      | Term.InstanceFun (f,ts,_) ->
        let at_root = List.mem (Function.find_name f) syms1 in
        (at_root && List.exists (rooted syms2) ts) ||
        List.exists (has_nesting syms1 syms2) ts
      | _ -> false
    in
    let shifts = ["ashr"; "lshr";"shl"] in
    let disj = ["or"] in
    let conj = ["and"] in
    let xor = ["xor"] in
    has_nesting shifts (disj @ conj @ xor) t ||
    has_nesting disj (conj @ xor) t ||
    has_nesting conj xor t
;;

let nonjoinable_nfs ctxt ((u,nf),(v,nf')) = 
  let neq (u,phi) (v,psi) = u <> v && sat ctxt (conjunction ctxt [phi;psi]) in
  nf && nf' && neq u v  
;;

let nonjoinable_tcap ctxt trs (((u,phi),_),((v, psi),_)) =
  let u' = tcap ctxt trs (hat ctxt u, phi) in
  let v' = tcap ctxt trs (hat ctxt v, psi) in
  (*Format.printf "  tcapped %s ~ %s:\n%!" (P.to_string_term u') (P.to_string_term v');*)
  not (Elogic.are_unifiable u' v') && sat ctxt (conjunction ctxt [phi;psi])
;;

let find_nonjoinable_reducts ctxt trs ((s,t,phis),o) =
  let show_reducts (t,phi) ts =
    Format.printf "Reducts of %s:\n" (P.to_string_term t);
    let show ((u,psi),nf) =
      Format.printf "  %s [%s] %s\n"
      (P.to_string_term u) (P.to_string_term psi) (if nf then "NF" else "")
    in
    List.iter show ts;
    Format.printf "\n%!"
  in
  let phi = conjunction ctxt phis in
  (* calc simp gen *)
  let rewrite = Constrainedrewriter.rewrite_bounded false false true trs 2 in
  (*Format.printf "Rewrite %s = %s\n  [%s]\n" (P.to_string_term s)
    (P.to_string_term t) (P.to_string_term phi);*)
  let ss = rewrite (s,phi) in
  let ts = rewrite (t,phi) in
  (*show_reducts (t,phi) ts;
  show_reducts (s,phi) ss;
  Format.printf "check conditions\n%!";*)
  let nonjoinable ((((u,phi),_),((v,psi),_)) as uv) =
    if nonjoinable_nfs ctxt uv then (
      Format.printf "%s" (cp_string "" ((s,t,phis),o));
      Format.printf "and the reduct pair %s ~ %s [%s]:\n"
        (P.to_string_term u) (P.to_string_term v)
        (P.to_string_term (conjunction ctxt [phi;psi]));
      Format.printf "    nonjoinable NFs found\n\n%!";
      true
    ) else false
  in
  let check_nfs ((t,phi),nf) =
    if non_canonical_nf ((t,phi),nf) then (
    Format.printf "%s" (cp_string "" ((s,t,phis),o));
    Format.printf " gives rise to possibly non-canonical NF\n   %s\n   [%s]\n%!"
      (Term.to_string t) (Term.to_string phi))
  in
  List.map check_nfs ss;
  List.map check_nfs ts;
  List.exists nonjoinable (List.product ss ts)
;;

(* replaces the variables of [rule] by variables in [newenv] *)
let update_environment newenv alf (rule, oldenv) =
  try Rule.environment_transfer rule oldenv newenv (Alphabet.fun_names alf), newenv
  with Failure msg ->
    failwith ("Variable error with rule " ^ (Rule.to_string rule) ^
              ": " ^ msg)
;;

let nonconfluence verbose trs =
  let alph = Trs.get_alphabet trs in
  let e = Trs.get_main_environment trs in
  let rls = Trs.get_rules trs in
  let not_flag_removing (rl,_) =
    let l,r,c = Rule.lhs rl, Rule.rhs rl, Rule.constraints rl in
    match l,r with
      | Term.Fun (f,_), Term.Fun(g,_) ->
        let fn,gn = Function.find_name f, Function.find_name g in
        not (Term.size l = 3 && Term.size r = 3 &&
             String.length fn > String.length gn &&
             String.equal (String.sub fn 0 (String.length gn)) gn)
      | _ -> true
  in
  let rls' = List.filter not_flag_removing rls in
  let (cps, _, newenv) = critical_pairs' rls' in

  (*if Util.query_debugging () then*) Format.printf "%d CPs computed\n%!"
    (List.length cps);
  let ctxt = { alph = alph; env = newenv} in
  let rules = Trs.get_rules trs in
  let rules' = List.map (update_environment newenv alph) rules in
  let trs' = Trs.create alph newenv in
  Trs.set_rules rules' trs';

  let non_joinables = List.filter (find_nonjoinable_reducts ctxt trs') cps in
  let msg =
    if not verbose then ""
    else
      let non_joinable_msg = List.fold_left cp_string "" non_joinables in
      if non_joinables <> [] then
        let n = (string_of_int (List.length non_joinables)) in
        n ^ " non-joinable peaks:\n" ^ non_joinable_msg
      else ""
  in
  Format.printf "%s\n%!" msg;
  Environment.drop newenv;
  (if non_joinables = [] then UNKNOWN else NONCONFLUENT), msg
;;

let all verbose trs =
  if weak_orthogonal trs = CONFLUENT then CONFLUENT,"Weak orthogonality applies"
  else match nonconfluence verbose trs with
    | NONCONFLUENT, msg -> NONCONFLUENT, msg
    | r -> r(*knuth_bendix verbose trs*)
;;