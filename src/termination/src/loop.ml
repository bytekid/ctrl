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
open Util;;

(*** MODULES ******************************************************************)
module L = List
module H = Hashtbl
module LL = LazyList
module Sub = Substitution
module P = Io.Printer
module Alph = Alphabet
module Rewriter = Rewriting.Rewriter
module Pos = Position
module Ctx = Context
module T = Term

(*** TYPES ********************************************************************)
type t_unfold = Forward | Backward

(* context *)
type t = {
  alph: Alph.t;
  env: Environment.t;
  max_length: int;
  max_size: int;
  max_rule_inc: int;
  unfold : t_unfold
}

(* loop candidate *)
type seq = Rule.t * (Rule.t * Pos.t * T.t) list * Sub.t

(*** GLOBALS ******************************************************************)
let check_time = ref 0.;;
let loop_count = ref 0;;
let seq_cache : (int, seq list) H.t = H.create 5096;;
let constr_sat_cache : (T.t, bool) H.t = H.create 1024;;

(*** FUNCTIONS ****************************************************************)
let is_forward c = c.unfold = Forward

let rule (a,_,_) = a

(* Create a context record. *)
let mk_ctxt a e ml ms inc u = {
  alph = a;
  env = e;
  max_length = ml;
  max_size = ms;
  max_rule_inc = inc;
  unfold = u
}

(* Returns the SMT-solver we will use (just the default) *)
let smt () = Rewriter.smt_solver (Rewriter.get_current ());;

(* String representation of loop. *)
let sequence_to_string (st, rs) =
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
  fst (L.fold_left add_step (sstr ^ " -> \n", Rule.lhs st) rs)
;;

(* String representation of constraints. *)
let constraints_to_string = function
    [] -> ""
  | [c] -> P.to_string_term c
  | c :: cs ->
    let add_constr str c = (P.to_string_term c) ^ " /\\ " ^ str in
    L.fold_left add_constr (P.to_string_term c) cs
;;

(* String representation of loop, with explanation. *)
let explanation ((rl,_) as loop) =
  let cs = Rule.constraints rl in
  let cexp = " with side condition " ^ (constraints_to_string cs) in
  "A loop is given by the sequence \n" ^ (sequence_to_string loop) ^
  (if cs = [] then "" else cexp ^ " (" ^ (string_of_float !check_time) ^ ")\n" )
;;

let show loop =
  let s = explanation loop in
  Format.printf "%d. %s\n%!" !loop_count s;
  loop_count := !loop_count + 1
;;

let explain_all loops =
  let rec explain_all xs =
    if xs <> [] then (
    show (L.hd xs);
    explain_all (L.tl xs))
  in explain_all loops
;;

let substr sigma =
  let xstr x = P.to_string_term (T.make_var x) in
  let app x t s = " " ^ (xstr x) ^ " -> " ^ (P.to_string_term t) ^ "\n" ^ s in
  "{" ^ (Sub.fold app sigma "}")
;;

(* *** properties of sequences ********************************************** *)
let rule_lhs (rl, _,_) = Rule.lhs rl;;
let rule_rhs (rl, _,_) = Rule.rhs rl;;
let size_increasing seq = T.size (rule_lhs seq) < T.size (rule_rhs seq);;
let size_decreasing seq = T.size (rule_lhs seq) > T.size (rule_rhs seq);;
let size_keeping seq = T.size (rule_lhs seq) = T.size (rule_rhs seq);;
let same_root seq seq' = T.root (rule_rhs seq) = T.root (rule_lhs seq');;

let seq_has_dp_root c (rl, _,_) =
 match T.root (Rule.lhs rl) with
   | None -> false
   | Some f ->
     let n = Function.find_name f in
     String.get n (String.length n - 1) = '#'
;;

let subst_terms sigma = List.map (fun (rl,p,t) -> (rl,p,Sub.apply_term sigma t))

(* *** some logic stuff to check loop conditions **************************** *)
let conjunction ctxt =
  let mk_fun = T.make_function ctxt.alph ctxt.env in
  let conj = Alph.get_and_symbol ctxt.alph in
  let top = mk_fun (Alph.get_top_symbol ctxt.alph) [] in
  function
    | [] -> top
    | c :: cs -> L.fold_left (fun a b -> mk_fun conj [a; b]) c cs
;;

let logical_check check ctxt f =
  let not_logical = T.check_logical_term ctxt.alph f <> None in
  if not_logical then false
  else check [f] (smt ()) ctxt.env
;;

let logical_sat = logical_check Smt.Solver.satisfiable

let logical_valid = logical_check Smt.Solver.valid

(* (1) Given constraints cs and a loop substitution sigma, check whether
   cs => cs sigma is a logical term and valid. *)
let condition1 ctxt cs sigma =
  let mk_fun = T.make_function ctxt.alph ctxt.env in
  let disj = Alph.get_or_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let c1 = conjunction ctxt cs in
  let c2 = Sub.apply_term sigma c1 in
  let c = mk_fun disj [mk_fun neg [c1]; c2] in
  let valid = logical_valid ctxt c in
  if not valid then None
  else (
    let r = Smt.Solver.satisfiable_formulas [c1] (smt ()) ctxt.env in
    if fst r = Smt.Smtresults.SAT then Some (snd r)
    else failwith "Loop.condition1: unsatisfiable constraint")
;;

(* (4) Given constraints cs and a loop substitution sigma, check whether
   cs sigma is logical, and, if yes,
   cs /\ \bigwedge_{x \in Dom(sigma)} (x = x sigma) is satisfiable. If yes,
   the resulting substitution is a loop witness *)
let refined_condition2 rl ctxt cs sigma =
  let mk_fun = T.make_function ctxt.alph ctxt.env in
  let eq = Alph.get_equal_symbol ctxt.alph in
  let app x t cs = (mk_fun eq [T.make_var x; t]) :: cs in
  let c = conjunction ctxt (Sub.fold app sigma cs) in
  let not_logical = T.check_logical_term ctxt.alph c <> None in
  if not_logical then None
  else (
    let r = Smt.Solver.satisfiable_formulas [c] (smt ()) ctxt.env in
    (if Util.query_debugging () then
      Format.printf "Condition (2) on rule %s, substitution %s\n%!"
        (P.to_string_rule rl) (substr (snd r)));
    if fst r = Smt.Smtresults.SAT then Some (snd r) else None)
;;


(* (5) Given constraints cs and a loop substitution \sigma. Let
   X \subseteq Dom(\sigma) be the variables x such that x\sigma = x, and
   Y = Dom(\sigma) - X be the variables y such that y\sigma != y. Check whether
   \forall Y.(cs => cs\sigma) /\ cs [Y \mapsto Z] for fresh variables is
   satisfiable. If yes, the resulting substitution is a loop witness.
   cs sigma is logical, and, if yes, 
   cs /\ \bigwedge_{x \in Dom(sigma)} (x = x sigma) is satisfiable. If yes,
   the resulting substitution is a loop witness *)
let refined_condition3 rl ctxt cs sigma =
  let fresh_rep sub y =
    let s = T.get_sort ctxt.alph ctxt.env (T.Var y) in
    Sub.add y (T.make_var (Environment.create_sorted_var s [] ctxt.env)) sub 
  in
  let mk_fun = T.make_function ctxt.alph ctxt.env in
  let disj = Alph.get_or_symbol ctxt.alph in
  let conj = Alph.get_and_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let not_rl x = not (L.mem x (Rule.vars rl)) in
  let app x t vs = if T.Var x = t || not_rl x then vs else x::(T.vars t) @ vs in
  let ys = L.unique (Sub.fold app sigma []) in
  let ys = L.intersect ys (Rule.vars rl) in
  let ys_zs = L.fold_left fresh_rep Sub.empty ys in
  let c = conjunction ctxt cs in
  let csigma = Sub.apply_term sigma c in
  let imp = mk_fun disj [mk_fun neg [c]; csigma] in
  let phi = mk_fun conj [imp; Sub.apply_term ys_zs c] in
  let not_logical = T.check_logical_term ctxt.alph phi <> None in
  if not_logical then None
  else (
    let r = Smt.Solver.forall_satisfiable ys phi (smt ()) ctxt.env in
    (if Util.query_debugging () then
      let yss = L.fold_left (fun s x -> s^" "^(P.to_string_term (T.Var x))) in
      Format.printf "Condition (3) on rule %s, qvs %s is substitution %s\n%!"
        (P.to_string_rule rl) (yss "" ys) (substr (snd r)));
    if fst r <> Smt.Smtresults.SAT then None
    else Some (Sub.compose Sub.apply_term ys_zs (snd r)))
;;

(* Check whether constraints cs are satisfiable. *)
let constr_sat ctxt cs =
  let mk_fun = T.make_function ctxt.alph ctxt.env in
  let conj = Alph.get_and_symbol ctxt.alph in
  let top = mk_fun (Alph.get_top_symbol ctxt.alph) [] in
  let conj_cs = L.fold_left (fun a b -> mk_fun conj [a; b]) top cs in
  try H.find constr_sat_cache conj_cs
  with Not_found ->
    let res = logical_sat ctxt conj_cs in
    H.add constr_sat_cache conj_cs res;
    res
;;

(* Criterion for loop being redundant (output is suppressed):
   - initial rule maximal to avoid copies (this is already partially
    filtered out in narrow, but if loop length is smaller or equal than half of
    original loop length it's still returned) *)
let loop_init_rule_maximal c (_,rpts) =
  let rs = L.map rule rpts in
  let rl0, rs' =
    if is_forward c then L.hd rs, L.tl rs
    else L.last rs, L.take (L.length rs - 1) rs
  in
  L.for_all (fun rl -> Rule.compare rl rl0 <= 0) rs'
;;

let init_rule_maximal c (st,rpts,_) = loop_init_rule_maximal c (st,rpts)

(* Check whether the given rewrite sequence constitutes a loop; to that end
   it is checked whether the initial term unifies with (a subterm of) the final
   term, and constraint conditions are satisfied. *)
let check ctxt (rule, rs, sigma) =
  let start = Unix.gettimeofday () in
  let (s, t) = Rule.to_terms rule in
  let cs = Rule.constraints rule in
  let check' get_subst t' b =
    try
      let tau = get_subst t' s in
      let sigma' = Sub.compose Sub.apply_term sigma tau in
      let rule' = if b then Rule.apply_sub tau rule else rule in
      let rs' = if b then subst_terms tau rs else rs in
      let sub_map rho = (Rule.apply_sub rho rule', subst_terms rho rs') in
      let res1 = Option.map sub_map (condition1 ctxt cs sigma') in
      if Option.is_some res1 then res1
      else
        let res2 = refined_condition2 rule ctxt cs sigma' in
        if Option.is_some res2 then Option.map sub_map res2
        else Option.map sub_map (refined_condition3 rule ctxt cs sigma')
    with Elogic.Not_unifiable | Elogic.Not_matchable -> None
  in
  (* Only return loops starting with a DP symbol to avoid duplicates. *)
  if not (constr_sat ctxt cs) then None
  else
    let check t' =
      match check' Elogic.match_term t' false with
        | Some loop -> Some loop
        | None -> ( match check' Elogic.unify t' true with
          | Some loop -> Some loop
          | None -> None)
    in
    let res = check t in
    check_time := !check_time +. Unix.gettimeofday () -. start;
    res
;;

let check_all c seqs =
  let chk (ls,ss) s = match check c s with Some l -> l::ls,ss | _ -> ls,s::ss in
  let seqs = L.filter (seq_has_dp_root c) seqs in
  let loops, seqs = List.fold_left chk ([],[]) seqs in
  let loops, seqs = L.filter (loop_init_rule_maximal c) loops, seqs in
  if Util.query_debugging () then
    explain_all loops;
  loops, seqs
;;

(* Shorthand to rename a rule. *)
let rename_rule c rule =
  let rho = Elogic.renaming [Rule.lhs rule; Rule.rhs rule] [] c.env in
  Rule.apply_sub rho rule, rho
;;

let to_ctxt ctx (rl,q,t) = (rl,Pos.append (Ctx.hole_pos ctx) q,Ctx.apply t ctx)

let sub_constr_sat c cs tau = constr_sat c (L.map (Sub.apply_term tau) cs)

(* Narrow last term in sequence using given rule at position p. *)
let forward c (st,rs,sigma) p (rl,rs',sigma') =
  let rule',rho = rename_rule c rl in
  let l,r = Rule.lhs rule', Rule.rhs rule' in
  try
    let s,t = Rule.lhs st, Rule.rhs st in
    let mgu = Elogic.unify (T.subterm p t) l in
    let rs = subst_terms mgu rs in
    let rs' = subst_terms (Sub.compose Sub.apply_term rho mgu) rs' in
    let cnstr = Rule.constraints st @ (Rule.constraints rule') in
    let sigma' = Sub.compose Sub.apply_term sigma mgu in
    if not (sub_constr_sat c cnstr sigma') then []
    else
      let st' = Rule.apply_sub mgu (Rule.create s (T.replace p r t) cnstr) in
      let ctxt_rs = List.map (to_ctxt (Ctx.of_term p t)) rs' in
      [st', rs @ ctxt_rs, sigma']
  with Elogic.Not_unifiable -> []
;;

(* Try to narrow subterm of lhs of seq forward or backwards using rule. *)
let narrow c (st,rs,sigma) p (rl,rs',sigma') =
  let rule',rho = rename_rule c rl in
  let l,r = Rule.lhs rule', Rule.rhs rule' in
  let fw = is_forward c in
  try
    let s,t = Rule.lhs st, Rule.rhs st in
    let t_st,t_rl = if fw then T.subterm p t,l else T.subterm p s,r in
    let mgu = Elogic.unify t_st t_rl in
    let rs = subst_terms mgu rs in
    let rs' = subst_terms (Sub.compose Sub.apply_term rho mgu) rs' in
    let cnstr = Rule.constraints st @ (Rule.constraints rule') in
    let sigma' =
      if fw then Sub.compose Sub.apply_term sigma mgu
      else Sub.compose Sub.apply_term mgu sigma
    in
    if not (sub_constr_sat c cnstr sigma') then []
    else
      let u,v = if fw then s,T.replace p r t else T.replace p l s,t in
      let st' = Rule.apply_sub mgu (Rule.create u v cnstr) in
      let ctxt_rs = L.map (to_ctxt (Ctx.of_term p (if fw then t else s))) rs' in
      [st', (if fw then rs @ ctxt_rs else ctxt_rs @ rs), sigma']
  with Elogic.Not_unifiable -> []
;;

let last (_,rs,_) c = L.length rs + 1 = c.max_length

let root_changes rl = T.root (Rule.lhs rl) <> T.root (Rule.rhs rl)

(* Do unfold narrowing using rules in trs from last terms in sequence, trying
   possible rules and positions. For the rules to be applied at the root
    srem(X, shl(A, B)) -> srem(X, shl_nuw(A, B))  [ (isPowerOf2(A) /\ hasOneUse)] ; /* MulDivRem 8*/
   (typically dependency pairs) only consider rules which are smaller or equal
   to the first rule (with respect to some arbitrary order), to avoid redundant
   representations of same loop that start at different term. *)
let size_filter seq rl_seqs =
  if size_decreasing seq then L.filter size_increasing rl_seqs else rl_seqs
;;

(* If is_final is true then we are only interested in loops where the added
   step is the final step.  *)
let unfold c do_all is_final (rs_root, rs_below) ((st,rs,_) as seq) =
  (* If final and different symbols at root, must rewrite at root.*)
  let rs_below = if is_final && root_changes st then [] else rs_below in
  (* If final and size decrease so far, restrict to size-increasing rules.*)
  let rs_root, rs_below =
    Pair.map (if is_final then size_filter seq else id) (rs_root, rs_below)
  in
  let rs_root = L.filter (same_root seq) rs_root in
  let rs_root =
    let r0,_,_ = L.nth rs (if is_forward c then 0 else L.length rs - 1) in
    if do_all then rs_root
    else L.filter (fun rl_seq -> Rule.compare (rule rl_seq) r0 <= 0) rs_root
  in
  let rlps_root = (L.map (Util.Pair.make Pos.root) rs_root) in
  let term = if is_forward c then Rule.rhs st else Rule.lhs st in
  let ps = L.remove Pos.root (T.funs_pos term) in
  let rlps = rlps_root @ (L.product ps rs_below) in
  let seqs = L.flat_map (fun (p,rl) -> narrow c seq p rl) rlps in
  check_all c seqs
;;

(* Checking whether the sequence does not exceed the maximal term size. *)
let small c (st,_,_) =
  T.size (Rule.lhs st) <= c.max_size && T.size (Rule.lhs st) <= c.max_size
;;

let within_step ctx seq =
  T.size (rule_lhs seq) - T.size (rule_rhs seq) <= ctx.max_rule_inc
;;

let within_2_steps ctx seq =
  T.size (rule_lhs seq) - T.size (rule_rhs seq) <= ctx.max_rule_inc * 2
;;

(* Do unfolding, trying all possible rules and positions but eliminating
   sequences that exceed the bounds.
   Use previously computed results of shorter sequences. *)
let rec unfold_all c ruleseqs i (loops,seqs) =
  let len = i + 1 in
  if len > c.max_length then loops
  else (
    (* determine whether we can use precomputed result*)
    let seqs, ruleseqs =
      if len < 5 then seqs, ruleseqs
      else
        let j = (len + 1) / 2 in
        let rlseqs = H.find seq_cache (len - j) in
        H.find seq_cache j, L.partition (seq_has_dp_root c) rlseqs
    in
    let do_all = len <= c.max_length / 2 in
    let is_final = len > (c.max_length + 1) / 2 in
    (* if the currently computed sequences are not required for a computation
       step later on, we can restrict to those starting with a DP symbol *)
    let seqs = if do_all then seqs else L.filter (seq_has_dp_root c) seqs in
    (* Wlog assume that first/last rule is maximal (to avoid duplicates) *)
    let seqs = if do_all then seqs else L.filter (init_rule_maximal c) seqs in
    let fold_unfold (loops', seqs') seq =
      let lps, sqs = unfold c do_all is_final ruleseqs seq in
      L.rev_append lps loops', L.rev_append sqs seqs'
    in
    let rs1, rs2 = ruleseqs in
    if Util.query_debugging () then
      Format.printf "Combining %d sequences of length %d with %d rules %i\n%!"
        (L.length seqs) i (L.length rs1 + (L.length rs2))
        (if do_all then 1 else 0);
    let seqss =
      if is_final then L.filter (within_step c) seqs
      else if len <> (c.max_length + 1) / 2 then seqs
      else L.filter (within_2_steps c) seqs 
    in
    let loops, seqs' = L.fold_left fold_unfold (loops,[]) seqss in
    let seqs'' = L.filter (small c) seqs' in
    if seqs'' = [] then loops
    else (
      H.add seq_cache len seqs'';
      unfold_all c ruleseqs len (loops,seqs'')))
;;

(* The initial sequence, starting from a rule. *)
let init_seq rule = (rule, [rule, Position.root, Rule.rhs rule], Sub.empty);;
let init_seqs = L.map init_seq;;

(* Generates loops, starting from rule set rules and using the step function
   to extend sequences. *)
let generate_loops ctxt init_seqs step = step 1 (check_all ctxt init_seqs)

let max_diff rls = 
  let m = List.fold_left (fun m rl ->
    let l,r = Rule.lhs rl, Rule.rhs rl in
    max m (T.size r - (T.size l))) 0 rls in
  (*Format.printf "max term size diff is %d\n%!" m;*)
  m
;;

let non_size_dec =
  List.filter (fun rl -> Term.size (Rule.lhs rl) <= Term.size (Rule.rhs rl))

(* Main functionality *)
let process verbose prob =
  let dps = Dpproblem.get_dps prob in
  let rules = Dpproblem.get_rules prob in
  max_diff rules;
  let alph = Dpproblem.get_alphabet prob in
  let env = Dpproblem.get_environment prob in
  let maxlen = 7 in
  let ctxt = mk_ctxt alph env maxlen 25 (max_diff rules) Forward in
  let dprlseqs = Pair.map init_seqs (dps, rules) in
  let init_seqs = fst dprlseqs @ (snd dprlseqs) in
  let loops = generate_loops ctxt init_seqs (unfold_all ctxt dprlseqs) in
  if loops = [] then None
  else
    let e = "We use the loop processor to conclude nontermination.\n" in
    Some ([ ],  e ^ (explanation (L.hd loops)))
;;

