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

let check_time = ref 0.;;
let loop_count = ref 0;;
let seq_cache : (int, seq list) H.t = H.create 5096;;
let constr_sat_cache : (Term.t, bool) H.t = H.create 1024;;

let rule (a,_,_) = a

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
let explanation ((rl,_,_) as loop) =
  let cs = Rule.constraints rl in
  "A loop is given by the sequence \n" ^ (sequence_to_string loop) ^
  (if cs = [] then "" else " if " ^ (constraints_to_string cs) ^ " (" ^ (string_of_float !check_time) ^ ")\n" )
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
  let xstr x = P.to_string_term (Term.make_var x) in
  let app x t s = " " ^ (xstr x) ^ " -> " ^ (P.to_string_term t) ^ "\n" ^ s in
  "{" ^ (Sub.fold app sigma "}")
;;

(* *** properties of sequences ********************************************** *)
let rule_lhs (rl, _,_) = Rule.lhs rl;;
let rule_rhs (rl, _,_) = Rule.rhs rl;;
let size_increasing seq = Term.size (rule_lhs seq) < Term.size (rule_rhs seq);;
let size_decreasing seq = Term.size (rule_lhs seq) > Term.size (rule_rhs seq);;
let size_keeping seq = Term.size (rule_lhs seq) = Term.size (rule_rhs seq);;
let same_root seq seq' = Term.root (rule_rhs seq) = Term.root (rule_lhs seq');;

let seq_has_dp_root c (rl, _,_) =
 match Term.root (Rule.lhs rl) with
   | None -> false
   | Some f ->
     let n = Function.find_name f in
     String.get n (String.length n - 1) = '#'
;;

let subst_terms sigma = List.map (fun (rl,p,t) -> (rl,p,Sub.apply_term sigma t))

(* *** some logic stuff to check loop conditions **************************** *)
let conjunction ctxt =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let conj = Alph.get_and_symbol ctxt.alph in
  let top = mk_fun (Alph.get_top_symbol ctxt.alph) [] in
  function
    | [] -> top
    | c :: cs -> L.fold_left (fun a b -> mk_fun conj [a; b]) c cs
;;

let logical_check check ctxt f =
  let not_logical = Term.check_logical_term ctxt.alph f <> None in
  if not_logical then false
  else check [f] (smt ()) ctxt.env
;;

let logical_sat = logical_check Smt.Solver.satisfiable

let logical_valid = logical_check Smt.Solver.valid

(* (1) Given constraints cs and a loop substitution sigma, check whether
   cs => cs sigma is a logical term and valid. *)
let condition1 ctxt cs sigma =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let disj = Alph.get_or_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let c1 = conjunction ctxt cs in
  let c2 = Sub.apply_term sigma c1 in
  let c = mk_fun disj [mk_fun neg [c1]; c2] in
  let r = logical_valid ctxt c in
  r
;;

(* (3) Given constraints cs and a loop substitution sigma, check whether
   cs => lcap(cs sigma) is valid. *)
let condition3 ctxt cs sigma =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let disj = Alph.get_or_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let c1 = conjunction ctxt cs in
  let c2 = Term.logical_cap ctxt.alph ctxt.env (Sub.apply_term sigma c1) in
  let c = mk_fun disj [mk_fun neg [c1]; c2] in
  let r = logical_valid ctxt c in
  r
;;

(* (4) Given constraints cs and a loop substitution sigma, check whether
   cs sigma is logical, and, if yes, 
   cs /\ \bigwedge_{x \in Dom(sigma)} (x = x sigma) is satisfiable. If yes,
   the resulting substitution is a loop witness *)
let refined_condition4 ctxt cs sigma =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let eq = Alph.get_equal_symbol ctxt.alph in
  let app x t cs = (mk_fun eq [Term.make_var x; t]) :: cs in
  let c = conjunction ctxt (Sub.fold app sigma cs) in
  let not_logical = Term.check_logical_term ctxt.alph c <> None in
  if not_logical then None
  else (
    let r = Smt.Solver.satisfiable_formulas [c] (smt ()) ctxt.env in
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
let refined_condition5 ctxt cs sigma =
  let fresh_rep sub y =
    let s = Term.get_sort ctxt.alph ctxt.env (Term.Var y) in
    Sub.add y (Term.make_var (Environment.create_sorted_var s [] ctxt.env)) sub 
  in
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let disj = Alph.get_or_symbol ctxt.alph in
  let conj = Alph.get_and_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let ys = Sub.fold (fun x _ vs -> x::vs) sigma [] in
  let ys_zs = L.fold_left fresh_rep Sub.empty ys in
  let c = conjunction ctxt cs in
  let csigma = Sub.apply_term sigma c in
  let imp = mk_fun disj [mk_fun neg [c]; csigma] in
  let phi = mk_fun conj [imp; Sub.apply_term ys_zs c] in 
  let not_logical = Term.check_logical_term ctxt.alph phi <> None in
  if not_logical then None
  else (
    Format.printf "TEST new condition\n%!";
    let r = Smt.Solver.forall_satisfiable ys phi (smt ()) ctxt.env in
    if fst r = Smt.Smtresults.SAT then
     Format.printf "results in substitution %s\n%!" (substr (snd r));
    if fst r = Smt.Smtresults.SAT then Some (snd r) else None)
;;

let refined_condition6 ctxt cs sigma =
  let fresh_rep sub y =
    let s = Term.get_sort ctxt.alph ctxt.env (Term.Var y) in
    Sub.add y (Term.make_var (Environment.create_sorted_var s [] ctxt.env)) sub 
  in
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let disj = Alph.get_or_symbol ctxt.alph in
  let conj = Alph.get_and_symbol ctxt.alph in
  let neg = Alph.get_not_symbol ctxt.alph in
  let ys = Sub.fold (fun x _ vs -> x::vs) sigma [] in
  let ys_zs = L.fold_left fresh_rep Sub.empty ys in
  let c = conjunction ctxt cs in
  let csigma = Sub.apply_term sigma c in
  let csigma' = Term.logical_cap ctxt.alph ctxt.env csigma in
  let zs = L.diff (Term.vars csigma') (Term.vars csigma) in
  let imp = mk_fun disj [mk_fun neg [c]; csigma'] in
  let phi = mk_fun conj [imp; Sub.apply_term ys_zs c] in 
 (
    Format.printf "TEST new condition\n%!";
    let r = Smt.Solver.forall_satisfiable (zs @ ys) phi (smt ()) ctxt.env in
    if fst r = Smt.Smtresults.SAT then
     Format.printf "results in substitution %s\n%!" (substr (snd r));
    if fst r = Smt.Smtresults.SAT then Some (snd r) else None)
;;

(* Check whether constraints cs are satisfiable. *)
let constr_sat ctxt cs =
  let mk_fun = Term.make_function ctxt.alph ctxt.env in
  let conj = Alph.get_and_symbol ctxt.alph in
  let top = mk_fun (Alph.get_top_symbol ctxt.alph) [] in
  let conj_cs = L.fold_left (fun a b -> mk_fun conj [a; b]) top cs in
  try H.find constr_sat_cache conj_cs
  with Not_found ->
    let res = logical_sat ctxt conj_cs in
    H.add constr_sat_cache conj_cs res;
    res
;;

(* Check whether the given rewrite sequence constitutes a loop; to that end
   it is checked whether the initial term unifies with (a subterm of) the final
   term, and constraint conditions are satisfied. *)
let check' ctxt (rule, rs, sigma) =
  let start = Unix.gettimeofday () in
  let (s, t) = Rule.to_terms rule in
  let cs = Rule.constraints rule in
  let check' get_subst t' b =
    try
      let tau = get_subst t' s in
      let sigma' = Sub.compose Sub.apply_term sigma tau in
      let rule' = if b then Rule.apply_sub tau rule else rule in
      if condition1 ctxt cs sigma' then
        Some (rule', subst_terms tau rs, sigma')
      else (
        match refined_condition5 ctxt cs sigma' with
          | None -> None
          | Some rho ->
            let rule'' = Rule.apply_sub rho rule' in
            Some (rule'', rs, Sub.compose Sub.apply_term sigma' rho))
    with Elogic.Not_unifiable | Elogic.Not_matchable -> None
  in
  if not (constr_sat ctxt cs) then []
  else
    let check t' =
      match check' Elogic.match_term t' false with
        | Some loop -> [loop]
        | None -> ( match check' Elogic.unify t' true with
          | Some loop -> [loop]
          | None -> [])
    in
    let res = check t in
    check_time := !check_time +. Unix.gettimeofday () -. start;
    explain_all res;
    res
;;
(* Only return loops starting with a DP symbol to avoid duplicates. *)
let check c seq = if not (seq_has_dp_root c seq) then [] else check' c seq

(* Shorthand to rename a rule. *)
let rename_rule c rule =
  let newenv = Environment.empty 10 in
  Rule.rename rule c.env
;;

let to_ctxt ctx (rl,q,t) = (rl,Pos.append (Ctx.hole_pos ctx) q,Ctx.apply t ctx)

(* Narrow last term in sequence using given rule at position p. *)
let narrow c ((st,rs,sigma) as seq) p (rl,rs',sigma') =
  let rule' = rename_rule c rl in
  let l,r = Rule.lhs rule', Rule.rhs rule' in
  try
    let s,t = Rule.lhs st, Rule.rhs st in
    let mgu = Elogic.unify (Term.subterm p t) l in
    let constr = Rule.constraints st @ (Rule.constraints rule') in
    let st' = Rule.apply_sub mgu (Rule.create s (Term.replace p r t) constr) in
    let sigma' = Sub.compose Sub.apply_term sigma mgu in
    let ctxt_rs = List.map (to_ctxt (Ctx.of_term p t)) rs' in
    [st', rs @ ctxt_rs, sigma']
  with Elogic.Not_unifiable -> []
;;

let last (_,rs,_) c = L.length rs + 1 = c.max_length

let root_changes rl = Term.root (Rule.lhs rl) <> Term.root (Rule.rhs rl)

(* Do forward narrowing using rules in trs from last terms in sequence, trying
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
let forward c do_all is_final (rs_root, rs_below) ((st,rs,_) as seq) =
  (* If final and different symbols at root, must rewrite at root.*)
  let rs_below = if is_final && root_changes st then [] else rs_below in
  (* If final and size decrease so far, restrict to size-increasing rules.*)
  let rs_root, rs_below =
    Pair.map (if is_final then size_filter seq else id) (rs_root, rs_below)
  in
  let rs_root = L.filter (same_root seq) rs_root in
  let rs_root =
    let r0,_,_ = L.nth rs 0 in
    if do_all then rs_root
    else L.filter (fun rl_seq -> Rule.compare (rule rl_seq) r0 <= 0) rs_root
  in
  let rlps_root = (L.map (Util.Pair.make Pos.root) rs_root) in
  let ps = L.remove Pos.root (Term.funs_pos (Rule.rhs st)) in
  let rlps = rlps_root @ (L.product ps rs_below) in
  let seqs = L.flat_map (fun (p,rl) -> narrow c seq p rl) rlps in
  L.partition (fun seq -> check c seq <> []) seqs
;;

(* Checking whether the sequence does not exceed the maximal term size. *)
let small c (st,_,_) =
  Term.size (Rule.lhs st) <= c.max_size && Term.size (Rule.lhs st) <= c.max_size
;;

let seq_sat c (rl,_,tau) =
  constr_sat c (L.map (Sub.apply_term tau) (Rule.constraints rl))
;;

let first_rule_maximal (_,rpts,_) =
  match L.map rule rpts with
    | rl0 :: rs -> L.for_all (fun rl -> Rule.compare rl rl0 <= 0) rs
    | [] -> failwith "Loop.first_rule_maximal: empty rule set"
;;

(* Do forward narrowing from last terms in sequences, trying all possible
   rules and positions but eliminating sequences that exceed the bounds.
   Use previously computed results of shorter sequences. *)
let rec all_forward c ruleseqs i (loops,seqs) =
  let len = i + 1 in
  if len > c.max_length then loops
  else (
    Format.printf "Looking for sequences of length %d\n%!" len;
    (* determine whether we can use precomputed result*)
    let seqs, ruleseqs =
      if len < 4 then seqs, ruleseqs
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
    (* Wlog assume that first rule is maximal (to avoid duplicates) *)
    let seqs = if do_all then seqs else L.filter first_rule_maximal seqs in
    let useful seq = small c seq && (seq_sat c seq) in
    let fw (loops', seqs') seq =
      let lps, sqs = forward c do_all is_final ruleseqs seq in
      L.rev_append lps loops', L.rev_append sqs seqs'
    in
    let rs1, rs2 = ruleseqs in
    Format.printf "Combining %d sequences of length %d with %d rules\n%!"
      (L.length seqs) i (L.length rs1 + (L.length rs2));
    let loops, seqs' = L.fold_left fw (loops,[]) seqs in
    let seqs'' = L.filter useful seqs' in
    Format.printf "Found %d sequences of length %d\n%!" (L.length seqs'') len;
    if seqs'' = [] then loops
    else (
      H.add seq_cache len seqs'';
      all_forward c ruleseqs len (loops,seqs'')))
;;

(* The initial sequence, starting from a rule. *)
let init_seq rule = (rule, [rule, Position.root, Rule.rhs rule], Sub.empty);;
let init_seqs = L.map init_seq;;

(* Generates loops, starting from rule set rules and using the step function
   to extend sequences.
*)
let generate_loops ctxt init_seqs step =
  let lps, seqs = L.partition (fun seq -> check ctxt seq <> []) init_seqs in
  let loops = step 1 (lps, seqs) in
  loops
;;
(* Main functionality *)
let process verbose prob =
  Format.printf "Go looping %f\n%!" !check_time;
  let dps = Dpproblem.get_dps prob in
  let rules = Dpproblem.get_rules prob in
  let alph = Dpproblem.get_alphabet prob in
  let env = Dpproblem.get_environment prob in
  let maxlen = 2 in
  let ctxt = mk_ctxt alph env maxlen 25 in
  let dprlseqs = Pair.map init_seqs (dps, rules) in
  let init_seqs = fst dprlseqs @ (snd dprlseqs) in
  let loops = generate_loops ctxt init_seqs (all_forward ctxt dprlseqs) in
  if loops = [] then None
  else
    let e = "We use the loop processor to conclude nontermination.\n" in
    Some ([ ],  e ^ (explanation (L.hd loops)))
;;

