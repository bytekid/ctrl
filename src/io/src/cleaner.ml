(* Copyright 2015 Cynthia Kop
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
open Smt;;
open Rewriting;;
open Util;;

(*** FUNCTIONS ***************************************************************)

(*****************************************************************************)
(*                        IDENTIFYING VALUE PARAMETERS                       *)
(*****************************************************************************)

(* returns true if there are no rules of the given sort *)
let check_rule_sort_safety a sort rules =
  let checksafe (rule, e) =
    sort <> Term.get_sort a e (Rule.rhs rule)
  in
  List.for_all checksafe rules
;;

(* returns true if there are no non-logical symbols of the given sort *)
let check_symbol_sort_safety a sort symbols =
  let checksafe f =
    if Alphabet.find_symbol_kind f a <> Alphabet.Terms then true else
    match Alphabet.find_sortdec f a with
      | Left sd -> Sortdeclaration.output_sort sd <> sort
      | Right _ -> false
  in
  List.for_all checksafe symbols
;;

let add_nf_constraints innermost trs =
  (* gathering data *)
  let rules = Trs.get_rules trs in
  let a = Trs.get_alphabet trs in
  let lsorts = Alphabet.find_logical_sorts a in
  (* determining which sorts are purely logical *)
  let symbols = List.unique (List.flat_map (Rule.funs <.> fst) rules) in
  let safesort sort =
    (check_rule_sort_safety a sort rules) &&
    (check_symbol_sort_safety a sort symbols)
  in
  let safesorts = List.filter safesort lsorts in
  (* making the new constraints *)
  let make_constraint e ignoresafety x =
    let v = Term.make_var x in
    let sort = Environment.find_sort x e in
    let boolsort = Alphabet.boolsort in
    let ssorts = if ignoresafety then lsorts else safesorts in
    if not (List.mem sort ssorts) then []
    else if sort = boolsort then (
      try
        let (vee, neg) = ( Alphabet.get_or_symbol a,
                           Alphabet.get_not_symbol a ) in
        [ Term.make_function a e vee
          [v; Term.make_function a e neg [v]]
        ]
      with Not_found -> []
    )
    else (
      try
        let eq = Alphabet.get_equal_symbol a in
        match Alphabet.find_sortdec eq a with
          | Left sd ->
            if Sortdeclaration.output_sort sd <> boolsort then []
            else if Sortdeclaration.input_sorts sd <> [sort;sort] then []
            else [ Term.make_fun eq [v;v] ]
          | Right spd ->
            let osort = Specialdeclaration.output_sort spd in
            let badarity _ =
              if not (Specialdeclaration.known_arity spd) then false
              else Specialdeclaration.arity spd <> 2
            in
            if Specialdeclaration.is_polymorphic osort then []
            else if Specialdeclaration.pol_to_sort osort <> boolsort then []
            else if badarity spd then []
            else (
              let inpdec = Specialdeclaration.input_sort 0 spd in
              if inpdec <> Specialdeclaration.input_sort 1 spd then []
              else if (not (Specialdeclaration.is_polymorphic inpdec)) &&
                      (Specialdeclaration.pol_to_sort inpdec <> sort) then []
              else (
                let sd = Sortdeclaration.create [sort;sort] boolsort in
                [ Term.make_instance eq [v;v] sd ]
              )
            )
      with Not_found -> []
    )
  in
  (* going over all the rules, adding constraints where appropriate *)
  let update (rule, e) =
    let (lhs, rhs) = (Rule.lhs rule, Rule.rhs rule) in
    let cs = Rule.constraints rule in
    let lvars = (Term.vars (Rule.lhs rule)) in
    let rvars = List.diff (Term.vars (Rule.rhs rule)) lvars in
    let cvars = List.unique (List.flat_map Term.vars cs) in
    let xs = List.diff lvars cvars in
    let ys = List.diff rvars cvars in
    let newcs = cs @ (List.flat_map (make_constraint e false) xs) @ 
                     (List.flat_map (make_constraint e true) ys) in
    let rule = Rule.create lhs rhs newcs in
    (rule, e)
  in
  Trs.replace_rules (List.map update rules) trs
;;

(*****************************************************************************)
(*                COMBINING STEPS WITH TRIVIAL FOLLOWUP RULES                *)
(*****************************************************************************)

(* if [rule] is a non-recursive rule of the form f(x1,...,xn) -> r,
 * then this function returns Some (f, [x1,...,xn], r), otherwise it
 * returns None
 *)
let trivial_rule rule =
  let (lhs, rhs) = (Rule.lhs rule, Rule.rhs rule) in
  if Rule.constraints rule <> [] then None else
  match Term.root lhs with None -> None | Some f ->
  if List.mem f (Term.funs rhs) then None else
  let args = Term.args lhs in
  if not (List.for_all Term.is_var args) then None else
  let xs = List.flat_map Term.vars args in
  if List.length xs <> List.length (List.unique xs) then None
  else Some (f, xs, rhs)
;;

(* [detect_simple_rule mayremove rulesa rulesb], where [rulesa] and
 * [rulesb] are both lists of pairs (fs, (rule, e)) where [fs]
 * contains function symbols in [rule] and [e] is the environment of
 * [rule], returns - if possible - a triple Some (rulesa', (f, xs, r,
 * e), rulesb') where [rulesa'] is an extension of [rulesa] with rules
 * from [rulesb] which are either non-trivial or have a root symbol
 * which occurs elsewhere or for which [mayremove] returns false,
 * f(xs) -> r is a rule with environment [e] from [rulesb] and
 * [rulesb'] contains the remainder of [rulesb].
 * If no suitable rule remains in [rulesb], None is returned.
 *)
let rec detect_simple_rule mayremove rulesa rulesb =
  match rulesb with
    | [] -> None
    | (fs, (rule, e)) :: rest -> (
      let recurse _ = detect_simple_rule mayremove
                      ((fs, (rule, e)) :: rulesa) rest in
      match trivial_rule rule with
        | None -> recurse ()
        | Some (f, xs, rhs) ->
          let getfuns = List.flat_map fst in
          if not (mayremove f) then recurse ()
          else if List.mem f (getfuns rulesa) then recurse ()
          else if List.mem f (getfuns rest) then recurse ()
          else Some (rulesa, (f, xs, rhs, e), rest)
    )
;;

(* [simplify_rules alf mayremove checked remaining] considers all the
 * rules in remaining and, if one of them is "simple" as given by the
 * detect_simple_rule function, rewrites the right-hand side of all
 * other rules using it.  We assume that [checked] is already tested
 * and does not contain such rules, while [remaining] might.  [alf]
 * is the alfabet, which is used to guarantee that fresh variables do
 * not overlap with function symbols.
 *)
let rec simplify_rules alf mayremove checked remaining =
  (* returns a suitable name, which does not yet occur in [env] or
  in [alf], for a fresh variable; it should ideally be a little like
  [orig_name] *)
  let fresh_variable_name orig_name env =
    let rec num_name start num =
      let n = start ^ (string_of_int num) in
      if not (Environment.mem_var_name n env) then n
      else num_name start (num+1)
    in
    if not (Environment.mem_var_name orig_name env) then orig_name
    else if String.length orig_name < 3 then num_name orig_name 1
    else num_name (String.sub orig_name 0 3) 1
  in
  (* assuming all the variables in [varlist] are in the [envorig]
  environment, creates fresh variables in the [envnew] environment
  with the same sort and similar name, and returns a substitution
  updated from [gamma] which maps the originals to the new variables
  *)
  let rec add_fresh_mapping varlist envorig envnew gamma =
    match varlist with
      | [] -> gamma
      | x :: xs ->
        let xname = Variable.find_name x in
        let yname = fresh_variable_name xname envnew in
        let ysort = Environment.find_sort x envorig in
        let y = Environment.create_var yname ysort envnew in
        let delta = Substitution.add x (Term.make_var y) gamma in
        add_fresh_mapping xs envorig envnew delta
  in
  (* [rewrite_term argvars rhs var_adder posses], where [argvars] is
  a list of variables (x1,...,xn), and for every position p in
  [posses], [term]|_p has the form f(s1,...,sn), rewrites each such
  subterm to rhs[x1:=s1,...,xn:=sn].  In addition, var_adder is used
  to append the substitution with mappings x:=y where x is a variable
  occurring in [rhs] but not in [argvars], and [y] is fresh; it is
  required that [posses] is oriented depth-first *)
  let rec rewrite term argvars rhs var_adder = function
    | [] -> term
    | p :: posses ->
      let pargs = Term.args (Term.subterm p term) in
      let gamma = Substitution.of_list (List.zip argvars pargs) in
      let newsub = Substitution.apply_term (var_adder gamma) rhs in
      let term = Term.replace p newsub term in
      rewrite term argvars rhs var_adder posses
  in
  (* [sort_pos_list posses] sorts the given list of positions such
  that deeper positions come before higher positions in a term *)
  let sort_pos_list posses =
    let addlength p = (p, List.length (Position.to_list p)) in
    let posinfo = List.map addlength posses in
    let cmp (_, l1) (_, l2) = compare l2 l1 in
    let sortedinfo = List.sort cmp posinfo in
    List.map fst sortedinfo
  in
  (* rewrites the right-hand side of the given rule using the rule
  f(xs) -> rhs in environment e *)
  let rewrite_with (f, xs, rhs, e) newvars (rule, env) =
    let (l, r, cs) = (Rule.lhs rule, Rule.rhs rule, Rule.constraints rule) in
    let posses = sort_pos_list (Term.fun_pos f r) in
    let dangervars =
      if posses = [] || e <> env then newvars
      else if List.intersect newvars (Term.vars r) = [] then []
      else newvars
    in
    let var_adder = add_fresh_mapping dangervars e env in
    let r = rewrite r xs rhs var_adder posses in
    ( Rule.create l r cs, env )
  in
  (* main functionality: checks for a simple rule, applies it to
  everything else if we find one, and recurses if not *)
  match detect_simple_rule mayremove checked remaining with
    | None -> List.map snd (List.rev_append checked remaining)
    | Some (before, t, after) ->
      let (_, xs, rhs, _) = t in
      let newvars = List.diff (Term.vars rhs) xs in
      let rew (fs, r) = (fs, rewrite_with t newvars r) in
      let before = List.map rew before in
      let after = List.map rew after in
      simplify_rules alf mayremove before after
;;

(*****************************************************************************)
(*                 COMBINING RULES WITH THE SAME LHS AND RHS                 *)
(*****************************************************************************)

(* returns whether the given pair of rules can be combined, which is
 * the case if they have the same lhs and rhs (modulo renaming)
 *)
let combinable (rule1, env1) (rule2, env2) = Rule.is_variant rule1 rule2;;

(* makes a conjunction out of a sequence of constraints *)
let rec make_conjunction make_and sofar = function
  | [] -> sofar
  | hd :: tl ->
    make_conjunction make_and (make_and [sofar; hd]) tl
;;

(* given two rules for which we already know they have the same lhs
 * and rhs (modulo renaming), we create a single rule with environment
 * combining them
 *)
let combine funnames alf conj disj (rule1, env1) (rule2, env2) =
  let (lhs1, lhs2) = (Rule.lhs rule1, Rule.lhs rule2) in
  let (rhs1, rhs2) = (Rule.rhs rule1, Rule.rhs rule2) in
  let (css1, css2) = (Rule.constraints rule1, Rule.constraints rule2) in
  let makeand1 = Term.make_function alf env1 conj in
  let makeand2 = Term.make_function alf env2 conj in
  let phi =
    match css1 with
      | [] -> []
      | hd :: tl -> [make_conjunction makeand1 hd tl]
  in
  let psi =
    match css2 with
      | [] -> []
      | hd :: tl -> [make_conjunction makeand1 hd tl]
  in
  let restvars = List.diff (Rule.vars rule2)
                  ((Term.vars lhs2) @ (Term.vars rhs2)) in
  try
    let gamma = Elogic.match_problem [(lhs1, lhs2); (rhs1, rhs2)] in
    let add_fresh subst x =
      let y = Environment.create_var_like x env2 funnames env1 in
      Substitution.add x (Term.make_var y) subst
    in
    let gamma = List.fold_left add_fresh gamma restvars in
    let psi = List.map (Substitution.apply_term gamma) psi in
    let phipsi = phi @ psi in
    let cs = match phipsi with
      | [x;y] -> [Term.make_function alf env1 disj [x;y]]
      | nulorone -> nulorone
    in
    (Rule.create lhs1 rhs1 cs, env1)
  with Elogic.Not_matchable ->
    failwith "combine called for rules which are not combinable"
;;

let combine_similar alf rules =
  let rec all_combinations comb = function
    | [] -> []
    | hd :: tl ->
      let (matches, others) = List.partition (combinable hd) tl in
      let combined = List.fold_left comb hd matches in
      combined :: all_combinations comb others
  in
  try
    let conj = Alphabet.get_and_symbol alf in
    let disj = Alphabet.get_or_symbol alf in
    let funnames = Alphabet.fun_names alf in
    all_combinations (combine funnames alf conj disj) rules
  with Not_found -> rules
;;

(*****************************************************************************)
(*                  COMBINING RULES WHICH DO HAVE CONTRAINTS                 *)
(*****************************************************************************)

(* If there is no good rule to append to, returns None.  Otherwise, returns
 * a tuple (i, function symbol, rule, combinations, remaining rules) where the
 * given rule can safely be appended to all the combinations, and the other
 * rules of [rules] are in the [remaining] list. The remaining rules are
 * indexed, with the intention that the rules combined with the given rule are
 * placed at position [i] in the list. *)
let combination_candidate maytouch alf rules =
  let indexed = List.mapi (fun i (r, e) -> (i,(r,e))) rules in
  (* STEP 1: get all symbols which occur only once on the right *)
  let right_root (i,(r,e)) = try [(Rule.right_root r, i)] with _ -> [] in
  let rsymbols = List.flat_map right_root indexed in
  let compare (f1, i1) (f2, i2) = Function.compare f1 f2 in
  let groups = List.group_fully ~c:compare rsymbols in
  let singles = List.filter (fun x -> List.length x = 1) groups in
  let candidates= List.flat_map id singles in
  (* STEP 2: filter out those symbols which occur deeply elsewhere, or
  which are part of bad rules *)
  let defineds = List.map (fun (_,(r,_)) -> Rule.left_root r) indexed in
  let defineds = List.unique defineds in
  let occurs_in f rule =
    let lfuns = List.flat_map Term.funs (Term.args (Rule.lhs rule)) in
    let rfuns = Rule.right_funs rule in
    List.mem f (lfuns @ rfuns)
  in
  let acceptable_rule f rule =
    if List.mem f (Term.funs (Rule.lhs rule)) then false else
    let rfuns = List.flat_map Term.funs (Term.args (Rule.rhs rule)) in
    let is_constructor g = not (List.mem g defineds) in
    List.for_all is_constructor (List.unique rfuns)
  in
  let no_conflict (f,j) (i,(r,_)) =
    if i = j then acceptable_rule f r
    else not (occurs_in f r)
  in
  let safe_symbol s = List.for_all (no_conflict s) indexed in
  let candidates = try List.filter safe_symbol candidates with _ -> failwith "meh" in
  (*  STEP 3: filter out those symbols which we may not touch, which do not at
  all occur on the left, or which occur in inconvenient rules *)
  let candidates = List.filter (maytouch <.> fst) candidates in
  let candidates = List.filter (fun (f,_) -> List.mem f defineds) candidates in
  let bad_combination_rule f (_,(rule,_)) =
    if Rule.left_root rule <> f then false else
    let args = Term.args (Rule.lhs rule) in
    let vars = Term.vars (Rule.lhs rule) in
    let funs = List.flat_map Term.funs args in
    (funs <> []) || (List.length args <> List.length vars) ||
    not (List.is_subset (Rule.vars rule) vars)
  in
  let check (f,_) = not (List.exists (bad_combination_rule f) indexed) in
  let candidates = List.filter check candidates in
  (* STEP 4: pick one, and find combinations for it *)
  match candidates with | [] -> None | (f,i) :: _ ->
  let frule = List.assoc i indexed in
  let remainder = List.filter (fun (j,_) -> i <> j) indexed in
  let ingroup (_,(rule,_)) = Rule.left_root rule = f in
  let (group, rest) = List.partition ingroup remainder in
  Some (i, f, frule, List.map snd group, rest)
;;

(* Assuming that rule2 has the form f(x1,...,xn) -> r [cs] where no
variables other than [x1,...,xn] occur in r or cs, it is appended to
rule1 and returned in the environment env1. *)
let safe_append (rule1, env1) (rule2, env2) =
  let lhs1 = Rule.lhs rule1 in
  let rhs1 = Rule.rhs rule1 in
  let cs1 = Rule.constraints rule1 in
  let lhs2 = Rule.lhs rule2 in
  let rhs2 = Rule.rhs rule2 in
  let cs2 = Rule.constraints rule2 in
  let gamma = Elogic.match_term rhs1 lhs2 in
  let rhs3 = Substitution.apply_term gamma rhs2 in
  let cs3 = List.map (Substitution.apply_term gamma) cs2 in
  let newrule = Rule.create lhs1 rhs3 (cs1 @ cs3) in
  (newrule, env1)
;;

let rec combine_remainder maytouch alf rules =
  (* find a rule we can append to *)
  let candidate = combination_candidate maytouch alf rules in
  match candidate with
    | None -> rules
    | Some (id, f, rule, group, restrules) ->
      let combis = List.map (safe_append rule) group in
      let (small, big) = List.partition (fun (i,_) -> i < id) restrules in
      let newrules = (List.map snd small) @ combis @ (List.map snd big) in
      combine_remainder maytouch alf newrules
;;

(*****************************************************************************)
(*                         REMOVING UNUSED ARGUMENTS                         *)
(*****************************************************************************)

(* given a set of rules, returns a list mapping f to [0,...,arity(f)-1]
 * for every symbol f which occurs in the rules; symbols in ignore are
 * omitted
 *)
let rec relevant_symbols a ignore sofar = function
  | [] -> sofar
  | rule :: tail ->
    let funs = List.diff (Rule.funs rule) ignore in
    let combi f = (f, List.range 0 (Alphabet.find_ari f a)) in
    let newsofar = (List.map combi funs) @ sofar in
    relevant_symbols a (funs @ ignore) newsofar tail
;;

(* given an alphabet and a set of rules, returns a list of pairs
 * (f, [0,...,arity(f)-1]) of defined symbols with argument positions
 * of that symbol where it is a priori possible that the argument is
 * filtered away *)
let base_removable_combinations a rules =
  let roots = List.unique (List.map Rule.left_root rules) in
  let termsymb f = Alphabet.find_symbol_kind f a = Alphabet.Terms in
  let roots = List.filter termsymb roots in
  let makelist f = (f, List.range 0 (Alphabet.find_ari f a)) in
  List.map makelist roots
;;

(* adapts the tuples base_removable_combinations by removing those
 * parameter indexes where some rule has a defined symbol in the
 * parameter position (on the left or right) *)
let strong_removable_combinations a rules =
  let combis = base_removable_combinations a rules in
  let terms = List.flat_map (fun r -> [Rule.lhs r; Rule.rhs r]) rules in
  (* returns either (None, [], []), or (Some f, indexes of that f which
     must not be filtered away, terms which should also be investigated *)
  let badindexes = function
    | Term.Var _ | Term.Exists _ | Term.Forall _ -> ( None, [], [] )
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      let iargs = List.mapi (fun i a -> (i,a)) args in
      let hasdefined (_,arg) = Term.check_logical_term a arg <> None in
      let iargs = List.filter hasdefined iargs in
      if iargs = [] then ( None, [], [] )
      else ( Some f, List.map fst iargs, List.map snd iargs )
  in
  (* updates the "combis" list, removing the given combination *)
  let rec remove_bad_combinations f indexes = function
    | [] -> [] (* f does not occur in the combis list *)
    | (g, ids) :: rest ->
      if f = g then (f, List.diff ids indexes) :: rest
      else (g, ids) :: remove_bad_combinations f indexes rest
  in
  (* updates the combis list so every function f is combined with all
     parameter indexes which are forbidden due to the shape of the
     given set of terms *)
  let rec ditch_bad combis = function
    | [] -> combis
    | term :: rest -> match badindexes term with
      | ( None, _, _ ) -> ditch_bad combis rest
      | ( Some f, indexes, subs ) ->
        let newcombis = remove_bad_combinations f indexes combis in
        let newrest = subs @ rest in
        ditch_bad newcombis newrest
  in
  ditch_bad combis terms
;;

(* combines each rule with the set of variables occurring in the
 * left-hand side exactly once, and not in the constraint; these are
 * the variables that, without looking at the right-hand side, may
 * potentially be filtered away *)
let add_variable_information rules =
  let rec get_single_variables single double = function
    | Term.Var x ->
      if List.mem x single then (List.diff single [x], x :: double)
      else if List.mem x double then (single, double)
      else (x :: single, double)
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      let parse_arg (s, d) arg = get_single_variables s d arg in
      List.fold_left parse_arg (single,double) args
    | Term.Forall _ | Term.Exists _ ->
      failwith "Quantifier occurrence in the left-hand side of a rule!"
  in
  let add_information rule =
    let lhs = Rule.lhs rule in
    let cs = Rule.constraints rule in
    let (single, double) = get_single_variables [] [] lhs in
    let csvars = List.unique (List.flat_map Term.vars cs) in
    (List.diff single csvars, rule)
  in
  List.map add_information rules
;;

(* [unfilterable_variables xs combis term] returns those variables in
 * [xs] which occur in [term] at "unfilterable" positions; here, a
 * position is unfilterable if it is untouched even if we remove every
 * i^th argument of a function symbol f whenever (f,[...,i,...])
 * occurs in [combis]
 *)
let rec unfilterable_variables xs combis term =
  match term with
    | Term.Var x ->
      if List.mem x xs then [x]
      else []
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      let filterable_positions =
        try List.assoc f combis
        with Not_found -> []
      in
      let rec unfilterable args filterposses i =
        match (args, filterposses) with
          | (_, []) -> args
          | ([], _) -> [] (* shouldn't happen, but let's have this case *)
          | (hd :: tl, j :: rest) ->
            if i = j then unfilterable tl rest (i+1)
            else hd :: unfilterable tl filterposses (i+1)
      in
      let goodargs = unfilterable args filterable_positions 0 in
      List.flat_map (unfilterable_variables xs combis) goodargs
    | Term.Forall (_, s) | Term.Exists (_, s) ->
      unfilterable_variables xs combis s
;;

(* given a list of tuples (f, parameter indexes of f that may be
 * filtered away), a set of variables and a term, this function
 * updates the tuple list (combis) such that combis[f] no longer
 * contains i if the term has a subterm f(...,si,...) where si is
 * not a variable in vars; if anything is changed, [changed] is
 * updated to be true, otherwise it is returned unmodified *)
let rec check_combination_validity combis vars changed = function
  | Term.Var _ -> (combis, changed)
  | Term.Forall (_, term) | Term.Exists (_, term) ->
    check_combination_validity combis vars changed term
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    (* identify what arguments we need to be messing around with *)
    let ids =
      try List.assoc f combis
      with Not_found -> []
    in
    (* recognise all ids of bad arguments *)
    let rec removable i args ids =
      match (args, ids) with
        | (_, []) -> []
        | ([], _) -> [] (* shouldn't happen, but meh *)
        | (arg :: tail, j :: restids) ->
          let recurse rids = removable (i+1) tail rids in
          if j <> i then recurse ids
          else if not (Term.is_var arg) then i :: recurse restids
          else if List.intersect (Term.vars arg) vars = [] then
            i :: recurse restids
          else recurse restids
    in
    let removable_indexes = removable 0 args ids in
    (* remove those from combis[f] *)
    let update (g, is) = 
      if g = f then (g, List.diff ids removable_indexes)
      else (g, is)
    in
    let (combis, changed) =
      if removable_indexes = [] then (combis, changed)
      else (List.map update combis, true)
    in
    (* finally, recurse over the arguments *)
    let update_for_arg (co, ch) = check_combination_validity co vars ch in
    List.fold_left update_for_arg (combis, changed) args
;;

(* given a list of tuples (f, parameter indexes of f that may be
 * filtered away) and a term, returns all variables in the term which
 * are at positions that can NOT be filtered away *)
let rec unfilterable_variables combis = function
  | Term.Var x -> [x]
  | Term.Forall (_, term) | Term.Exists (_, term) ->
    unfilterable_variables combis term
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    let filterable =
      try List.assoc f combis
      with Not_found -> []
    in
    let rec unfilterable i args filterable =
      match (args, filterable) with
        | (terms,[]) -> terms
        | ([],_) -> [] (* shouldn't happen *)
        | (arg::restargs, j::restposses) ->
          if i = j then unfilterable (i+1) restargs restposses
          else arg :: unfilterable (i+1) restargs filterable
    in
    let unfilterable_args = unfilterable 0 args filterable in
    List.flat_map (unfilterable_variables combis) unfilterable_args
;;

(* Given a list of tuples (f, parameter indexes of f that may be
 * filtered away) and two lists of combinations (xs, rule) where xs
 * are the variables occurring in the rule that may be filtered away,
 * goes through ruleinfo2, updating both the variable parts taking
 * combis into account, and combis taking the ruleinfo data into
 * account.  If we ever get to the end of ruleinfo2 without having
 * changed anything, the resulting combination list is returned,
 * otherwise we just go over the rules again.
 *)
let rec update_usage_info combis ruleinfo1 ruleinfo2 changed =
  (* main functionality *)
  match ruleinfo2 with
    | [] ->
      if changed then update_usage_info combis [] ruleinfo1 false
      else combis
    | (xs, rule) :: tail ->
      let (lhs, rhs) = (Rule.lhs rule, Rule.rhs rule) in
      (* positions i should be removed from combis[f] if this lhs
      contains a subterm f(...,si,...) where si is not a variable in
      xs *)
      let (combis, changed) = check_combination_validity combis xs
                              changed lhs in
      (* variables should be removed from xs if they are at a
      position in the left or right which may not be filtered away *)
      let leftvars = unfilterable_variables combis lhs in
      let rightvars = unfilterable_variables combis rhs in
      let vars = leftvars @ rightvars in
      let rec exclude_from sofar ch = function
        | [] -> (sofar, ch)
        | x :: tail ->
          if List.mem x vars then exclude_from sofar true tail
          else exclude_from (x :: sofar) ch tail
      in
      let (xs, changed) = exclude_from [] changed xs in
      (* recurse over the remaining rules *)
      update_usage_info combis ((xs,rule) :: ruleinfo1) tail changed
;;

(* Helping function: given an ordered list of numbers and a list
 * containing at least max([nums])+1 elements, replaces each element
 * el of [lst] by g true el if its index is in [nums], otherwise by
 * g false else.  This should be called with i = 0.
 *)
let rec fill_list i g nums lst =
  match (nums, lst) with
    | (_,[]) -> []
    | ([], hd :: tl) -> (g false hd) :: fill_list (i+1) g [] tl
    | (num :: rest, hd :: tl) ->
      if num = i then (g true hd) :: fill_list (i+1) g rest tl
      else (g false hd) :: fill_list (i+1) g nums tl
;;

(* returns the elements of [lst] whose index is not in [filtered] *)
let unfiltered_elements lst filtered =
  let check filtered element = if filtered then [] else [element] in
  List.flat_map id (fill_list 0 check filtered lst)
;;

(* Given that combis[f] contains those indexes of f which should be
 * filtered away, applies the given filtering on all subterms of the
 * given rule. *)
let filter_rule combis (rule, env) =
  let find_filter f =
    try List.assoc f combis
    with Not_found -> []
  in
  let rec filter_term = function
    | Term.Var x -> Term.Var x
    | Term.Exists (x, term) -> Term.Exists (x, filter_term term)
    | Term.Forall (x, term) -> Term.Forall (x, filter_term term)
    | Term.Fun (f, args) ->
      let filtered = find_filter f in
      let unfiltered_args = unfiltered_elements args filtered in
      let newargs = List.map filter_term unfiltered_args in
      Term.Fun (f, newargs)
    | Term.InstanceFun (f, args, sd) ->
      let filtered = find_filter f in
      let unfiltered_args = unfiltered_elements args filtered in
      let newargs = List.map filter_term unfiltered_args in
      let inpsorts = Sortdeclaration.input_sorts sd in
      let outsort = Sortdeclaration.output_sort sd in
      let newinpsorts = unfiltered_elements inpsorts filtered in
      let newsd = Sortdeclaration.create newinpsorts outsort in
      Term.InstanceFun (f, newargs, newsd)
  in
  (Rule.project filter_term rule, env)
;;

(* Given that the indexes in [ids] should be filtered away, applies
 * this filtering directly into the alphabet. *)
let register_function_filtering alf (f, ids) =
  match Alphabet.find_sortdec f alf with
    | Left sd ->
      let inputs = Sortdeclaration.input_sorts sd in
      let output = Sortdeclaration.output_sort sd in
      let newinputs = unfiltered_elements inputs ids in
      let newdec = Sortdeclaration.create newinputs output in
      Alphabet.replace_sortdec f (Left newdec) alf
    | Right spd ->
      if Specialdeclaration.known_arity spd then
        let inputs = Specialdeclaration.input_sorts spd in
        let output = Specialdeclaration.output_sort spd in
        let newinputs = unfiltered_elements inputs ids in
        let newdec = Specialdeclaration.polymorphic_declaration
                                                 newinputs output in
        Alphabet.replace_sortdec f (Right newdec) alf
      else failwith ("ERROR: defined symbols must not have a " ^
             "polymorphic variable declaration with unknown arity!")
;;

(*****************************************************************************)
(*                          SIMPLIFYING CONSTRAINTS                          *)
(*****************************************************************************)

let simplify_constraints rules alf =
  let solver = Rewriter.smt_solver (Rewriter.get_current ()) in
  (* get standard symbols, if set (if not, we just won't do anything here) *)
  let funs = Alphabet.funs alf in
  if funs = [] then rules else
  let defsymb = List.hd funs in
  let (andsymb, orsymb, negsymb, botsymb, ok) =
    try (Alphabet.get_and_symbol alf, Alphabet.get_or_symbol alf,
         Alphabet.get_not_symbol alf, Alphabet.get_bot_symbol alf,
         true)
    with Not_found -> (defsymb, defsymb, defsymb, defsymb, false)
  in
  if not ok then rules else
  let falseterm = Term.make_fun botsymb [] in
  (* building and destroying conjunctions *)
  let rec split_conjunction term =
    match term with
      | Term.Fun (f, lst) | Term.InstanceFun (f, lst, _) ->
        if f = andsymb then List.flat_map split_conjunction lst
        else [term]
      | _ -> [term]
  in
  let rec make_conjunction env = function (* uses reverse order *)
    | [] -> failwith "make_conjunction"
    | [x] -> x
    | x :: ys ->
      let y = make_conjunction env ys in
      Term.make_function alf env andsymb [y;x]
  in
  (* removing unnecessary constraints, and replacing unsatisfiable ones
  by false *)
  let rec filter_constraints env noothers sofar = function
    | [] -> sofar
    | hd :: tl ->
      let hdimplies = Term.make_function alf env orsymb [hd;noothers] in
      (* nothers \/ hd is valid => noothers implies hd => we don't need to
         include it *)
      if Solver.valid [hdimplies] solver env then
        filter_constraints env noothers sofar tl else
      let nothd = Term.make_function alf env negsymb [hd] in
      let antihdimplies = Term.make_function alf env orsymb [nothd;noothers] in
      (* nothers \/ -hd is valid => noothers implies -hd => the constraint is
         unsatisfiable together! *)
      if Solver.valid [antihdimplies] solver env then [falseterm] else
      filter_constraints env antihdimplies (hd :: sofar) tl
  in
  (* main work: simplifying the constraint for a single rule *)
  let simplify_constraint (rule, e) =
    let (l, r, phis) = (Rule.lhs rule, Rule.rhs rule, Rule.constraints rule) in
    let start = Term.make_fun botsymb [] in
    let phis = List.flat_map split_conjunction phis in
    let psis = filter_constraints e start [] phis in
    if psis = [] then [(Rule.create l r [], e)]
    else if psis = [falseterm] then []
    else [(Rule.create l r [make_conjunction e psis], e)]
  in
  List.flat_map simplify_constraint rules
;;

(*****************************************************************************)
(*          MAKING A STRING REPRESENTATION OF THE SIMPLIFIED SYSTEM          *)
(*****************************************************************************)

(* This function sorts the given list of function / function name
 * pairs in such a way that it is *mostly* oriented alphabetically
 * by name, but u_3 still comes before u_11. *)
let sort_symbols lst =
  (* split a name of the form <string><int> into the separate
  components, where <int> is taken as large as possible *)
  let rec split_string str pos len =
    let pm = pos - 1 in
    if pos = 0 then ("", int_of_string str)
    else if Char.is_digit (String.get str pm) then
      split_string str pm len 
    else if pos >= len then (str, -1) 
    else ( String.sub str 0 pos,
           int_of_string (String.sub str pos (len-pos)) )
  in  
  let split str =
    let len = String.length str in
    split_string str len len 
  in
  let cmp (_, name1) (_, name2) =
    let (n1name, n1num) = split name1 in
    let (n2name, n2num) = split name2 in
    if n1name = n2name then compare n1num n2num
    else compare n1name n2name
  in
  List.sort cmp lst
;;

(* This function returns the group symbols, such as integers,
 * occurring in the given alphabet, along with the method how to
 * declare them. *)
let group_symbols alf =
  (* arrays of all sorts *)
  let arrayable = Alphabet.arraysorts_of alf in
  let arrdata sort =
    let arrsort = Alphabet.array_sort sort alf in
    let sortstring = String.uppercase_ascii (Sort.to_string sort) in
    (arrsort, "  !ARRAY!" ^ sortstring ^ " : " ^ (Sort.to_string arrsort))
  in
  let extra_sorts = List.map arrdata arrayable in
  (* integers *)
  let extra_sorts =
    try
      let isort = Alphabet.integer_sort alf in
      let txt = "  !INTEGER : " ^ (Sort.to_string isort) ^ " ;" in
      (isort, txt) :: extra_sorts
    with Not_found -> extra_sorts
  in
  extra_sorts
;;

(* This function prints a sort declaration or a special sort
 * declaration in the way needed for input files. *)
let print_sortdec = function
  | Left sd ->
    let osort = Sortdeclaration.output_sort sd in
    let isorts = Sortdeclaration.input_sorts sd in
    if isorts = [] then Sort.to_string osort
    else (List.implode Sort.to_string " * " isorts) ^ " => " ^
         (Sort.to_string osort)
  | Right spd ->
    let tostr = Specialdeclaration.pol_to_string in
    let osort = Specialdeclaration.output_sort spd in
    let isorts = Specialdeclaration.input_sorts spd in
    let isortstring =
      if Specialdeclaration.known_arity spd then
        List.implode tostr " * " isorts
      else "<" ^ (tostr (List.hd isorts)) ^ ">"
    in
    if isorts = [] then tostr osort
    else isortstring ^ " => " ^ (tostr osort)
;;

let print_alphabet alf rules =
  (* get all the relevant symbols *)
  let relevant_symbols = List.unique (List.flat_map Rule.funs rules) in
  let is_term_symbol f = Alphabet.find_symbol_kind f alf <> Alphabet.Logical in
  let term_symbols = List.filter is_term_symbol relevant_symbols in
  (* make sure that true is there if and only if false is *)
  let top = Alphabet.get_top_symbol alf in
  let bot = Alphabet.get_top_symbol alf in
  let term_symbols =
    if List.mem top term_symbols then (
      if List.mem bot term_symbols then term_symbols
      else bot :: term_symbols
    )
    else if List.mem bot term_symbols then top :: term_symbols
    else term_symbols
  in
  (* make sure that integers and arrays are included if necessary
  (and not the individual elements *)
  let term_symbols = List.filter Function.is_standard term_symbols in
  let extra_sorts = group_symbols alf in
  let sort_occurs sort f =
    match Alphabet.find_sortdec f alf with
      | Right spd ->
        let sorts = (Specialdeclaration.output_sort spd) ::
                    (Specialdeclaration.input_sorts spd) in
        let is_danger polsort =
          (Specialdeclaration.is_polymorphic polsort) ||
          (sort = Specialdeclaration.pol_to_sort polsort)
        in
        List.exists is_danger sorts
      | Left sd ->
        let sorts = (Sortdeclaration.output_sort sd) ::
                    (Sortdeclaration.input_sorts sd) in
        List.mem sort sorts
  in
  let is_used (sort, _) = List.exists (sort_occurs sort) term_symbols in
  let extra_sorts = List.filter is_used extra_sorts in
  (* print the symbols *)
  let addname f = (f, Function.find_name f) in
  let sorted_symbols = sort_symbols (List.map addname term_symbols) in
  let print_declaration (f, name) =
    let sortdec = Alphabet.find_sortdec f alf in
    "  " ^ name ^ " : " ^ (print_sortdec sortdec) ^ " ;"
  in
  "SIGNATURE\n" ^ (List.implode print_declaration "\n" sorted_symbols) ^ "\n" ^
    (List.implode snd "\n" extra_sorts) ^ "\n"
;;

let print_rules  print_term rules =
  let print_rule (rule, env) =
    let p term = print_term term in
    let lhs = p (Rule.lhs rule) in
    let rhs = p (Rule.rhs rule) in
    let constraints = Rule.constraints rule in
    let start = "  " ^ lhs ^ " -> " ^ rhs ^ " " in
    match constraints with
      | [] -> start ^ ";"
      | _ -> start ^ "[" ^ (List.implode p ", " constraints) ^ "] ;"
  in
  let rules = List.rev rules in
  "RULES\n" ^ (List.implode print_rule "\n" rules) ^ "\n"
;;

(*****************************************************************************)
(*                      MAIN SIMPLIFICATION FUNCTIONALIT                     *)
(*****************************************************************************)

let simplify trs maytouch print_term =
  (* gathering data *)
  let rules = Trs.get_rules trs in
  let a = Trs.get_alphabet trs in
  (* combining rules l -> f(r) [phi] with unconstrained rules f(x) -> t *)
  let symbs = List.map (Term.funs <.> Rule.lhs <.> fst) rules in
  let ruleswithsymbs = List.zip symbs rules in
  let rules = simplify_rules a maytouch [] ruleswithsymbs in
  (* combining rules with the same lhs and rhs *)
  let rules = combine_similar a rules in
  let rules = combine_remainder maytouch a rules in
  (* removing unused arguments in function symbols *)
  let rs = List.map fst rules in
  let ruleinfo = add_variable_information rs in
  let removable_combinations = strong_removable_combinations a rs in
  let removable_combinations =
    List.filter (fun (f,_) -> maytouch f ) removable_combinations in
  let combis =
    update_usage_info removable_combinations [] ruleinfo false in
  let rules = List.map (filter_rule combis) rules in
  List.iter (register_function_filtering a) combis ;
  (* removing the constraints *)
  let rules = simplify_constraints rules a in
  (* make a new TRS with only relevant rules, and return a string
  representation which only shows relevant symbols for the alphabet *)
  let txt = ( print_alphabet a (List.map fst rules) ) ^ "\n" ^
            ( print_rules print_term rules ) in
  Trs.set_rules rules trs ;
  txt
;;

let simplify_trs trs maytouch =
  let _ = simplify trs maytouch Term.to_string in
  add_nf_constraints true trs
;;

