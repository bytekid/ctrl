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

(*** TYPES *******************************************************************)

type equation = Term.t * Term.t * Term.t;;
  (* constraints have the form (s,t,phi), for s = t [phi] *)

type recursion = NonRecursive | TailRecursive | GeneralRecursive

type cterm = Constrainedrewriter.cterm

(*** MODULES *****************************************************************)

module VarSet = Set.Make(Variable);;
module SymbolGraph = Graph.Make(Function);;
module SymbolIndex = Map.Make(Function)(Int);;

(*** VARIABLES ***************************************************************)

let internal_rules : Rule.t list ref = ref [];; 
let internal_alphabet : Alphabet.t option ref = ref None;;
let internal_funnames : string list ref = ref [];; 
let internal_cons : Function.t list ref = ref [];; 
let internal_defs : Function.t list ref = ref [];; 
let internal_environment : Environment.t option ref = ref None;;
let internal_specialvars : VarSet.t ref = ref VarSet.empty;;
let internal_logicsorts : Sort.t list ref = ref [];; 
let internal_equation : (Sort.t * Function.t) list ref = ref [];;
let internal_recursion_data : (Function.t * recursion) list ref = ref [];;
let internal_weights : SymbolIndex.t ref = ref SymbolIndex.empty;;

(*** FUNCTIONS ***************************************************************)

let rules () = !internal_rules;;
let alphabet () = Option.the !internal_alphabet;;
let environment () = Option.the !internal_environment;;
let funnames () = !internal_funnames;;
let defsymbs () = !internal_defs;;
let specialvars () = !internal_specialvars;;
let logicsorts () = !internal_logicsorts;;
let smt () = Rewriter.smt_solver (Rewriter.get_current ());;
let equationsymb () = !internal_equation;;

let get_data () = (alphabet (), environment (), rules ());;
let get_special_vars () = VarSet.elements (specialvars ());;
let is_constructor f = List.mem f (!internal_cons);;

let recursion_style f =
  try List.assoc f !internal_recursion_data
  with Not_found -> NonRecursive
;;

(*******************************************************************)
(* the following functions serve to build logical constructions    *)
(*******************************************************************)

let rec create_logical fgetter name args =
  let a = alphabet () in
  try Term.make_function a (environment ()) (fgetter a) args
  with Not_found ->
    if name <> "imply" then
      failwith ("Internal " ^ name ^ " symbol is not set, cannot " ^
                "apply inductive theorem proving technique!")
    else (
      let (a, b) = (List.hd args, List.hd (List.tl args)) in
      create_not (create_and a (create_not b))
    )

and create_top () = create_logical Alphabet.get_top_symbol "truth" []
and create_not s = create_logical Alphabet.get_not_symbol "not" [s]
and create_equal s t = create_logical Alphabet.get_equal_symbol "equal" [s;t]
and create_and s t = create_logical Alphabet.get_and_symbol "and" [s;t]
and create_imply s t = create_logical Alphabet.get_imply_symbol "imply" [s;t]

(** Creates a conjunction of possibly more than one part *)
let create_conjunction lst =
  let rec make_constraint = function
    | [] -> create_top ()
    | a :: [] -> a
    | a :: tail -> create_and (make_constraint tail) a
  in
  make_constraint (List.rev lst)
;;

(** Gets all non-trivial parts of a conjunction, omitting duplicates *)
let get_conjunction_parts term =
  let topsymbol = Alphabet.get_top_symbol (alphabet ()) in
  let andsymbol = Alphabet.get_and_symbol (alphabet ()) in
  let rec get_parts term =
    let fop = Term.root term in
    match fop with
      | None -> [term]
      | Some f -> (
        if f = topsymbol then []
        else if f = andsymbol then List.flat_map get_parts (Term.args term)
        else [term]
      )
  in
  List.unique (get_parts term)
;;

(*******************************************************************)
(* the following functions handle conversions                      *)
(*******************************************************************)

let make_equation_cterm (l,r,phi) =
  let sort = Term.get_sort (alphabet ()) (environment ()) l in
  let symb =
    try List.assoc sort (equationsymb ())
    with Not_found ->
      failwith ("Sort " ^ (Sort.to_string sort) ^ " used in " ^
        "equation does not have an EQUAL-symbol!")
  in
  let term = Term.make_fun symb [l;r] in
  Constrainedrewriter.make_cterm term [phi] (Some (alphabet ()))
;;

let unmake_constrained_term (combi, phi) =
  let phi = Constrainedrewriter.trivial_constraint_simplification
              (alphabet ()) (environment ()) phi in
  match Term.args combi with
    | l :: r :: [] -> (l,r,phi)
    | _ -> failwith ("Having transformed the equation into a " ^
                     "constrained term and rewritten it, somehow " ^
                     "the result is no longer an equation!")
;;

let rule_to_equation rule =
  let (l, r) = (Rule.lhs rule, Rule.rhs rule) in
  let cs = Rule.constraints rule in
  if List.length cs = 1 then (l,r,List.hd cs)
  else (
    let combined = create_equal l r in
    let cterm = Constrainedrewriter.make_cterm combined cs
                                       (Some (alphabet ())) in
    unmake_constrained_term cterm
  )
;;

let equation_to_rule (l,r,phi) = Rule.create l r [phi];;

(* returns a string representation of the given position *)
let to_string_position pos =
  let lst = List.map (fun i -> i + 1) (Position.to_list pos) in
  "[" ^ (List.join string_of_int "." lst) ^ "]"
;;

(**
 * Returns whether the given variable is of a logical sort (and,
 * therefore, can be assumed to be instantiated by a value)
 *)
let is_logical_variable x =
  let sort x = Environment.find_sort x (environment ()) in
  List.mem (sort x) (logicsorts ())
;;

(**
 * for all variables of a logical sort which do not already occur
 * in phi, adds an equation x = x into phi
 *)
let equation_variables (l,r,phi) =
  let lvars = Term.vars l in
  let rvars = Term.vars r in
  let phivars = Term.vars phi in
  let trickyvars = List.union (List.diff lvars phivars)
                              (List.diff rvars phivars) in
  let simplyvars = List.filter is_logical_variable trickyvars in
  let obvious x = create_equal (Term.make_var x) (Term.make_var x) in
  let newconstraints = List.map obvious simplyvars in
  let c = List.fold_left create_and phi newconstraints in
  (l,r,c)
;;

(*******************************************************************)
(* the following functions handle analysis of symbol-relations     *)
(*******************************************************************)

(**
 * This function stores a mapping, indicating for every defined
 * function symbol whether it is recursive, and if so, whether it
 * is tail-recursive.
 *)
let get_recursion_data rules =
  (* group rules by their main symbol *)
  let rulewithsymb (r,_) = (Rule.left_root r, r) in
  let c (f, _) (g, _) = compare f g in
  let groups = List.group_fully ~c:c (List.map rulewithsymb rules) in
  let takeout_symbol = function
    | [] -> []
    | (f, rule) :: tail -> [(f, rule :: List.map snd tail)]
  in
  let symbol_groups = List.flat_map takeout_symbol groups in
  (* determine symbols immediately reduced to by a defined symbol *)
  let is_defined g = List.mem_assoc g symbol_groups in
  let get_root t = match Term.root t with Some g -> [g] | _ -> [] in
  let target_symbols (f, frules) =
    let rights = List.map Rule.rhs frules in
    let right_args = List.flat_map Term.args rights in
    let right_arg_symbs = List.flat_map Term.funs right_args in
    let right_arg_symbs = List.unique right_arg_symbs in
    let right_arg_defineds = List.filter is_defined right_arg_symbs in
    let right_roots = List.flat_map get_root rights in
    let only_right_roots = List.diff right_roots right_arg_defineds in
    let right_defineds = List.filter is_defined only_right_roots in
    ( f, (List.map (fun x -> (x, true)) right_defineds) @
         (List.map (fun x -> (x, false)) right_arg_defineds) )
  in
  let symbol_data = List.map target_symbols symbol_groups in
  (* determine symbols at all reduced to by a defined symbol;
  top_treatment: 0 if we don't care whether a symbol is at the top
  or not, 1 if we need a symbol not at the top, 2 if we need a
  symbol at the top *)
  let rec function_reductions f sofar visited top_treatment =
    try
      let children = List.assoc f symbol_data in
      let add_child (sofar, visited) (g, top) =
        if (not top) && (top_treatment = 2) then (sofar, visited)
        else if List.mem g visited then (
          if List.mem g sofar then (sofar, visited)
          else if top && (top_treatment = 1) then (sofar, visited)
          else (g :: sofar, visited)
        )
        else (
          let top_policy = if top then top_treatment else 0 in
          if top && (top_treatment = 1) then
            function_reductions g sofar (g :: visited) top_policy
          else function_reductions g (g :: sofar) (g :: visited) top_policy
        )
      in
      List.fold_left add_child (sofar, visited) children
    with Not_found -> (sofar, visited)
  in
  let freductions k (f,_) = (f, fst (function_reductions f [] [f] k)) in
  let lower_symbol_data = List.map (freductions 1) symbol_data in
  let top_symbol_data = List.map (freductions 2) symbol_data in
  (* find out recursion style for each symbol *)
  let recursion_style ((f, topdata), (_, lowerdata)) =
    if List.mem f lowerdata then (f, GeneralRecursive)
    else if List.mem f topdata then (f, TailRecursive)
    else (f, NonRecursive)
  in
  let combination = List.zip top_symbol_data lower_symbol_data in
  List.map recursion_style combination
;;

(**
 * This function assigns to each defined function symbol an index,
 * such that if f(...) -> r, then r contains only symbols with an
 * index that's at most as high as the index of f
 *)
let calculate_function_weight rules =
  (* step 1: make a graph with as nodes all defined symbols, and an
  edge from A to B if symbol A reduces to an rhs containing B *)
  let defs = List.unique (List.map Rule.left_root rules) in
  let graph = SymbolGraph.make defs [] in
  let add_edge x graph y =
    if not (List.mem y defs) then graph
    else if SymbolGraph.mem_edge (x, y) graph then graph
    else SymbolGraph.add_edge (x, y) graph
  in
  let add_edges x ys graph = List.fold_left (add_edge x) graph ys in
  let add_edges_for graph rule =
    add_edges (Rule.left_root rule) (Rule.right_funs rule) graph in
  let graph = List.fold_left add_edges_for graph rules in
  (* step 2: determine groups, and an ordering between groups *)
  let remove_nodes nodes graph =
    List.fold_left (Util.flip SymbolGraph.remove_node) graph nodes in
  let group_outedges group graph =
    SymbolGraph.find_edges group (List.diff defs group) graph in
  let rec find_minimal_group sofar graph = function
    | [] -> None
    | group :: rest ->
      if group_outedges group graph = [] then
        Some ( group, remove_nodes group graph, rest @ sofar )
      else find_minimal_group (group :: sofar) graph rest
  in
  let rec order_groups groups graph =
    match find_minimal_group [] graph groups with
      | None -> []
      | Some ( group, newgraph, newgroups ) ->
        group :: order_groups newgroups newgraph
  in
  let ordered_groups = order_groups (SymbolGraph.sccs graph) graph in
  (* step 3: assign every function a number *)
  let update_group i group = List.map (fun x -> (x, i)) group in
  let lst = List.flat_mapi update_group ordered_groups in
  SymbolIndex.of_list lst
;;

(**
 * Returns the weights of all symbols occurring in the given term, and
 * how often they occur, with the higher weights first.
 *)
let get_all_symbol_weights term =
  let get_weight f =
    try [SymbolIndex.find f !internal_weights]
    with Not_found -> []
  in
  let weights = List.flat_map get_weight (Term.funs term) in
  let weightgroups = List.rev (List.group_fully weights) in
  let flatten_group = function
    | [] -> []
    | hd :: tl -> [(hd, 1 + List.length tl)]
  in
  List.flat_map flatten_group weightgroups
;;

(**
 * Compares two terms, ordering by the symbols occurring in them in a
 * multiset order kind of way.
 *)
let term_compare s t =
  let slst = get_all_symbol_weights s in
  let tlst = get_all_symbol_weights t in
  let rec lexcompare = function
    | ([], []) -> 0
    | ([], _) -> -1
    | (_, []) -> 1
    | ( (wght1, num1) :: rest1, (wght2, num2) :: rest2 ) ->
      if wght1 > wght2 then 1
      else if wght1 < wght2 then -1
      else if num1 > num2 then 1
      else if num1 < num2 then -1
      else lexcompare (rest1, rest2)
  in
  lexcompare (slst, tlst)
;;

(*******************************************************************)
(* the following functions handle the initialisation of the method *)
(*******************************************************************)

(** returns whether !rules united with extra_rules is terminating *)
let terminating extra_rules silent =
  let trs = Trs.get_current () in
  let extra = List.map (fun r -> (r, environment ())) extra_rules in
  let terminating = Terminator.check_extended (not silent) trs extra in
  match terminating with
    | Terminator.TERMINATING -> true
    | Terminator.NONTERMINATING ->
      if not silent then
        Printf.printf "Resulting LCTRS is non-terminating!\n" ;
      false
    | Terminator.UNKNOWN ->
      if not silent then
        Printf.printf "%s\n" ("Termination proof required for " ^
          "resulting system, but could not be found!\n") ;
      false
;;

(**
 * Checks all required properties, such as quasi-reductivity and
 * termination, returning f <errormess> if one of them does not hold,
 * or g () if all hold.
 *
 * Note that this immediately updates the TRS to be left-value-free.
*)
let precheck f g trs eqs allownonterm =
  let terms = List.flat_map (fun x -> [Rule.lhs x; Rule.rhs x]) eqs in
  if not (Completenesschecker.check_value_sound trs) then
    f ("Inductive Theorem Proving can only be used for " ^
       "LCTRSs where all logical sorts admit values.\n")
  else if not (Trs.is_left_linear trs) then
    f ("Inductive Theorem Proving can only be used for " ^
       "left-linear LCTRSs.\n")
  else if not (Completenesschecker.check_constructor_sound trs) then
    f ("Inductive Theorem Proving can only be used for LCTRSs " ^
       "where all sorts are inhabited by ground constructor terms\n")
  else ( match Completenesschecker.completely_reducible trs terms with
    | None -> ()
    | Some msg -> f ("Inductive Theorem Proving can only be used " ^
        "for quasi-reductive LCTRSs (or at least, where the " ^
        "symbols in the original terms and the rules are " ^
        "quasi-reductive); the given rules do not satisfy this " ^
        "requirement.  In particular: " ^ msg)
  ) ;
  if not (terminating [] true) then (
    if allownonterm then Printf.printf "\n%s\n\n\n"
      "WARNING!! Termination of this LCTRS could not be proved!"
    else f ("Inductive Theorem Proving can only be used for " ^
      "terminating LCTRSs, and we could not automatically " ^
      "prove termination.\n")
  )
  else g ()
;;

(**
 * Assuming that num is the last number such that the special
 * variable v<num> is in use, returns (x, newnum) where x is a new
 * special variable v<newnum> of the given sort.
 *)
let fresh_replacement_var alf env sort num =
  let construct_name num = "v" ^ (string_of_int num) in
  let isused name = (Alphabet.mem_fun_name name alf) ||
                    (Environment.mem_var_name name env)
  in
  let rec find_unused num =
    let attempt = construct_name num in
    if isused attempt then find_unused (num + 1)
    else (attempt, num)
  in
  let (name, newnum) = find_unused (num + 1) in
  let x = Environment.create_var name sort env in
  internal_specialvars := VarSet.add x !internal_specialvars ;
  (x, newnum)
;;

(**
 * This function replaces all initialisations in the given term by
 * variables, and returns a tuple of the resulting term, and all
 * replacements that were done
 *)
let replace_initialisations a e term =
  let rec replace term defs num = match Term.root term with
    | None -> (term, defs, num)
    | Some f ->
      if Alphabet.is_value f a then (
        let sort = (Term.get_sort a e term) in
        let (x, lastnum) = fresh_replacement_var a e sort num in
        (Term.make_var x, (x, term) :: defs, lastnum)
      )
      else if Term.check_logical_term a term = None then (term, defs, num)
      else (
        let (args, s, n) = replacelist defs num (Term.args term) in
        let newterm = Term.make_function a e f args in
        (newterm, s, n)
      )
  and replacelist defs num = function
    | [] -> ([], defs, num)
    | head :: tail ->
      let (newhead, newdefs, newnum) = replace head defs num in
      let (newtail, nd, nn) = replacelist newdefs newnum tail in
      (newhead :: newtail, nd, nn)
  in
  let (newterm, defs, _) = replace term [] 0 in
  (newterm, defs)
;;

(**
 * This function replaces all initialisations in the right-hand sides
 * of a rule by a special variable, which is initialised in the
 * corresponding constraint
 *)
let replace_rule_initialisations a e rule =
  let (newright, defs) = replace_initialisations a e (Rule.rhs rule) in
  let make_equality (x, term) = create_equal (Term.make_var x) term in
  let l = Rule.lhs rule in
  let cs = Rule.constraints rule in
  let cparts = List.flat_map get_conjunction_parts cs in
  let allparts = List.rev_append (List.map make_equality defs) cparts in
  if allparts = [] then Rule.create l newright []
  else (
    let phi = create_conjunction allparts in
    equation_to_rule (l, newright, phi)
  )
;;

(* turn the list of rules representing equations into a list of
equations, with as much extra data as we can offer *)
let prepare_equations eqs =
  let equations = List.map rule_to_equation eqs in
  let equations = List.map equation_variables equations in
  let simpeq (s,t,phi) =
    (s, t, Constrainedrewriter.trivial_constraint_simplification
              (alphabet ()) (environment ()) phi)
  in
  List.map simpeq equations
;;

(**
 * This function starts up inductive theorem proving for the
 * given TRS: we get the rules from [trs], move them to their own
 * environment, move initializations into the constraint, and store
 * the alphabet and resulting environment and rules in the global
 * variables.
 * It returns a tuple: the old default TRS (if any), and the
 * equations ported to the new main environment.  The variables for
 * the equations are assumed to be in the given TRS's main
 * environment.
 *)
let initialise trs eqs =
  (* get data from trs *)
  let oldalf = Trs.get_alphabet trs in
  let oldenv = Trs.get_main_environment trs in
  let funnames = Alphabet.fun_names oldalf in
  let trsrules = Trs.get_rules trs in
  (* create new environment, and move all equations to it *)
  let e = Environment.empty 100 in
  let update_environment kind (rule, oldenv) =
    let environment_change =
      if kind = "rule" then Rule.environment_transfer
      else Rule.fresh_renaming
    in
    try environment_change rule oldenv e funnames
    with Failure msg ->
      failwith ("Environment error with " ^ kind ^ " " ^
        (Rule.to_string rule) ^ ": " ^ msg)
  in
  let fulleqs = List.map (fun eq -> (eq, oldenv)) eqs in
  let neweqs = List.map (update_environment "equation") fulleqs in
  (* create new alphabet and add equation symbol *)
  let a = Alphabet.copy oldalf in
  let relevantsort rule = Term.get_sort a e (Rule.lhs rule) in
  let sorts = List.unique
    ((List.map relevantsort eqs) @ (Alphabet.find_sorts a)) in
  let rulesort = Sort.from_string "rule" in
  let makesd sort = Sortdeclaration.create [sort;sort] rulesort in
  let makesymb sort =
    let sd = makesd sort in
    let rec attempt name =
      if Alphabet.mem_fun_name name a then attempt (name ^ "'")
      else name
    in
    let choosename = attempt ("EQUAL_" ^ (Sort.to_string sort)) in
    let f = Alphabet.create_fun sd choosename a in
    Alphabet.set_symbol_kind f Alphabet.Terms a ;
    (sort, f)
  in
  let eqsymbs = List.map makesymb sorts in
  (* save everything for accessing ease *)
  internal_alphabet := Some a ;
  internal_environment := Some e ;
  internal_funnames := Alphabet.fun_names a ;
  internal_defs := Trs.def_symbols trs ;
  let is_constructor f =
    (Alphabet.find_symbol_kind f a = Alphabet.Terms) &&
    not (List.mem f !internal_defs)
  in
  internal_cons := Alphabet.funs ~p:is_constructor a ;
  internal_specialvars := VarSet.empty ;
  internal_logicsorts := Alphabet.find_logical_sorts a ;
  internal_equation := eqsymbs; ;
  internal_recursion_data := get_recursion_data trsrules ;
  internal_weights := calculate_function_weight (List.map fst trsrules) ;
  (* move all rules to the same environment, and move fresh variables
  from right-hand sides into the constraints (as these must be
  instantiated by values too); also replace variable initialisations
  by fields v_i of special variables. *)
  let rules = List.map (update_environment "rule") trsrules in
  let update_lvar rule =
    let (l,r,phi) = rule_to_equation rule in
    let (lvars, rvars) = (Term.vars l, Term.vars r) in
    let newvars = List.diff (List.diff rvars lvars) (Term.vars phi) in
    let obvious x = create_equal (Term.make_var x) (Term.make_var x) in
    let newconstraints = List.map obvious newvars in
    let c = List.fold_left create_and phi newconstraints in
    equation_to_rule (l,r,c)
  in
  let rules = List.map update_lvar rules in
  let rules = List.map (replace_rule_initialisations a e) rules in
  let calcfree rule = Rule.calculation_free a e rule in
  let rules = List.map calcfree rules in
  internal_rules := rules ;
  (* create new default TRS, and return the old one *)
  let newtrs = Trs.create a e in
  let addenv rule = (rule, e) in
  Trs.set_rules (List.map addenv rules) newtrs ;
  let retval =
    if Trs.has_current () then Some (Trs.get_current ())
    else None
  in
  Trs.set_current newtrs ;
  (retval, prepare_equations neweqs)
;;

(*******************************************************************)
(* the following functions supply the main functionality for       *)
(* inductive theorem proving (rules like simplify and expand)      *)
(*******************************************************************)

(** checks whether the deletion rule is applicable *)
let try_deletion (s, t, phi) =
  if s = t then Some true else
  match Solver.satisfiable_formulas [phi] (smt ()) (environment ()) with
    | (Smtresults.SAT, _) -> Some false
    | (Smtresults.UNSAT, _) -> Some true
    | _ -> None
;;

(**
 * applies eq-deletion to the given goal as much as possible; returns
 * None if this is not possible, otherwise returns an updated goal
 *)
let try_eqdelete (s, t, phi) =
  let is_logical term =
    if Term.check_logical_term (alphabet ()) term = None then
      let fv = Term.vars term in
      List.for_all is_logical_variable fv
    else false
  in
  let rec unequal_in_context a b =
    if Term.is_var a then (
      if (a = b) then []
      else if is_logical b then [(a,b)]
      else raise Elogic.Not_matchable
    )
    else if Term.is_var b then (
      if is_logical a then [(a,b)]
      else raise Elogic.Not_matchable
    )
    else (
      let (f, ss) = (Term.root a, Term.args a) in
      let (g, tt) = (Term.root b, Term.args b) in
      if f <> g then raise Elogic.Not_matchable
      else (
        let merged = List.combine ss tt in
        List.flat_map (uncurry unequal_in_context) merged
      )
    )
  in
  try
    let lst = unequal_in_context s t in
    if lst = [] then None else
    let eqlst = List.map (uncurry create_equal) lst in
    let psi = create_not (create_conjunction eqlst) in
    Some (s, t, create_and phi psi)
  with _ -> None
;;

(* attempts to apply the constructor clause, taking children out of
constructor parents (not only topmost); this returns a list of
pairs (newgoal, position within the constructor context) *)
let try_constructor (lhs, rhs, phi) =
  let rec constructor_children (l, r) =
    let failure = ([((l, r, phi), Position.root)], false) in
    match (l, r) with
      | (Term.Fun (f, args1), Term.Fun (g, args2)) ->
        if f <> g then failure
        else if not (is_constructor f) then failure
        else (
          try
            let zipped = List.zip args1 args2 in
            let children i pair =
              let lst = fst (constructor_children pair) in
              let f (eq, p) = (eq, Position.add_first i p) in
              List.map f lst
            in
           let pairs = List.flat_mapi children zipped in
           (pairs, true)
          with _ -> failure
        )
      | (Term.Forall (x, a), Term.Forall (y, b))
      | (Term.Exists (x, a), Term.Exists (y, b)) ->
        let xvar = Term.make_var x in
        let gamma = Substitution.of_list [(y, xvar)] in
        let bsub = Substitution.apply_term gamma b in
        let isvalue = create_equal xvar xvar in
        let phi = create_and phi isvalue in
        ([((a, bsub, phi), Position.of_list [0])], true)
      | _ -> failure
  in
  let (pairs, didsomething) = constructor_children (lhs, rhs) in
  if not didsomething then None
  else Some pairs
;;

(* checks whether the sides of the goal are headed by different constructors *)
let try_anti_constructor (lhs, rhs, phi) =
  match (Term.root lhs, Term.root rhs) with
    | (Some f, Some g) ->
      if f = g then false
      else (is_constructor f) && (is_constructor g)
    | (Some f, _) -> is_constructor f
    | (_, Some g) -> is_constructor g
    | _ -> false
;;

(* checks whether both sides are logical terms (all variables count) *)
let try_all_logical (lhs, rhs, _) =
  let alf = alphabet () in
  (Term.check_logical_term alf lhs = None) &&
  (Term.check_logical_term alf rhs = None)
;;

(** Swaps the left- and right-hand side of a goal. *)
let try_swap (lhs, rhs, phi) = (rhs, lhs, phi);;

(* applies eq-delete and delete on the given goal, returning either
the commands to delete the goal or none *)
let try_riddance goal =
  let (eqed_equation, base) = (
    match try_eqdelete goal with
      | Some eq -> (eq, ["eq-delete"])
      | None -> (goal, [])
  ) in
  match try_deletion (eqed_equation) with
    | Some true -> Some (base @ ["delete"], true)
    | Some false ->
      if try_all_logical goal then Some (base @ ["disprove"], false)
      else None
    | None -> None
;;

(* applies the constructor rule, eq-delete and delete on all results,
until nothing changes anymore *)
let try_trivial goal =
  let equations = (
    match try_constructor goal with
      | None -> [goal]
      | Some lst -> List.map fst lst
  ) in
  let riddance equation = (
    match try_riddance equation with
      | Some (_, true) -> []
      | _ -> [equation]
  ) in
  List.flat_map riddance equations
;;

(**
 * attempts to simplify the goal on the given position by doing a
 * calculation step; returns None if this is impossible, or Some
 * newgoal if it can be done!
 * Note: we do not currently check whether the constraint for the
 * equation is satisfiable!
 *)
let try_calculate goal pos =
  let a = Some (alphabet ()) in
  let e = Some (environment ()) in
  let cterm = make_equation_cterm goal in
  let p = Position.add_first 0 pos in
  match Constrainedrewriter.calc_reduce cterm p a e with
    | None -> None
    | Some cterm -> Some (unmake_constrained_term cterm)
;;

(**
 * Attempts to simplify the goal by calc-normalising both sides.
 *)
let calc_normalise goal =
  let cterm = make_equation_cterm goal in
  unmake_constrained_term (Constrainedrewriter.calc_normalise cterm None None)
;;

(**
 * Given a premise (already split up in its conjunctive parts) and
 * a number of conclusions, returns those conclusions which no longer
 * hold if you generalise the special variables
 *)
let nongeneralisable_conclusions a e premiseparts _ conclusionparts =
  (*
  let eq = try Some (Alphabet.get_equal_symbol a) with Not_found -> None in
  let no_definition term =
    if Term.root term <> eq then true else
    match Term.args term with
      | [Term.Var x; def] | [def; Term.Var x] ->
        not (VarSet.mem x (specialvars ()))
      | _ -> true
  in  
  let len = List.length premiseparts in
  let premiseparts = List.filter no_definition premiseparts in
  if List.length premiseparts = len then [] else
  let conclusionparts = List.filter no_definition conclusionparts in
  let premise = create_conjunction premiseparts in
  let negate form =
    Term.make_function a e (Alphabet.get_not_symbol a) [form] in
  let not_implied conclusion =
    Solver.satisfiable [premise;negate conclusion] (smt ()) e
  in
  let newconclusions = List.filter not_implied conclusionparts in
  List.filter not_implied conclusionparts
  *)
  []
  (*
  TODO: this costs too much time, but perhaps we can use it in a
        new strategy which doesn't use backtracking?
  *)
;;

(** main part of simplification: simplifies a constrained term *)
let try_simplify_main cterm rule pos =
  let vphi = List.flat_map Term.vars (Rule.constraints rule) in
  (*let forbidden = List.diff vphi (Term.vars (Rule.lhs rule)) in*)
  let isspecial y = VarSet.mem y (specialvars ()) in
  let forbidden = List.filter isspecial vphi in
  let allowed x s =
    if Term.is_var s then
      let y = List.hd (Term.vars s) in
      not (VarSet.mem y (specialvars ()))
    else true
  in
  Constrainedrewriter.rule_reduce_single_env cterm
          (environment ()) pos [rule] true
          ~forbidden_variables:[forbidden]
          ~subst_allowed:[allowed]
          ~shuffle:false
          ~extra_constraints:nongeneralisable_conclusions
          false
;;

(**
 * attempts to simplify the goal on the given position with the given
 * rule; returns None if this is impossible, or Some newgoal if it
 * can be done!
 * Note: we do not currently check whether the constraint for the
 * equation is satisfiable!
 *)
let try_simplify goal rule pos =
  let cterm = make_equation_cterm goal in
  let p = Position.add_first 0 pos in
  match try_simplify_main cterm rule p with
    | None -> None
    | Some newcterm -> Some (unmake_constrained_term newcterm)
;;

(** returns None if the given position in s does not have the form
f(s1,...,sn) with f a defined symbol and all si constructor terms,
otherwise Some (f, [s1,...,sn], f(s1,...,sn)) *)
let expandable_position s pos =
  let subterm = Term.subterm pos s in
  match subterm with
    | Term.Var _ -> None
    | Term.Forall _ | Term.Exists _ -> None
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      let defs = defsymbs () in
      let notadef f = not (List.mem f defs) in
      if notadef f then None
      else (
        let symbs = List.unique (List.flat_map Term.funs args) in
        let a = alphabet () in
        let ok f =
            (Alphabet.is_value f a) ||
            ((Alphabet.find_symbol_kind f a = Alphabet.Terms) &&
             (notadef f))
        in
        if List.for_all ok symbs then Some (f, args, subterm)
        else None
      )
;;

(**
 * A weak version of expansion that doesn't add an extra rule (and
 * thus doesn't care whether the root symbol of the expanded side is
 * defined, or whether the resulting system is terminating), and, if
 * weak is set to true, also doesn't automatically reduce the results.
 *)
let try_case goal pos weak =
  let (s, t, phi) = goal in
  match expandable_position s pos with | None -> None | Some (f, args, sub) ->
  let e = environment () in
  let fresh_replace x =
    let y = Environment.create_var_like x e (funnames ()) e in
    (x, Term.make_var y)
  in
  let is_special x = VarSet.mem x (specialvars ()) in
  (* makes sure substitution(vi) maps to itself, or throws
  Not_unifiable if this cannot be achieved *)
  let fix_special substitution =
    let f x gx subst =
      if VarSet.mem x (specialvars ()) then (
        match gx with
          | Term.Var y -> Substitution.add y (Term.Var x) subst
          | _ -> raise Elogic.Not_unifiable
      )
      else subst
    in
    try
      let extra = Substitution.fold f substitution Substitution.empty in
      let result = Substitution.map (Substitution.apply_term extra) substitution in
      Substitution.union result extra
    with Substitution.Inconsistent -> failwith ("Strange variable " ^
      "replacement in induction module: when unifying an equation " ^
      "with a rule, two special variables are mapped to the same " ^
      "result variable.  This should never happen in a left-linear " ^
      "system!")
      (* Note: left-linearity needs only to be required for variables
         of a sort in Sigma_theory, which can always be achieved. *)
  in
  let fix_rest freshvars substitution =
    let add_fresh subst x =
      let replacement =
        if is_special x then Term.Var x
        else snd (fresh_replace x)
      in
      try Substitution.add x replacement subst
      with Substitution.Inconsistent -> failwith ("Looks like rule " ^
        "variables are not unique in try_case!")
    in
    List.fold_left add_fresh substitution freshvars
  in
  let fix_vars vars substitution =
    let sublist = Substitution.to_list substitution in
    let f (_, s) = Term.vars s in
    let svars = List.intersect vars (List.flat_map f sublist) in
    let gamma = Substitution.of_list (List.map fresh_replace svars) in
    let update (x, s) = (x, Substitution.apply_term gamma s) in
    let newsublist = List.map update sublist in
    let newsub = Substitution.of_list newsublist in
    try Substitution.union newsub gamma
    with Substitution.Inconsistent -> failwith ("Strange variable " ^
      "replacement in induction module: a variable is both in the " ^
      "domain and mapped to something else in the range.  While " ^
      "this is allowed, it's unexpected.  Please rewrite try_case.")
  in
  let case_for rule =
    let l = Rule.lhs rule in
    let lvars = Term.vars l in
    let cs = Rule.constraints rule in
    let restvars = List.diff (List.unique (List.flat_map Term.vars cs)) lvars in
    try
      let base = Elogic.unify l sub in
      let gamma = fix_vars lvars (fix_rest restvars (fix_special base)) in
      let fix q = Substitution.apply_term gamma q in
      let newconstr = create_conjunction ((fix phi) :: (List.map fix cs)) in
      let neweq = (fix s, fix t, newconstr) in
      if weak then [neweq]
      else match try_simplify neweq rule pos with
        | None ->
          if Util.query_debugging () then
            Printf.printf "Strange! Simplifying fails after case!\n" ;
          []
        | Some result -> [result]
    with Elogic.Not_unifiable -> []
  in
  let neweqs = List.flat_map case_for (rules ()) in
  let equation_compare_left (s1, _, _) (s2, _, _) = term_compare s1 s2 in
  let neweqs = List.sort equation_compare_left neweqs in
  Some neweqs
;;

(**
 * Attempts to apply the expansion rule on the goal on the given position;
 * if this fails, None is returned, otherwise a list of new goals together
 * with the resulting rule.
 *)
let try_expand force goal pos extra =
  let (s, t, phi) = goal in
  let newrules = equation_to_rule goal :: extra in
  if (not force) && (not (terminating newrules true)) then None else
  match try_case goal pos false with
    | None -> None
    | Some expd -> Some (expd, Rule.create s t [phi])
;;

(**
 * Generalises the given list of constants in the goal, and returns
 * the updated goal!
 *)
let try_generalise (s, t, phi) vars =
  let env = environment () in
  let alf = alphabet () in
  let fn = funnames () in
  let renaming name =
    if name.[0] != 'v' then None else
    let n = "w" ^ (String.sub name 1 ((String.length name) - 1)) in
    if Environment.mem_var_name n env then None else
    if Alphabet.mem_fun_name n alf then None else
    Some n
  in
  let freshvar x =
    let sort = Environment.find_sort x env in
    let y = match renaming (Variable.find_name x) with
      | None -> Environment.create_sorted_var sort fn env
      | Some newname -> Environment.create_var newname sort env
    in
    (x, Term.make_var y)
  in
  let eq =
    try Alphabet.get_equal_symbol alf
    with Not_found -> failwith "No equality symbol set!"
  in
  let getsymb f = try [f alf] with Not_found -> [] in
  let comparison_symbols = List.flat_map getsymb
    [Alphabet.get_geq_symbol; Alphabet.get_leq_symbol;
     Alphabet.get_greater_symbol; Alphabet.get_smaller_symbol]
  in
  let splitdef term =
    match term with
      | Term.Fun (f, [a;b]) | Term.InstanceFun (f, [a;b], _) ->
        if f <> eq then None
        else if (Term.is_var a) && (List.is_supset vars (Term.vars a))
        then Some (List.hd (Term.vars a), b)
        else if (Term.is_var b) && (List.is_supset vars (Term.vars b))
        then Some (List.hd (Term.vars b), a)
        else None
    | term -> None
  in
  let replace_deffed_var defs = function
    | Term.Var x -> (
        try List.assoc x defs
        with Not_found -> Term.Var x
      )
    | term -> term
  in
  let fix_quantification defs = function
    | Term.Forall (x, term) ->
      let ((lower, lstrict), (upper, ustrict), body) =
        Smtquantifiers.universal_range x alf term in
      let lower = replace_deffed_var defs lower in
      let upper = replace_deffed_var defs upper in
      Smtquantifiers.universal_quantification x lower lstrict upper
                                              ustrict body alf
    | term -> term
  in
  let fix_comparisons defs x =
    let rep = replace_deffed_var defs in
    match x with
      | Term.Fun (f, [a;b]) ->
        if not (List.mem f comparison_symbols) then [x]
        else [x; Term.Fun (f, [rep a; rep b])]
      | Term.InstanceFun (f, [a;b], sort) ->
        if not (List.mem f comparison_symbols) then [x]
        else [x; Term.InstanceFun (f, [rep a; rep b], sort)]
      | _ -> [x]
  in
  let replace = Substitution.of_list (List.map freshvar vars) in
  let parts = get_conjunction_parts phi in
  let (defs, goodparts) = List.partition_option splitdef parts in
  let betterparts = List.map (fix_quantification defs) goodparts in
  let bestparts = List.flat_map (fix_comparisons defs) betterparts in
  let rep = Substitution.apply_term replace in
  (rep s, rep t, rep (create_conjunction bestparts))
;;

let try_abstraction (s, t, phi) =
  (* returns the outermost subterms of term, together with their
     position (as a sub-position of pos), whose root symbol is
     anything other than a non-recursive defined symbol *)
  let rec subs term pos = match term with
    | Term.Var _ | Term.Forall _ | Term.Exists _ -> [(term, pos)]
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      if (not (is_constructor f)) &&
         (recursion_style f = NonRecursive) then
        let recurse i arg = subs arg (Position.add_last i pos) in
        List.flat_mapi recurse args
      else [(term, pos)]
  in
  (* tests whether the given two terms are equivalent under phi *)
  let equivalent_subs u v =
    if u = v then true else
    match try_eqdelete (u, v, phi) with
      | None -> false
      | Some (_,_,psi) -> (
        match try_deletion (u, v, psi) with
          | Some true -> true
          | _ -> false
      )
  in
  (* finds a pairing of the subterms in ssubs with those in tsubs
     such that each pair consists of two equivalent terms *)
  let rec find_pairings ssubs tsubs sofar =
    match ssubs with [] -> Some sofar | (sterm,spos) :: ssubtail ->
    let matches (tterm,tpos) = equivalent_subs sterm tterm in
    try
      let (tterm,tpos) = List.find matches tsubs in
      let nottpos (x,p) = p <> tpos in
      let tsubtail = List.filter nottpos tsubs in
      find_pairings ssubtail tsubtail ((sterm,tterm,spos,tpos) :: sofar)
    with Not_found -> None
    (* TODO: in the future, we will likely want to find a better
       heuristic if there are multiple matching alternatives! *)
  in
  (* main functionality *)
  let ssubs = subs s Position.root in
  let tsubs = subs t Position.root in
  (* they need to have the same, positive number of subterms *)
  if List.length ssubs <> List.length tsubs then None else
  if List.length ssubs = 0 then None else
  (* it should be a real context *)
  if snd (List.hd ssubs) = Position.root then None else
  (* see if we can pair up all the subterms appropriately *)
  match find_pairings ssubs tsubs [] with None -> None | Some pairings ->
  (* make the abstractions *)
  let do_abstraction (term1, term2) (sub1,sub2,pos1,pos2) =
    let a = alphabet () in
    let e = environment () in
    if (sub1 = sub2) && (Term.is_var sub1) then (term1, term2) else
    if (sub1 = sub2) && (Term.check_logical_term a sub1 = None) then
      (term1, term2) else
    let sort = Term.get_sort a e sub1 in
    let x = Environment.create_sorted_var sort (funnames ()) e in
    let xvar = Term.make_var x in
    let t1 = Term.replace pos1 xvar term1 in
    let t2 = Term.replace pos2 xvar term2 in
    (t1, t2)
  in
  let (lhs,rhs) = List.fold_left do_abstraction (s,t) (List.rev pairings) in
  (* get the part of phi that is only about the remaining variables *)
  let vars = List.flat_map Term.vars [lhs;rhs] in
  let parts = get_conjunction_parts phi in
  let vargood x = List.mem x vars in
  let varsgood constr =
    let vs = Term.vars constr in
    List.for_all vargood vs
  in
  let newphi = create_conjunction (List.filter varsgood parts) in
  Some (lhs, rhs, newphi)
;;

(**
 * Rewrites the constraint in as convenient by introducing quantifiers
 * where it seems useful.
 *)
let try_alter_constraint (s, t, phi) =
  let smt = Rewriter.smt_solver (Rewriter.get_current ()) in
  let alf = alphabet () in
  let env = environment () in
  let vars = List.union (Term.vars s) (Term.vars t) in
  (s, t, Solver.simplify_constraint smt alf env vars phi)
;;

(** Merges the given variables (replacing x by y), if appropriate;
appropriate always holds if check is false, and if check is true,
then we must check whether phi => x = y holds. *)
let try_merge (s, t, phi) x y check =
  let test = if not check then true else (
    let eq = create_equal (Term.make_var x) (Term.make_var y) in
    let total = create_imply phi eq in
    Solver.valid [total] (smt ()) (environment ()) 
  ) in
  if not test then None else
  let subst = Substitution.of_list [(x, Term.make_var y)] in
  let s = Substitution.apply_term subst s in
  let t = Substitution.apply_term subst t in
  let phi = Substitution.apply_term subst phi in
  if VarSet.mem x !internal_specialvars then
    internal_specialvars := VarSet.add y !internal_specialvars ;
  Some (s, t, phi)
;;

(*******************************************************************)
(* miscellandeous functions                                        *)
(*******************************************************************)

(* returns a list of all function positions in the given term, sorted
in an innermost way *)
let term_positions term =
  let rec comp (p, f) (q, g) =
    if Position.is_root p then
      ( if Position.is_root q then 0 else 1 )
    else if Position.is_root q then -1
    else (
      let (hp, tp) = Position.split_first p in
      let (hq, tq) = Position.split_first q in
      if hp > hq then 1
      else if hp < hq then -1
      else comp (tp, f) (tq, g)
    )
  in
  List.sort comp (Term.funs_pos_with_fun term)
;;

(* returns a list of tuples: (false, <position in the left hand side
of the given goal>) or (true, <position in the right hand side>).
Variable positions are ignored, all others are present, and sorted
in an innermost way. *)
let goal_positions goal =
  let (lhs, rhs, phi) = goal in
  let left_positions = term_positions lhs in
  let right_positions = term_positions rhs in
  List.append (List.map (fun x -> (false, x)) left_positions)
              (List.map (fun x -> (true, x)) right_positions)
;;

(* returns all normal and extra rules, together with their name, in
the best order to try them *)
let get_all_rules extra_rules =
  let makeid pre i rule = (pre ^ (string_of_int (i+1)), rule) in
  let arules = List.mapi (makeid "") (rules ()) in
  let brules = List.mapi (makeid "X") extra_rules in
  List.rev_append brules arules
;;

(*******************************************************************)
(* the following functions handle strategy                         *)
(*******************************************************************)

let rec difference = function
  | (Term.Var x, Term.Var y) ->
    if x = y then Some Position.root
    else None
  | (Term.Fun (f1, args1) ,Term.Fun (f2, args2)) |
    (Term.InstanceFun (f1, args1, _), Term.InstanceFun (f2, args2, _)) ->
    let rec check i = function
      | [] -> None
      | (s, t) :: rest ->
        match difference (s, t) with
          | None -> check (i + 1) rest
          | Some position ->
            if List.for_all (fun (x, y) -> x = y) rest then
              Some (Position.add_first i position)
            else Some Position.root
    in
    if f1 <> f2 then Some Position.root
    else check 0 (List.zip args1 args2)
  | _ -> Some Position.root

(* returns true if t is unifiable with (s with all defined function
symbol occurrences replaced by distinct variables) *)
let rec def_similar (s, t) =
  match s with
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      if List.mem f (defsymbs ()) then true
      else (match t with
        | Term.Var _ -> true
        | Term.Fun (g, lst) | Term.InstanceFun (g, lst, _) ->
          (f = g) &&
          List.for_all def_similar (List.zip args lst)
        | _ -> false
      )
    | _ -> true
;;

let finalising_simplifications (s, t, phi) rules =
  let rec try_finalise s t posend posstart sofar =
    let try_finalise_with u v swap (name, rule) =
      let (lhs, rhs) = (Rule.lhs rule, Rule.rhs rule) in
      if Term.root u <> Term.root lhs then [] else
      try
        let gamma = Elogic.match_term u lhs in
        let rhsgamma = Substitution.apply_term gamma rhs in
        if not (def_similar (rhsgamma, v)) then []
        else [(swap, Position.of_list (List.rev posstart), name, rule)]
      with Elogic.Not_matchable -> []
    in
    let lst1 = List.flat_map (try_finalise_with s t false) rules in
    let lst2 = List.flat_map (try_finalise_with t s true) rules in
    let lst = lst1 @ lst2 @ sofar in
    if posend = Position.root then lst else
    let (hd, tl) = Position.split_first posend in
    let hdpos = Position.make hd in
    try_finalise (Term.subterm hdpos s) (Term.subterm hdpos t)
                 tl (hd :: posstart) lst
  in
  match difference (s, t) with
    | None -> []
    | Some pos -> try_finalise s t pos [] []
;;

let standard_simplifications goal rules =
  let positions = goal_positions goal in
  let combinations = List.product positions rules in
  let check_combination ((swap,(pos,f)), (name, rule)) =
    if Rule.left_root rule <> f then []
    else if (recursion_style f = TailRecursive) &&
            (name.[0] == 'X') then []
    else [(swap,pos,name,rule)]
  in
  List.flat_map check_combination combinations
;;

(* returns a position, the name of a rule, and whether or not you
must swap first; note that what we deem to be bad ideas are not
suggested even if they are the only possibility *)
let recommended_simplifications goal extras =
  let allrules = get_all_rules extras in
  let xrules = List.filter (fun (n,_) -> n.[0] = 'X') allrules in
  (finalising_simplifications goal xrules) @
  (standard_simplifications goal allrules)
;;

(* returns (newgoal, swap, pos, name of rule) for the best
simplification to apply to the current goal, or None if it is not
not recommended to apply a simplification here *)
let recommended_simplification goal extras =
  let rec try_options = function
    | [] -> None
    | (swap, pos, name, rule) :: rest ->
      let eq = if swap then try_swap goal else goal in
      match try_simplify eq rule pos with
        | None -> try_options rest
        | Some newgoal -> Some (newgoal, swap, pos, name)
  in
  try_options (recommended_simplifications goal extras)
;;

(* Returns all positions in the given goal where expansion or case
may be used (with false positives).  The result is a list of tuples:
(should we swap to do this expansion, should we add the rule, were
any recursive functions expanded, the position of the expansion,
the step to do this expansion). *)
let expandable_positions goal erules priority_only case_only =
  (* find the relevant positions *)
  let positions = goal_positions goal in
  let goodpos (_, (_, f)) = List.mem f !internal_defs in
  let positions = List.filter goodpos positions in
  (* determining whether the goal or inversed goal can be added as
  an extra rule *)
  let constructor_head = function
    | Term.Var _ | Term.Forall _ | Term.Exists _ -> true
    | Term.Fun (f, _) | Term.InstanceFun (f, _, _) ->
      is_constructor f
  in
  let logical_head = function
    | Term.Var _ | Term.Forall _ | Term.Exists _ -> true
    | Term.Fun (f,_) | Term.InstanceFun (f,_,_) ->
      Alphabet.find_symbol_kind f (alphabet ()) <> Alphabet.Terms
  in
  let general_recursive_head = function
    | Term.Var _ | Term.Forall _ | Term.Exists _ -> false
    | Term.Fun (f,_) | Term.InstanceFun (f,_,_) ->
      recursion_style f = GeneralRecursive
  in
  let tail_recursive_head = function
    | Term.Var _ | Term.Forall _ | Term.Exists _ -> false
    | Term.Fun (f,_) | Term.InstanceFun (f,_,_) ->
      recursion_style f = TailRecursive
  in
  let generalised (l, r, phi) =
    let vars = List.unique (List.flat_map Term.vars [l;r;phi]) in
    let isnormal y = not (VarSet.mem y (specialvars ())) in
    List.for_all isnormal vars
  in
  let variables_freed (l, r, phi) =
    let lvars = Term.vars l in
    let rvars = Term.vars r in
    let pvars = Term.vars phi in
    let dangerous = List.diff rvars lvars in
    List.diff dangerous pvars <> []
  in
  let acceptable_rule equation =
    let (l, _, _) = equation in
    if case_only then false
    else if (constructor_head l) || (logical_head l) then false
    else if Term.check_logical_term (alphabet ()) l = None then false
    else if variables_freed equation then false
    else if (not (general_recursive_head l)) &&
            (not (generalised equation)) then false
    else terminating ((equation_to_rule equation) :: erules) true
  in
  (* determining whether we have any symbols that really ought to be
  cased away immediately because they are non-recursive *)
  let norecurse (swap, (pos, f)) = recursion_style f = NonRecursive in
  let (nonrecursive, recursive) = List.partition norecurse positions in
  let left_feasible =
    if List.exists (not <.> fst) recursive then acceptable_rule goal
    else false
  in
  let right_feasible =
    if List.exists fst recursive then acceptable_rule (try_swap goal)
    else false
  in
  let swappingsensible =
    let (l, r, _) = goal in
    match (Term.root l, Term.root r) with
      | (None, _) -> true
      | (_, None) -> false
      | (Some f, Some g) ->
        (* we try getting rid of generally recursive functions first! *)
        (recursion_style f = TailRecursive) &&
        (recursion_style g <> TailRecursive)
  in
  (* calculate acceptable positions! *)
  let (expandpositions, casepositions) = (
    let (rights, lefts) = List.partition (fun (w,_) -> w) recursive in
    if (not (left_feasible)) && (not (right_feasible)) then ([], recursive)
    else if not (left_feasible) then (rights, lefts)
    else if not (right_feasible) then (lefts, rights)
    else if not swappingsensible then (recursive, [])
    else (List.append rights lefts, [])
  ) in
  let casepositions = if priority_only then [] else casepositions in
  (* return positions in the right format *)
  let fixpair expanding inc (swap, (pos, _)) =
    let kind = if expanding then "expand " else "case " in
    (swap, expanding, inc, pos, kind ^ " " ^ (to_string_position pos))
  in
  (* split general recursive expansions (which we want to do ASAP)
  and normal recursive expansions *)
  let is_general_expansion (_, (_, f)) =
    recursion_style f = GeneralRecursive in
  let (genexpandposses, nongenexpandposses) =
    List.partition is_general_expansion expandpositions
  in
  (* return positions in the order we should try them *)
  ( List.map (fixpair true true) genexpandposses ) @
  ( List.map (fixpair false false) nonrecursive ) @
  ( List.map (fixpair true true) nongenexpandposses ) @
  ( List.map (fixpair false true) casepositions )
;;

(* returns (swap, pos, command, new goals, added rules) for the
best expansion to apply to the current goal, or None if it is not
recommended to apply an expansion here *)
let recommended_expansion goal extras =
  let rec try_options = function
    | [] -> None
    | (swap, add, _, pos, cmd) :: rest ->
      let eq = if swap then try_swap goal else goal in
      if add then
        match try_expand true eq pos extras with
          | None -> try_options rest
          | Some (newgoal, rule) ->
            Some (swap, pos, cmd, newgoal, [rule])
      else
        match try_case eq pos false with
          | None -> try_options rest
          | Some newgoal ->
            Some (swap, pos, cmd, newgoal, [])
  in
  try_options (expandable_positions goal extras false false)
;;

