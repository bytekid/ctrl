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
open Util;;
open Ctrs;;
open Smt;;

module Sub = Substitution

(*** TYPES *******************************************************************)
type cterm = Term.t * Term.t;;

(*** VARIABLES ***************************************************************)
let assume_value_instantiations = ref false;;

(*** FUNCTIONS ***************************************************************)

let solver _ = Rewriter.smt_solver (Rewriter.get_current ());;

let get_some_environment = function
  | None -> Trs.get_main_environment (Trs.get_current ())
  | Some e -> e
;;

let get_some_alphabet = function
  | None -> Trs.get_alphabet (Trs.get_current ())
  | Some a -> a
;;

(*******************************************************************)
(* interactions with the smt-solver                                *)
(*******************************************************************)

let smt_check form = Solver.satisfiable_formulas [form] (solver ());;

(*******************************************************************)
(* building and recognising logical terms                          *)
(*******************************************************************)

let get_symbol getter name alphabet =
  try getter alphabet
  with Not_found -> failwith ("Cannot rewrite constrained terms " ^
    "when the " ^ name ^ " symbol is not set.")
;;

let and_symbol = get_symbol Alphabet.get_and_symbol "conjunction";;
let eq_symbol = get_symbol Alphabet.get_equal_symbol "equality";;
let not_symbol = get_symbol Alphabet.get_not_symbol "negation";;
let top_symbol = get_symbol Alphabet.get_top_symbol "top (truth)";;
let bot_symbol = get_symbol Alphabet.get_bot_symbol "bottom (falsehood)";;
let imply_symbol = get_symbol Alphabet.get_imply_symbol "implication";;

let create_logical fgetter args a e = Term.make_function a e (fgetter a) args;;

let create_top () = create_logical top_symbol [];;
let create_not s = create_logical not_symbol [s];;
let create_equal s t = create_logical eq_symbol [s;t];;
let create_and s t = create_logical and_symbol [s;t];;
let create_imply s t = create_logical imply_symbol [s;t];;

(* split a conjunction into a list of constraints (reversed, as
reversing the constraint list is typically a better heuristic) *)
let split_conjunction a constr =
  let rec parse_args app = function
    | [] -> app
    | head :: [] -> split_append app head (* optimisation *)
    | head :: tail -> parse_args (split_append app head) tail
  and split_append app phi =
    match phi with
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) -> (
          if f <> (and_symbol a) then phi :: app
          else parse_args app args
        )
      | _ -> phi :: app
  in
  split_append [] constr
;;

(* restores a reversed conjunction list into a conjunction *)
let rec build_conjunction a e constr =
  match constr with
    | [] -> Term.make_fun (top_symbol a) []
    | [head] -> head
    | head :: tail -> create_and (build_conjunction a e tail) head a e
;;
(*
(* or for right-infix: *)
let build_conjunction a constr =
  let rec build sofar = function
    | [] -> sofar
    | head :: tail ->
      let conj = and_symbol a in
      let newsofar = Term.make_fun conj [head;sofar] in
      build newsofar tail
  in
  match constr with
    | [] -> Term.make_fun (top_symbol a) []
    | head :: tail -> build head tail
;;
*)

(*******************************************************************)
(* calculating equivalent constrained terms                        *)
(*******************************************************************)

let ditch_trivialities alf phis =
  (* remove duplicates *)
  let unique = List.unique phis in
  (* remove "true" *)
  let notbydef term = Term.root term <> Some (top_symbol alf) in
  let statements = List.filter notbydef unique in
  let statements = (if statements = [] then unique else statements) in
  (* distinguish s = s terms *)
  let rec is_obvious = function
    | Term.Fun (f, [a;b]) | Term.InstanceFun (f, [a;b], _) ->
      if f = eq_symbol alf then a = b else false
    | Term.Forall (_, s) -> is_obvious s
    | _ -> false
  in
  let (equalities, remainder) = List.partition is_obvious statements in
  (* remove those trivial terms whose variables occur in the rest *)
  let rec check remainder rvars = function
    | [] -> remainder
    | equality :: tail ->
      let vars = Term.vars (List.hd (Term.args equality)) in
      if List.is_subset vars rvars then
        check remainder rvars tail
      else check (equality :: remainder) (List.union vars rvars) tail
  in
  let rvars = List.flat_map Term.vars remainder in
  check remainder rvars (List.rev equalities)
;;

let trivial_constraint_simplification alf env phi =
  let split = split_conjunction alf phi in
  let phis = ditch_trivialities alf split in
  build_conjunction alf env phis
;;

let make_cterm s phis a =
  let alphabet = get_some_alphabet a in
  (s, build_conjunction alphabet (Environment.dummy ()) phis)
;;

let restore_from_cterm (t, phi) a =
  let alphabet = get_some_alphabet a in
  (t, split_conjunction alphabet phi)
;;

(* calc-evaluates all constraints in the given list, and removes
trivial elements *)
let calculate_constraints constraintlist a =
  let simplify_constraint term = Rewriter.calc_normalise term in
  let normalised = List.map simplify_constraint constraintlist in
  let bot = bot_symbol a in
  let top = top_symbol a in
  let is_constant c term = Term.root term = Some c in
  let notop term = not (is_constant top term) in
  let bots = List.filter (is_constant bot) normalised in
  if bots <> [] then bots
  else List.filter notop normalised
;;

let cstr = List.fold_left (fun s phi -> s ^" ^ "^ (Term.to_string phi)) ""

(* performs calculations in the constraints and splits off fully
defined definitions *)
let simplify_constraints alf lst =
  let normalised = calculate_constraints lst alf in
  let rec split_conj term = match term with
    | Term.Fun (f, [a;b]) | Term.InstanceFun (f, [a;b], _) ->
      if f <> and_symbol alf then [term]
      else split_conj a @ (split_conj b)
    | _ -> [term]
  in
  let normalised' = List.concat (List.map split_conj normalised) in
  let split_def term =
    match term with
      | Term.Var x -> Left (x, Term.make_fun (top_symbol alf) [])
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) -> (
          if f <> eq_symbol alf then Right term
          else match args with
            (* do no longer require that a/b are values; ok?*)
            | (Term.Var x) :: b :: [] -> (
              Format.printf " map  %s  -> %s\n" (Term.to_string (Term.Var x)) (Term.to_string b);
              Left (x, b))
            | a :: (Term.Var x) :: [] -> 
            Format.printf " map  %s  -> %s\n" (Term.to_string (Term.Var x)) (Term.to_string a);
              Left (x, a)
            | _ :: _ :: [] -> Right term
            | _ -> failwith ("Unexpected equality: should have " ^
                             "exactly two arguments!")
          )
      | Term.Forall _ | Term.Exists _ -> Right term
  in
  let rec split_list (defs, constraints) = function
    | [] -> (defs, constraints)
    | head :: tail ->
      let sofar = ( match split_def head with
        | Left (var, value) -> ( (var, value) :: defs, constraints )
        | Right term -> ( defs, term :: constraints )
      ) in
      split_list sofar tail
  in
  let (defs, constraints) = split_list ([], []) normalised' in
  try
    let gamma = Sub.of_list defs in
    if defs = [] then (List.rev constraints, gamma)
    else (
      let subst = Sub.apply_term gamma in
      let newconstraints = List.rev_map subst constraints in
      (newconstraints, gamma)
    )
  with Sub.Inconsistent ->
    let bottom = Term.make_fun (bot_symbol alf) [] in
    ([bottom], Sub.of_list [])
;;

(* given a constrained term s [[phi /\ x = t]], returns the term
s[x:=t] [[ phi[x:=t] ]] *)
let rec simplified_form (term, phiparts) a =
  let (phiparts, gamma) = simplify_constraints a phiparts in
  if Sub.is_empty gamma then (term, phiparts)
  else simplified_form (Sub.apply_term gamma term, phiparts) a
;;

(* given a constrained term s [phi] where a variable of x is uniquely
defined by the conditions of phi, replaces x in s (and phi) by its
unique value *)
let strong_simplified_form (term, phiparts) a e =
  let (term, phiparts) = simplified_form (term, phiparts) a in
  let vars_term = Term.vars term in
  let vars_constraint = List.flat_map Term.vars phiparts in
  let logical_vars = List.intersect vars_term vars_constraint in
  let formula = build_conjunction a e phiparts in
  let (satisfiable, gamma) = smt_check formula e in
  let rec test_uniques = function
    | [] -> []
    | x :: tail ->
      try
        let xval = Sub.find x gamma in
        let eq = eq_symbol a in
        let equal = Term.make_fun eq [Term.make_var x; xval] in
        let different = Term.make_fun (not_symbol a) [equal] in
        let form = create_and formula different a e in
        let (result, newgamma) = smt_check form e in
        if (result = Smtresults.UNSAT) then (x, xval) :: test_uniques tail
        else if (result = Smtresults.SAT) then (
          let maybeunique y =
            (Sub.find y gamma) = (Sub.find y newgamma)
          in
          test_uniques (List.filter maybeunique tail)
        )
        else test_uniques tail
      with Not_found -> test_uniques tail
        (* can happen when for instance the formula is x = x, which 
        is always true; in such a case the value is definitely not
        uniquely determined! *)
  in
  match satisfiable with
    | Smtresults.UNSAT -> (term, [Term.make_fun (bot_symbol a) []])
    | Smtresults.UNKNOWN -> (term, phiparts)
    | Smtresults.SAT -> (
      let var_values = test_uniques logical_vars in
      if var_values = [] then (term, phiparts)
      else (
        let gamma = Sub.of_list var_values in
        let subst = Sub.apply_term gamma in
        (subst term, calculate_constraints (List.map subst phiparts) a)
      )
    )
;;

(** (strong) simplified form, but for outsiders *)
let simplify_constrained_term ?(trs=Trs.get_current ()) (term, phi) strong =
  let a = Trs.get_alphabet trs in
  let e = Trs.get_main_environment trs in
  let phiparts = split_conjunction a phi in
  let (s, psiparts) = (
    if strong then strong_simplified_form (term, phiparts) a e
    else simplified_form (term, phiparts) a
  ) in
  let psi = build_conjunction a e psiparts in
  (s, psi)
;;

(*******************************************************************)
(* Doing calculations                                              *)
(*******************************************************************)

(* blockedvars may not be seen as instantiated by values, even if
assume_value_instantiations is set to true! *)
let top_calc_reduce blockedvars (term, phi) alf env =
  let phivars = Term.vars phi in
  let a = get_some_alphabet alf in
  let e = get_some_environment env in
  (* returns true if the given term will be a value after
  instantiating all variables that should be logical with values,
  and after upwards-instantiating all binders with values (so
  e.g. f(a,g(x,b)) becomes a value if x is a binder and a, b are
  values, but f(g(a,a),x) does not become a value because g(a,a) is
  not a value and not above x *)
  let rec calc_normal binders term =
    if Term.is_value a term then true
    else match term with
      | Term.Var x ->
        if (!assume_value_instantiations) then
          not (List.mem x blockedvars)
        else (List.mem x phivars) || (List.mem x binders)
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
        if binders = [] then false
        else if Alphabet.find_symbol_kind f a <> Alphabet.Logical then false
        else (
          let vs = Term.vars term in
          if List.intersect vs binders = [] then false
          else List.for_all (calc_normal binders) args
        )
      | Term.Forall (x,arg) | Term.Exists (x,arg) ->
        if binders = [] then false else
        let vs = Term.vars arg in
        if List.intersect vs binders = [] then false else
        calc_normal (x :: binders) arg
  in
  let do_calculation () =
    let sort = Term.get_sort a e term in
    let anames = Alphabet.fun_names a in
    let x = Environment.create_sorted_var sort anames e in
    if (Variable.find_name x) = "b476" then
      Format.printf "b476 has sort %s\n%!" (Sort.to_string (Environment.find_sort x e));
    let xterm = Term.make_var x in
    let equality = create_equal xterm term a e in
    let newphi = create_and phi equality a e in
    (xterm, newphi)
  in
  match term with
    | Term.Var _ -> None
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      if Alphabet.find_symbol_kind f a <> Alphabet.Logical then None
      else if not (List.for_all (calc_normal []) args) then None
      else Some (do_calculation ())
    | Term.Forall (x, arg) | Term.Exists (x, arg) ->
      if not (calc_normal [x] arg) then None
      else Some (do_calculation ())
;;

let calc_reduce (term, phi) position a env =
  let (bound, sub) = Term.subterm_with_binders position term in
  match top_calc_reduce bound (sub, phi) a env with
    | None -> None
    | Some (newsub, newphi) ->
      Some (Term.replace position newsub term, newphi)
;;

let rec calc_normalise_recurse bound (term, phi) alf env =
  (* normalises calculations in each element of the given list,
  updating the constraint as we go along *)
  let rec normalise_each sofar c = function
    | [] -> (List.rev sofar, c)
    | head :: tail ->
      let (s, psi) = calc_normalise_recurse bound (head, c) alf env in
      normalise_each (s :: sofar) psi tail
  in
  (* attempts a topmost reduction after children are normalised *)
  let finish (args, psi) =
    let updatedterm = Term.replace_args term args in
    match top_calc_reduce bound (updatedterm, psi) alf env with
      | None -> (updatedterm, psi)
      | Some result -> result
  in
  (* main functionality *)
  match term with
    | Term.Var _ -> (term, phi)
    | Term.Fun (_, args) | Term.InstanceFun (_, args, _) ->
      finish (normalise_each [] phi args)
    | Term.Forall (x, arg) | Term.Exists (x, arg) ->
      let (newarg, psi) =
        calc_normalise_recurse (x :: bound) (arg, phi) alf env in
      finish ([newarg], psi)
;;

let calc_normalise = calc_normalise_recurse [];;

(*******************************************************************)
(* Doing rule steps for constrained terms                          *)
(*******************************************************************)

(**
 * returns whether all variables which occur in terms either do not
 * occur in the domain of gamma, or are mapped to variables in the
 * list of acceptable_variables, or to arbitrary variables and
 * assume_value_instantiations is set, or to values;
 * if allincluded is true, then all variables should be in the domain
 *)
let suitable_substitution gamma terms alphabet acceptable_variables allincluded =
  let vars = List.flat_map Term.vars terms in
  let test_variable x =
    if not (Sub.mem x gamma) then not allincluded
    else (
      let value = Sub.find x gamma in
      if Term.is_value alphabet value then true
      else if not (Term.is_var value) then false
      else if !assume_value_instantiations then true
      else List.is_subset (Term.vars value) acceptable_variables
    )    
  in
  List.for_all test_variable vars 
;;

(** Adds a mapping x:=y in gamma, with y fresh. *)
let add_fresh_var_mapping gamma x a xenv newenv =
  let fn = Alphabet.fun_names a in
  let replace_var x = Environment.create_var_like x xenv fn newenv in
  if Sub.mem x gamma then gamma
  else Sub.add x (Term.make_var (replace_var x)) gamma
;;

(** Adds a mapping x:=y in gamma, with y fresh, for all variables x
occurring in terms which do not yet occur in gamma. *)
let add_fresh_termsvars_mapping gamma terms forbidden a domainenv newenv =
  let add_fresh gamma x = add_fresh_var_mapping gamma x a domainenv newenv in
  let vars = List.diff (List.flat_map Term.vars terms) forbidden in
  List.fold_left add_fresh gamma vars
;;

(** check_similar returns either None, or an extension gamma of
substitution such that phi = psi gamma; the additions to the
domain are not variables in forbidden, and if sub_allowed x v
returns false, then gamma(x) = v is not added either *) 
let rec check_similar substitution phi psi forbidden sub_allowed =
  (* find a substitution gamma such that s = t gamma *)
  let correspond s t =
    try Some (Elogic.match_term s t)
    with Elogic.Not_matchable -> None
  in
  (* returns true if the suggested replacement clashes with the
  existing substitution or the forbidden and allowed variables *)
  let badreplacement (x, value) =
    if not (sub_allowed x value) then false
    else if (List.mem x forbidden) then false
    else value <> (Sub.find x substitution)
  in
  (* given Some substitution, checks whether it contains at least
  one variable occurring in substitution, and where it corresponds,
  the value also corresponds! *)
  let domain_okay = function
    | None -> false
    | Some gamma ->
      let parts = Sub.to_list gamma in
      let existing = List.filter (fun (x,_) -> Sub.mem x substitution) parts in
      let badones = List.filter badreplacement existing in
      (existing <> []) && (badones = [])
  in
  (* main functionality *)
  let somegamma = correspond phi psi in
  if not (domain_okay somegamma) then None
  else somegamma
;;

(** Updates substitution with mappings x := term, where x is a
variable occuring in psi which is not yet in the domain of the
substitution; to choose such mappings, we consider the mappings which
are already there; for example, if gamma(x) = y, and phi contains a
constraint y = u + v and psi contains a constraint x = a + b, and if
a and b are unmapped variables, then we choose gamma(a) = y and
gamma(b) = v!
However, variables in the list "forbidden" are not added, and if
sub_allowed x v returns false, then gamma(x) = v is not added.
*)
let rec degeneralise substitution phi psi forbidden sub_allowed =
  (* given an element c of psi, either returns an updated version
  gamma of substitution such that p = c gamma for some element p
  of phi, or None if we can't have that *)
  let rec update_for_constraint substitution c = function
    | [] -> None
    | phipart :: tail -> (
      match check_similar substitution phipart c forbidden sub_allowed with
        | None -> update_for_constraint substitution c tail
        | Some gamma ->
          try Some (Sub.union substitution gamma)
          with Sub.Inconsistent ->
            update_for_constraint substitution c tail
      )
  in
  (* runs update_for_constraint for each of the elements of psi,
  iteratively updating the substitution as we go along *)
  let rec update_for_all substitution didsomething = function
    | [] -> (substitution, didsomething)
    | psipart :: tail ->
      let psipartvars = Term.vars psipart in
      let notinsubst x = not (Sub.mem x substitution) in
      let relevantvars = List.filter notinsubst psipartvars in
      if relevantvars = [] then update_for_all substitution didsomething tail
      else ( match update_for_constraint substitution psipart phi with
        | None -> update_for_all substitution didsomething tail
        | Some gamma -> update_for_all gamma true tail
      )
  in
  (* repeat update_for_all until we gain no further updates! *)
  let (gamma, didsomething) = update_for_all substitution false psi in
  if didsomething then degeneralise gamma phi psi forbidden sub_allowed
  else gamma
;;

(* checks whether the given rule is top-applicable on the given
constrained term, and returns both the relevant substitution, and an
updated constraint (such that (term,phi) is equivalent to (term,newphi);
if general is false, then the substitution is chosen to be as defined
as possible also for variables which do not occur in the left-hand side
of the rule *)
let top_applicable (term, phi) e (rule, env) forbidden_variables
                   sub_allowed general extra_conclusions =
  try
    let substitution = Elogic.match_term term (Rule.lhs rule) in
    let a = Trs.get_alphabet (Trs.get_current ()) in
    let cs = Rule.constraints rule in
    let cs = List.flat_map (split_conjunction a) cs in
    let suitablevars = Term.vars phi in
    if not (suitable_substitution substitution cs a suitablevars false) then None
    else (
      let phiparts = split_conjunction a phi in
      let subst = (
        if general then substitution
        else degeneralise substitution phiparts cs
                          forbidden_variables sub_allowed
      ) in
      let gamma = add_fresh_termsvars_mapping subst
        ((Rule.rhs rule) :: cs) forbidden_variables a env e in
      let csgamma = List.map (Sub.apply_term gamma) cs in
      (* Now we split csgamma into psi1 and psi2, such that all new
      variables occur in psi1. *)
      let oldvars = List.unique (List.flat_map Term.vars (term :: phiparts)) in
      let allvars = List.unique (List.flat_map Term.vars csgamma) in
      let newvars = List.diff allvars oldvars in
      let hasnewvar c = List.intersect newvars (Term.vars c) <> [] in
      let (psi1, psi2) = List.partition hasnewvar csgamma in
      let psi2 = List.diff psi2 phiparts in
      (* Suppose we can prove that phi => EX x1...xn[psi1 /\ psi2].
      Then phi => EX x1...xn[phi /\ psi1], and phi /\ psi1 => phi, so
      the constrained term s [phi] is equivalent to s [phi /\ psi1].
      Moreover, (phi /\ psi1) => (psi1 /\ psi2) (as phi => psi2), so 
      we can apply the rule on this new constrained term, leading to
      r gamma [phi /\ psi1]. *)
      (* Remove parts which are obviously implied *)
      if Solver.existential_implication newvars phi psi1 psi2
                                        (solver ()) e then (
        let constraints = List.append psi1 phiparts in
        let constraints = (extra_conclusions a e phiparts psi1 psi2) @
                          constraints in
        Some (gamma, build_conjunction a e constraints)
      )
      else None
    )
  with
    | Elogic.Not_matchable -> None
    | Rule.Not_an_lctrs -> failwith "Please use constrained reduction only for LCTRS rules"
    | Sub.Inconsistent -> failwith "Inconsistent substitution"
;;

(* given a simplified constrained term and a rule, tries to reduce
the term at the root with the given rule *)
let top_rule_reduce cterm ctermenv (rule, env) calculate
                    forbidden_variables sub_allowed general extra =
  match top_applicable cterm ctermenv (rule, env) forbidden_variables
                       sub_allowed general extra with
    | None -> None
    | Some (gamma, phi) -> (
        let rhs = Rule.rhs rule in
        let q = Sub.apply_term gamma rhs in
        if not calculate then Some (q, phi)
        else Some (calc_normalise (q,phi) None (Some ctermenv))
      )
;;

(* Reduces a constrained term (s, phi) at position p using one of the
rules in rulelist; if calc is true, then the result is calc-normalised
and if general is true, then the result is as general as possible.
Here, rulelist contains tuples (rule, rule_environment,
forbidden_variables, sub_allowed), where forbidden_variables is a list
of variables in rule_environment which should not be in the domain of
the substitution used, and should not be considered for simplification
of the constraint; sub_allowed is a function mapping pairs (x,term)
(where x is a variable in rule_environment) to true or false, with
false making it so gamma(x) <> term. Here, the choice for gamma(x)
with x in the left-hand side of the rule is not affected by either
forbidden_variables or sub_allowed *)
let all_rule_reduce (s, phi) e p rulelist calc general extra =
  (* necessary information *)
  let a = Trs.get_alphabet (Trs.get_current ()) in
  (* find the first rule which "sub" can be top-reduced with *)
  let rec try_each sub = function
    | [] -> None
    | (rule, env, forbidden_variables, sub_allowed) :: tail -> (
      match top_rule_reduce (sub, phi) e (rule, env) calc
              forbidden_variables sub_allowed general extra with
        | None -> try_each sub tail
        | t -> t
      )
  in
  (* returns whether this is something that can be assumed to be
  instantiated with a value *)
  let is_calculatable term psi =
    if Term.is_value a term then true
    else if not (Term.is_var term) then false
    else List.mem (List.hd (Term.vars term)) (Term.vars psi) ||
         !assume_value_instantiations
  in
  (* returns whether the given term is a logical value-context,
  PROVIDED that a child is a logical value-context <==> checker
  <boundvars> <index> <child> returns true *)
  let is_checked_logical_value_context psi bound checker term =
    if is_calculatable term psi then true
    else if bound = [] then false
    else if List.intersect (Term.vars term) bound = [] then false
    else match term with
      | Term.Var x -> List.mem x bound
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
        if not (Alphabet.find_symbol_kind f a = Alphabet.Logical) then false
        else List.for_alli (checker bound) args
      | Term.Exists (x, arg) | Term.Forall (x, arg) ->
        checker (x :: bound) 0 arg
  in
  (* returns whether the given term is a logical value-context, that
  is, all its subterms are values, unless they are logical terms with
  a bound variable as subterm *)
  let rec is_logical_value_context psi bound term =
    let checker bd _ = is_logical_value_context psi bd in
    is_checked_logical_value_context psi bound checker term
  in
  (* handles the functionality for all_rule_reduce, by recursing over
  the term and position; the return value is a pair, the second item
  of which indicates whether the result is a logical value-context
  AND we have to do something about logical value-contexts (if so,
  additional calculations may be done with it) *)
  let rec subfun term position bound =
    if position = Position.root then (
      match try_each term rulelist with
        | None -> (None, false)
        | Some (q, newphi) as pair ->
          if not calc then (pair, false)
          else (pair, is_logical_value_context newphi bound q)
    )
    else (
      let (head, tail) = Position.split_first position in
      let poshead = Position.make head in
      let (xs, sub) = Term.subterm_with_binders poshead term in
      match subfun sub tail (xs @ bound) with
        | (None, _) -> (None, false)
        | (Some (newsub, newphi), isvalue) ->
          let replaced = Term.replace poshead newsub term in
          if not isvalue then (Some (replaced, newphi), false)
          else match top_calc_reduce bound (replaced, newphi) (Some a)
                                (Some e) with
            | Some value -> (Some value, true)
            | None ->
              let checker bd i arg =
                if i = head then true
                else is_logical_value_context newphi bd arg
              in
              let logicalcontext = is_checked_logical_value_context
                        newphi bound checker replaced in
              (Some (replaced, newphi), logicalcontext)
    )
  in
  fst (subfun s p [])
;;

(** returns a convenient default function for sub_allowed *)
let substokay x y = true;;

(** given a list lst which is either empty or has the same length as
rules, returns a list of the same length as rules, simply creating a
default list if lst is originally empty *)
let fixlist lst rules default =
  if lst = [] then List.map (const default) rules
  else lst
;;

(* reduces using an aribtrary rule in a trs *)
let trs_reduce ?(trs=Trs.get_current ()) (s, phi) p calc general =
  let e = Trs.get_main_environment trs in
  let rules = Rewriter.shuffle (Trs.get_rules trs) in
  let allok (rule, env) = (rule, env, [], substokay) in
  let rulelist = List.map allok rules in
  let extracs _ _ _ _ _ = [] in
  all_rule_reduce (s, phi) e p rulelist calc general extracs
;;

(* reduces using one of the given rules with environment *)
let rule_reduce (s, phi) env p rules calc
    ?(forbidden_variables = []) ?(subst_allowed = []) ?(shuffle = true)
    ?(extra_constraints = fun _ _ _ _ _ -> []) general =
  let forbidden_variables = fixlist forbidden_variables rules [] in
  let subst_allowed = fixlist subst_allowed rules substokay in
  let combi = List.zip rules forbidden_variables in
  let combi = List.zip combi subst_allowed in
  let make_quadruple (((rule, env), fv), sa) = (rule, env, fv, sa) in
  let rulelist = List.map make_quadruple combi in
  let rulelist =
    if shuffle then Rewriter.shuffle rulelist
    else rulelist
  in
  all_rule_reduce (s, phi) env p rulelist calc general extra_constraints
;;

(* reduces using one of the given rules, which are all based in the
   given environment *)
let rule_reduce_single_env (s, phi) env p rules calc
    ?(forbidden_variables = []) ?(subst_allowed = []) ?(shuffle = true)
    ?(extra_constraints = fun _ _ _ _ _ -> []) general =
  let addenv rule = (rule, env) in
  rule_reduce (s, phi) env p (List.map addenv rules) calc
              ~forbidden_variables:forbidden_variables
              ~subst_allowed:subst_allowed
              ~shuffle:shuffle
              ~extra_constraints:extra_constraints general
;;

(** reduces the constrained term to "normal form" in an innermost way *)
let innermost_normalise (t, phi) general simp =
  let constraint_from_reduction = function
    | [] -> None
    | (s, phi) :: tail -> Some phi
  in
  let rec map_with_info f info infogetter = function
    | [] -> []
    | head :: tail ->
      let f_head = f info head in
      let newinfo = (match infogetter f_head with
        | None -> info
        | Some i -> i
      ) in
      f_head :: map_with_info f newinfo infogetter tail
  in
  let rec rec_reduce bound t phi sofar =
    match t with
    | Term.Var _ -> sofar
    | Term.Fun (_, args) | Term.InstanceFun (_, args, _) ->
      let f psi arg = rec_reduce bound arg psi [] in
      let argsreduction = map_with_info f phi constraint_from_reduction args in
      let argsreduction = List.map List.rev argsreduction in
      make_reduction bound 0 t phi sofar argsreduction
    | Term.Forall (x, arg) | Term.Exists (x, arg) ->
      let argreduction = rec_reduce (x :: bound) arg phi [] in
      make_reduction bound 0 t phi sofar [argreduction]
  and make_reduction bound i term phi sofar = function
    | [] -> make_head_step bound term phi sofar
    | [] :: tail -> make_reduction bound (i+1) term phi sofar tail
    | ((s, psi) :: rest) :: tail ->
      let pos = Position.make i in
      let q = Term.replace pos s term in
      make_reduction bound i q psi ((q, psi) :: sofar) (rest :: tail)
  and make_head_step bound t phi sofar =
    match top_calc_reduce bound (t, phi) None None with
      | Some (s, psi) -> (s, psi) :: sofar
      | None -> 
        let (t, phi) = (
          if simp then simplify_constrained_term (t, phi) true
          else (t, phi)
        ) in
        match trs_reduce (t, phi) Position.root false general with
          | Some (s, psi) -> rec_reduce bound s psi ((s, psi) :: sofar)
          | None -> sofar
  in
  List.rev (rec_reduce [] t phi [(t, phi)])
;;

let rec reduce_to_normal (t, phi) general simp =
  let (t, phi) = (
    if simp then simplify_constrained_term (t, phi) true
    else (t, phi)
  ) in
  let positions = Term.pos t in
  let attempt p =
    match calc_reduce (t, phi) p None None with
      | Some (s, psi) -> Some (s, psi)
      | None -> match trs_reduce (t, phi) p false general with
        | Some (s, psi) -> Some (s, psi)
        | None -> None
  in
  let rec try_all = function
    | [] -> []
    | p :: tail -> (
      match attempt p with
        | None -> try_all tail
        | Some (s, psi) -> reduce_to_normal (s, psi) general simp
    )
  in
  (t, phi) :: try_all positions
;;

(* bounded rewriting *)

let do_root_steps rules calc simp gen tc =
  let alph,env = Trs.get_alphabet rules, Trs.get_main_environment rules in
  let option_list = function Some x -> [x] | _ -> [] in
  let tc = if simp then simplify_constrained_term ~trs:rules tc true else tc in
  let rs = option_list (calc_reduce tc Position.root (Some alph) (Some env)) in
  if rs <> [] then rs
  else  option_list (trs_reduce ~trs:rules tc Position.root calc gen)
;;

let rewrite_bounded calc simp general rules n t =
  let rec one_step_reducts (t,phi) =
      let root_rdcts = do_root_steps rules calc simp general (t,phi) in
      let arg_rdcts = match t with
        | Term.Var _ -> []
        | Term.Fun (f, args) ->
          arg_reducts (fun ts -> Term.Fun (f, ts)) phi [] args
        | Term.InstanceFun (f, args,x) ->
          arg_reducts (fun ts -> Term.InstanceFun (f, ts,x)) phi [] args
        | Term.Forall (x, arg) ->
          arg_reducts (fun ts -> Term.Forall(x, List.hd ts)) phi [] [arg]
        | Term.Exists (x, arg) ->
          arg_reducts (fun ts -> Term.Exists(x, List.hd ts)) phi [] [arg]
      in root_rdcts @ arg_rdcts
  and arg_reducts mk_term phi bef = function
      [] -> []
    | ti :: aft ->
      let tis = one_step_reducts (ti,phi) in
      let ts' = List.map (fun (u,psi) -> mk_term (bef @ (u :: aft)),psi) tis in
      ts' @ (arg_reducts mk_term phi (bef @ [ti]) aft)
  in
  let rec rewrite acc n ts =
    if n < 0 then acc
    else
      let reducts = List.map (fun t -> t,one_step_reducts t) ts in
      let nfs, trdcts = List.partition (fun (_,rs) -> rs = []) reducts in
      let acc' = List.map (fun (t,rs) -> (t, rs = [])) reducts @ acc in
      let rdcts = List.concat (List.map snd trdcts) in
      let ts_new = List.diff rdcts (List.map fst acc) in
      rewrite acc' (n-1) ts_new
  in rewrite [] n [t]
;;
exception Not_equal

let equivalent_cterms alph env s t phis =
  let term f = Alphabet.find_symbol_kind f alph = Alphabet.Terms in
  match s,t with 
  | Term.Fun (f,_), Term.Fun(g,_) when term f && term g && f<>g -> false
  | _ ->
    (*Format.printf "equivalent?  %s %s\n"
      (Term.to_string s) (Term.to_string t);*)
    let _,sigma = simplify_constraints alph phis in
    (*Format.printf "sub  %s \n" (Sub.to_string sigma);*)
    let s',t' = Sub.apply_term sigma s, Sub.apply_term sigma t in
    Format.printf "simp equivalent?  %s %s\n"
      (Term.to_string s') (Term.to_string t');
    if s' = t' then true
    else (
      let logical t = Term.check_logical_term alph t = None in
      let rec constraints s t =
        if s = t then []
        else match (s,t) with
          | Term.Fun (f,ss), Term.Fun(g,ts) when f = g ->
            List.concat (List.map2 constraints ss ts)
          | _ -> 
            if logical s && logical t then [create_equal s t alph env]
            else raise Not_equal
      in
      try
        let cs = constraints s t in
        let phi = create_logical and_symbol phis alph env in
        let c = create_logical and_symbol cs alph env in
        let c_imp_phi = create_imply phi c alph env in
        if Solver.valid [c_imp_phi] (solver ()) env then
         (Format.printf "this was useful\n%!"; true) else false
      with Not_equal -> false
    )
      
;;

let equalities_into_rule alph env rl =
  let l,r,phis = Rule.lhs rl, Rule.rhs rl, Rule.constraints rl in
  let term f = Alphabet.find_symbol_kind f alph = Alphabet.Terms in
  let psi,sigma = simplify_constraints alph phis in
  (*Format.printf "sub  %s \n" (Sub.to_string sigma);*)
  let l',r' = Sub.apply_term sigma l, Sub.apply_term sigma r in
  if l' <> l && not (Term.is_value alph l') then Rule.create l r' phis
  else Rule.create l' r' psi
;;

let simplify_constraints' alf lst =
  let normalised = calculate_constraints lst alf in
  let rec split_conj term = match term with
    | Term.Fun (f, [a;b]) | Term.InstanceFun (f, [a;b], _) ->
      if f <> and_symbol alf then [term]
      else split_conj a @ (split_conj b)
    | _ -> [term]
  in
  let normalised' = List.concat (List.map split_conj normalised) in
  let split_def term =
    match term with
      | Term.Var x -> Left (x, Term.make_fun (top_symbol alf) [])
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) -> (
          if f <> eq_symbol alf then Right term
          else match args with
            | (Term.Var x) :: b :: [] when Term.is_value alf b -> Left (x, b)
            | a :: (Term.Var x) :: [] when Term.is_value alf a ->  Left (x, a)
            | _ :: _ :: [] -> Right term
            | _ -> failwith ("Unexpected equality: should have " ^
                             "exactly two arguments!")
          )
      | Term.Forall _ | Term.Exists _ -> Right term
  in
  let rec split_list (defs, constraints) = function
    | [] -> (defs, constraints)
    | head :: tail ->
      let sofar = ( match split_def head with
        | Left (var, value) -> ( (var, value) :: defs, constraints )
        | Right term -> ( defs, term :: constraints )
      ) in
      split_list sofar tail
  in
  let (defs, constraints) = split_list ([], []) normalised' in
  try
    let gamma = Sub.of_list defs in
    if defs = [] then (List.rev constraints, gamma)
    else (
      let subst = Sub.apply_term gamma in
      let newconstraints = List.rev_map subst constraints in
      (newconstraints, gamma)
    )
  with Sub.Inconsistent ->
    let bottom = Term.make_fun (bot_symbol alf) [] in
    ([bottom], Sub.of_list [])
;;

let equalities_into_rule alph env rl =
  let l,r,phis = Rule.lhs rl, Rule.rhs rl, Rule.constraints rl in
  let term f = Alphabet.find_symbol_kind f alph = Alphabet.Terms in
  let psi,sigma = simplify_constraints' alph phis in
  (*Format.printf "sub  %s \n" (Sub.to_string sigma);*)
  let l',r' = Sub.apply_term sigma l, Sub.apply_term sigma r in
  Rule.create l' r' psi
;;
