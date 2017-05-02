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
open Io;;

(*** TYPES *******************************************************************)

type formula = And of formula list | Or of formula list |
               Equal of Variable.t * int |
               Unequal of Variable.t * int |
               AtleastOne of Variable.t list |
               True | False

(*** FUNCTIONS ***************************************************************)

(*****************************************************************************)
(*                            basic functionality                            *)
(*****************************************************************************)

(* the sort to make variables out of *)
let intsort = Sort.from_string "Int";;

(* returns a term representing the given number *)
let make_num num = Term.make_fun (Function.integer_symbol num) [];;

(* creates an integer variable *)
let freshvar env _ = Environment.create_sorted_var intsort [] env;;

(*****************************************************************************)
(*                       manipulating integer formulas                       *)
(*****************************************************************************)

(* gives a string representation of the given formula *)
let rec tostr_formula formula =
  let tostr_var x = Variable.find_name x in
  let tostr_sum = List.implode tostr_var " + " in
  match formula with
    | True -> "true"
    | False -> "false"
    | AtleastOne lst -> (tostr_sum lst) ^ " >= 1"
    | Equal (x, k) -> (tostr_var x) ^ " = " ^ (string_of_int k)
    | Unequal (x, k) -> (tostr_var x) ^ " != " ^ (string_of_int k)
    | And lst -> List.implode tostr_formula " /\\ " lst
    | Or lst -> List.implode tostr_formula " \\/ " lst
;;

let rec simplify_formula equalities inequalities formula =
  (* deal with and and or checks *)
  let size = function
    | True -> 0 | False -> 1
    | Equal _ -> 2 | Unequal _ -> 3 | AtleastOne _ -> 4
    | Or _ -> 5 | And _ -> 6
  in
  let compare_formulas a b =
    let cmp = compare (size a) (size b) in
    if cmp = 0 then compare a b else cmp
  in
  let handle_andor_children heq huneq (eq, ineq, sofar, changed) arg =
    let (child, ch) = simplify_formula eq ineq arg in
    let (neweq, newineq) = (
      match child with
        | Equal (x, k) -> heq x k eq ineq
        | Unequal (x, k) -> huneq x k eq ineq
        | _ -> (eq, ineq)
    ) in
    (neweq, newineq, child :: sofar, changed || ch)
  in
  let handle_andor splitter builder trivial propagate
                   handle_equal handle_unequal args =
    let args = List.flat_map splitter args in
    let args = List.sort compare_formulas args in
    let base = (equalities, inequalities, [], false) in
    let f = handle_andor_children handle_equal handle_unequal in
    let (_,_,args, changed) = List.fold_left f base args in
    let args = List.diff args [trivial] in
    if List.mem propagate args then (propagate, true)
    else match args with
      | [] -> (trivial, true)
      | [single] -> (single, true)
      | _ -> (builder args, changed)
  in
  (* deal with equality and inequality checks *)
  let mem x = List.exists (fun (y,_) -> y = x) in
  let equality_inequality ifequal ifunequal x k =
    if mem x equalities then (
      if List.assoc x equalities = k then (ifequal, true)
      else (ifunequal, true)
    )
    else (
      let xuneqk (y, i) = (y = x) && (k = i) in
      if List.exists xuneqk inequalities then (ifunequal, true)
      else (formula, false)
    )
  in
  (* deal with the Atleast checks *)
  let is_val k x =
    (List.mem (x,k) equalities) || (List.mem (x,1-k) inequalities)
  in
  let handle_atleast lst =
    if List.exists (is_val 1) lst then (True, true)
    else (
      let (nuls, rest) = List.partition (is_val 0) lst in
      if rest = [] then (False, true)
      else (AtleastOne rest, nuls <> [])
    )
  in
  (* check each of the options *)
  match formula with
    | True | False -> (formula, false)
    | Equal (x, k) -> equality_inequality True False x k
    | Unequal (x, k) -> equality_inequality False True x k
    | AtleastOne lst -> handle_atleast lst
    | And lst ->
      let and_arguments = function | And l -> l | True -> [] | a -> [a] in
      let handle_equal x num eq ineq = ((x,num) :: eq, ineq) in
      let handle_unequal x num eq ineq = (eq, (x,num)::ineq) in
      handle_andor and_arguments (fun l -> And l) True False
                   handle_equal handle_unequal lst
    | Or lst ->
      let or_arguments = function | Or l -> l | False -> [] | a -> [a] in
      let handle_equal x num eq ineq = (eq, (x,num)::ineq) in
      let handle_unequal x num eq ineq = ((x,num) :: eq, ineq) in
      handle_andor or_arguments (fun l -> Or l) False True
                   handle_equal handle_unequal lst
;;

(*****************************************************************************)
(*  doing basic SMT-checks ourselves, to avoid external calls when trivial   *)
(*****************************************************************************)

(* returns whether the given variable assignment is safe in [req],
so if there is a satisfying solution, there is one with x = value *)
let rec is_safe x value req =
  let satisfies = function
    | Equal (y, k) -> (x = y) && (value = k)
    | Unequal (y, k) -> (x = y) && (value <> k)
    | _ -> false
  in
  match req with
    | And lst -> List.for_all (is_safe x value) lst
    | Or lst ->
      if List.exists satisfies lst then true
      else List.for_all (is_safe x value) lst
    | Equal (y,_) | Unequal (y,_) ->
      if x <> y then true
      else satisfies req
    | AtleastOne lst -> (value > 0) || (not (List.mem x lst))
    | True | False -> true
;;

(* returns variable assignments which definitely do not harm the
satisfiability of the given formulas [reqs] *)
let rec find_safe reqs varswithrange =
  match varswithrange with
    | [] -> []
    | (_, 0) :: tail -> find_safe reqs tail
    | (x, n) :: tail ->
      let nmin = n - 1 in
      if List.for_all (is_safe x nmin) reqs then
        (x,nmin) :: find_safe reqs tail
      else find_safe reqs ((x,nmin) :: tail)
;;

(* simplifies the given formulas, and returns a list of variables
with values they must be set to, where this is either obvious, or
can be chosen safely *)
let rec simple_smt eqssofar formulas varswithrange =
  (* start by simplifying the formula until we have no choice
  anymore; given the shape we can expect of the original formula,
  all variables should still be in there *)
  let rec simplified formula =
    let (form, changed) = simplify_formula [] [] formula in
    if changed then simplified form
    else form
  in
  let formula = simplified (And formulas) in
  (* turn a list of Equal (x,k) constraints into (x,k) pairs *)
  let make_pair = function
    | Equal (x,k) -> (x,k)
    | _ -> failwith "WEIRD"
  in
  let make_equalities lst = List.map make_pair lst in
  (* take the equalities out of the resulting constraint, and
  consider those as fixed! *)
  let pick_equalities lst  =
    let is_equality = function | Equal _ -> true | _ -> false in
    let (equalities, rest) = List.partition is_equality lst in
    (rest, List.append (make_equalities equalities) eqssofar)
  in
  let (rest, equalities) =
    match formula with
      | Equal _ -> pick_equalities [formula]
      | And lst -> pick_equalities lst
      | _ -> ([formula], eqssofar)
  in
  (* propagate the information to varswithrange, too *)
  let notmapped assoc (x,_) = not (List.mem_assoc x assoc) in
  let vwr = List.filter (notmapped equalities) varswithrange in
  (* check whether there are problem-free choices *)
  let safechoices = find_safe rest vwr in
  if safechoices = [] then (rest, equalities, vwr)
  else (
    let instantiate p = fst (simplify_formula safechoices [] p) in
    let fs = List.map instantiate rest in
    let varsremaining = List.filter (notmapped safechoices) vwr in
    let eqs = List.append safechoices equalities in
    simple_smt eqs fs varsremaining
  )
;;

(*****************************************************************************)
(*                      interacting with the smt-solver                      *)
(*****************************************************************************)

(* makes an SMT-input style description of the given intformula *)
let rec make_smt_formula form =
  let is_num x k = "(= " ^ (Variable.find_name x) ^ " " ^
                   (string_of_int k) ^ ")" in
  match form with
    | And lst -> "(and " ^ (List.implode make_smt_formula " " lst) ^ ")"
    | Or lst -> "(or " ^ (List.implode make_smt_formula " " lst) ^ ")"
    | Equal (x,k) -> is_num x k 
    | Unequal (x,k) -> "(not " ^ (is_num x k) ^ ")"
    | AtleastOne lst ->
      let isone x = is_num x 1 in
      "(or " ^ (List.implode isone " " lst) ^ ")"
    | True -> "true"
    | False -> "false"
;;

(* calls the external smt-solver to satisfy the given formulas *)
let full_smt_check env reqs varswithrange =
  let params = List.map fst varswithrange in
  let contents = Externalsolver.create_smt_file env params reqs
                 make_smt_formula "QF_LIA" in
  let smt = Solver.solvername (Solver.intsolver) in
  let alf = Alphabet.value_alphabet () in
  let ret = Externalsolver.check_smt_file_and_parse contents smt env alf in
  ret
;;

(*****************************************************************************)
(*                          handling the processor                           *)
(*****************************************************************************)

(* returns a list of tuples (f, arity) where arity is the arity of f,
and f any root symbol of the given terms *)
let get_arities a terms =
  let getroot term = match Term.root term with
    | None -> failwith "Dependency pair with a variable!"
    | Some f -> f
  in
  let get_symbol_data f = (f, Alphabet.find_ari f a) in
  let symbs = List.unique (List.map getroot terms) in
  List.map get_symbol_data symbs
;;

let get_dp_data prob =
  let a = Dpproblem.get_alphabet prob in
  let dps = Dpproblem.get_dps prob in
  let getterms rule = [Rule.lhs rule; Rule.rhs rule] in
  let terms = List.flat_map getterms dps in
  let arities = get_arities a terms in
  (* create an environment for the interpretation variables *)
  let env = Environment.copy (Dpproblem.get_environment prob) in
  (a, env, dps, arities)
;;

(* returns the range requirements on the newly introduced variables *)
let range_requirements strictness projection =
  let inrange min max var =
    let range = List.range min max in
    let equal i = Equal (var, i) in
    let equalrange = List.map equal range in
    match equalrange with
      | [single] -> single
      | _ -> Or equalrange
  in
  let projreq (f, (x, ar)) = inrange 0 ar x in
  let strictreq x = inrange 0 2 x in
  let proj = List.map projreq projection in
  let str = List.map strictreq strictness in
  List.append proj str
;;

(* returns 0 if a = b, or 1 if a |> b; -1 otherwise *)
let superterm a b =
  let posses = Term.subterm_pos b a in
  if posses = [] then -1
  else if posses = [Position.root] then 0
  else 1
;;

(* returns the requirements that always phi => left >= right + strict
   and if strict is 1 also phi => left >= 0 *)
let dp_requirements projection strictness dps =
  let check_combi ((i, arg1), (j, arg2)) =
    (i, j, superterm arg1 arg2)
  in
  let requirements x y strictvar (i, j, value) =
    if value = -1 then
      [Or [Unequal (x,i); Unequal (y, j)]]
    else if value = 0 then
      [Or [Unequal (x, i); Unequal (y, j); Unequal (strictvar, 1)]]
    else []
  in
  let badchoice1 x goodcombis i =
    if List.for_all (function (j,_,_) -> i <> j ) goodcombis then
      [Unequal (x, i)]
    else []
  in
  let badchoice2 x goodcombis i =
    if List.for_all (function (_,j,_) -> i <> j ) goodcombis then
      [Unequal (x, i)]
    else []
  in
  let badstrict x goodcombis =
    if List.exists (fun (_,_,s) -> s = 1) goodcombis then []
    else [Unequal (x, 1)]
  in
  let requirements_for (dp, var) =
    let f1 = Rule.left_root dp in
    let f2 = Rule.right_root dp in
    let args1 = Term.args (Rule.lhs dp) in
    let args2 = Term.args (Rule.rhs dp) in
    let addindex i arg = (i, arg) in
    let (var1, var2, combinations) = (
      if f1 = f2 then
        let (x, _) = List.assoc f1 projection in
        let argoptions1 = List.mapi addindex args1 in
        let argoptions2 = List.mapi addindex args2 in
        (x, x, List.zip argoptions1 argoptions2)
      else
        let (x, _) = List.assoc f1 projection in
        let (y, _) = List.assoc f2 projection in
        let argoptions1 = List.mapi addindex args1 in
        let argoptions2 = List.mapi addindex args2 in
        (x, y, List.product argoptions1 argoptions2)
    ) in
    let combis = List.map check_combi combinations in
    let goodcombis = List.filter (fun (_,_,i) -> i >= 0) combis in
    let leftrange = List.range 0 (List.length args1) in
    let rightrange = List.range 0 (List.length args2) in
    List.flat_map id
      [List.flat_map (badchoice1 var1 goodcombis) leftrange;
       List.flat_map (badchoice2 var2 goodcombis) rightrange;
       badstrict var goodcombis; 
       List.flat_map (requirements var1 var2 var) combis]
  in
  List.flat_map requirements_for (List.zip dps strictness)
;;

(* does an SMT-check on the given formulas *)
let check_formulas env reqs varswithrange =
  let (remainder, choices, varsremaining) =
    simple_smt [] reqs varswithrange
  in

  let failure _ = failwith ("Unexpected output from SMT solver!") in
  let makeint = function
    | Term.Fun (f, []) | Term.InstanceFun (f, [], _) ->
      if Function.is_integer f then Function.integer_to_int f
      else failure ()
    | _ -> failure ()
  in
  match remainder with
    | [] | [True] -> Some choices
    | [False] -> None
    | _ -> (
      match full_smt_check env remainder varsremaining with
        | (Smtresults.SAT, gamma) ->
          let addpair var term lst = (var, makeint term) :: lst in
          Some (Substitution.fold addpair gamma choices)
        | _ -> None
    )
;;

(* assuming that the given projection function satisfies the
subterm criterion, returns (dp, left, right, strict), where strict is
true if left |> right and false if left = right *)
let check_arguments nu dp =
  let split_term = function
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) -> (f, args)
    | _ -> failwith ("Encountered variable or quantifier as left- " ^
                     "or right-hand side of a dependency pair!")
  in
  let get_arg term =
    let (f, args) = split_term term in
    List.nth args (List.assoc f nu)
  in
  let l = get_arg (Rule.lhs dp) in
  let r = get_arg (Rule.rhs dp) in
  (dp, l, r, l <> r)
;;

(* prints an explanation of how ther subterm criterion is applied;
here, nu maps function symbols to argument index *)
let explanation a dpinfo nu =
  (* print an interpretation to the user *)
  let tostr_interpretation (f, i) =
    let arity = Alphabet.find_ari f a in
    let xs = List.gen (fun i -> "x" ^ (string_of_int i)) arity in
    let xsstring = "(" ^ (List.implode id "," xs) ^ ")" in
    "  NU[" ^ (Function.find_name f) ^ xsstring ^ "] = x"
            ^ (string_of_int i)
  in
  (* print an interpreted dependency pair *)
  let tostr_interpreted_dp (_, lhs, rhs, strict) =
    let l = Printer.to_string_term lhs in
    let r = Printer.to_string_term rhs in
    let rel = if strict then " |> " else " = " in
    "  " ^ l ^ rel ^ r
  in
  (* actually do all the printing! *)
  let text =
    "We use the subterm criterion with the projection function NU:\n" ^
    (List.implode tostr_interpretation "\n" nu) ^ "\n\n" ^
    "This gives the following inequalities:\n" ^
    (List.implode tostr_interpreted_dp "\n" dpinfo) ^ "\n\n"
  in
  if List.for_all (fun (_,_,_,strict) -> strict) dpinfo then
    text ^ "All dependency pairs are strictly oriented, so the entire " ^
      "dependency pair problem may be removed.\n"
  else text ^ "We remove all the strictly oriented dependency pairs.\n"
;;

(* after having determined a suitable projection function and
strictness settings, determine the remaining dependency pairs and
report on what we did! *)
let finish a e verbose dpinfo dpprob projection =
  let expl = explanation a dpinfo projection in
  if verbose then Printf.printf "%s" expl ;
  Environment.drop e ;
  let goodinfo = List.filter (fun (_,_,_,x) -> not x) dpinfo in
  let remainingdp = List.map (fun (d,_,_,_) -> d)  goodinfo in
  if remainingdp = [] then Some ([], expl)
  else Some ([Dpproblem.set_dps remainingdp dpprob], expl)
;;

(* returns the projection function given by the chosen variables *)
let get_projection projection choices =
  let get_projection_value (f, (x,_)) =
    try (f, List.assoc x choices)
    with _ -> failwith ("Error in subterm criterion: variable " ^
      "is not assigned a value for some reason.")
  in
  List.map get_projection_value projection
;;

(* main functionality *)
let process verbose prob =
  (* basic checks *)
  let (a, env, dps, arities) = get_dp_data prob in
  if List.exists (fun (_, x) -> x = 0) arities then None else
  (* create projection and bits to indicate strict ordering *)
  let choose_projection (f, arity) = (f, (freshvar env (), arity)) in
  let projection = List.map choose_projection arities in
  let strictness = List.map (freshvar env) dps in
  let basereqs = range_requirements strictness projection in
  (* create requirements for each of the dependency pairs *)
  let dpreqs = dp_requirements projection strictness dps in
  (* and see whether they're solvable! *)
  let fullreqs = (AtleastOne strictness) ::
                 List.append dpreqs basereqs in
  let varswithrange = List.append (List.map snd projection)
                      (List.map (fun x -> (x, 2)) strictness) in
  match check_formulas env fullreqs varswithrange with
    | Some gamma ->
      let nu = get_projection projection gamma in
      let info = List.map (check_arguments nu) dps in
      finish a env verbose info prob nu
    | _ ->
      if verbose then
        Printf.printf "The subterm criterion is not applicable.\n" ;
      Environment.drop env ;
      None
;;

