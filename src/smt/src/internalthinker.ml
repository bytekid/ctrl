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

(**
 * NOTE: this code is unfinished.  The intention is to eventually move all the
 * preparsing here, and leave the internal solver to do the actual solving.
 *)


(*** OPENS *******************************************************************)

open Util;;
open Ctrs;;

(*** TYPES *******************************************************************)

type intexpression = Value of int |
                     Plus of intexpression list |
                     Times of intexpression list |
                     Var of bool * Variable.t |
                     UnknownExp of string list * intexpression list

    (* The lists for UnknownEx p(and for UnknownPred later) have a
       very specific form: the string list is exactly one longer than
       the int list, and should give a valid smt-formula in
       combination with the intexpressions; for example,
           ["(pair "; " "; ")"] [Var x; Value 3]
       together represent the smt-formula (pair x 3).
       All variables should occur inside integer expressions, to allow
       for instantiation!
    *)

and  intformula = True | False |
                  And of intformula list |
                  Or of intformula list |
                  GeqZero of intexpression |
                  IsZero of intexpression |
                  NonZero of intexpression |
                  UnknownPred of bool * string list * intexpression list |
                  Quantifier of bool * Variable.t * intexpression *
                                intexpression * intformula
    (* There is no Negation constructor, as all formulas have an obvious
       negation (for UnknownPred, the first argument indicates whether the
       predicate should be taken positively or negatively (negated) *)

type possible_results = Smtresults.t = SAT | UNSAT | UNKNOWN;;

(*** FUNCTIONS ***************************************************************)

(*****************************************************************************)
(*                                 QUICKJUMP                                 *)
(*                                                                           *)
(* - HELPER FUNCTIONS: general helping functions                             *)
(* - TRANSLATING: translating intformulas and -expressions to smt-strings    *)
(* - STRUCTURE: restructuring intformulas and -expressions to a standard form*)
(* - BOOLEANS AS INTEGERS: functions dealing with the representation of      *)
(*   boolean variables as integers                                           *)
(* - MAIN ACCESS FUNCTIONS: those called from InternalSolver                 *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(*                              HELPER FUNCTIONS                             *)
(*****************************************************************************)

(* helping function for printing an UnknownExp or UnknownPred *)
let rec combine_unknown exp_printer strs exp =
  match (strs, exp) with
    | ([last], []) -> last
    | (s :: ss, e :: es) -> s ^ (exp_printer e) ^
                            (combine_unknown exp_printer ss es)
    | ([], _) -> failwith "Illegal UnknownExp: string list too short!"
    | (lst,[]) -> failwith ("Illegal UnknownExp: string list too " ^
      "long! (" ^ (List.implode id ", " lst) ^ ")")
;;

(* helping function for find_sub_exp and find_sub_exp_int;
   finds the first argument where f returns something other than
   None, and updates its position accordingly
*)
let rec find_first f i = function
  | [] -> None
  | head :: tail -> (
    match f head with
      | None -> find_first f (i+1) tail
      | Some (pos, expr) -> Some (i::pos, expr)
  )
;;

(* returns the first position and subexpression at this position
   where checker is satisfied, or None if there is no such position;
   if "deep" is set to true, then this position must be as deep
   inside the expression as possible, otherwise it must be as low
   inside the expression as possible *)
let rec find_sub_expr checker deep expression =
  let checkargs args =
    match find_first (find_sub_expr checker deep) 0 args with
      | None ->
        if deep && (checker expression) then Some ([], expression)
        else None
      | answer -> answer
  in
  if (not deep) && (checker expression) then Some ([], expression)
  else match expression with
    | Plus args | Times args -> checkargs args
    | UnknownExp ( _, es) -> find_first (find_sub_expr checker deep) 0 es
    | Value _ | Var _ -> checkargs []
;;

(* returns the first position and expression at this position where
   the given formula has an expression, for which checker is
   satisfied; if there is no such position, None is returned *)
let rec find_sub_expr_in checker deep = function
  | And args | Or args ->
    find_first (find_sub_expr_in checker deep) 0 args
  | GeqZero arg | IsZero arg | NonZero arg ->
    find_first (find_sub_expr checker deep) 0 [arg]
  | UnknownPred (_, _, es) -> find_first (find_sub_expr checker deep) 0 es
  | Quantifier (universal, x, lower, upper, form) ->
    let answer = find_first (find_sub_expr checker deep) 0 [lower;upper] in
    if answer <> None then answer
    else find_first (find_sub_expr_in checker deep) 2 [form]
  | True | False -> None
;;

(*****************************************************************************)
(*                                 DEBUGGING                                 *)
(*****************************************************************************)

let dobracket brackets str =
  if brackets then "[" ^ str ^ "]"
  else str
;;

(* makes an SMT-input style description of the given intexpression *)
let rec print_expression brackets = function
  | Value k -> string_of_int k
  | Plus lst ->
    dobracket brackets (List.implode (print_expression true) " + " lst)
  | Times lst ->
    dobracket brackets (List.implode (print_expression true) " * " lst)
  | Var (_, x) -> Variable.to_string x
  | UnknownExp (strs, exprs) ->
    "\"" ^ (combine_unknown (print_expression true) strs exprs) ^ "\""
;;

let rec print_formula brackets = function
  | True -> "true"
  | False -> "false"
  | And lst ->
    dobracket brackets (List.implode (print_formula true) " /\\ " lst)
  | Or lst ->
    dobracket brackets (List.implode (print_formula true) " \\/ " lst)
  | GeqZero x -> dobracket brackets ((print_expression false x) ^ " >= 0")
  | IsZero x -> dobracket brackets ((print_expression false x) ^ " == 0")
  | NonZero x -> dobracket brackets ((print_expression false x) ^ " != 0")
  | UnknownPred (true, strs, exprs) ->
    "\"" ^ (combine_unknown (print_expression true) strs exprs) ^ "\""
  | UnknownPred (false, strs, exprs) ->
    dobracket brackets ("not \"" ^
      (combine_unknown (print_expression true) strs exprs) ^ "\"")
  | Quantifier (universal, x, lower, upper, form) ->
    let vname = Variable.to_string x in
    let quant = if universal then "?A " else "?E " in
    dobracket brackets (quant ^ vname ^ " in {" ^
      (print_expression false lower) ^ ",...," ^
      (print_expression false upper) ^ "} [" ^
      (print_formula false form) ^ "]")
;;

(*****************************************************************************)
(*                   TRANSLATING TO THE EXTERNAL SMT-SOLVER                  *)
(*****************************************************************************)

(* makes an SMT-input style description of the given intexpression *)
let rec make_smt_expression = function
  | Value k -> string_of_int k
  | Plus lst -> "(+ " ^ (List.implode make_smt_expression " " lst) ^ ")"
  | Times lst -> "(* " ^ (List.implode make_smt_expression " " lst) ^ ")"
  | Var (_, x) -> Variable.to_string x
  | UnknownExp (strs, exprs) ->
    combine_unknown make_smt_expression strs exprs
;;

let rec make_smt_formula = function
  | True -> "true"
  | False -> "false"
  | And lst -> "(and " ^ (List.implode make_smt_formula " " lst) ^ ")"
  | Or lst -> "(or " ^ (List.implode make_smt_formula " " lst) ^ ")"
  | GeqZero x -> "(>= " ^ (make_smt_expression x) ^ " 0)"
  | IsZero x -> "(= " ^ (make_smt_expression x) ^ " 0)"
  | NonZero x -> "(not (= " ^ (make_smt_expression x) ^ " 0))"
  | UnknownPred (true, strs, exprs) ->
    combine_unknown make_smt_expression strs exprs
  | UnknownPred (false, strs, exprs) ->
    "(not (" ^ (combine_unknown make_smt_expression strs exprs) ^ "))"
  | Quantifier (universal, x, lower, upper, form) ->
    let vname = Variable.to_string x in
    let (quant, andor, c1, c2) =
      if universal then ("forall", "or", ">", "<")
      else ("exists", "and", "<=", ">=")
    in
    "(" ^ quant ^ " ((" ^ vname ^ " Int)) (" ^ andor ^ " (" ^ c1 ^
    " " ^ (make_smt_expression lower) ^ " " ^ vname ^ ") (" ^ c2 ^
    " " ^ (make_smt_expression upper) ^ " " ^ vname ^ ") " ^
    (make_smt_formula form) ^ "))"
;;

(* makes an SMT-input file for the given list of formulas *)
let make_smt_file env parameters formulas logic =
  Externalsolver.create_smt_file env parameters formulas make_smt_formula logic
;;

(* returns whether there are any occurrences of Mul, not counting
Value * variable *)
let rec hasmuls form =
  let badmul = function
    | Times [Value _; Var _] -> false
    | Times _ -> true
    | _ -> false
  in
  let ehasmuls e = find_sub_expr badmul false e <> None in
  match form with
    | And lst | Or lst -> List.exists hasmuls lst
    | GeqZero x | IsZero x | NonZero x -> ehasmuls x
    | UnknownPred (_, _, es) -> (List.exists ehasmuls es)
    | Quantifier (universal, x, lower, upper, form) ->
      (ehasmuls lower) || (ehasmuls upper) || (hasmuls form)
    | True | False -> false
;;

(* returns whether there are any occurrences of Quantifier *)
let rec hasquantifiers = function
  | Quantifier _ -> true
  | And lst | Or lst -> List.exists hasquantifiers lst
  | _ -> false
;;

let determine_logic formula =
  let nonlinear = hasmuls formula in
  let quant = hasquantifiers formula in
  match (nonlinear, quant) with
    | (true, true) -> "UFNIA"
    | (true, false) -> "QF_NIA"
    | (false, true) -> "AUFLIA"
    | (false, false) -> "QF_LIA"
;;

(* passes a satisfiability problem on to the given external
   SMT-solver to determine the answer *)
let solve_externally formula vars alf env logic solvername =
  let problems = ( match formula with | And lst -> lst | _ -> [formula] ) in
  let text = make_smt_file env vars problems logic in
  match Externalsolver.check_smt_file_and_parse text solvername env alf with
    | (SAT, gamma) -> (SAT, gamma)
    | other -> other
;;

(*****************************************************************************)
(*                                 STRUCTURE                                 *)
(*****************************************************************************)

(* assigns a size list to every integer expression, to be used in sorting *)
let rec expression_size = function
  | Value k -> [(0, k)]
  | UnknownExp (ss, es) ->
    (1, List.length es) :: List.flat_map expression_size es
  | Var (univ, x) -> [((if univ then 3 else 2), Variable.to_int x)]
  | Plus args ->
    (4, List.length args) :: List.flat_map expression_size args
  | Times args ->
    List.flat_map id (List.rev_map expression_size args)
;;

(* assigns a size list to every formula, to be used in sorting *)
let rec formula_size = function
  | True -> [(0, 0)]
  | False -> [(1, 0)]
  | IsZero n -> (2, 1) :: expression_size n
  | NonZero n -> (3, 1) :: expression_size n
  | GeqZero n -> (4, 1) :: expression_size n
  | And lst -> (5, List.length lst) :: List.flat_map formula_size lst
  | Or lst -> (6, List.length lst) :: List.flat_map formula_size lst
  | Quantifier (b, x, l, u, phi) ->
    ((if b then 7 else 8), 3) :: (expression_size l) @
     (expression_size u) @ (formula_size phi)
  | UnknownPred (b, ss, es) ->
    ((if b then 9 else 10), List.length es) ::
    List.flat_map expression_size es
;;

(* comparing size lists *)
let rec comparelist lst1 lst2 =
  let comparetuple (a1,b1) (a2,b2) =
    if a1 = a2 then compare b1 b2 else compare a1 a2
  in
  if (lst1 = []) then ( if lst2 = [] then 0 else -1 ) else
  if lst2 = [] then 1 else
  let (hd1, tl1) = (List.hd lst1, List.tl lst1) in
  let (hd2, tl2) = (List.hd lst2, List.tl lst2) in
  let comparison = comparetuple hd1 hd2 in
  if comparison = 0 then compare tl1 tl2 else comparison
;;

(* sort the arguments of a Plus or Times *)
let sort_integer_arguments lst =
  let compare x y =
    comparelist (expression_size x) (expression_size y)
  in
  List.sort compare lst
;;

(* sort the arguments of an And or Or *)
let sort_boolean_arguments lst =
  let compare x y =
    comparelist (formula_size x) (formula_size y)
  in
  List.sort compare lst
;;

(* Simplify an integer expression Plus args; all elements of args are
   already assumed to be restructured.  Note: parts are shamelessly
   copied / adapted from the similar function in InternalSolver. *)
let restructure_plus lst =
  let lst = List.flat_map (function Plus x -> x | y -> [y]) lst in
  let lst = sort_integer_arguments lst in
  let checktimes = function
    | Times (Value 0 :: _) -> []
    | whatever -> [whatever]
  in
  let rec merge_parts = function
    | [] -> []
    | [single] -> [single]
    | (Value 0) :: rest -> merge_parts rest
    | (Value x) :: (Value y) :: rest ->
      merge_parts ((Value (x+y)) :: rest)
    | (Value x) :: rest -> (Value x) :: merge_parts rest
    | first :: second :: tail -> (
      let isvar = function | Var _ -> true | _ -> false in
      if (first = second) && (isvar first) then
        merge_parts ((Times [Value 2; first]) :: tail)
      else let continue _ = first :: merge_parts (second :: tail) in
      match (first, second) with
        | (Times (Value n :: x), Times (Value m :: y)) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (Times (Value (n+m) :: x))) @ tail)
        | (Times [Value n; x], y) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (Times (Value (n+1) :: [x]))) @ tail)
        | (Times x, Times (Value m :: y)) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (Times (Value (m+1) :: y))) @ tail)
        | (x, Times [Value m; y]) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (Times [Value (m+1); x])) @ tail)
        | _ -> continue ()
    )
  in
  ( match merge_parts lst with
      | [] -> Value 0
      | [single] -> single
      | lst -> Plus lst
  )
;;

(* Restructure an integer expression Times args; all elements of args
   are already assumed to be simplified.  Note: parts are shamelessly
   copied / adapted from the similar function in InternalSolver. *)
let rec restructure_times args =
  let rec merge_parts = ( function
    | [] -> []
    | [single] -> [single]
    | (Value 0) :: rest -> [Value 0]
    | (Value 1) :: rest -> merge_parts rest
    | (Value x) :: (Value y) :: rest ->
      merge_parts ((Value (x*y)) :: rest)
    | lst -> lst
  ) in
  (* given a list [a1,...,an] of simplified expressions which may be
  products but not sums, build the resulting multiplication *)
  let restructure_plusfree lst =
    let flatten_times = function | Times lst -> lst | expr -> [expr] in
    let lst = List.flat_map flatten_times lst in
    let lst = sort_integer_arguments lst in
    let lst = merge_parts lst in
    match lst with
      | [] -> Value 1
      | [single] -> single
      | lst -> Times lst
  in
  let isplus = function | Plus _ -> true | _ -> false in
  let (plusses, nonplusses) = List.partition isplus args in
  match plusses with
    | [] -> restructure_plusfree args
    | Plus lst :: tl ->
      let multiply_part x = restructure_times (x :: tl) in
      restructure_plus (List.map multiply_part lst)
    | _ -> failwith "Should not happen."
;;

(* All of these assume that n is already a restructured intexpression *)
let negative n = restructure_times [Value (-1); n];;
let successor n = restructure_plus [Value 1; n];;
let predecessor n = restructure_plus [Value (-1); n];;

(* Restructure a boolean expression And args; all elements of args
   are already assumed to be restructured. *)
let restructure_conjunction lst =
  let lst = List.flat_map (function | And x -> x | y -> [y]) lst in
  let lst = sort_boolean_arguments lst in
  let rec check_trivial = function
    | [] -> True
    | [single] -> single
    | True :: tl -> check_trivial tl
    | False :: tl -> False
    | l -> And l
  in
  check_trivial lst
;;

(* Restructure a boolean expression Or args; all elements of args
   are already assumed to be restructured. *)
let restructure_disjunction lst =
  let lst = List.flat_map (function | Or x -> x | y -> [y]) lst in
  let lst = sort_boolean_arguments lst in
  let rec check_trivial = function
    | [] -> False
    | [single] -> single
    | False :: tl -> check_trivial tl
    | True :: tl -> True
    | l -> Or l
  in
  check_trivial lst
;;

(* returns the product of the given list of terms, which we assume to
already be in restructured and correctly ordered form (so
restructure_times s *not* necessary) *)
let build_product = function
  | [] -> Value 1
  | [single] -> single
  | lst -> Times lst
;;

(* builds the (simplified!) equality x = 0 or the inequality x != 0 *)
let rec build_is0 equality x =
  let notequal = if equality then False else True in
  match x with
    | Value k -> if (k = 0) = equality then True else False
    | Times ((Value k) :: lst) -> (* k * x = 0 <=> x = 0 *)
      build_is0 equality (build_product lst)
    | Times lst -> (* a1 * ... * an = 0 <==> some ai = 0 *)
      let is0lst = List.map (build_is0 equality) lst in
      if equality then Or is0lst
      else And is0lst
    | Plus [Value n; Times ((Value k) :: lst)] -> (* k * x = -n *)
      let times = build_product lst in
      if n = 0 then build_is0 equality times
      else if k = 0 then notequal (* n + 0 = 0 can't hold when n != 0 *)
      else if n mod k <> 0 then notequal
      else build_is0 equality (restructure_plus [Value (n / k); times])
        (* m * k + k * x = 0 <=> m + x = 0 *)
    | _ ->
      if equality then IsZero x
      else NonZero x
;;

(* builds the (simplified!) inequality x >= 0 *)
let rec build_geq0 x =
  (* returns x / y, rounded down; here -1.5 rounded down is -1,
  not -2; no risks for bitcalculations are taken! *)
  let rounddowndiv x y =
    if x mod y = 0 then x / y else
    let division = (float x) /. (float y) in
    let answer = (floor division) +. 0.1 in
    if answer < 0.0 then (truncate answer) - 1
    else truncate answer
  in
  match x with
    | Value k -> if k >= 0 then True else False
    | Times ((Value k) :: lst) ->
      if k = 0 then True
      else if k > 0 then build_geq0 (build_product lst)
      else GeqZero (Times (Value (-1) :: lst))
    | Plus [Value n; Times ((Value k) :: lst)] ->
        (* k * (+/-)x >= -n <=> (+/-)x >= CEIL(-n/k) <==>
           FLOOR(n/k) + (+/-)x >= 0 *)
      if n = 0 then build_geq0 (Times ((Value k) :: lst))
      else if k = 0 then build_geq0 (Value n)
      else if k > 0 then (
        let roundeddown = rounddowndiv n k in
        build_geq0 (Plus [Value roundeddown; build_product lst])
      )
      else if k < -1 then (
        let roundeddown = rounddowndiv n (-k) in
        let newprod = build_product ((Value (-1)) :: lst) in
        build_geq0 (Plus [Value roundeddown; newprod])
      )
      else GeqZero x
    | _ -> GeqZero x
;;

(* Tests whether a given base formula (>= 0, = 0, != 0) can be reduced
   to True or False or a simpler formula, and does so in that case! *)
let restructure_basic_formula = function
  | IsZero n -> build_is0 true n
  | NonZero n -> build_is0 false n
  | GeqZero n -> build_geq0 n
  | x -> x
;;

(* substitute_in_int gamma exp replaces every variable [x] in [exp] by
   gamma([x]), if defined; if [exp] was originally well-structured and
   the same hold for all values of [gamma], then so is the result.
   The second returned value is true if anything was instantiated. *)
let rec substitute_in_int gamma expression =
  let recurse args =
    let (a, b) = List.split (List.map (substitute_in_int gamma) args) in
    ( a, List.exists id b )
  in
  match expression with
    | Value k -> ( expression, false )
    | Var (u, x) ->
      ( try (List.assoc (Variable.to_int x) gamma, true)
        with Not_found -> ( expression, false )
      )
    | Plus args ->
      let (newargs, didstuff) = recurse args in
      if didstuff then ( restructure_plus newargs, true )
      else ( Plus newargs, false )
    | Times args ->
      let (newargs, didstuff) = recurse args in
      if didstuff then ( restructure_times newargs, true )
      else ( Times newargs, false )
    | UnknownExp (ss, es) ->
      let (newes, didstuff) =
        List.split (List.map (substitute_in_int gamma) es) in
      ( UnknownExp (ss, newes), List.exists id didstuff )
;;

(* substitute_in_form gamma formula replaces every variable [x] in
   [form] by gamma([x]), if defined; if [formula] was originally
   well-structured and the same holds for all values of [gamma], then
   so is the result.
   The second returned value is true if anything was instantiated. *)
let rec substitute_in_form gamma formula =
  match formula with
    | True | False -> ( formula, false )
    | IsZero n | NonZero n | GeqZero n ->
      let (m, d) = substitute_in_int gamma n in
      if d then
        match formula with
          | GeqZero _ -> ( restructure_basic_formula (GeqZero m), true )
          | NonZero _ -> ( restructure_basic_formula (NonZero m), true )
          | _ -> ( restructure_basic_formula (IsZero m), true )
      else ( formula, false )
    | And lst | Or lst ->
      let (args, didstuff) =
        List.split (List.map (substitute_in_form gamma) lst) in
      let didsomething = List.exists id didstuff in
      if didsomething then
        match formula with
          | And _ -> ( restructure_conjunction lst, true )
          |     _ -> ( restructure_disjunction lst, true )
      else ( formula, false )
    | UnknownPred (b, ss, es) ->
      let (newes, didstuff) =
        List.split (List.map (substitute_in_int gamma) es) in
      ( UnknownPred (b, ss, newes), List.exists id didstuff )
    | Quantifier (univ, x, lower, upper, form) ->
      let (newlower, a) = substitute_in_int gamma lower in
      let (newupper, b) = substitute_in_int gamma upper in
      let (newform, c) = substitute_in_form gamma form in
      if a || b || c then
        ( restructure_quantifier univ x newlower newupper newform, true )
      else ( formula, false )

(* Restructure a quantifier formula, where both lower, upper and
   formula are already assumed to be restructured. *)
and restructure_quantifier univ x lower upper formula =
  (* ditch the quantifier if x does not occur in formula *)
  let is_x = function | Var (_, y) -> y = x | _ -> false in
  if find_sub_expr_in is_x false formula = None then (
    let difference = restructure_plus [lower; predecessor (negative upper)] in
    let nothingquantified = restructure_basic_formula (GeqZero difference) in
      (* lower > upper  <=>  lower - upper - 1 >= 0 *)
    restructure_disjunction [nothingquantified; formula]
  )
  (* also ditch it if both lower and upper are known *)
  else match (lower, upper) with
    | (Value n, Value m) ->
      let iform i = fst (substitute_in_form [(Variable.to_int x,
                    Value i)] formula) in
      let formulas = List.map_range iform n (m + 1) in
      restructure_conjunction formulas
    | _ -> Quantifier (univ, x, lower, upper, formula)
;;

(* returns the negation of a formula (so phi => not phi) *)
let rec negate = function
  | True -> False
  | False -> True
  | And lst -> Or (List.map negate lst)
  | Or lst -> And (List.map negate lst)
  | GeqZero n -> GeqZero (predecessor (negative n))
      (* not (n >= 0)  <=>  n < 0  <=>  -n > 0   <=> -n - 1 >= 0 *)
  | IsZero n -> NonZero n
  | NonZero n -> IsZero n
  | UnknownPred (b, ss, es) -> UnknownPred (not b, ss, es)
  | Quantifier (univ, x, l, u, form) ->
    Quantifier (not univ, x, l, u, negate form)
;;

(* returns the highest part of a given plus (in restructured form,
   which means that the "largest" parts are at the end) *)
let highest_component = function
  | Plus [] -> Value 0
  | Plus lst -> List.last lst
  | x -> x
;;

(* returns whether the highest part of a given plus (in restructured
   form, which means that the largest parts are at the end) is
   explicitly made negative *)
let highest_negative expr = match highest_component expr with
  | Value k -> k < 0
  | Times ((Value k) :: _) -> k < 0
  | _ -> false
;;

(* Puts the given expression in the expected normalised form.  Makes
   no assumptions about the current form. *)
let rec restructure_integer = function
  | Value _ | Var _ as x -> x
  | Plus lst ->
    restructure_plus (List.map restructure_integer lst)
  | Times lst ->
    restructure_times (List.map restructure_integer lst)
  | UnknownExp (ss, es) -> UnknownExp (ss, List.map restructure_integer es)
;;

(* Puts all integers in the given formula in the expected normalised
   form, and does the same for the clauses in the formula.  Makes no
   assumptions about the current form. *)
let rec restructure_formula = function
  | True -> True
  | False -> False
  | And lst -> restructure_conjunction (List.map restructure_formula lst)
  | Or lst -> restructure_disjunction (List.map restructure_formula lst)
  | GeqZero n -> restructure_basic_formula (GeqZero (restructure_integer n))
  | IsZero n ->
    let rn = restructure_integer n in
    if highest_negative rn then restructure_basic_formula (IsZero (negative rn))
    else restructure_basic_formula (IsZero rn)
  | NonZero n ->
    let rn = restructure_integer n in
    if highest_negative rn then restructure_basic_formula (NonZero (negative rn))
    else restructure_basic_formula (NonZero rn)
  | UnknownPred (b, ss, es) ->
    UnknownPred (b, ss, List.map restructure_integer es)
  | Quantifier (univ, x, l, u, form) ->
    restructure_quantifier univ x (restructure_integer l)
       (restructure_integer u) (restructure_formula form)
;;

(*****************************************************************************)
(*                            BOOLEANS AS INTEGERS                           *)
(*****************************************************************************)

(* replaces Bool as a sort by Int for all variables in [vars] *)
let resort_boolvars vars env alf =
  let isboolvar x = Environment.find_sort x env = Alphabet.boolsort in
  let boolvars = List.filter isboolvar vars in
  let intsort = Alphabet.integer_sort alf in
  let resort x = Environment.replace_sort x intsort env in
  List.iter resort boolvars ;
  boolvars
;;

(* replaces Int as a sort by Bool for all variables in [boolvars] *)
let undo_resorting boolvars env =
  let resort x = Environment.replace_sort x Alphabet.boolsort env in
  List.iter resort boolvars
;;

(* replaces integer valuations by booleans for all variables in [boolvars] *)
let boolfix_substitution boolvars gamma alf =
  let nul = Function.integer_symbol 0 in
  let bot = Alphabet.get_bot_symbol alf in
  let top = Alphabet.get_top_symbol alf in
  let fixbool subst x =
    let value = Substitution.find x subst in
    let newvalue =
      if Term.root value = Some nul then bot
      else top
    in
    Substitution.replace x (Term.make_fun newvalue []) subst
  in
  List.fold_left fixbool gamma boolvars
;;

(*****************************************************************************)
(*                             CORE FUNCTIONALITY                            *)
(*****************************************************************************)

(* find the GCD of all constant parts of the multiplication in the
given list *)
let constant_gcd lst =
  let get_constant = function
    | Value k -> k
    | Times ((Value k) :: _) -> k
    | _ -> 1
  in
  let rec gcd n m =
    if m = 0 then n
    else gcd m (n mod m)
  in
  let gcd n m =
    let n = if n < 0 then -n else n in
    let m = if m < 0 then -m else m in
    if m > n then gcd n m
    else gcd m n
  in
  let rec list_gcd sofar = function
    | [] -> sofar
    | head :: tail ->
      let best = gcd sofar head in
      if best = 1 then 1
      else list_gcd best tail
  in
  let constants = List.map get_constant lst in
  if constants = [] then 37 (* any number would do *)
  else list_gcd (List.hd constants) (List.tl constants)
;;

(* calculates [everything in pos] - [everything in neg] + extra *)
let calculate_triple (pos, neg, extra) =
  let posargs = if extra = 0 then pos else (Value extra) :: pos in
  let negargs = List.map negative neg in
  let args = List.append posargs negargs in
  restructure_plus args
;;

(* helping functions: compare the expression calculate triple with 0,
using the given compare function; returns false if the compare
function returns false, or if the given expression does not evaluate
to a value *)
let check_position compare triple =
  match calculate_triple triple with
    | Value n -> compare n 0
    | _ -> false
;;

(* calls to compare calculations to 0 *)
let atleast0 = check_position (>=);;
let atmost0 = check_position (<=);;
let exactly0 = check_position (=);;

let notexactly0 triple =
  match calculate_triple triple with
    | Value n -> n != 0
    | Plus ((Value k) :: rest) ->
      let n = constant_gcd rest in
      (n <> 0) && (k mod n <> 0)
    | _ -> false
;;

(* returns whether the given formula is basic, so something we can
handle in assumptions *)
let is_basic = function
  | GeqZero _ | IsZero _ | NonZero _ -> true
  | _ -> false
;;

(* checks whether the first given formula implies the second (this
obviously admits false negatives *)
let implies form1 form2 =
  match (form1, form2) with
    | (NonZero x, NonZero y) -> x = y
        (* x <> 0 ==> x <> 0 *)
    | (GeqZero x, GeqZero y) -> atleast0 ([y],[x],0)
        (* x >= 0 ==> y >= 0 certainly if y >= x, so if y-x >= 0 *)
    | (GeqZero x, NonZero y) ->
      atmost0 ([x;y],[],1) || atmost0 ([x],[y],1)
        (* x >= 0 /\ y = 0 cannot hold together if x+y or x-y < 0 *)
    | (IsZero x, GeqZero y) ->
      atleast0 ([y],[x],0) || atleast0 ([y;x],[],0)
        (* x = 0 ==> y >= 0 if y + N * x >= 0 *)
    | (IsZero x, IsZero y) ->
      exactly0 ([y],[x],0) || exactly0 ([y;x;x],[],0) || exactly0 ([y],[x;x],0)
        (* x = 0 ==> y = 0 if x = y, or y + N * x = 0;
           we do not test for y - x because the highest term for
           IsZero is always guaranteed to be positive *)
    | (IsZero x, NonZero y) ->
      notexactly0 ([y],[x],0) || notexactly0 ([y;x],[],0)
        (* x = 0 ==> y != 0 if y + N * x != 0 *)
    | _ -> false
;;

(* checks whether the given formulae together imply falsehood *)
let inconsistent form1 form2 =
  match form1 with
    | IsZero x -> implies form2 (NonZero x)
    | GeqZero x ->
      let negx = negative x in
      let negated = GeqZero (predecessor negx) in
      implies form2 negated
    | NonZero x -> implies form2 (IsZero x)
    | _ -> false
;;

(* checks whether the given formulas together always hold *)
let alwaystogether form1 form2 =
  match (form1, form2) with
    | (NonZero x, form) | (form, NonZero x) ->
       implies (IsZero x) form
    | (GeqZero x, GeqZero y) -> atleast0 ([x;y],[],1)
    | _ -> false
;;

(* returns a list of formulas such that satisfying any of them
suffices to prove that form1 and form2 are always true together (not
a complete list of such formulas) *)
let always_together_formula form1 form2 =
  (* helping function for equality_implication *)
  let compare f x y =
    [f (calculate_triple ([y],[x],0));
     f (calculate_triple ([y;x],[],0))
    ]
  in
  (* equality_impliciation x form returns requirements which
  guarantee that x = 0 ==> form *)
  let equality_implication x = function
    | GeqZero y -> compare (fun a -> GeqZero a) x y
    | NonZero y -> compare (fun a -> NonZero a) x y
    | IsZero y -> compare (fun a -> IsZero a) x y
    | _ -> []
  in
  (* main part *)
  match (form1, form2) with
    | (NonZero x, form) | (form, NonZero x) ->
      equality_implication x form
    | (GeqZero x, GeqZero y) ->
      [build_geq0 (calculate_triple ([x;y],[],1))]
    | _ -> []
;;

(* given both form1 and form2, tries to find a simpler formula that
implies both *)
let combine_conjunction_strong form1 form2 =
  match (form1, form2) with
    | (GeqZero x, GeqZero y) ->
      if exactly0 ([x;y],[],0) then Some (build_is0 true x)
      else None
        (* x + y = 0 ==> x >= 0 /\ y >= 0 <=> x = y = 0 *)
    | (NonZero x, GeqZero y) | (GeqZero y, NonZero x) ->
      if exactly0 ([x],[y],0) then Some (build_geq0 (predecessor y))
        (* y != 0 /\ y >= 0  <==>  y - 1 >= 0 *)
      else if exactly0 ([x;y],[],0) then
        Some (build_geq0 (predecessor y))
        (* -y != 0 /\ y >= 0  <==>  y - 1 >= 0 *)
      else None
    | _ -> None
;;

(* given a formula and a clause which is assumed *not* to hold, tries
to find a stronger assumption that implies both clause and not anti *)
let combine_disjunction_strong anti clause =
  match (anti, clause) with
    | (IsZero x, _) -> combine_conjunction_strong (NonZero x) clause
    | (NonZero x, _) -> combine_conjunction_strong (IsZero x) clause
    | (GeqZero x, GeqZero y) ->
      (* (not x >= 0) /\ y >= 0  <==>  -x-1 >= 0 /\ y >= 0 *)
      if exactly0 ([y],[x],-1) then Some (build_is0 true y)
      else None
    | (GeqZero x, NonZero y) ->
      (* suppose x = -y - 1 (so x + y + 1 = 0); we have:
         not (-y-1 >= 0) /\ y != 0  <==>  not (y < 0) /\ y != 0  <==>
         y >= 0  /\ y != 0  <==>  y - 1 >= 0 *)
      if exactly0 ([x;y],[],1) then Some (build_geq0 (predecessor y))
      (* suppose x = y - 1 (so x - y + 1 = 0); we have
         not (y - 1 >= 0) /\ y != 0  <==>  not (y > 0) /\ y != 0  <==>
         y <= 0 /\ y != 0  <==>  y < 0  <==>  -y - 1 >= 0 *)
      else if exactly0 ([x],[y],1) then
        Some (build_geq0 (predecessor (negative y)))
      else None
    | _ -> None
;;

(* given either form1 or form2, find a simpler formula equivalent to
the disjunction *)
let combine_disjunction_weak form1 form2 =
  match (form1, form2) with
    | (GeqZero x, GeqZero y) ->
      if exactly0 ([x;y],[],2) then
        Some (build_is0 false (successor x))
        (* x + y = -2 ==> x >= 0 \/ y >= 0 <=> x != -1 *)
      else None
    | (IsZero x, GeqZero y) | (GeqZero y, IsZero x) ->
      if exactly0 ([y],[x],1) then Some (build_geq0 x)
        (* y = x - 1 ==> x = 0 \/ y >= 0 <=> x >= 0 *)
      else if exactly0 ([y;x],[],1) then
        Some (build_geq0 (successor y))
        (* y = -x - 1 ==> -x = 0 \/ y >= 0 <=> y + 1 >= 0 *)
      else None
    | _ -> None
;;

(* given a formula and a prmise, tries to find a weaker assumption,
equivalent to not premise \/ clause *)
let combine_conjunction_weak premise clause =
  match (premise, clause) with
    | (IsZero x, _) -> combine_disjunction_weak (NonZero x) clause
    | (NonZero x, _) -> combine_disjunction_weak (IsZero x) clause
    | (GeqZero x, GeqZero y) ->
      if exactly0 ([y],[x],1) then Some (build_is0 false (successor y))
        (* not (y + 1 >= 0) \/ y >= 0  <==>  (y < -1) \/ y >= 0  <==>
           y != -1 *)
      else None
    | (GeqZero x, IsZero y) ->
      if exactly0 ([x],[y],0) then Some (build_geq0 (negative x))
        (* not (x >= 0) \/ x = 0  <==>  x < 0 \/ x = 0  <==>  x <= 0 
           <==>  -x >= 0 *)
      else None
    | _ -> None
;;

(* given that all statements in assumptions can be assumed true, and
all statements in antiassumptions can be assumed false, finds a
replacement for the given formula which is either as strong as
possible (if strong is true) or as weak as possible (if strong is
false) *)
let improve formula assumptions antiassumptions strong =
  let use_assumption =
    if strong then combine_conjunction_strong
    else combine_conjunction_weak
  in
  let use_anti =
    if strong then combine_disjunction_strong
    else combine_disjunction_weak
  in
  (* checks whether formula can be simplified using any of the
  given assumptions or anti-assumptions *)
  let rec improve improvefun formula = function
    | [] -> formula
    | head :: tail ->
      let form = match improvefun head formula with
        | Some f -> f
        | None -> formula
      in
      improve improvefun form tail
  in
  (* runs f until formula doesn't change anymore *)
  let rec repeat f formula count =
    let newform = f formula in
    if formula = newform || count <= 0 then formula
    else repeat f newform (count - 1)
  in
  (* decide how to do the improvements *)
  if not (is_basic formula) then formula else
  let form = repeat (fun x -> improve use_assumption x assumptions)
                    formula 3 in
  repeat (fun x -> improve use_anti x antiassumptions) form 3
;;

(* checks whether the given definition list is consistent *)
let rec consistent_definitions = function
  | [] -> true
  | (x, k) :: tail ->
    let findx = List.filter (fun (y,_) -> x = y) tail in
    if findx = [] then consistent_definitions tail
    else if snd (List.hd findx) <> k then false
    else consistent_definitions tail
;;

(* [do_reasoning assumptions antiassumptions definitions formula]
   attempts to simplify [formula] by simplifying combinations of
   basic formulas, and instantiating terms where relevant
*)
let rec do_reasoning assumptions antiassumptions definitions formula =
  (* check the given formula against the list of assumptions and
  antiassumptions *)
  let basic_reasoning (form, changed) =
    if List.exists (fun x -> implies x form) assumptions then True 
    else if List.exists (implies form) antiassumptions then False
    else if List.exists (inconsistent form) assumptions then False
    else if List.exists (alwaystogether form) antiassumptions then True 
    else if not changed then form
    else match form with
      | IsZero n -> build_is0 true n
      | NonZero n -> build_is0 false n
      | GeqZero n -> build_geq0 n
      | _ -> form
  in
  (* split the last item off the list (reordering the first part) *)
  let rec split_last sofar = function
    | [] -> (sofar, Value 0)
    | [single] -> (sofar, single)
    | hd :: tl -> split_last (hd :: sofar) tl
  in
  (* checks whether the given expression has the form (-e) + x, where
  x is a variable; note that x must be the "largest" variable in the
  Plus for this to work, to avoid ambiguity *)
  let rec check_definition = function
    | Value _ | Times _ | UnknownExp _ -> None
    | Var (_, x) -> Some (x, Value 0)
    | Plus lst ->
      match split_last [] lst with
        | (main, Var (_, x)) ->
          Some (x, negative (restructure_plus main))
        | _ -> None
  in
  (* splits the given list into definitions or anti-definitions,
  other basic formulas, and the remaining (non-basic) formulas; the
  the definitions and basic formulas may end up reordered (note that
  this works because we assume lst is ordered) *)
  let rec split_junction conjunction defs basics lst =
    match (conjunction, lst) with
      | (true, IsZero n :: tl) | (false, NonZero n :: tl) ->
        ( match check_definition n with
            | None ->
              split_junction conjunction defs ((List.hd lst) :: basics) tl
            | Some (x, value) ->
              let xval = Variable.to_int x in
              if List.mem_assoc xval definitions then
                split_junction conjunction defs ((List.hd lst) :: basics) tl
              else
                let deflist = ((xval, value), IsZero n) :: defs in
                split_junction conjunction deflist basics tl
        )
      | (_, hd :: tl) ->
        if is_basic hd then
          ( split_junction conjunction defs (hd :: basics) tl )
        else ( defs, basics, hd :: tl )
      | (_, []) -> ( defs, basics, [] )
  in
  (* simplifies the given clause with both assumptions and anti-assumptions *)
  let use_assumptions conj claim =
    if List.exists (fun x -> implies x claim) assumptions then True
    else if List.exists (implies claim) antiassumptions then False
    else improve claim assumptions antiassumptions conj
  in
  (* does the reasoning work for an And or Or formula *)
  let handle_andor conjunction lst =
    (* determine "definitions": assignments x = a that we may assume to hold *)
    let (defcombis, basics, rest) = split_junction conjunction [] [] lst in
    let deflist = List.map fst defcombis in
    let junction_definitions = List.map snd defcombis in
    (* apply these definitions on the assumptions for further use in this part
    of the formula *)
    let substitute defs target = fst (substitute_in_form defs target) in
    let def_contradiction () = if conjunction then False else True in
    let asses = List.map (substitute deflist) assumptions in
    if List.mem False asses then def_contradiction () else
    let antiasses = List.map (substitute deflist) antiassumptions in
    if List.mem True antiasses then def_contradiction () else
    (* and apply them, and the pre-given definitions, on the other basic
    formulas *)
    let alldefs = deflist @ definitions in
    let basics = List.map (substitute alldefs) basics in
    let basics = List.map (use_assumptions conjunction) basics in
    (* also combine the basics with each other *)
    let rec combine_basics combiner = function
      | [] -> []
      | head :: tail ->
        match List.partition_option (combiner head) tail with
          | ([], _) -> head :: combine_basics combiner tail
          | (a, b) -> combine_basics combiner (a @ b)
    in
    let basics =
      if conjunction then combine_basics combine_conjunction_strong basics
      else combine_basics combine_disjunction_weak basics
    in
    (* and recursively handle rest *)
    let (asses, antiasses) =
      if conjunction then (basics @ asses, antiasses)
      else (asses, basics @ antiasses)
    in
    let rest = List.map (do_reasoning asses antiasses alldefs) rest in
    if conjunction then
      restructure_conjunction (junction_definitions @ basics @ rest)
    else
      restructure_disjunction (junction_definitions @ basics @ rest)
  in
  match formula with
    | True | False -> formula
    | UnknownPred (b, ss, es) ->
      UnknownPred (b, ss, List.map (fst <.> (substitute_in_int definitions)) es)
    | GeqZero _ | IsZero _ | NonZero _ ->
      basic_reasoning (substitute_in_form definitions formula)
    | Quantifier (univ, x, lower, upper, form) ->
      let phi = do_reasoning assumptions antiassumptions definitions form in
      restructure_quantifier univ x lower upper phi
    | And lst -> handle_andor true lst
    | Or lst -> handle_andor false lst
;;

let advanced_simplify formula timeout =
  do_reasoning [] [] [] formula
  (*
  let timeout = timeout * 10 in
  let time = truncate ((Unix.time ()) *. 10.0) in
  let rec repeat formula count =
    if count < 0 then formula
    else if (truncate ((Unix.time ()) *. 10.0) >= time + timeout) then formula
    else (
      let simplified = do_reasoning [] [] [] formula in
      let changed = simplified <> formula in
      if changed then repeat simplified (count - 1) 
      else formula
    )    
  in
  repeat formula 10
  *)
;;

(*****************************************************************************)
(*                           MAIN ACCESS FUNCTIONS                           *)
(*****************************************************************************)


let solve_satisfiability formula vars a e logic solvername =
  (* make sure that formula has the expected shape! *)
  let formula = restructure_formula formula in
  let boolvars = resort_boolvars vars e a in

  (* TODO: actually try something like the following yourself:
  let remainder = advanced_simplify problem 3 in 
  if remainder = True then (
    let vars = List.unique (List.flat_map Term.vars formulas) in
    let addvarchoice subst x =
      let sort = Environment.find_sort x env in
      Substitution.add x (get_value sort alf) subst
    in   
    (SAT, List.fold_left addvarchoice Substitution.empty vars)
  )
  else if remainder = False then (UNSAT, Substitution.empty)
  * plus, of course, a straighforward satisfying instantiation
  *)

  if solvername = "" then (UNKNOWN, Substitution.empty)
  else (
    let logic =
      if logic = "" then determine_logic formula
      else logic
    in
    let answer = solve_externally formula vars a e logic solvername in
    undo_resorting boolvars e ;
    match answer with
      | (SAT, gamma) -> (SAT, boolfix_substitution boolvars gamma a)
      | x -> x
  )
;;

let solve_validity formula vars a e logic solvername =
  Printf.printf "Asked to solve validity of %s\n" (print_formula false formula) ;
  (* make sure that formula has the expected shape! *)
  let formula = restructure_formula formula in
  Printf.printf "Now: %s\n" (print_formula false formula) ;
  (* make sure that formula has the expected shape! *)
  let boolvars = resort_boolvars vars e a in
  (* do the more advanced simplifications *)
  let remainder = advanced_simplify formula 3 in
  Printf.printf "Remainder = %s\n" (print_formula false remainder) ;
  failwith "Stop!" ;
  (* make sure that formula has the expected shape! *)
  (* are we done yet? Excellent. *)
  if remainder = True then SAT
  else if remainder = False then UNSAT
  else if solvername = "" then UNKNOWN
  (* we're not? Well, send it to the SMT-solver then *)
  else (
    let negform = negate formula in
    let logic =
      if logic = "" then determine_logic formula
      else logic
    in
    let answer = solve_externally negform vars a e logic solvername in
    undo_resorting boolvars e ;
    match answer with
      | (UNKNOWN, _) -> UNKNOWN
      | (SAT, _) -> UNSAT
      | (UNSAT, _) -> SAT
  )
;;

