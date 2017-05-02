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
open Util;;
open Ctrs;;
open Smt;;

(*** TYPES *******************************************************************)
type t = int;;
type possible_results = Smtresults.t = SAT | UNSAT | UNKNOWN;;
type smtsolver = string * bool * string * ((string * string) list);;

(** STATE VARIABLES **********************************************************)

type internal = { mutable solvers : smtsolver array };;
let state = { solvers = [| ("intsolver", true, "QF_NIA", []) |] };;

(*** FUNCTIONS ***************************************************************)

(* constructors and modifying solver settings *)

let create _ =
  let len = Array.length state.solvers in
  state.solvers <- Array.append state.solvers
                   [| ("smtsolver", false, "none", []) |] ;
  len
;;

let intsolver = 0;;

let use_solver solver t =
  let (_, internal, logic, lst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, internal, logic, lst)
;;

let use_internal_solver t =
  let (solver, _, logic, lst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, true, logic, lst)
;;

let use_logic logic t =
  let (solver, internal, _, lst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, internal, logic, lst)
;;

let add_symbol_translation symb trans t =
  let (solver, internal, logic, lst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, internal, logic, (symb, trans) :: lst)
;;

(* printers *)

let fprintf fmt t =
  let (solver, internal, logic, translations) = state.solvers.(t) in
  Format.fprintf fmt "Solver %s%s with logic %s.%s%s\n"
    solver
    (if internal then " (plus internal solver)" else "")
    logic
    (if translations = [] then "" else "\nWith symbol translations:\n")
    (List.to_string (fun (a, b) -> "  " ^ a ^ " becomes " ^ b) "\n" translations)
;;

(* interfacing with the external solver *)

(**
 * Iterate the function f over all elements of the given list; if
 * false is encountered at any point, we immediately abort.
 *)
let rec test_all f = function
  | [] -> true
  | head :: tail ->
    if f head then test_all f tail
    else false
;;

let translated_symbol symb translations =
  try List.assoc symb translations
  with Not_found -> symb
;;

let rec internal_possible a translations = function
  | Term.Var _ -> false
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    let args_okay = List.fold_left
      (fun b arg -> b && (internal_possible a translations arg))
      true args
    in
    if not args_okay then false
    else if Function.is_integer f then true
    else
      let name = translated_symbol (Alphabet.find_fun_name f a) translations in
      let supported = ["true";"false";"not";"and";"or";"xor";
                       "=>";"=";"distinct";"ite";"-";"+";"*";
                       "div";"mod";"abs";"<=";">=";"<";">"] in
      let rec check_support = function
        | [] -> false
        | head :: tail -> name = head || check_support tail
      in
      check_support supported
;;

let all_internal_possible a t = test_all (internal_possible a t);;

let rec calculate_internally a translations term =
  Internalsolver.calculate term translations a (Environment.dummy ())
;;

let check_formula_internally term a translations =
  if Internalsolver.trivial_test term translations a (Environment.dummy ())
  then (SAT, Substitution.empty)
  else (UNSAT, Substitution.empty)
;;

let check_formulas_internally terms a translations =
  let f term = match check_formula_internally term a translations with
    | (SAT, _) -> true
    | _ -> false
  in
  if test_all f terms then (SAT, Substitution.empty)
  else (UNSAT, Substitution.empty)
;;

let check_smt_file problem env alf smt =
  let (solver, _, _, _) = state.solvers.(smt) in
  Externalsolver.check_smt_file_and_parse problem solver env alf
;;

let create_smt_file env params exprs tostr logic =
  Externalsolver.create_smt_file env params exprs tostr logic
;;

let check_formulas forms t e =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let (solver, internal, logic, translations) = state.solvers.(t) in
  if internal && all_internal_possible a translations forms then
    check_formulas_internally forms a translations
  else
  Externalsolver.check_formulas forms (solver, logic) translations a e
;;

let check_formula term t e = check_formulas [term] t e;;

let satisfiable forms t e =
  let (result, _) = check_formulas forms t e in result = SAT
;;

let unsatisfiable forms t e =
  let (result, _) = check_formulas forms t e in result = UNSAT
;;

let rec valid_external forms t e =
  match forms with
    | [] -> true
    | head :: tail ->
      let a = Trs.get_alphabet (Trs.get_current ()) in
      let negation = (
        try Alphabet.get_not_symbol a
        with Not_found -> failwith ("Cannot check formula " ^
          "validity: no negation symbol has been set.")
      ) in
      let unhead = Term.make_function a e negation [head] in
      let (result, _) = check_formula unhead t e in
      if result = UNSAT then valid_external tail t e
      else false
;;

let valid forms t e =
  (* TODO: test whether we are actually allowed to use internal stuff,
  so the logic is right and no failures are thrown *)
  let (_, internal, _, translations) = state.solvers.(t) in
  if not internal then valid_external forms t e else
  let a = Trs.get_alphabet (Trs.get_current ()) in
  try
    match Internalsolver.solve_validity forms "intsolver"
                                         translations a e with
      | SAT -> true
      | _ -> false
  with Internalsolver.NoIntegerProblem _ -> valid_external forms t e
;;

let exists_valid vars form t e =
  if List.length vars = 0 then valid [form] t e
  else (
    (*
    let a = Trs.get_alphabet (Trs.get_current ()) in
    Printf.printf "\n\nWARNING: %s%s%s\n\n"
      "existential validity requested of formula "
      (Term.to_stringm a e form)
      ", but this has not yet been implemented!" ;
    *)
    false
  )
;;

let existential_implication vars phi psi1 psi2 smt env =
  (* get alphabet *)
  let a = Trs.get_alphabet (Trs.get_current ()) in
  (* get logical symbols needed for creating formulas *)
  let (topsymb, andsymb, eqsymb, implsymb) =
    try
      ( Alphabet.get_top_symbol a,
        Alphabet.get_and_symbol a,
        Alphabet.get_equal_symbol a,
        Alphabet.get_imply_symbol a
      )
    with Not_found ->
      failwith ("Cannot calculate an existential implication " ^
        "unless all of the following symbols are set: top (truth), " ^
        "and (conjunction), => (implication) and = (equality).")
  in
  (* we map psi1 into splitpsi1 as follows: x = def is mapped to
  Left (x, def, x = def), and formulas c of another form to Right c *)
  let split_def term =
    match term with
      | Term.Var x ->
        if List.mem x vars then Left (x, [], term)
        else Right term
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) -> (
          if f <> eqsymb then Right term
          else match args with
            | a :: b :: [] ->
              if Term.is_var a
              then Left (List.hd (Term.vars a), Term.vars b, term)
              else if Term.is_var b
              then Left (List.hd (Term.vars b), Term.vars a, term)
              else Right term
            | _ -> failwith ("Unexpected equality: should have " ^
                             "exactly two arguments!")
          )   
  in
  let splitpsi1 = List.map split_def psi1 in
  (* we let splitpsi1defs consist of the definitions of splitpsi1,
     and splitpsi1rest consist of the rest *)
  let rec parsesplit defs rest = function
    | [] -> (defs, rest)
    | (Left x) :: tail -> parsesplit (x :: defs) rest tail
    | (Right x) :: tail -> parsesplit defs (x :: rest) tail
  in
  let (splitpsidefs, splitpsirest) = parsesplit [] [] splitpsi1 in
  (* handle_split parses a list of the form splitpsi1 as follows:
        handle_split vars base [] rest false splitpsi
    returns 
        (vars', base', splitpsi', rest', changed),
    where all definitions (x,s) with x in vars and s not containing
    anything in vars are moved into base' (and those x are removed
    from vars'), everything which will never be such a definition is
    moved into rest', and the remainder stays in splitpsi'; changed
    indicates whether any variables were removed from vars. *)
  let rec handle_split vars base remaining rest changed = function
    | [] -> (vars, base, remaining, rest, changed)
    | triple :: tail ->
      let (x, xvars, term) = triple in
      if not (List.mem x vars) then
        handle_split vars base remaining (term :: rest) changed tail
      else if List.intersect vars xvars = [] then
        handle_split (List.diff vars [x]) (term :: base) remaining rest true tail
      else handle_split vars base (triple :: remaining) rest changed tail
  in
  (* we repeat handle_split until nothing changes anymore, resulting
  in phiparts (phi combined with the definitions from splitpsidefs)
  and psi1parts (splitpsirest combined with the parts from
  splitpsidefs which cannot be seen as definitions) *)
  let rec repeat_handle_split vars phiparts psi1defs psi1rest =
    match handle_split vars phiparts [] psi1rest false psi1defs with
      | (vars, base, remaining, rest, false) ->
        (vars, base, List.append (List.map (fun (a,b,c) -> c) remaining) rest)
      | (vars, base, remaining, rest, true) ->
        repeat_handle_split vars base remaining rest
  in
  let (vars, phiparts, psi1parts) =
    repeat_handle_split vars [phi] splitpsidefs splitpsirest
  in
  (* we use the conjunction function to combine the parts into
  conjunctions *)
  let rec conjunction = function
    | [] -> Term.make_function a env topsymb []
    | [form] -> form
    | head :: tail ->
      Term.make_function a env andsymb [head; conjunction tail]
  in
  let psi = conjunction (List.append psi1parts psi2) in
  let phi = conjunction phiparts in
  let implication = Term.make_function a env implsymb [phi;psi] in
  if psi1parts = [] then valid [implication] smt env
  else exists_valid vars implication smt env
;;

let calculate_externally term solver logic translations a e =
  Externalsolver.calculate term (solver, logic) translations a e
;;

let calculate term t =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let e = Trs.get_main_environment (Trs.get_current ()) in
  let (solver, internal, logic, translations) = state.solvers.(t) in
  if internal && internal_possible a translations term then
    calculate_internally a translations term
  else calculate_externally term solver logic translations a e
;;

let get_value sort t =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let (solver, internal, logic, translations) = state.solvers.(t) in
  Externalsolver.get_value sort (solver, logic) a
;;

let setup_core setup name smt a =
  let (_, _, _, translations) = state.solvers.(smt) in
  let rec original = function
    | [] -> name
    | (key, value) :: tl -> if value = name then key else original tl
  in
  if Alphabet.mem_fun_name name a then (
    let f = Alphabet.find_fun name a in setup f a
  )
  else (
    let name = original translations in
    if Alphabet.mem_fun_name name a then (
      let f = Alphabet.find_fun name a in setup f a
    )
  )
;;

let setup_core_symbols smt a =
  setup_core Alphabet.set_and_symbol "and" smt a ;
  setup_core Alphabet.set_or_symbol "or" smt a ;
  setup_core Alphabet.set_imply_symbol "=>" smt a ;
  setup_core Alphabet.set_not_symbol "not" smt a ;
  setup_core Alphabet.set_top_symbol "true" smt a ;
  setup_core Alphabet.set_bot_symbol "false" smt a ;
  setup_core Alphabet.set_equal_symbol "=" smt a
;;

