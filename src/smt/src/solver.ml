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

(*** TYPES *******************************************************************)

type t = int;;
type possible_results = Smtresults.t = SAT | UNSAT | UNKNOWN;;
type internally = INTERNAL | EXTERNAL | MANUAL of (Term.t -> string);;
type renaming = (string * string) list;;
type translation = (string * (string,int) Util.either list) list;;
type smtsolver = string * internally * string * renaming * translation;;

(** STATE VARIABLES **********************************************************)

type internal = { mutable solvers : smtsolver array };; 
let state = { solvers = [| ("intsolver", INTERNAL, "QF_NIA", [], []) |] };; 

(*** FUNCTIONS ***************************************************************)

(* constructors and modifying solver settings *)

let create _ =
  let len = Array.length state.solvers in
  state.solvers <- Array.append state.solvers
                   [| ("smtsolver", EXTERNAL, "none", [], []) |] ;
  len
;;

let intsolver = 0;;

let use_solver solver t =
  let (_, internal, logic, rlst, tlist) = state.solvers.(t) in
  state.solvers.(t) <- (solver, internal, logic, rlst, tlist)
;;

let use_internal_solver t =
  let (solver, _, logic, rlst, tlst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, INTERNAL, logic, rlst, tlst)
;;

let use_manual_solver t printer =
  let (solver, _, logic, rlst, tlst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, MANUAL printer, logic, rlst, tlst)
;;

let use_logic logic t =
  let (solver, internal, _, rlst, tlst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, internal, logic, rlst, tlst)
;;

let get_logic t =
  let (_, _, logic, _, _) = state.solvers.(t) in logic
;;

let rec add_symbol_renaming symb renaming t addtoint =
  let (solver, internal, logic, rlst, tlst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, internal, logic, (symb, renaming) :: rlst, tlst) ;
  if addtoint then add_symbol_renaming symb renaming intsolver false
;;

let rec add_symbol_translation symb translation t addtoint =
  let (solver, internal, logic, rlst, tlst) = state.solvers.(t) in
  state.solvers.(t) <- (solver, internal, logic, rlst, (symb, translation) :: tlst) ;
  if addtoint then add_symbol_translation symb translation intsolver false
;;

let solvername t = let (name, _, _, _, _) = state.solvers.(t) in name;;

(* executes the given situation either on the external or the
internal smt-solver, depending on settings *)
let internal_or_external t a e fi fe fm =
  let (solver, internal, logic, renamings, translations) = state.solvers.(t) in
  let fef = fe (solver, logic) in
  if (internal = INTERNAL) && (Internalsolver.acceptable_logic logic) then (
    try fi renamings translations a e
    with
      Internalsolver.NoInternalProblem _ |
      Smtquantifiers.UnboundedQuantification _ ->
      fef renamings translations a e
  )
  else match internal with
    | MANUAL printer -> fm printer a
    | _ -> fef renamings translations a e
;;

(* handling core symbols *)

let setup_core setup name smt a = 
  let (_, _, _, renamings, _) = state.solvers.(smt) in
  let rec original = function
    | [] -> name
    | (key, value) :: tl -> if value = name then key else original tl
  in  
  if Alphabet.mem_fun_name name a then (
    let f = Alphabet.find_fun name a in setup f a 
  )
  else (
    let name = original renamings in
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
  setup_core Alphabet.set_equal_symbol "=" smt a ;
  setup_core Alphabet.set_geq_symbol ">=" smt a ;
  setup_core Alphabet.set_leq_symbol "<=" smt a ;
  setup_core Alphabet.set_greater_symbol ">" smt a ;
  setup_core Alphabet.set_smaller_symbol "<" smt a
;;

(* calculating *)

let calculate term t =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let e = Trs.get_main_environment (Trs.get_current ()) in
  internal_or_external t a e (Internalsolver.calculate term)
                             (Externalsolver.calculate term)
                             (Manualsolver.calculate term)
;;

let get_value sort t =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let (solver, internal, logic, _, _) = state.solvers.(t) in
  if internal = INTERNAL then
    try Internalsolver.get_value sort a
    with Internalsolver.NoInternalProblem _ ->
      Externalsolver.get_value sort (solver, logic) a
  else match internal with
    | MANUAL _ -> Manualsolver.get_value sort a
    | _ -> Externalsolver.get_value sort (solver, logic) a
;;

(* more advanced calculations *)

let satisfiable_formulas' formulas get_model t e =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  internal_or_external t a e
    (Internalsolver.solve_satisfiability formulas "intsolver")
    (Externalsolver.check_formulas formulas get_model)
    (Manualsolver.satisfiability formulas)
;;

let valid_formulas formulas t e =
  let a = Trs.get_alphabet (Trs.get_current ()) in
  let negation = (
    try Alphabet.get_not_symbol a
    with Not_found -> failwith ("Cannot check formula " ^
      "validity: no negation symbol has been set.")
  ) in
  let rec exter formulas data ren tr a e =
    match formulas with
      | [] -> SAT
      | head :: tail ->
        let negated = Term.make_function a e negation [head] in
        let (result, _) =
          Externalsolver.check_formula negated false data ren tr a e
        in
        if result = SAT then UNSAT
        else if result = UNSAT then exter tail data ren tr a e
        else UNKNOWN
  in
  internal_or_external t a e
    (Internalsolver.solve_validity formulas "intsolver")
    (exter formulas)
    (Manualsolver.validity formulas)
;;

let satisfiable fs t e = fst (satisfiable_formulas' fs false t e) = SAT;;
let unsatisfiable fs t e = fst (satisfiable_formulas' fs false t e) = UNSAT;;
let valid fs t e = valid_formulas fs t e = SAT;;
(* existential validity *)

let satisfiable_formulas formulas t e = satisfiable_formulas' formulas true t e


(* returns the alphabet, and the important core symbols *)
let alphabet_data trs =
  (* get alphabet *)
  let a = Trs.get_alphabet trs in
  (* get logical symbols needed for creating formulas *)
  let (topsymb, andsymb, eqsymb, implsymb) =
    try 
      ( Alphabet.get_top_symbol a,
        Alphabet.get_and_symbol a,
        Alphabet.get_equal_symbol a,
        Alphabet.get_imply_symbol a
      )   
    with Not_found ->
      failwith ("Cannot calculate an existential validity " ^
        "unless all of the following symbols are set: top (truth), " ^
        "and (conjunction), => (implication) and = (equality).")
  in
  (a, topsymb, andsymb, eqsymb, implsymb)
;;

(* returns either Left (x, def, x = def), or Right term if the given
term does not represent a definition of a variable in vars *)
let split_def vars eqsymb term =
  let is_suitable_var = function
    | Term.Var x -> List.mem x vars
    | _ -> false
  in
  match term with
    | Term.Var x ->
      if List.mem x vars then Left (x, [], term)
      else Right term
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) -> (
        if f <> eqsymb then Right term
        else match args with
          | a :: b :: [] ->
            if is_suitable_var a then
              Left (List.hd (Term.vars a), Term.vars b, term)
            else if is_suitable_var b then
              Left (List.hd (Term.vars b), Term.vars a, term)
            else Right term
          | _ -> Right term
        )
    | Term.Forall _ | Term.Exists _ -> Right term
;;

(* returns (hopefully) whether Ex vars [form] is valid; this does not
use any internal checks, but simply hopes for the best that the
SMT-solver is any good with quantifiers (most aren't) *)
let exists_valid_base vars form t e = 
  if List.length vars = 0 then valid [form] t e else
  let rec exists = function
    | [] -> form
    | x :: tail -> Term.Exists (x, exists tail)
  in
  valid [exists vars] t e
;;

let existential_implication vars phi psi1 psi2 smt env =
  let (a, topsymb, andsymb, eqsymb, implsymb) =
    alphabet_data (Trs.get_current ()) in
  (* we map psi1 into splitpsi1 as follows: x = def is mapped to
  Left (x, def, x = def), and formulas c of another form to Right c *)
  let splitpsi1 = List.map (split_def vars eqsymb) psi1 in
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
  else exists_valid_base vars implication smt env
;;

(* returns (hopefully) whether Ex vars [form] is valid *)
let exists_valid vars form smt env = 
  (* the easy case! *)
  if List.length vars = 0 then valid [form] smt env else
  (* okay, split the constraint into multiple constraints, so we
  can at least pick out definitions *)
  let (a, topsymb, andsymb, _, _) =
    alphabet_data (Trs.get_current ()) in
  let rec split_conjunction term = match term with
    | Term.Fun (f, [x;y]) | Term.InstanceFun (f, [x;y], _) ->
      if f = andsymb then
        (split_conjunction x) @ (split_conjunction y)
      else [term]
    | _ -> [term]
  in
  let parts = split_conjunction form in
  let top = Term.make_function a env topsymb [] in
  (* split in parts with and without the existential variables *)
  let has_elem_of_vars term =
    List.intersect (Term.vars term) vars <> [] in
  let (parts1, parts2) = List.partition has_elem_of_vars parts in
  existential_implication vars top parts1 parts2 smt env
;;

(* returns (hopefully) whether Al vars [form] is satisfiable; this
does not have quite so many optimisations yet *)
let forall_satisfiable vars form t e =
  if List.length vars = 0 then satisfiable_formulas [form] t e
  else (
    let rec forall = function
      | [] -> form
      | x :: tail -> Term.Forall (x, forall tail)
    in
   satisfiable_formulas [forall vars] t e
  )
;;

let make_intlist a e substitution =
  let lst = Substitution.to_list substitution in
  let toint term =
    let functions = Term.funs term in
    if (List.length functions <> 1) ||
       (not (Function.is_integer (List.hd functions))) then
      failwith ("Unexpected result from SMT-solver: " ^
        (Term.to_string term) ^ "\n")
    else Function.integer_to_int (List.hd functions)
  in
  let togoodpair (x, term) = (x, toint term) in
  List.map togoodpair lst
;;

let find_values formulas varswithrange alf env =
  let (solvername, _, _, rens, transes) = state.solvers.(intsolver) in
  try match Internalsolver.solve_existential_validity formulas
          varswithrange solvername rens transes alf env with
    | (SAT, gamma) -> Some (make_intlist alf env gamma)
    | _ -> None
  with Internalsolver.NoInternalProblem _ -> None
;;

let simplify_constraint smt a e vars phi =
  let (_, _, _, ren, tr) = state.solvers.(intsolver) in
  try Internalsolver.simplify_constraint ren tr a e vars phi
  with Internalsolver.NoInternalProblem _ -> phi
;;

