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

type possible_results = Smtresults.t = SAT | UNSAT | UNKNOWN;;
type solverdata = string * string;;
type renaming = (string * string) list;;
type translation = (string * (string,int) Util.either list) list;;

(*** MODULES *****************************************************************)
module SmtResultReader = struct
  module P = Parsec.MakeCharParser(Parsec.StringInput)

  let (>>=) = P.(>>=)
  let (>>) = P.(>>)
  let (<|>) = P.(<|>)

  let bin2hex bs =
    let hex n = char_of_int (if n < 10 then n + 48 else n + 87) in
    let bin2hex =
      let rec b2h k num bs =
        if k > 3 then hex num :: b2h 0 0 bs
        else match bs with
            [] -> []
          | 0 :: bs -> b2h (k + 1) (num * 2) bs
          | 1 :: bs -> b2h (k + 1) (num * 2 + 1) bs
          | _ -> failwith "bin2hex: unexpected value in bit list"
      in b2h 0 0
    in
    let zeros = List.gen (fun _ -> 0) (4 - (List.length bs mod 4)) in
    let bs = List.map (fun c -> int_of_char c - 48 ) bs in
    bin2hex (zeros @ bs)
  ;;

  let assign =
    let ident = P.many1 (P.noneof " \t\n\r(),:;[]{}") >>= fun i -> P.return i in
    let no_rparen = P.many (P.noneof ")") in
    let psort = P.lex (P.between (P.char '(') no_rparen (P.char ')')) in
    let num =
      P.string "Int" >> P.spaces >>
      ((P.many1 P.digit) <|>
       (P.string "(- " >> P.many1 P.digit >>= fun n -> P.string ")" >> P.return ('-'::n) ))
      >>= fun cs ->  P.return (String.of_char_list cs)
    in
    let boolval =
      P.string "Bool" >> P.spaces >>
      (P.string "true" <|> P.string "false") >>= fun b ->
      P.return (String.of_char_list b)
    in
    let hexdec =
      P.string "x" >> P.many1 (P.oneof "0123456789abcdef") >>= fun n ->
      P.return ("#x" ^ (String.of_char_list n))
    in
    let binary =
      P.string "b" >> P.many1 (P.oneof "01") >>= fun n ->
      P.return ("#x" ^ (String.of_char_list (bin2hex n)))
    in
    let bitvector = psort >> P.spaces >> P.char '#' >> (hexdec <|> binary) in
    P.lex (P.string "(define-fun" >> P.spaces >> ident >>= fun id ->
          P.spaces >> P.string "()" >>
          P.spaces >> (num <|> bitvector <|> boolval) >>= fun v ->
          P.char ')' >> P.return (String.of_char_list id, v))
  ;;

  let parse_smt2_result =
    (P.lex (P.many1 P.letter) >>= function
      | ['u'; 'n';'s';'a';'t'] -> P.return (UNSAT, [])
      | ['s';'a';'t'] ->
        let model =
          P.spaces >> P.lex (P.string "(model") >>
          P.many assign >>= fun vals -> P.char ')' >> P.return vals
        in
        P.option [] model >>= fun vals -> P.return (SAT, vals)
      | _ -> P.return (UNKNOWN, []))
      <|> (P.return (UNKNOWN, []))
  ;;

  let read txt =
    let m = parse_smt2_result >>= P.return in
    match P.run m () (Parsec.StringInput.of_string txt) with
      | Left e -> failwith (Parsec.Error.to_string e)
      | Right answer -> answer
;;
end

(*** FUNCTIONS ***************************************************************)

(* ========== file and smt-solver interaction ========== *)

(* writes the given contents to file *)
let write_file filename contents =
  let output = open_out filename in
  Printf.fprintf output "%s\n" contents ;
  close_out output ;
;;

(* reads the given file into a list of lines *)
let read_file filename =
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; ""
  with End_of_file ->
    close_in chan;
    List.fold_right (fun l s -> l ^ "\n" ^ s) (List.rev !lines) ""
;;

(* this method replaces for instance "- 1" by "-1" *)
let fix_integers str =
  if String.length str > 2 && str.[0] = '-' && str.[1] = ' ' then
    "-" ^ (String.sub str 2 (String.length str - 2))
  else str
;;

(* maps a sequence of lines of the form "a b" into a sequence of pairs
("a","b") *)
let variable_assignments lst =
  (* FIXME: not needed; but is currently used stuff complete?*)
  let maketuple txt =
    let lst = String.split ~d:" " txt in
    if List.length lst < 3 then [] else
    let variable = List.hd lst in
    let lst = List.tl (List.tl lst) in
    let replacement = List.fold_left (fun a b -> a ^ b) "" lst in
    let replacement = fix_integers replacement in
    let replacement = String.trim replacement in
    [(variable, replacement)]
  in
  List.flat_map maketuple lst
;;

(* runs the smt-solver on the given problem and returns the list of
variable assignments *)
let call_solver problem solver =
  let file = Filename.temp_file "ctrl" ".smt" in
  let out = Str.string_before file (String.length file - 4) ^ ".out" in
  write_file file problem;
  let _ = Unix.system ("./timeout 3 ./" ^ solver ^ " " ^ file ^ " > " ^ out) in
  let ret = read_file out in
  ignore (Unix.system ("rm " ^ file));
  if Sys.file_exists out then (* might not exist if error/timeout occurred *)
    ignore (Unix.system ("rm " ^ out));
  let trouble () = (* DEBUGGING *)
    if Util.query_debugging () then
      Printf.printf "%s\n%s\n"
        "SMT-solver has trouble with the following problem:" problem ;
    (UNKNOWN, [])
  in
  let res = SmtResultReader.read ret in
  if Util.query_debugging () then (
    assert (not (Sys.file_exists out));
    assert (not (Sys.file_exists file)));
  if fst res = UNKNOWN then trouble () else res
;;

(* runs the smt-solver on the given problem and returns the list of
variable assignments parsed into string * string tuples *)
let check_smt_file problem solver =
  let (satisfiability, varass) = call_solver problem solver in
  if satisfiability <> SAT then (satisfiability, [])
  else (satisfiability, varass)
;;

(* ========== translating between terms / formulas and smt-format ========== *)

(* reads a variable name to a Term.Var, giving an appropriate error
if that fails (Not_found is frustrating!) *)
let variable_to_var var e =
  try Environment.find_var var e
  with Not_found -> failwith ("SMT-solver returns an unexpected variable " ^ var)
;;

(* reads a value to a Term, giving an appropriate error if that
fails *)
let value_to_term value a sort =
  match Alphabet.test_mixed sort a with
    | None -> Term.read_value value a "smt-solver"
    | Some (o,c) ->
      Term.make_fun (Function.mixed_symbol value o c) []
;;

(* translates the given symbol to its SMT-representation *)
let renamed_symbol symb renamings =
  try List.assoc symb renamings
  with Not_found -> symb
;;

(* creates an smt-input-style representation of the given term *)
let print_as_smt term renamings translations e = 
  let print_var x = Variable.find_name x in
  let print_fun f args =
    let symb =
      if Function.is_mixed f then Function.mixed_to_string f
      else Function.find_name f
    in
    let symb = renamed_symbol symb renamings in
    try
      let translation = List.assoc symb translations in
      let translate = function
        | Left str -> str
        | Right i ->
          try List.nth args i
          with Invalid_argument _ ->
            failwith ("Symbol translation " ^ symb ^ " does not " ^
                      "correspond with the symbol's usage!")
      in
      List.implode translate "" translation
    with Not_found ->
      if args = [] then symb else
      "(" ^ symb ^ " " ^ (List.to_string id " " args) ^ ")" 
  in
  let print_quantifier kind x arg =
    let xsort = Sort.to_string (Environment.find_sort x e) in
    let var = "((" ^ (print_var x) ^ " " ^ xsort ^ "))" in
    "(" ^ kind ^ " " ^ var ^ " " ^ arg ^ ")"
  in
  let print_forall = print_quantifier "forall" in
  let print_exists = print_quantifier "exists" in
  let print_sorted_fun f args _ = print_fun f args in
  Term.recurse print_var print_fun print_sorted_fun print_forall
               print_exists term
;;

(* turns the given expressions into an SMT-input file, using
[tostr] as the method to convert an expression to SMT-format, SMTLIB v.2.0 *)
let create_smt_file env params exprs tostr logic =
  let build_param v =
    "(declare-const " ^ (Variable.find_name v) ^ " " ^
    (Sort.to_string (Environment.find_sort v env)) ^ ")\n"
  in
  let build_formula f = "(assert " ^ (tostr f) ^ ")\n" in
  (*"(set-logic " ^ logic ^ ")\n" ^*) (* skip logic for now *)
  (List.implode build_param " " params) ^ "\n" ^
  (List.implode build_formula "\n" exprs) ^
  "(check-sat)\n(get-model)\n"
;;

(* turns the given combination into SMTLIB v.2.0 *)
let print_file vars formulas logic get_model =
  let print_var_type (xn, xt) = "(declare-const " ^ xn ^ " " ^ xt ^ ")\n" in
  let f formula rest = "(assert " ^ formula ^ ")\n" ^ rest in
  let assertions = List.fold_right f formulas "" in
  (*"(set-logic " ^ logic ^ ")\n" ^*) (* skip logic for now *)
  (List.implode print_var_type " " vars) ^
  assertions ^
  "(check-sat)\n" ^ (if get_model then "(get-model)\n" else "")
;;

(* returns variable / sort pairs for all variables in the given
term *)
let get_variables e term =
  let vars = Term.vars term in
  let varname x = Variable.find_name x in
  let sort x = Sort.to_string (Environment.find_sort x e) in
  let makepair x = (varname x, sort x) in
  List.map makepair vars
;;

(* passes the given problem to the given solver, and parses the result
to obtain a substitution if we have a satisfiable case *)
let check_smt_file_and_parse problem solver env alf =
  let (satisfiability, assignment) = check_smt_file problem solver in
  let gamma = Substitution.empty in
  if satisfiability <> SAT then (satisfiability, gamma)
  else (
    let rec update gamma = function
      | [] -> gamma
      | (var, value) :: tail ->
        try
          let x = Environment.find_var var env in
          let xsort = Environment.find_sort x env in
          let term =
            try
              value_to_term value alf xsort
            with _ ->
              if String.get value 0 == '#' && String.get value 1 == 'x'  then
                let csort = Sortdeclaration.create [] xsort in
                let c = Alphabet.create_fun csort value alf in
                Alphabet.add_symbol_kind c Alphabet.Logical alf;
                Term.Fun (c,[])
              else
                let ival = int_of_string value in
                Term.Fun (Function.integer_symbol ival,[])
          in
          update (Substitution.add x term gamma) tail
        with Not_found -> update gamma tail
    in
    (SAT, update gamma assignment)
  )
;;

(* ========== doing calculations ========== *)

let calculate term (solver, logic) renamings translations a e =
  let sort = Term.get_sort a e term in
  let vars = get_variables e term in
  let printed = print_as_smt term renamings translations e in
  let formula = "(= SMT_MODULE_SOLUTION " ^ printed ^ ")" in
  let termsort = Sort.to_string (Term.get_sort a e term) in
  let contents =
    print_file (("SMT_MODULE_SOLUTION",termsort) :: vars) [formula] logic true
  in
  let (satisfiability, assignment) = check_smt_file contents solver in
  if satisfiability <> SAT then
    failwith ("Could not calculate " ^ printed ^ ": SMT-solver fails")
  else (
    let value = List.assoc "SMT_MODULE_SOLUTION" assignment in
    value_to_term value a sort
  )
;;

let get_value sort (solver, logic) a =
  let sortstring = Sort.to_string sort in
  let contents = print_file ["SMT1", sortstring; "SMT2", sortstring ]
                            ["(= SMT1 SMT2)"] logic true in
  let (satisfiability, assignment) = check_smt_file contents solver in
  if satisfiability <> SAT then
    failwith ("Could not calculate value of sort " ^ (Sort.to_string sort) ^
              ": SMT-solver fails")
  else (
    let value = List.assoc "SMT1" assignment in
    value_to_term value a sort
  )
;;

(* ========== testing satisfiability ========== *)

let check_formulas terms get_model (solver, logic) renamings translations a e =
  try
  (*let print term = print_as_smt term renamings translations e in
  let s = List.fold_left (^) "" (List.map print terms) in
  let t = Printexc.get_callstack 13 |> Printexc.raw_backtrace_to_string in
  Format.printf "check %s \n%s\n%!" s t;*)
  let vars = List.unique (List.flat_map (get_variables e) terms) in
  let print term = print_as_smt term renamings translations e in
  let formulas = List.map print terms in
  let contents = print_file vars formulas logic get_model in
  if Util.query_debugging () then Format.printf "SMT checks %s\n%!" contents;
  check_smt_file_and_parse contents solver e a
  with Not_found -> failwith "Not_found in check_formulas"
;;

let check_formula term get_model = check_formulas [term] get_model;;

(* ========== testing validity ========== *)

