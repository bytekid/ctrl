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
open Smt;;
open Rewriting;;
open Util;;

(*** TYPES *******************************************************************)

type query = NormalForm of Term.t | ConstrainedNormalForm of Term.t * Term.t |
             Termination of bool | Nontermination | Confluence |
             SimplifiedLctrs of Function.t list * String.t |
             Equivalence of Rule.t list | AssistEquivalence of Rule.t list |
             NoQuery | Smt of Term.t list
type infixkind = InfixLeft | InfixRight | InfixNeither | NoInfix
type infixpriority = int

(*** MODULES *****************************************************************)

module InfixInfo = struct
  type t = infixkind * infixpriority

  let compare = compare

  let fprintf fmt (k, p) =
    let str_infix = function
      | InfixLeft -> "left-infix"
      | InfixRight -> "right-infix"
      | InfixNeither -> "infix"
      | NoInfix -> "not infix"
    in
    Format.fprintf fmt "%s, priority %d" (str_infix k) p
end;;

module ChainInfo = struct
  type t = int list * string list

  let compare = compare
  let rec fprintf fmt (ilst, slst) =
    match slst with
      | [] -> Format.fprintf fmt "x%d\n" (List.hd ilst)
      | head :: tail ->
        Format.fprintf fmt "x%d %s %a" (List.hd ilst) head
          fprintf (List.tl ilst, tail)
end;;

module InfixMap = Map.Make(String)(InfixInfo);;
module ChainMap = Map.Make(String)(ChainInfo);;
module StringStringMap = Map.Make(String)(String);;

module State = struct
  type t = InfixMap.t * ChainMap.t * query * Function.t list option

  let compare = compare
  let fprintf fmt (i, c) =
    Format.fprintf fmt "Infix Properties:\n%a\nChains:%a\n"
      InfixMap.fprintf i ChainMap.fprintf c
end;;

module Parser = Parsec.MakeStatefulCharParser(Parsec.StringInput)(State)

(* abbreviation *)
module P = Parser;;
module Sdec = Specialdeclaration;;

(* NOTE: the state is used to keep track of infix symbols and the
corresponding chains.

The parsing calls have side effects on the current TRS.  This means
that if some parsing step fails, all side effects before the failure
have already happened.  With the current code, this is not a problem,
but this should be kept in mind for future extensions.
*)

(*** FUNCTIONS ***************************************************************)

(* ===== Accessing the current TRS ===== *)

let trs () = Trs.get_current ()
let alphabet () = Trs.get_alphabet (Trs.get_current ());;
let environment () = Trs.get_main_environment (Trs.get_current ());;
let csmapping () = Trs.get_context_sensitivity (Trs.get_current ());;
let smtsolver () = Rewriter.smt_solver (Rewriter.get_current ());;

let functions_declared = ref true;;
let arrays_permitted = ref true;;

(* ===== Basic Parse Functions ===== *)

let (>>=) = Parser.(>>=);;
let (>>) = Parser.(>>);;
let (<?>) = Parser.(<?>);;
let (<|>) = Parser.(<|>);;

let ident = (Parser.many1 (Parser.noneof " \t\n\r(),:;[]{}") >>= function
  | ['-';'>'] | ['<';'-';'-'] | ['-';'>';'*'] | ['-';'>';'<';'-'] -> Parser.fail
  | i -> Parser.return i) <?> "identifier"
;;

let ident_with_array = (Parser.many1 (Parser.noneof " \t\n\r(),;[]") >>= function
  | ['-';'>'] | ['<';'-';'-'] | ['-';'>';'*'] | ['-';'>';'<';'-'] -> Parser.fail
  | i -> Parser.return i) <?> "identifier"
;;

let number = Parser.many1 Parser.digit <?> "non-negative integer"

let integer =
  Parser.lex number >>= fun n ->
  Parser.return (int_of_string (String.of_char_list n))
;;

let sortident = (Parser.many1 (Parser.noneof " \t\n\r(),.:;[]^*<>?") >>=
  fun i ->Parser.return i) <?> "sort"
;;

let parse_identifier f =
  Parser.lex f >>= fun i -> Parser.return (String.of_char_list i)
;;

(* ===== Advanced Parsing Functions ===== *)

let parser_fail msg =
  Parser.get_position >>= fun pos ->
  let start = "Parsing error encountered at " ^
              "line " ^ (string_of_int (Parsec.Pos.row pos)) ^ ", " ^
              "column " ^ (string_of_int (Parsec.Pos.col pos)) in
  match Parsec.Pos.file pos with
    | None -> failwith (start ^ ":\n  " ^ msg)
    | Some fname -> failwith (start ^ " in file " ^ fname ^ ": \n" ^ msg)
;;

let keywords = ["THEORY";"LOGIC";"SOLVER";"SIGNATURE";"RULES";
                "CONTEXT-SENSITIVE";"ERROR";"NON-STANDARD";"IRREGULAR";
                "QUERY";"INCLUDE";"DECLARE";"CHAIN";"SMT-RENAMINGS";
                "SMT-TRANSLATIONS";"WELLFOUNDED"];;

let is_keyword txt = List.exists (fun word -> txt = word) keywords;;

(* this checks whether the next thing in line is a keyword, but does
not read it; if it is, the given value "ret" is returned *)
let parse_keyword ret =
  let check_keyword word =
    ( Parser.tempt (Parser.lookahead (Parser.string word)) ) >>
    Parser.return ret
  in
  ( Parser.choice (List.map check_keyword keywords) ) <?> "keyword"
;;

(* this function checks whether we have reached a new keyword or the
end of the file *)
let end_of_part ret =
  ( parse_keyword ret ) <|>
  ( Parser.eoi >> Parser.return ret )
;;

(* this function checks whether we have reached the end of the file *)
let end_of_input _ =
  ( Parser.eoi >> Parser.return () )
;;

(* this function is called after reading one element of a 'list',
to read the rest of the list or abort; if there is a separator
(element of the char list separators), which isn't followed by the
end of the section, then f ret is called, otherwise ret is returned
*)
let parse_rest_of_list separators f ret =
  let check_separator c =
    Parser.lex (Parser.char c) >>= fun _ ->
    ( end_of_part ret ) <|>
    ( Parser.get_state >>= fun _ -> f ret)
      (* the get_state only serves to make sure f won't be executed
         if it's not necessary *)
  in
  ( Parser.choice (List.map check_separator separators) ) <|>
  ( end_of_part ret )
;;

(* used whenever we start up the parser *)
let start_state = (InfixMap.empty, ChainMap.empty, NoQuery, None);;

(* start the parser with the given function on the given text *)
let parse_text f arg txt startstate filename =
  let m = f arg >>= Parser.return in
  match Parser.run ~file:filename m startstate (Parsec.StringInput.of_string txt) with
    | Left e -> failwith (Parsec.Error.to_string e)
    | Right answer -> answer
;;

(* if the current input starts with the given keyword, call f b,
otherwise just return b *)
let attempt_parse keyword f b =
  Parser.spaces >>= fun _ ->
  ( Parser.tempt (Parser.lex (Parser.string keyword)) >>= fun _ -> f b ) <|>
  ( Parser.get_state >> Parser.return b )
;;

(* ===== File Access ===== *)

let file_contents fname =
  let channel = open_in fname in
  let txt = ref "" in
  try
    while true do (
      let s = input_line channel in
      txt := !txt ^ "\n" ^ s
    ) done ; ""
  with _ ->
    let lst = String.split ~d:"END OF FILE" !txt in
    close_in channel ;
    List.hd lst
;;

(* ===== Dealing with comments ===== *)

(* This function handles the main decommenting functionality,
replacing comments by whitespace *)
let rec parse_comments start i =
  Parser.many (Parser.noneof "*/\n") >>= fun txt ->
  let stxt =
    if i = 0 then String.of_char_list txt
    else String.make (List.length txt) ' '
  in
  let text = start ^ stxt in
  ( Parser.eoi >>= fun _ ->
    if i > 0 then failwith "Error reading file: unclosed comment!"
    else Parser.return text
  ) <|>
  ( Parser.tempt (Parser.string "/*") >>= fun _ -> parse_comments text (i+1) ) <|>
  ( Parser.tempt (Parser.string "*/") >>= fun _ ->
    if i > 0 then parse_comments text (i-1)
    else Parser.failwith "Unmatched closing comment */"
  ) <|>
  ( Parser.oneof "\n*/" >>= fun c ->
    parse_comments (text ^ (String.make 1 c)) i
  ) <|>
  ( Parser.get_state >>= fun _ -> parse_comments text i )
;;

(* This function replaces all the comments in txt by whitespace *)
let decomment txt fname =
  parse_text (parse_comments "") 0 txt start_state fname
;;

(* ===== Parsing INCLUDE and THEORY lists ===== *)

(* this reads a list and includes it *)
let rec parse_include sofar =
  parse_identifier ident >>= fun name ->
  parse_rest_of_list [',';';'] parse_include (name :: sofar)
;;

(* this returns the list of includes from a file, where keyword is
the include keyword (this might be THEORY or INCLUDE *)
let include_list keyword fname =
  let contents = decomment (file_contents fname) fname in
  let parse_theory keyword = attempt_parse keyword parse_include [] in
  parse_text parse_theory keyword contents start_state fname
;;

(* this returns the list of all files to be read according to the
THEORY declaration in the given file, and the includes in the
corresponding theories. *)
let get_theories fname =
  let rec recursive_include_list keyword handled = function
    | [] -> handled
    | head :: tail ->
      let lst = include_list keyword head in
      let lst = List.map (fun s -> "theories/" ^ s ^ ".thr") lst in
      let rest = recursive_include_list keyword (head :: handled) tail in
      recursive_include_list "INCLUDE" rest lst
  in
  recursive_include_list "THEORY" [] [fname]
;;

(* ===== Parsing a Signature (DECLARE or SIGNATURE) ===== *)

(* save the given infix information in the state *)
let register_infix name (priority, kind) =
  Parser.get_state >>= fun (infixes, chains, query, simplifying) ->
  let symbolprops = (
    if InfixMap.mem name infixes then InfixMap.find name infixes
    else (NoInfix, -1)
  ) in
  let update_infix (ifk, p) =
    if ifk = NoInfix then
      Parser.return (kind, priority)
    else if p <> priority || kind != ifk then
      parser_fail ("Symbol " ^ name ^ " redeclared with different " ^
                   "infix properties.")
    else Parser.return (ifk, p)
  in
  update_infix symbolprops >>= fun updatedsymbolprops ->
  let infixes = InfixMap.replace name updatedsymbolprops infixes in
  Parser.set_state (infixes, chains, query, simplifying)
;;

(* register a new sort declaration for an already existing symbol *)
let register_sortdeclaration f normal special a =
  if normal = None && special = None then Parser.return ()
  else if not (Alphabet.mem_sortdec f a) then (
    if normal <> None then Parser.return
      (Alphabet.add_normal_sortdec f (Option.the normal) a)
    else Parser.return
      (Alphabet.add_special_sortdec f (Option.the special) a)
  )
  else
    let ok = (match Alphabet.find_sortdec f a with
      | Left original ->
          if normal = None then false
          else original = (Option.the normal)
      | Right original ->
          if special = None then false
          else original = (Option.the special)
    ) in
    if ok then Parser.return ()
    else parser_fail ("Trying to override previously declared " ^
            "symbol " ^ (Function.find_name f)^
            " with a different sort declaration.")
;;

(* deal with a declaration for !INTEGER *)
let register_integers normal special a =
  let check_sortdec sd =
    if Sortdeclaration.arity sd <> 0 then
      parser_fail "Integers may only have arity 0!"
    else Parser.return (Sortdeclaration.output_sort sd)
  in
  if special <> None then
    parser_fail ("Cannot declare the integers with a polymorphic " ^
      "sort declaration!")
  else if not (Alphabet.has_integers a) then (
    if normal = None then
      parser_fail ("Integers must always be declared with a sort.")
    else (
      check_sortdec (Option.the normal) >>= fun sort ->
      Parser.return (Alphabet.include_integers sort a)
    )
  )
  else (
    if normal = None then Parser.return ()
    else ( 
      check_sortdec (Option.the normal) >>= fun sort ->
      if Alphabet.integer_sort a <> sort then
        parser_fail ("Integers declared with sort " ^
          (Sort.to_string sort) ^ " but were previously declared " ^
          "with sort " ^ (Sort.to_string (Alphabet.integer_sort a))
          ^ ".")
      else Parser.return ()
    )
  )
;;

(* deal with a declaration for !ARRAY!sort *)
let register_arrays isort normal special a =
  let check_sortdec sd =
    if Sortdeclaration.arity sd <> 0 then
      parser_fail "Arrays may only have arity 0!"
    else Parser.return (Sortdeclaration.output_sort sd)
  in
  if special <> None then
    parser_fail ("Cannot declare the arrays with a polymorphic " ^
      "sort declaration!")
  else (
    try
      let osort = Alphabet.array_sort isort a in
      if normal = None then Parser.return () else
      check_sortdec (Option.the normal) >>= fun sort ->
      if osort <> sort then
        parser_fail ((Sort.to_string isort) ^ "-arrays declared " ^
          "with sort " ^ (Sort.to_string sort) ^ " but were " ^
          "previously declared with sort " ^ (Sort.to_string osort) ^
          ".")
      else Parser.return ()
    with Not_found ->
      if normal = None then
        parser_fail ("Arrays must always be declared with a sort.")
      else (
        check_sortdec (Option.the normal) >>= fun sort ->
        Parser.return (Alphabet.include_arrays isort sort a)
      )
  )
;;

(* deal with a declaration for !MIXED!bo!bc *)
let register_mixed bo bc normal special a =
  let check_sortdec sd =
    if Sortdeclaration.arity sd <> 0 then
      parser_fail "Mixed symbols must be constants!"
    else Parser.return (Sortdeclaration.output_sort sd)
  in
  if special <> None then
    parser_fail ("Cannot declare mixed symbols with a polymorphic " ^
      "sort declaration!")
  else (
    try
      let osort = Alphabet.mixed_sort (bo, bc) a in
      if normal = None then Parser.return () else
      check_sortdec (Option.the normal) >>= fun sort ->
      if osort <> sort then
        parser_fail (bo ^ "-" ^ bc ^ "-arrays declared " ^
          "with sort " ^ (Sort.to_string sort) ^ " but were " ^
          "previously declared with sort " ^ (Sort.to_string osort) ^
          ".")
      else Parser.return ()
    with Not_found ->
      if normal = None then
        parser_fail ("Mixed symbols must always be declared with a sort.")
      else (
        check_sortdec (Option.the normal) >>= fun sort ->
        Parser.return (Alphabet.include_mixed bo bc sort a)
      )
  )
;;

(* save the given symbol information in the alphabet *)
let register_declaration name sd logical =
  let variable, monomorphic, normal, special =
    match sd with
      | None -> (false, true, None, None)
      | Some d ->
        let m = Specialdeclaration.is_normal_sortdec d in
        (
          not (Specialdeclaration.known_arity d), m,
          (if m then Some (Specialdeclaration.make_normal_sortdec d) else None),
          if m then None else Some d
        )
  in
  let rec check_occurrence x = function
    | [] -> false
    | head :: tail -> if x = head then true else check_occurrence x tail
  in
  let check_polymorphism_ok = match special with
    | None -> true
    | Some d ->
      let outp = Specialdeclaration.output_sort d in
      if not (Specialdeclaration.is_polymorphic outp) then true
      else check_occurrence outp (Specialdeclaration.input_sorts d)
  in
  let add_symbol_kind a f = Parser.return (
      if logical then Alphabet.add_symbol_kind f Alphabet.Logical a
      else Alphabet.add_symbol_kind f Alphabet.Terms a
    )
  in
  if variable && not logical then
    parser_fail ("Function symbol declarations with variable " ^
      "arity may only occur in the logical alphabet.")
  else if (not monomorphic) && (not logical) then
    parser_fail ("Polymorphic symbol declarations may only " ^
      "occur in the logical alphabet.")
  else if sd = None && logical then
    parser_fail ("Symbols in the logical alphabet must be fully " ^
      "declared (problem with " ^ name ^ ").")
  else if not check_polymorphism_ok then
    parser_fail ("Output sort of " ^ name ^ " is a sort variable " ^
      "which does not occur in the input sorts.")
  else (
    let a = alphabet () in
    if name = "!INTEGER" then register_integers normal special a
    else if (String.length name > 7) &&
            (String.sub name 0 7 = "!ARRAY!") then (
      let isort = String.sub name 7 ((String.length name) - 7) in
      register_arrays (Sort.from_string isort) normal special a
    )
    else if (String.length name > 7) &&
            (String.sub name 0 7 = "!MIXED!") then (
      let remainder = String.sub name 7 ((String.length name) - 7) in
      if not (String.contains remainder '!') then
        parser_fail ("Syntax failure for mixed symbol " ^ name ^ " : MIXED" ^
          " must be specified as !MIXED!<open bracket>!<close bracket>") else
      let splitter = String.index remainder '!' in
      let before = String.sub remainder 0 splitter in
      let after = String.sub remainder (splitter + 1)
        ((String.length remainder) - splitter - 1) in
      if before = "" || after = "" then
        parser_fail ("Illegal mixed symbol " ^ name ^ " : both brackets " ^
          "must be non-empty!")
      else register_mixed before after normal special a
    )
    else if Alphabet.mem_fun_name name a then (
      let f = Alphabet.find_fun name a in
      register_sortdeclaration f normal special a >>= fun _ ->
      add_symbol_kind a f
    )
    else add_symbol_kind a (
      if Option.is_some normal then
        Alphabet.create_fun (Option.the normal) name a
      else if Option.is_some special then
        Alphabet.create_instance_fun (Option.the special) name a
      else Alphabet.fresh_fun name a
    )
  )
;;

(* infix = (infix <num>) | (l-infix <num>) | (r-infix <num>) *)
let parse_infix name ret =
  let infix_main kind =
    integer >>= fun n ->
    Parser.lex (Parser.char ')') >>= fun _ ->
    register_infix name (n, kind) >>
    Parser.return (name, ret)
  in
  Parser.char '(' >>= fun _ ->
  ( Parser.lex (Parser.string "infix") >>= fun _ ->
    infix_main InfixNeither
  ) <|>
  ( Parser.lex (Parser.string "l-infix") >>= fun _ ->
    infix_main InfixLeft
  ) <|>
  ( Parser.lex (Parser.string "r-infix") >>= fun _ ->
    infix_main InfixRight
  )
;;

(* sortdeclaration = sortidentifier | argslist => sortidentifier
   argslist = normalargslist | <sort>
   normalargslist = sortidentifier | sortidentifier * normalargslist

   this will always return a special declaration (which may be
   converted to a normal declaration)
*)
let parse_sortdec =
  let nums = integer <|> (P.char '_' >> P.return (-1)) in
  (* possibly polymorphic sort *)
  let psort =
    let id = P.lex (parse_identifier sortident) in
    P.lex (
      ((P.option [] (P.string "?") >>= fun p -> id >>= fun n ->
      P.return (Sdec.make_polsort (String.of_char_list p ^ n) ~index:None))
        <?> "sort")
      <|> (
        P.char '(' >> id >>= fun n -> nums >>= fun i -> P.char ')' >>
        P.return (Sdec.make_polsort n ~index:(Some i))))
  in
  let arglist =
    let star = P.lex (P.char '*') in
    P.option [] (star >> P.sep_by psort star) <?> "argument list"
  in
  let arrow = P.lex (P.string "=>") <?> "arrow" in
  let ssort = P.lex (P.between (P.char '<') psort (P.char '>')) <?> "?sort" in
  (* case of argument list <...> (only allowed as the first argument) *)
  (ssort >>= fun arg -> arrow >> psort >>= fun res ->
   P.return (Specialdeclaration.variable_declaration arg res))
  <|>
  (psort >>= fun a ->
    (* case of other arrow type *)
    ((arglist >>= fun args -> arrow >> psort >>= fun res ->
      P.return (Specialdeclaration.polymorphic_declaration (a::args) res))
     <|>
     (* case of non-arrow type *)
     (P.return (Specialdeclaration.polymorphic_declaration [] a))))
;;

(* declaration = identifier ix | identifier : sortdeclaration ix
   ix = <empty> | infix
   if logical is true, then the sort declaration may not be omitted,
   and the sort declarations may be polymorphic
*)
let parse_declaration _ =
  parse_identifier ident >>= fun name ->
  (
    Parser.lex (Parser.char ':') >>= fun _ ->
    parse_sortdec (*[] false false*) >>= fun sd ->
    ( parse_infix name (Some sd) ) <|>
    ( Parser.return (name, (Some sd)) )
  ) <|>
  ( parse_infix name None ) <|>
  ( Parser.return (name, None) )
;;

(* alphabet = declaration list *)
let rec parse_signature logical =
  parse_declaration () >>= fun (name, sd) ->
  register_declaration name sd logical >>
  parse_rest_of_list [',';';'] parse_signature logical
;;

(* parse signature, and check whether the infix values in the
result are set correctly (left- and right-infix must have arity
2) *)
let rec parse_check_signature logical =
  let _ = parse_signature logical in
  let check_infix name (kind, _) =
    let a = alphabet () in
    if kind = InfixLeft || kind = InfixRight then (
      let f = Alphabet.find_fun name a in
      if Alphabet.mem_ari f a then (
        if Alphabet.find_ari f a <> 2 then
          failwith ("Symbol " ^ name ^ " declared with " ^
            "associativity, but has arity other than 2; " ^
            "this leads to ambiguity.")
      )
    )
  in
  Parser.get_state >>= fun (infixes,_,_,_) ->
  try
    InfixMap.iter check_infix infixes ;
    Parser.return logical
  with Failure msg -> parser_fail msg
;;

(* ===== Parsing a WELLFOUNDED list ===== *)

(* this reads a list and includes it *)
let rec parse_wellfounded _ =
  parse_identifier ident >>= fun name ->
  let a = alphabet () in
  if not (Alphabet.mem_fun_name name a) then
    parser_fail ("No such symbol declared: " ^ name ^ ".") else
  let f = Alphabet.find_fun name a in
  if not (Alphabet.mem_sortdec f a) then
    parser_fail ("Cannot mark a symbol as wellfounded when its " ^
      "sort declaration is not given! (Problem: " ^ name ^ ".)") else
  let sortattempt =
    match Alphabet.find_sortdec f a with
      | Left sd ->
        if (Sortdeclaration.output_sort sd <> Alphabet.boolsort) ||
           (Sortdeclaration.arity sd <> 2) ||
           (Sortdeclaration.input_sort sd 1 <>
            Sortdeclaration.input_sort sd 2) then None
        else Some (Sortdeclaration.input_sort sd 1)
      | Right spd ->
        let outp = Specialdeclaration.output_sort spd in
        if (Specialdeclaration.is_polymorphic outp) then None
        else if (Specialdeclaration.pol_to_sort outp <>
                 Alphabet.boolsort) then None
        else if (Specialdeclaration.known_arity spd) &&
                (Specialdeclaration.arity spd <> 2) then None
        else if (Specialdeclaration.known_arity spd) &&
                (Specialdeclaration.input_sort 1 spd <>
                 Specialdeclaration.input_sort 2 spd) then None
        else if (Specialdeclaration.is_polymorphic
                 (Specialdeclaration.input_sort 1 spd)) then None
        else Some (Specialdeclaration.pol_to_sort (
                    (Specialdeclaration.input_sort 1 spd)))
  in
  match sortattempt with
    | None -> parser_fail ("Cannot mark " ^ name ^ " as " ^
        "wellfounded: not a relation symbol (should be declared as " ^
        "sort * sort => Bool).")
    | Some sort ->
      Alphabet.add_wellfounded sort f a ;
      parse_rest_of_list [',';';'] parse_wellfounded ()
;;

(* ===== Parsing a CHAIN list ===== *)

let check_is_infix f =
  Parser.get_state >>= fun (p,_,_,_) ->
  if not (InfixMap.mem f p) then
    parser_fail ("symbol " ^ f ^ " occurring in chain " ^
      "transformation list is not declared as an infix symbol!")
  else (match InfixMap.find f p with
    | (NoInfix,_) ->
        parser_fail ("symbol " ^ f ^ " occurring in chain " ^
          "transformation list is not declared as an infix symbol!")
    | _ -> Parser.return ()
  )
;;

let rec parse_replace_list vars symbs =
  parse_identifier ident >>= fun x ->
  ( Parser.lookahead (Parser.oneof ",;") >> Parser.return (x::vars,symbs) ) <|>
  ( parse_identifier ident >>= fun f ->
    Parser.get_state >>= fun (infixes, _, _, _) ->
    if not (InfixMap.mem f infixes) then
      parser_fail ("Symbol " ^ f ^ " occurs in chain transformation "^
        "list, but was not declared as an infix symbol.")
    else parse_replace_list (x::vars) (f::symbs)
  )
;;

let parse_chain_elem _ =
  parse_identifier ident >>= fun x1 ->
  parse_identifier ident >>= fun f1 ->
  check_is_infix f1 >>= fun _ ->
  parse_identifier ident >>= fun x2 ->
  parse_identifier ident >>= fun f2 ->
  check_is_infix f2 >>= fun _ ->
  parse_identifier ident >>= fun x3 ->
  Parser.lex (Parser.char ':') >>= fun _ ->
  parse_replace_list [] [] >>= fun (lst1, lst2) ->
  let rec numerify rest = function
    | [] -> Parser.return rest
    | name :: tail ->
      if name = x1 then numerify (1 :: rest) tail
      else if name = x2 then numerify (2 :: rest) tail
      else if name = x3 then numerify (3 :: rest) tail
      else parser_fail ("Encountered symbol " ^ name ^ " at a " ^
        "variable position in chain declaration; should be one " ^
        "of " ^ x1 ^ ", " ^ x2 ^ " or " ^ x3)
  in
  let symbols = List.rev lst2 in
  numerify [] lst1 >>= fun vars ->
  Parser.get_state >>= fun (p,c,q,s) ->
  let name = f1 ^ " " ^ f2 in
  if ChainMap.mem name c then
    parser_fail ("Trying to declare a chain combination for " ^
      "x " ^ f1 ^ " y " ^ f2 ^ " z, but this was previously " ^
      "declared!")
  else (
    let newc = ChainMap.add name (vars, symbols) c in
    Parser.set_state (p,newc,q,s)
  )
;;

let rec parse_chain _ =
  parse_chain_elem () >>= fun _ ->
  parse_rest_of_list [',';';'] parse_chain ()
;;

(* ===== Parsing SMT-RENAMINGS and SMT-TRANSLATIONS lists ===== *)

let register_renaming original renaming =
  Solver.add_symbol_renaming original renaming (smtsolver ()) true
;;

let rec parse_renamings _ =
  parse_identifier ident >>= fun original ->
  Parser.lex (Parser.string "->") >>= fun _ ->
  parse_identifier ident >>= fun renaming ->
  register_renaming original renaming ;
  parse_rest_of_list [',';';'] parse_renamings ()
;;

let rec parse_smt_term_sub sofar =
  Parser.many (Parser.noneof "()") >>= fun x ->
  let read = sofar ^ (String.of_char_list x) in
  (
    Parser.lex (Parser.char ')') >>= fun _ ->
    Parser.return (read ^ ")")
  ) <|>
  (
    Parser.lex (Parser.char '(') >>= fun _ ->
    parse_smt_term_sub (read ^ "(") >>= fun newsofar ->
    parse_smt_term_sub (newsofar ^ " ")
  )

let parse_smt_term _ =
  Parser.lex (Parser.char '(') >>= fun _ ->
  parse_smt_term_sub "("
;;

let register_translation original translation =
  Solver.add_symbol_translation original translation (smtsolver ()) true
;;

let rec split_smt vars start sofar str =
  let is_abnormal ch = List.mem ch ['(';')';' '] in
  let is_normal ch = not (is_abnormal ch) in
  let rec find_char prop k =
    if k >= String.length str then -1
    else if prop (String.get str k) then k
    else find_char prop (k + 1)
  in
  if str = "" then [] else
  let i = find_char is_normal start in
  if i < 0 then (
    let ending = String.sub str start ((String.length str) - start) in
    [Left (sofar ^ ending)]
  ) else
  let j = find_char is_abnormal i in
  let x = sofar ^ (String.sub str start (i - start)) in
  let y = String.sub str i (j - i) in
  try
    let rec find_index i = function
      | [] -> raise Not_found
      | hd :: tl -> if hd = y then i else find_index (i+1) tl
    in
    if x = "" then (Right (find_index 0 vars)) :: split_smt vars j "" str
    else (Left x) :: (Right (find_index 0 vars)) :: split_smt vars j "" str
  with Not_found -> split_smt vars j (x ^ y) str
;;

let rec parse_translations _ =
  parse_identifier ident >>= fun original ->
  Parser.lex (Parser.char '(') >>= fun _ ->
  Parser.sep_by (parse_identifier ident)
    (Parser.lex (Parser.char ',')) >>= fun vars ->
  Parser.lex (Parser.char ')') >>= fun _ ->
  Parser.lex (Parser.string "->") >>= fun _ ->
  parse_smt_term () >>= fun translation ->
  let tr = split_smt vars 0 "" translation in
  register_translation original tr ;
  parse_rest_of_list [',';';'] parse_translations ()
;;

(* ===== Parsing LOGIC and SOLVER statements ===== *)

(* store that we are using a particular logic *)
let use_logic name =
  Solver.use_logic name (smtsolver ())
;;

(* store that we are using a particular logic *)
let use_solver name =
  if name = "internal" then Solver.use_internal_solver (smtsolver ())
  else if name = "manual" then
    Solver.use_manual_solver (smtsolver ()) Printer.to_string_term
  else Solver.use_solver name (smtsolver ())
;;

(* logic = identifier
   solver = identifier
   (a , or ; may be added in the end)
*)
let parse_single f _ =
  parse_identifier ident >>= fun name ->
  f name ;
  parse_rest_of_list [',';';'] Parser.return ()
;;

let rec parse_list f _ =
  parse_identifier ident >>= fun name ->
  f name ;
  parse_rest_of_list [',';';'] (parse_list f) ()
;;

(* ===== Parsing terms ===== *)

(* create a variable with the given name in the given environment *)
let make_variable_term name env =
  let x =
    if Environment.mem_var_name name env then
      Environment.find_var name env
    else Environment.create_unsorted_var name env
  in
  Parser.return (Term.make_var x)
;;

(* create a function with the given name and the given list of
arguments; as might be expected, this function is mostly about
doing checks that the term is okay! *)
let make_functional_term name lst =
  let a = alphabet () in
  let n = List.length lst in
  let ok f = Parser.return (Term.make_fun f lst) in
  if not (Alphabet.mem_fun_name name a) then (
    (*
    if name = "forall" || name = "exists" then (
      match lst with
        | [Term.Var x; arg] ->
          ( try
              let sort = Alphabet.integer_sort a in
              Environment.add_sort x sort (environment ())
            with _ -> failwith ("Occurrence of " ^ name ^
              " is only allowed if the integers are explicitly included.")
          ) ;
          if name = "forall" then Parser.return (Term.Forall (x, arg))
          else Parser.return (Term.Exists (x, arg))
        | _ -> parser_fail ("Occurrence of " ^ name ^ " with " ^
          "unsuitable arguments (should be: variable, formula).")
    )
    else
    *)
    if !functions_declared then
      parser_fail ("Symbol " ^ name ^ " cannot be a variable, " ^
        "but is not declared as a function symbol.")
    else (
      let f = Alphabet.create_unsorted_fun n name a in
      Alphabet.set_symbol_kind f Alphabet.Terms a ;
      ok f
    )
  )
  else (
    let f = Alphabet.find_fun name a in
    if Alphabet.mem_sortdec f a then (
      let sd = Alphabet.find_sortdec f a in
      match sd with
        | Right _ -> ok f
        | Left d ->
          let k = Sortdeclaration.arity d in
          if k <> n then
            parser_fail ("Symbol " ^ name ^ " occurs with arity " ^
            (string_of_int n) ^ " while it was declared with " ^
            "arity " ^ (string_of_int k) ^ ".")
          else ok f
    )
    else if Alphabet.mem_ari f a then (
      let k = Alphabet.find_ari f a in
      if k <> n then (
          parser_fail ("Symbol " ^ name ^ " occurs with arity " ^
            (string_of_int n) ^ " while it previously occurred " ^
            "with arity " ^ (string_of_int k) ^ ".")
      )
      else ok f
    )
    else ( Alphabet.add_ari f n a ; ok f )
  )
;;

(* in particular when dealing with infix symbols, we often need to
use lists of pairs *)
let ($::) (a,b) x =
  x >>= fun (lst1,lst2) ->
  Parser.return (a::lst1,b::lst2)
;;

(* Given a chain of infix symbols and terms, this modifies the chain
to take chain transformations into account *)
let rec make_chain_transformations termlist symblist chainmap =
  match symblist with
    | [] -> (termlist, symblist)
    | head :: [] -> (termlist, symblist)
    | f :: g :: tail ->
      let combined = f ^ " " ^ g in
      if not (ChainMap.mem combined chainmap) then
        let (terms, symbs) = make_chain_transformations (List.tl termlist)
                             (g :: tail) chainmap in
        ((List.hd termlist) :: terms, f :: symbs)
      else
      let t1, lst1 = List.hd termlist, List.tl termlist in
      let t2, lst2 = List.hd lst1, List.tl lst1 in
      let t3, lst3 = List.hd lst2, List.tl lst2 in
      let nums, symbs = ChainMap.find combined chainmap in
      let f i = if i = 1 then t1 else if i = 2 then t2 else t3 in
      let terms = List.map f nums in
      make_chain_transformations (List.append terms lst3)
                                 (List.append symbs tail) chainmap
;;

(* This takes two lists: one of infix symbols of length n, and
   one of terms of length n+1.  The return value encapsulates
   the corresponding term, taking priorities into account as well
   as registered chain transformations, or an error.
*)
let build_from_infix_list termlist symblist =
  Parser.get_state >>= fun (infixes, chains, _, _) ->
  let (termlist, symblist) =
    make_chain_transformations termlist symblist chains
  in
  let rec local_top top p k = function
    | [] -> Parser.return (top, k)
    | f :: tail ->
      let (kind, priority) = InfixMap.find f infixes in
      if priority > p then local_top f priority kind tail
      else if priority < p then Parser.return (top, k)
      else if k = InfixLeft && kind = InfixLeft then Parser.return (top, k)
      else if (k = InfixRight && kind = InfixRight) || top = f then
        local_top f priority kind tail
      else parser_fail ("Ambiguous sequence: symbol " ^ top ^
        " followed by symbol " ^ f ^ ", please use brackets or " ^
        "declare associativity in a non-ambiguous way.")
  in
  let rec handle_left_symbol f terms symbs =
    match symbs with
      | [] -> failwith "strange error, top symbol doesn't occur in list"
      | g :: tail ->
        let t1, terms = List.hd terms, List.tl terms in
        if f <> g then (t1, g) $:: handle_left_symbol f terms tail
        else
          let t2, terms = List.hd terms, List.tl terms in
          make_functional_term f [t1;t2] >>= fun newterm ->
          Parser.return (newterm :: terms, tail)
  in
  let rec handle_right_symbol f terms symbs =
    match symbs with
      | [] -> failwith "strange error, top symbol doesn't occur in list"
      | g :: [] ->
        make_functional_term g terms >>= fun term ->
        Parser.return ([term], [])
      | g :: h :: tail ->
        let t1, terms = List.hd terms, List.tl terms in
        let continue _ =
          (t1,g) $:: (handle_right_symbol f terms (h :: tail))
        in
        if f <> g then continue ()
        else if f = h then continue ()
        else (
          let (k1, p1) = InfixMap.find f infixes in
          let (k2, p2) = InfixMap.find h infixes in
          if k1 = k2 && p1 = p2 then continue ()
          else
            let t2, terms = List.hd terms, List.tl terms in
            make_functional_term f [t1;t2] >>= fun newterm ->
            Parser.return (newterm :: terms, h :: tail)
        )
  in
  let rec handle_neither_symbol f terms symbs sofar =
    let t1, terms = List.hd terms, List.tl terms in
    let sf = t1 :: sofar in
    match symbs with
      | [] ->
        make_functional_term f (List.rev sf) >>= fun t ->
        Parser.return ([t],[])
      | g :: tail ->
        if f = g then
          handle_neither_symbol f terms tail sf
        else (
          if sofar <> [] then
            make_functional_term f (List.rev sf) >>= fun t ->
            Parser.return (t :: terms, symbs)
          else
            (t1,g) $:: (handle_neither_symbol f terms tail [])
        )
  in
  let handle_best terms symbs =
    local_top "" (-1) InfixNeither symbs >>= fun (top, kind) ->
    if kind = InfixLeft then handle_left_symbol top terms symbs
    else if kind = InfixRight then handle_right_symbol top terms symbs
    else handle_neither_symbol top terms symbs []
  in
  let rec make_term terms symbs =
    match symbs with
      | [] -> Parser.return (List.hd terms)
      | _ ->
        handle_best terms symbs >>= fun (t, s) -> make_term t s
  in
  make_term termlist symblist
;;

(* This reads a string and returns a term, updating the environment
   [e] along the way.  Unknown symbols are assumed to be variables.

  term = var | func(term,...,tern) | term infixsymbol term
*)
let rec parse_term e =
  parse_term_list e >>= fun (terms, symbs) ->
  build_from_infix_list terms symbs

and parse_term_list e =
  parse_basic_term e >>= fun t ->
  ( Parser.tempt (Parser.lookahead (Parser.string "\\in ")) >>= fun _ ->
    Parser.return ([t], [])
  ) <|>
  (
    ( ( Parser.tempt
        ( parse_identifier ident_with_array >>= fun ret ->
          if is_keyword ret then Parser.fail
          else Parser.return ret
        )
      ) <|>
      ( Parser.return "" )
    ) >>= fun symbol ->
    Parser.get_state >>= fun (infixes, _, _, _) ->
    if symbol = "" then Parser.return ([t], [])
    else if InfixMap.mem symbol infixes then (
      parse_term_list e >>= fun (terms, symbs) ->
      Parser.return (t :: terms, symbol :: symbs)
    )
    else parser_fail ("Symbol " ^ symbol ^ " used, but not " ^
                      "declared, as an infix symbol.")
  )

and parse_basic_term e =
  ( Parser.lex (Parser.char '(') >>= fun _ ->
    parse_term e >>= fun ret ->
    Parser.lex (Parser.char ')') >>= fun _ ->
    Parser.return ret
  ) <|>
  (
    parse_identifier ident_with_array >>= fun name ->
    ( Parser.lex (Parser.char '(') >>= fun _ ->
      Parser.sep_by (parse_term e)
        (Parser.lex (Parser.char ',')) >>= fun ts ->
      Parser.lex (Parser.char ')') >>= fun _ ->
      make_functional_term name ts
    ) <|>
    (
      Parser.get_state >>= fun _ ->  (* avoid evaluating too soon *)
      if Alphabet.mem_fun_name name (alphabet ()) then
        make_functional_term name []
      else if Environment.mem_var_name name e then
        make_variable_term name e
      else if !functions_declared then
        make_variable_term name e
      else make_functional_term name []
    )
  )
;;

(* ===== Parsing Constraints ===== *)

let parse_constraint e =
  (
    Parser.lex (Parser.char '[') >>= fun _ ->
    parse_term e >>= fun term ->
    Parser.lex (Parser.char ']') >>
    Parser.return term
  )
  (*
  <|>
  (
    Parser.get_state >>= fun _ ->  (* avoid evaluating too soon *)
    parse_term e >>= fun term ->
    (
      Parser.string("->") >>= fun _ ->
      ( Parser.lex (Parser.string "*") >>= fun _ ->
        parse_term e >>= fun otherterm ->
        Parser.return (Constraint.reduce_condition term otherterm)
      ) <|>
      ( Parser.lex (Parser.string "<-") >>= fun _ ->
        parse_term e >>= fun otherterm ->
        Parser.return (Constraint.join_condition term otherterm)
      )
    ) <|>
    (
      Parser.lex (Parser.string "\\in") >>= fun _ ->
      ( Parser.lex (Parser.string "CNF") >>
        Parser.return (Constraint.constructor_form_constraint term)
      ) <|>
      ( Parser.lex (Parser.string "GCNF") >>
        Parser.return (Constraint.ground_constructor_form_constraint term)
      )
    )
  )
  (
    Parser.sep_by (parse_identifier ident_with_array)
      (Parser.lex (Parser.char ',')) >>= fun lst ->
    let makevar name =
      if Environment.mem_var_name name e then
        Environment.find_var name e
      else Environment.create_unsorted_var name e
    in
    let varlist = List.map makevar lst in
    Parser.lex (Parser.string "\\in") >>= fun _ ->
    ( Parser.lex (Parser.string "CNF") >>
      Parser.return (Constraint.constructor_form_constraint varlist)
    ) <|>
    ( Parser.lex (Parser.string "GCNF") >>
      Parser.return (Constraint.ground_constructor_form_constraint varlist)
    )
  )
  *)
;;

let parse_constraints e =
  Parser.sep_by (parse_constraint e)
    (Parser.lex (Parser.char ','))
;;

(* ===== Parsing RULES list ===== *)

let parse_rule e =
  parse_term e <?> "left-hand side" >>= fun l ->
  Parser.lex (Parser.string "->") <?> "arrow '->'" >>
  parse_term e <?> "right-hand side" >>= fun r ->
  (
    Parser.lex (Parser.string "<--") >>= fun _ ->
    parse_constraints e >>= fun c ->
    Parser.return (Rule.create l r c)
  ) <|>
  (
    Parser.lookahead (Parser.char '[') >>= fun _ ->
    parse_constraint e >>= fun c ->
    Parser.return (Rule.create l r [c])
  ) <|>
  (
    Parser.return (Rule.create l r [])
  )
;;

let rec parse_rules_list trs =
  ( end_of_part trs ) <|>
  ( Parser.get_state >>= fun _ ->
    let e = Environment.empty 5 in
    parse_rule e >>= fun rule ->
    Trs.add rule e trs ;
    parse_rest_of_list [';'] parse_rules_list trs
  )
;;

let parse_rules _ =
  parse_rules_list (trs ()) >>= fun _ ->
  Parser.return ()
;;

(* ===== Parsing ERROR indication ===== *)

(* THIS FUNCTIONALITY WAS DISABLED *)
(*
let rec parse_sort_list sofar =
  ( end_of_part sofar ) <|>
  ( parse_identifier ident >>= fun sortname ->
    let sofar = (Sort.from_string sortname) :: sofar in
    parse_rest_of_list [','] parse_sort_list sofar
  )
;;

let parse_error _ =
  parse_identifier ident >>= fun name ->
  Parser.lex (Parser.char ':') >>= fun _ ->
  parse_sort_list [] >>= fun sorts ->
  Parser.return (name, sorts)
;;
*)

(* ===== Parsing CONTEXT-SENSITIVE list ===== *)

let parse_cs_entry _ =
  parse_identifier ident >>= fun symbol ->
  Parser.lex (Parser.char ':') >>
  Parser.lex (Parser.char '{') >>
  Parser.sep_by (Parser.lex number)
          (Parser.lex (Parser.char ',')) >>= fun args ->
  Parser.lex (Parser.char '}') >>
  let convert i = int_of_string (String.of_char_list i) - 1 in
  let positions = List.map convert args in
  let a = alphabet () in
  if not (Alphabet.mem_fun_name symbol a)
  then parser_fail ("Unknown symbol " ^ symbol ^ " in " ^
      "context-sensitivity list")
  else (
    let f = Alphabet.find_fun symbol a in
    let rec highest i = function
      | [] -> i
      | head :: tail -> highest (max i head) tail
    in
    Csmapping.set_reducable_positions f positions (csmapping ()) ;
    if Alphabet.mem_ari f a then (
      let h = highest 0 positions in
      let ar = Alphabet.find_ari f a in
      if ar <= h then
        parser_fail ("Symbol " ^ symbol ^ " in context-" ^
        "sensitivity list uses position " ^ (string_of_int (h+1)) ^
        " which is not a position because " ^ symbol ^ " has " ^
        "arity " ^ (string_of_int ar) ^ "!")
      else Parser.return ()
    )
    else Parser.return ()
  )
;;

let rec parse_cs _ =
  parse_cs_entry () >>= fun _ ->
  parse_rest_of_list [',';';'] parse_cs ()
;;

(* ===== Parsing QUERY ===== *)

let set_query q =
  Parser.get_state >>= fun (p, c, _, s) ->
  Parser.set_state (p, c, q, s)
;;

let set_simplifying lst =
  Parser.get_state >>= fun (p, c, q, _) ->
  Parser.set_state (p, c, q, Some lst)
;;

let rec parse_equivalence sofar =
  parse_term (environment()) >>= fun term1 ->
  Parser.lex (Parser.string "-><-") >>= fun _ ->
  parse_term (environment()) >>= fun term2 ->
  parse_constraint (environment()) >>= fun c ->
  let rule = Rule.create term1 term2 [c] in
  parse_rest_of_list [',';';'] parse_equivalence (rule :: sofar)
;;

let parse_constrained_term () =
  parse_term (environment ()) >>= fun s ->
  Parser.lex (Parser.char '[') >>= fun _ ->
  parse_term (environment ()) >>= fun phi ->
  Parser.lex (Parser.char ']') >>= fun _ ->
  Parser.return (s, phi)
;;

let rec parse_symbol_list sofar =
  Parser.spaces >>= fun _ ->
  ( Parser.lex (Parser.char ']') >>= fun _ ->
    Parser.return sofar
  ) <|>
  ( parse_identifier ident >>= fun name ->
    let f =
      try Some (Alphabet.find_fun name (alphabet ()))
      with Not_found -> None
    in
    match f with
      | Some g -> parse_symbol_list (g :: sofar)
      | None -> parser_fail ("No such symbol: " ^ name)
  )
;;

let starting_lines filename =
  let contents = file_contents filename in
  let parts = String.split ~d:"SIGNATURE" contents in
  let parts = String.split ~d:"RULES" (List.hd parts) in
  List.hd parts
;;

let rec parse_query filename _ =
  Parser.spaces >>= fun _ ->
  ( Parser.lex (Parser.string "normal form") >>= fun _ ->
    parse_term (environment ()) >>= fun term ->
    set_query (NormalForm term)
  ) <|>
  ( Parser.lex (Parser.string "termination") >>= fun _ ->
    set_query (Termination true)
  ) <|>
  ( Parser.lex (Parser.string "loops") >>= fun _ ->
    set_query Nontermination
  ) <|>
  ( Parser.lex (Parser.string "innermost-termination") >>= fun _ ->
    set_query (Termination false)
  ) <|>
  ( Parser.lex (Parser.string "confluence") >>= fun _ ->
    set_query Confluence
  ) <|>
  ( Parser.lex (Parser.string "equivalence") >>= fun _ ->
    parse_equivalence [] >>= fun rule ->
    set_query (Equivalence rule)
  ) <|>
  ( Parser.lex (Parser.string "user-equivalence") >>= fun _ ->
    parse_equivalence [] >>= fun rule ->
    set_query (AssistEquivalence rule)
  ) <|>
  ( Parser.lex (Parser.string "simplification [") >>= fun _ ->
    parse_symbol_list [] >>= fun lst ->
    set_query (SimplifiedLctrs (lst, starting_lines filename))
  ) <|>
  ( Parser.lex (Parser.string "print-simplification [") >>= fun _ ->
    parse_symbol_list [] >>= fun lst ->
    set_query (SimplifiedLctrs (lst, starting_lines filename))
  ) <|>
  ( Parser.lex (Parser.string "do-simplify [") >>= fun _ ->
    parse_symbol_list [] >>= fun lst ->
    Parser.string "and" >>= fun _ ->
    set_simplifying lst >>= fun _ ->
    parse_query filename ()
  ) <|>
  ( Parser.lex (Parser.string "reduce constrained") >>= fun _ ->
    parse_constrained_term () >>= fun (term, phi) ->
    set_query (ConstrainedNormalForm (term, phi))
  ) <|>
  ( Parser.lex (Parser.string "abort") >>= fun _ ->
    set_query NoQuery
  ) <|>
  ( Parser.get_state >>= fun _ ->
    set_query NoQuery
  )
;;

(* ===== Reading a Theory File (not including includes) ===== *)

let parse_theory _ =
  attempt_parse "INCLUDE" parse_include [] >>= fun _ ->
  attempt_parse "DECLARE" parse_signature true >>= fun _ ->
  attempt_parse "WELLFOUNDED" parse_wellfounded () >>= fun _ ->
  attempt_parse "CHAIN" parse_chain () >>= fun _ ->
  attempt_parse "SMT-RENAMINGS" parse_renamings () >>= fun _ ->
  attempt_parse "SMT-TRANSLATIONS" parse_translations () >>= fun _ ->
  Parser.eoi >> Parser.get_state >>= Parser.return
;;

let read_theory = parse_text parse_theory ();;

(* ===== Reading a Ctrs File (not including theories) ===== *)

let inform_printer _ =
  Parser.get_state >>= fun (infixes, _, _, _) ->
  let inform name (kind, priority) =
     match kind with
      | InfixLeft | InfixNeither ->
        Printer.add_infix_symbol name priority true
      | InfixRight ->
        Printer.add_infix_symbol name priority false
      | NoInfix -> ()
  in
  Parser.return (InfixMap.iter inform infixes)
;;

let typecheck_query query =
  let trs = Trs.get_current () in
  let newquery = ( match query with
    | NormalForm t ->
      let term = Typechecker.type_derive_term t trs in
      NormalForm term
    | ConstrainedNormalForm (t, c) ->
      let term = Typechecker.type_derive_term t trs in
      let constr = Typechecker.type_derive_term c trs in
      ConstrainedNormalForm (term, constr)
    | Equivalence lst | AssistEquivalence lst ->
      let alphabet = Trs.get_alphabet trs in
      let environment = Trs.get_main_environment trs in
      let lstenv = List.map (fun x -> (x, environment)) lst in
      let newlstenv = Typechecker.type_derive_rules lstenv alphabet in
      let newlist = List.map fst newlstenv in
      ( match query with
          | Equivalence _ -> Equivalence newlist
          | _ -> AssistEquivalence newlist
      )
    | _ -> query
  ) in
  set_query newquery
;;

let parse_trs filename =
  attempt_parse "THEORY" parse_include [] >>= fun _ ->
  attempt_parse "LOGIC" (parse_single use_logic) () >>= fun _ ->
  attempt_parse "SOLVER" (parse_single use_solver) () >>= fun _ ->
  attempt_parse "SIGNATURE" parse_signature false >>= fun _ ->
  attempt_parse "CHAIN" parse_chain () >>= fun _ ->
  attempt_parse "RULES" parse_rules () >>= fun _ ->
  attempt_parse "CONTEXT-SENSITIVE" parse_cs () >>= fun _ ->
  attempt_parse "NON-STANDARD" (fun _ -> Parser.return true) false >>= fun ns ->
  (*attempt_parse "ERROR" parse_error ("", []) >>= fun (errname, errorsorts) ->*)
  attempt_parse "IRREGULAR" (fun _ -> Parser.return true) false >>= fun ln ->
  attempt_parse "QUERY" (parse_query filename) () >>= fun _ ->
  Parser.eoi >>
  let msg = Trs.test_variables (trs ()) (not ln) in
  if msg <> "" then failwith msg ;
  let msg = Trs.test_reasonable (trs ()) in
  if msg <> "" then failwith msg ;
  let msg = Trs.test_values (trs ()) in
  if msg <> "" then failwith msg ;
  let msg = (if ns then "" else Trs.test_standard (trs ())) in
  if msg <> "" then failwith msg ;
  Typechecker.type_derive (trs ()) ;
  Parser.get_state >>= fun (_, _, q, _) ->
  typecheck_query q >>= fun _ ->
  Solver.setup_core_symbols (smtsolver ()) (alphabet ()) ;
  inform_printer () >>
  Parser.get_state >>= Parser.return
;;

let read_trs contents state fname =
  let (_, _, q, s) = parse_text parse_trs fname contents state fname in
  (q, s)
;;

(* ===== Reading an itrs file ===== *)

let decomment_itrs txt =
  let parts = String.split ~d:"\n" txt in
  let ditch_comment str =
    if str = "" then ""
    else if str.[0] = '#' then ""
    else str
  in
  List.implode id "\n" (List.map ditch_comment parts)
;;

let rec parse_itrs_vars sofar =
  ( parse_identifier ident >>= fun name ->
    parse_itrs_vars (name :: sofar)
  ) <|>
  ( Parser.return sofar )
;;

let itrs_ident = (Parser.many1 (Parser.noneof " \t\n\r(),:;[]{}/%+-*><=") >>= function
  | i -> Parser.return i) <?> "identifier"
;;

(* this checks whether the next thing in line is a keyword, but does
not read it; if it is, the given value "ret" is returned *)
let parse_itrs_infix infixes =
  let check_name word =
    ( ( Parser.tempt (Parser.string (word ^ "@z")) ) >> Parser.return word )
    <|>
    ( ( Parser.tempt (Parser.string word) ) >> Parser.return word )
  in
  ( Parser.choice (List.map check_name infixes) ) <?> "keyword"
;;

let negative_term term =
  let isint = match Term.root term with
    | None -> false
    | Some f -> Function.is_integer f
  in
  if isint then (
    let k = Function.integer_to_int (List.hd (Term.funs term)) in
    let mink = Function.integer_symbol (-k) in
    Parser.return (Term.make_fun mink [])
  )
  else (
    let nulterm = Term.make_fun (Function.integer_symbol 0) [] in
    make_functional_term "-" [nulterm; term]
  )
;;

let fix_identifier_name_itrs name =
  if name = "FALSE" then "false" else
  if name = "TRUE" then "true" else
  let len = String.length name in
  if (len > 2) && (String.sub name (len - 2) 2 = "@z") then
    String.sub name 0 (len - 2)
  else name
;;

let rec parse_itrs_term e =
  parse_itrs_term_list e >>= fun (terms, symbs) ->
  build_from_infix_list terms symbs

and parse_itrs_term_list e =
  parse_basic_itrs_term e >>= fun t ->
  Parser.get_state >>= fun (infixes, _, _, _) ->
  ( Parser.tempt (Parser.lookahead (Parser.string "->")) >>= fun _ ->
    Parser.return ([t], [])
  ) <|>
  ( parse_itrs_infix (InfixMap.domain infixes) >>= fun symbol ->
    Parser.spaces >>
    parse_itrs_term_list e >>= fun (terms, symbs) ->
    Parser.return (t :: terms, symbol :: symbs)
  ) <|>
  ( Parser.return ([t], []) )

and parse_basic_itrs_term e =
  (* terms in brackets *)
  ( Parser.lex (Parser.char '(') >>= fun _ ->
    parse_itrs_term e >>= fun ret ->
    Parser.lex (Parser.char ')') >>= fun _ ->
    Parser.return ret
  ) <|>
  (* negative terms *)
  ( Parser.lex (Parser.char '-') >>= fun _ ->
    parse_basic_itrs_term e >>= fun term ->
    negative_term term
  ) <|>
  (* negated terms *)
  ( Parser.lex (Parser.char '!') >>= fun _ ->
    parse_basic_itrs_term e >>= fun term ->
    make_functional_term "not" [term]
  ) <|>
  (* terms ident or ident(...) *)
  (
    parse_identifier itrs_ident >>= fun name ->
    let name = fix_identifier_name_itrs name in
    ( Parser.lex (Parser.char '(') >>= fun _ ->
      Parser.sep_by (parse_itrs_term e)
        (Parser.lex (Parser.char ',')) >>= fun ts ->
      Parser.lex (Parser.char ')') >>= fun _ ->
      make_functional_term name ts
    ) <|>
    (
      Parser.get_state >>= fun _ ->  (* avoid evaluating too soon *)
      if Environment.mem_var_name name e then
        make_variable_term name e
      else make_functional_term name []
    )
  )
;;

let parse_itrs_rule e =
  parse_itrs_term e <?> "left-hand side" >>= fun l ->
  Parser.lex (Parser.string "->") <?> "arrow '->'" >>
  parse_itrs_term e <?> "right-hand side" >>= fun r ->
  (
    Parser.lex (Parser.string ":|:") >>= fun _ ->
    parse_itrs_term e >>= fun c ->
    Parser.return (Rule.create l r [c])
  ) <|>
  (
    Parser.return (Rule.create l r [])
  )
;;

let rec parse_itrs_rules e trs =
  ( parse_itrs_rule e >>= fun rule ->
    Trs.add rule e trs ;
    parse_itrs_rules e trs
  ) <|>
  ( Parser.return trs )
;;

let set_all_integers trs =
  let rules = Trs.get_rules trs in
  let intsort = Alphabet.integer_sort (Trs.get_alphabet trs) in
  let guarantee_int env var =
    Environment.add_sort var intsort env
  in
  let guarantee_ints env =
    let vars = Environment.vars env in
    List.iter (guarantee_int env) vars ;
  in
  List.iter (guarantee_ints <.> snd) rules
;;

let parse_itrs _ =
  functions_declared := false ;
  arrays_permitted := false ;
  register_declaration "!INTEGER" None false >>
  register_declaration "true" None false >>
  register_declaration "false" None false >>

  Parser.spaces >>= fun _ ->
  (* VAR part: determine declared variables *)
  Parser.lex (Parser.string "(VAR") >>= fun _ ->
  parse_itrs_vars [] >>= fun vars ->
  Parser.lex (Parser.char ')') >>= fun _ ->
  let e = Environment.empty (List.length vars) in
  let addvar e name =
    let _ = Environment.create_unsorted_var name e in e
  in
  let e = List.fold_left addvar e vars in
  (* RULES part: determine (unsorted) rules *)
  Parser.lex (Parser.string "(RULES") >>= fun _ ->
  parse_itrs_rules e (trs ()) >>= fun _ ->
  Parser.lex (Parser.char ')') >>= fun _ ->
  Parser.eoi >>
  let msg = Trs.test_reasonable (trs ()) in
  if msg <> "" then failwith msg ;
  let msg = Trs.test_values (trs ()) in
  if msg <> "" then failwith msg ;
  let msg = Trs.test_standard (trs ()) in
  if msg <> "" then failwith msg ;
  Typechecker.type_derive (trs ()) ;
  set_all_integers (trs ()) ;
  Solver.use_internal_solver (smtsolver ()) ;
  Solver.use_logic "QF_NIA" (smtsolver ()) ;
  Solver.setup_core_symbols (smtsolver ()) (alphabet ()) ;
  (*Cleaner.innermost_cleanup (trs ()) ;*)
  inform_printer () >>
  Parser.get_state >>= Parser.return
;;

let read_itrs contents state fname =
  let _ = parse_text parse_itrs () contents state fname in
  (Termination false, None)
;;

(* ===== Reading an smt file, to send to the internal solver ===== *)

let rec parse_variables e =
  ( Parser.lex (Parser.char ')') >>= Parser.return )
  <|>
  ( Parser.lex (Parser.char '(') >>= fun _ ->
    parse_identifier ident >>= fun varname ->
    parse_identifier ident >>= fun sortname ->
    let sort = Sort.from_string sortname in
    let _ = Environment.create_var varname sort e in
    Parser.lex (Parser.char ')') >>= fun _ ->
    parse_variables e
  )
;;

let make_smt_func name args =
  let a = alphabet () in
  try
    let (f, arguments) =
      if name = "-" then (
        let num = List.length args in
        let minus = Alphabet.find_fun "-" a in
        if not (Alphabet.mem_ari minus a) then (minus, args) else
        let ari = Alphabet.find_ari minus a in
        if num = 1 && ari = 2 then
          let nul = Function.integer_symbol 0 in
          let nulterm = Term.make_fun nul [] in
          (minus, nulterm :: args)
        else if num = 2 && ari = 1 then
          let (x, y) = (List.hd args, List.hd (List.tl args)) in
          let negy = Term.make_fun minus [y] in
          (Alphabet.find_fun "+" a, [x;negy])
        else (minus, args)
      )
      else if name = "and" then (Alphabet.get_and_symbol a, args)
      else if name = "or" then (Alphabet.get_or_symbol a, args)
      else if name = "=>" then (Alphabet.get_imply_symbol a, args)
      else if name = "not" then (Alphabet.get_not_symbol a, args)
      else if name = "false" then (Alphabet.get_bot_symbol a, args)
      else if name = "true" then (Alphabet.get_top_symbol a, args)
      else if name = "=" then (Alphabet.get_equal_symbol a, args)
      else if name = ">=" then (Alphabet.get_geq_symbol a, args)
      else if name = "<=" then (Alphabet.get_leq_symbol a, args)
      else if name = ">" then (Alphabet.get_greater_symbol a, args)
      else if name = "<" then (Alphabet.get_smaller_symbol a, args)
      else (Alphabet.find_fun name a, args)
    in
    Parser.return (Term.make_fun f arguments)
  with Not_found ->
    parser_fail ("Undeclared symbol " ^ name ^ ".")
;;

let rec parse_smt_term e =
  ( Parser.lex (Parser.char '(') >>= fun _ ->
    parse_identifier ident_with_array >>= fun name ->
    let rec parse_list sofar =
      ( Parser.lex (Parser.char ')') >>= fun _ ->
        Parser.return (List.rev sofar)
      ) <|>
      ( parse_smt_term e >>= fun term ->
        parse_list (term :: sofar)
      )
    in
    parse_list [] >>= fun lst ->
    try
      let x = Environment.find_var name e in
      if lst <> [] then parser_fail ("Variable " ^ name ^ " given arguments!")
      else Parser.return (Term.make_var x)
    with Not_found -> make_smt_func name lst
  ) <|>
  ( parse_identifier ident_with_array >>= fun name ->
    try Parser.return (Term.make_var (Environment.find_var name e))
    with Not_found -> make_smt_func name []
  )
;;

let parse_smt _ =
  Parser.many (Parser.noneof ":)") >>= fun _ ->
  let env = environment () in
  let rec read_parts logic assumptions =
    ( Parser.lex (Parser.char ':') >>= fun _ ->
      read_part logic assumptions
    ) <|>
    ( Parser.lex (Parser.char ')') >>= fun _ ->
      Parser.return (logic, assumptions)
    )
  and read_part logic assumptions =
    ( Parser.lex (Parser.string "logic") >>= fun _ ->
      parse_identifier ident_with_array >>= fun logic ->
      read_parts (Some logic) assumptions
    ) <|>
    ( Parser.lex (Parser.string "extrafuns") >>= fun _ ->
      Parser.lex (Parser.char '(') >>= fun _ ->
      parse_variables env >>= fun _ ->
      read_parts logic assumptions
    ) <|>
    ( Parser.lex (Parser.string "assumption") >>= fun _ ->
      parse_smt_term env >>= fun ass ->
      read_parts logic (ass :: assumptions)
    ) <|>
    ( Parser.lex (Parser.string "formula") >>= fun _ ->
      Parser.lex (Parser.string "true") >>= fun _ ->
      read_parts logic assumptions
    )
  in
  read_parts None [] >>= fun (logic, goals) ->
  ( match logic with
      | Some l -> Solver.use_logic l (smtsolver ())
      | None -> ()
  ) ;
  Parser.return goals
;;

let read_smt contents state fname =
  (Smt (parse_text parse_smt () contents state fname), None)
;;

(* ===== Public Functionality: read functions ===== *)

let read_alphabet txt logical =
  let _ = parse_text parse_signature logical txt start_state "input" in ()
;;

let read_rules txt =
  parse_text parse_rules () txt start_state "input"
;;

let read_term txt =
  parse_text parse_term (environment ()) txt start_state "input"
;;

let rec read_theories state = function
  | [] -> state
  | head :: tail ->
    let contents = decomment (file_contents head) head in
    let newstate = read_theory contents state head in
    read_theories newstate tail
;;

let read_ctrs_file fname =
  let theories = (List.rev <.> List.tl <.> List.rev <.> List.unique)
                 (get_theories fname) in
  let state = read_theories start_state theories in
  let contents = decomment (file_contents fname) fname in
  read_trs contents state fname
;;

let read_itrs_file fname =
  let theories = ["theories/itrs.thr"] in
  let state = read_theories start_state theories in
  let contents = decomment_itrs (file_contents fname) in
  read_itrs contents state fname
;;

let read_smt_file fname =
  let theories = ["theories/core.thr"; "theories/ints.thr";
                  "theories/arrays.thr"; "theories/strings.thr"] in
  let state = read_theories start_state theories in
  let contents = file_contents fname in
  Solver.setup_core_symbols (smtsolver ()) (alphabet ()) ;
  Solver.use_internal_solver (smtsolver ()) ;
  read_smt contents state fname
;;

let read_file fname =
  let parts = String.split ~d:"\\." fname in
  let extension = List.last parts in
  if extension = "ctrs" then read_ctrs_file fname
  else if extension = "itrs" then read_itrs_file fname
  else if extension = "smt" then read_smt_file fname
  else failwith ("Cannot read file with extension " ^ extension ^ ".")
;;

