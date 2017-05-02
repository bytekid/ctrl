(* Copyright 2014 Cynthia Kop
 * GNU Lesser General Public License
 *
 * This file is associated to CTRL, although it defines a separate
 * program, referred to ass ARRSOLVER.
 * 
 * ARRSOLVER is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * ARRSOLVER is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with ARRSOLVER. If not, see
 * <http://www.gnu.org/licenses/>.
 *)

(***************************************************************************)
(*                                  types                                  *)
(***************************************************************************)

type term = Var of string |
            ArrayVal of term list |
            (* integer or boolean functions *)
            Fun of string * term list |
            Equal of term * term |
            And of term list |
            (* from arrays to ints *)
            Size of term |
            Select of term * term |
            (* functions which MAY output arrays *)
            Allocate of term * term |
            Store of term * term * term |
            Ite of term * term * term |
            (* quantifiers *)
            Quantifier of bool * ((string * string) list) *
                          ((string * term) list) * term;;

(**
 * NOTE:
 * we assume that the generic function symbols (the ones not listed) do not
 * have arrays either as input or output sort.  Thus, terms describing an
 * array have a very specific form.  This is important, as we will use it
 * to assume arrays only occur as variables, or in a form like var1 =
 * Allocate(n,m) or var1 = Store(var2, n, m).
 *
 * In translating, we will moreover use very specific variable naming, so
 * a free array variable starts with arr, variables representing stores or
 * allocates with ?st or ?al, and non-array variables either start with x
 * (if free) or ?y (if bound).
 *)


(***************************************************************************)
(*                              list functions                             *)
(***************************************************************************)

let id x = x;;

let rec flat_map f lst =
  let rec app_map rest = function
    | [] -> flat_map f rest
    | head :: tail -> head :: app_map rest tail
  in
  match lst with
    | [] -> []
    | head :: tail -> app_map tail (f head)
;;

let mapi f lst =
  let rec mapi i = function
    | [] -> []
    | head :: tail -> f i head :: mapi (i+1) tail
  in
  mapi 0 lst
;;

let rec list_remove lst item =
  match lst with
    | [] -> []
    | head :: tail ->
      if head = item then list_remove tail item
      else head :: list_remove tail item
;;

let list_diff main removal = List.fold_left list_remove main removal;;

let generate len f =
  let rec make start =
    if start >= len then []
    else f start :: make (start + 1)
  in
  make 0
;;

let rec forall f = function
  | [] -> true
  | head :: tail -> if f head then forall f tail else false
;;

let rec count f = function
  | [] -> 0
  | head :: tail -> if f head then 1 + count f tail else count f tail
;;

(***************************************************************************)
(*                             string functions                            *)
(***************************************************************************)

let rec implode f d = function
  | [] -> ""
  | [x] -> f x
  | x :: xs -> (f x) ^ d ^ (implode f d xs)
;;

let strsrch txt subtext =
  let len = String.length subtext in
  let rec search i =
    if i + len > String.length txt then raise Not_found
    else if String.sub txt i len = subtext then i
    else search (i+1)
  in
  search 0
;;

(* returns the part of text from position index onwards *)
let restsub text pos = String.sub text pos ((String.length text) - pos);;

let rec explode separator str =
  let len = String.length separator in
  try
    let i = strsrch str separator in
    let j = i + len in
    let remainder = restsub str j in
    (String.sub str 0 i) :: explode separator remainder
  with Not_found -> [str]
;;

let rec find_matching_bracket str pos opened =
  if pos >= String.length str then
    failwith "Input file has unmatched brackets." ;
  let opened =
    if str.[pos] = '(' then opened + 1
    else if str.[pos] = ')' then opened - 1
    else opened
  in
  if opened = 0 then pos
  else if opened < 0 then failwith "bracket matching check incorrect"
  else find_matching_bracket str (pos + 1) opened
;;

(* removes spaces on either end *)
let trim str =
  let len = String.length str in
  let rec first_non_space i f =
    if i < 0 then raise Not_found
    else if i >= len then raise Not_found
    else if str.[i] = ' ' then first_non_space (f i) f
    else i
  in
  try
    let i = first_non_space 0 (fun x -> x + 1) in
    let j = first_non_space (len-1) (fun x -> x - 1) in
    let len = j - i + 1 in
    String.sub str i len
  with Not_found -> ""
;;

(* removes outer brackets and trims away spaces *)
let rec ditch_outer_brackets str =
  let str = trim str in
  if str = "" then str else
  if str.[0] <> '(' then str else
  let closer = find_matching_bracket str 0 0 in
  if closer <> ((String.length str) - 1) then str else
  let subpart = String.sub str 1 (closer - 1) in
  ditch_outer_brackets subpart
;;

(***************************************************************************)
(*                          parsing the input file                         *)
(***************************************************************************)

(* reads the entire file into a single line (newlines are replaced by nl) *)
let file_contents nl fname =
  let channel = open_in fname in
  let txt = ref "" in
  try  
    while true do ( 
      let s = input_line channel in
      txt := !txt ^ nl ^ s
    ) done ; ""
  with _ -> 
    close_in channel ;
    ditch_outer_brackets !txt
;;

(* replaces the : separator in arrays in text by , *)
let rec replace_array_separator txt =
  let rec replacethem s =
    try
      let k = strsrch s ":" in
      replacethem ((String.sub s 0 k) ^ "," ^ (restsub s (k+1)))
    with Not_found -> s
  in
  try
    let k = strsrch txt "{" in
    let j = strsrch txt "}" in
    let before = String.sub txt 0 k in
    let arr = replacethem (String.sub txt (k+1) (j-k-1)) in
    let after = restsub txt (j+1) in
    before ^ "{" ^ arr ^ "}" ^ (replace_array_separator after)
  with Not_found -> txt
;;

(* returns the text starting after :<text>, until the next colon; if
there are more than one of these (as might for instance happen with
"assumption"), this returns all of them! *)
let get_parts text name =
  let len = String.length name in
  let rec get_parts text =
    try
      let id = (strsrch text (":" ^ name ^ " ")) + len + 2 in
      let rest = String.sub text id ((String.length text) - id) in
      ( try
          let k = strsrch rest ":" in
          let before = String.sub rest 0 k in
          let after = String.sub rest k ((String.length rest) - k) in
          (ditch_outer_brackets before) :: get_parts after
        with Not_found -> [rest]
      )
    with Not_found -> []
  in
  get_parts text
;;

(* returns whether the given logic is one we can handle *)
let acceptable_logic logic = List.mem logic
  ["INTARRAY"; "QF_INTARRAY"; "QF_IDL"; "QF_LIA"; "QF-NIA"; "LIA"; "NIA"]
;;

(* returns whether the given sort is not one we are used to *)
let acceptable_type sort = List.mem sort ["Int"; "Bool"; "IntArray"];;

(* given a text which is assumed to already be trimmed, splits it in
space-separated parts; spaces inside bracketing are not counted *)
let rec split text =
  if text = "" then [] else
  if text.[0] = '(' then (
    let j = find_matching_bracket text 0 0 in
    let first = String.sub text 1 (j-1) in
    let rest = String.sub text (j+1) ((String.length text) - j - 1) in
    (ditch_outer_brackets first) :: split (trim rest)
  )
  else (
    try
      let j = strsrch text " " in
      let first = String.sub text 0 j in
      let rest = String.sub text (j+1) ((String.length text) - j - 1) in
      first :: split (trim rest)
    with Not_found -> [text]
  )
;;

(* given a sequence of bracketed pairs, splits them; if the sequence
is not bracketed, this is assumed to be a single element *)
let split_bracketed str =
  if str = "" then [str]
  else if str.[0] = '(' then split str
  else [str]
;;

(* parses a declaration "varname type" into a tuple *)
let parse_declaration str =
  match split str with
    | [a;b] ->
      if acceptable_type b then (a, b)
      else failwith ("Illegal declaration [" ^ str ^ "]: unknown sort!")
    | _ -> failwith ("illegal declaration: " ^ str)
;;

(* gives all variables standard names *)
let make_translations decs =
  let isarray (_, sort) = sort = "IntArray" in
  let (arrayvars, restvars) = List.partition isarray decs in
  let makearr kind i dec = (kind ^ (string_of_int i), dec) in
  let avars = mapi (makearr "arr") arrayvars in
  let ivars = mapi (makearr "x") restvars in
  let vars = List.append avars ivars in
  let decs = List.map (fun (name, (_, sort)) -> (name, sort)) vars in
  let trans1 = List.map (fun (name, (org, _)) -> (name, org)) vars in
  let trans2 = List.map (fun (name, (org, _)) -> (org, name)) vars in
  (decs, trans1, trans2)
;;

(* parses an assumption *)
let rec parse_term vars boundnum str =
  let handle_quantifier universal decs arg =
    let decs = ditch_outer_brackets decs in
    let arg = ditch_outer_brackets arg in
    let extravars = split_bracketed decs in
    let extravars = List.map parse_declaration extravars in
    let makebound i (name, sort) =
      let start = if sort = "IntArray" then "?u" else "?y" in
      (start ^ (string_of_int (boundnum + i)), (name, sort))
    in
    let bounds = mapi makebound extravars in
    let get_translations (newname, (oldname, _)) = (oldname, newname) in
    let transes = List.map get_translations bounds in
    let decs = List.map (fun (name, (_, sort)) -> (name, sort)) bounds in
    let boundnum = boundnum + List.length bounds in
    let parsedarg = parse_term (transes @ vars) boundnum arg in
    Quantifier (universal, decs, [], parsedarg)
  in
  let is_array str =
    if str = "" then failwith "Cannot parse the empty string." ;
    (String.get str 0 = '{') &&
    (String.get str ((String.length str) - 1) = '}')
  in
  let recurse = parse_term vars boundnum in
  if is_array str then parse_array recurse str else
  let range_req below above termmaker =
    let binder = "?y" ^ (string_of_int boundnum) in
    let boundnum = boundnum + 1 in
    let bbelow = Fun ("<", [Var binder; parse_term vars boundnum below]) in
    let babove = Fun (">", [Var binder; parse_term vars boundnum above]) in
    let notbetween = Fun ("or", [bbelow; babove]) in
    let term = Fun ("or", [notbetween; termmaker binder boundnum]) in
    Quantifier (true, [(binder, "Int")], [], term)
  in
  match split str with
    | ["forall"; decs; arg] -> handle_quantifier true decs arg
    | ["exists"; decs; arg] -> handle_quantifier false decs arg
    | "forall" :: _ | "exists" :: _ ->
      failwith ("Strange quantifier format: " ^ str)
    | "and" :: args ->
      let newargs = List.map recurse args in
      let flattened = flat_map (function | And lst -> lst | x -> [x]) newargs
      in And flattened
    | ["size";arg] -> Size (recurse arg)
    | "size" :: _ -> failwith ("Strange size occurrence: " ^ str)
    | ["allocate";n;m] -> Allocate (recurse n, recurse m)
    | "allocate" :: _ -> failwith ("Strange allocate occurence: " ^ str)
    | ["="] | ["=";_] -> Fun ("true", [])
    | "=" :: args ->
      let newargs = List.map recurse args in
      let rec makepairs = function
        | [] | [_] -> failwith "makepairs, shouldn't happen"
        | [a;b] -> [Equal (a,b)]
        | a :: b :: tail -> (Equal (a,b)) :: makepairs (b :: tail)
      in
      let pairs = makepairs newargs in
      if List.tl pairs = [] then List.hd pairs
      else And pairs
    | ["store";arr;pos;value] ->
      Store (recurse arr, recurse pos, recurse value)
    | "store" :: _ -> failwith "store must be aplied on 3 arguments!"
    | ["select";arr;pos] -> Select (recurse arr, recurse pos)
    | "select" :: _ -> failwith "select must be applied on 2 arguments!"
    | ["ite";cond;a;b] -> Ite (recurse cond, recurse a, recurse b)
    | "ite" :: _ -> failwith "ite must be applied on 3 arguments!"
    | ["correspond";arr1;arr2;b;a] ->
      let f binder boundnum =
        let arr1 = parse_term vars boundnum arr1 in
        let arr2 = parse_term vars boundnum arr2 in
        let arr1bind = Select (arr1, Var binder) in
        let arr2bind = Select (arr2, Var binder) in
        Equal (arr1bind, arr2bind)
      in
      range_req b a f
    | ["nonzero";arr;b;a] ->
      let f binder boundnum =
        let arr = parse_term vars boundnum arr in
        Fun ("distinct", [Select (arr, Var binder); Fun ("0", [])])
      in
      range_req b a f
    | [] -> Fun ("true", [])
    | head :: tail ->
      if List.mem_assoc head vars then (
        if tail = [] then Var (List.assoc head vars)
        else failwith ("Variable applied on arguments: " ^ str)
      )
      else Fun (head, List.map recurse tail)

and parse_array recurse str =
  let str = String.sub str 1 ((String.length str) - 2) in
  let parts = explode "," str in
  ArrayVal (List.map recurse parts)
;;

(* reads the given smt input file into a format we can handle; we return both
the list of variable declarations on our self-generated variable names, the
translations from these names to the corresponding names in the input file
and finally a term representing the SMT problem *)
let read_smt_file filename =
  (* get data *)
  let content = file_contents " " filename in
  let content = replace_array_separator content in
  let logics = get_parts content "logic" in
  let extrafuns = get_parts content "extrafuns" in
  let assumptions = get_parts content "assumption" in
  (* check logics *)
  if not (List.for_all acceptable_logic logics) then
    failwith "Unexpected logic!" ;
  (* get variable declarations *)
  let extravars = flat_map split_bracketed extrafuns in
  let extravars = if extravars = [""] then [] else extravars in
  let originalvars = List.map parse_declaration extravars in
  let (vardecs, trans1, trans2) = make_translations originalvars in
  (* parse assumptions *)
  let goals = List.map (parse_term trans2 0) assumptions in
  let goal = And (flat_map (function | And lst -> lst | x -> [x]) goals) in
  (vardecs, trans1, goal)
;;

(***************************************************************************)
(*                         printing the output file                        *)
(***************************************************************************)

let tostring_declarations vars =
  let tostring_declaration (varname, sort) =
    "(" ^ varname ^ " " ^ sort ^ ")"
  in
  "(" ^ (implode tostring_declaration " " vars) ^ ")"
;;

(* prints in an SMT-format, but with additional codes to represent "bound
requirements" in the Quantifier terms; this is for debugging purposes only,
in the final print these do not occur anymore *)
let rec tostring_term term =
  let rec combine name = function
    | [] -> if name = "and" then "true" else "false"
    | [single] -> single
    | [a;b] -> "(" ^ name ^ " " ^ a ^ " " ^ b ^ ")"
    | a :: b :: tail -> combine name ((combine name [a;b]) :: tail)
  in
  match term with
  | Var x -> x
  | Fun (f, []) -> f
  | Fun (f, args) -> "(" ^ f ^ " " ^ (implode tostring_term " " args) ^ ")"
  | Ite (cond, a, b) -> tostring_term (Fun ("ite", [cond;a;b]))
  | Equal (a, b) -> "(= " ^ (tostring_term a) ^ " " ^ (tostring_term b) ^ ")"
  | Select (arr, n) -> "(select " ^ (tostring_term arr) ^ " " ^
                       (tostring_term n) ^ ")"
  | Store (arr, n, m) -> "(store " ^ (tostring_term arr) ^ " " ^
                         (tostring_term n) ^ " " ^ (tostring_term m) ^ ")"
  | And args -> combine "and" (List.map tostring_term args)
  | Quantifier (universal, decs, [], arg) ->
    "(" ^ (if universal then "forall" else "exists") ^ " " ^
    (tostring_declarations decs) ^ " " ^ (tostring_term arg) ^ ")"
  | Quantifier (universal, decs, lst, arg) ->
    let printreq (x, req) = "(= " ^ x ^ " " ^ (tostring_term req) ^ ")" in
    "(" ^ (if universal then "forall" else "exists") ^ " " ^
    "{" ^ (implode printreq "&&" lst) ^ "} " ^
    (tostring_declarations decs) ^ " " ^ (tostring_term arg) ^ ")"
  | Size k -> "(size " ^ (tostring_term k) ^ ")"
  | Allocate (n, m) -> "(allocate " ^ (tostring_term n) ^ " " ^
                       (tostring_term m) ^ ")"
  | ArrayVal lst -> "{" ^ (implode tostring_term ":" lst) ^ "}"
;;

let tostring_problem vars assumptions =
  let assumpt =
    if assumptions = [] then ""
    else ":assumption " ^
      (implode tostring_term "\n:assumption " assumptions) ^ "\n" 
  in
  "(benchmark none\n" ^
  ":logic AUFNIRA\n" ^
  ":extrafuns " ^ (tostring_declarations vars) ^ "\n" ^ assumpt ^
  ":formula true\n" ^
  ")"
;;

let print vars problem =
  Printf.printf "%s\n" (tostring_problem vars problem)
;;

let write_file filename contents =
  let output = open_out filename in
  Printf.fprintf output "%s\n" contents ;
  close_out output ;
;;

(***************************************************************************)
(*                    parsing output from the SMT-solver                   *)
(***************************************************************************)

type output = IntVal of int | StrVal of string | Argument |
              Referral of string | Case of (int * output) list * output |
              Apply of string * (output list)

(* splits the given string in a part before and after the -> arrow;
   if no such arrow is present, Not_found is raised *)
let split_arrow str =
  let k = strsrch str "->" in
  let before = trim (String.sub str 0 k) in
  let len = (String.length str) - k - 2 in
  let after = trim (String.sub str (k + 2) len) in
  (before, after)
;;

(* splits the list in the part until the ending } and the part after *)
let rec get_multiline_value varname = function
  | [] -> failwith ("unterminated value for variable " ^ varname ^
                    " in SMT output file!")
  | head :: tail ->
    if head = "" then get_multiline_value varname tail
    else if head = "}" then ([], tail)
    else if String.get head ((String.length head) - 1) = '}' then (
      let head = String.sub head 0 ((String.length head) -1) in
      ([head], tail)
    )
    else (
      let (lines, rest) = get_multiline_value varname tail in
      (head :: lines, rest)
    )
;;

(* returns Argument if this string represents the argument, otherwise
throws a failure *)
let rec parse_argument str =
  let len = String.length str in
  if str = "#0" then Argument
  else if len < 6 then failwith "not an argument"
  else if (String.sub str 0 4 = ":var") &&
          (str.[len-1] == '0') then Argument
  else if (str.[0] = '(') && (str.[len-1] == ')') then
    parse_argument (String.sub str 1 (len - 2))
  else failwith "not an argument"
;;

(* int_of_string which accepts the - i format from SMT-LIB *)
let int_of_string str =
  let str = trim (ditch_outer_brackets str) in
  if (String.length str <= 2) then int_of_string str
  else if (String.get str 0 = '-') && (String.get str 1 = ' ') then (
    let remainder = trim (restsub str 2) in
    - (int_of_string remainder)
  )
  else int_of_string str
;;

(* checks whether the given string represents a referral, and parses
it if so *)
let parse_referral str =
  let len = String.length str in
  if len <= 10 then failwith "not a referral"
  else if String.sub str 0 8 = "as-array" then (
    let ending = trim (String.sub str 8 (len - 8)) in
    let elen = String.length ending in
    if elen <= 2 then failwith "not a referral"
    else if (String.get ending 0 <> '[') ||
       (String.get ending (elen - 1) <> ']') then
      failwith "not a referral"
    else Referral (trim (String.sub ending 1 (elen - 2)))
  )
  else failwith "not a referral"
;;

(* checks whether the given string represents a value *)
let parse_basic str =
  if String.contains str ' ' then failwith "not basic"
  else (
    try IntVal (int_of_string str)
    with _ -> StrVal str
  )
;;

(* tries to parse the given list into a case analysis *)
let rec parse_case varname lst =
  let parts = List.map split_arrow lst in
  let iselse (x, _) = x = "else" in
  let (elsecase, othercases) = List.partition iselse parts in
  let elseresponse = match elsecase with
    | [] -> IntVal 37
    | [(_,single)] -> parse_single_value varname single
    | _ -> failwith ("Multiple else-cases in SMT-output file for " ^ varname)
  in
  let make_case (num, result) =
    let k = 
      try int_of_string num
      with _ -> failwith ("Encountered index " ^ num ^ " in SMT-output file "
                          ^ "for variable " ^ varname ^ ".")

    in
    (k, parse_single_value varname result)
  in
  let othervals = List.map make_case othercases in
  Case (othervals, elseresponse)

(* parses the given list of strings into an "output" value, without
trying the special cases for lists of length 1 *)
and parse_list_value varname lst =
  try parse_case varname lst with Not_found ->
  let text = ditch_outer_brackets (implode id " " lst) in
  match split text with
    | [] -> failwith ("splitting " ^ text ^ " somehow gives an empty list")
    | [single] -> StrVal single
    | ["let"; def; result] -> (
        match parse_single_value varname def with
          | Apply (newname, [definition]) ->
            let ret = parse_single_value varname result in
            let rec replace = function
              | Apply (n, l) -> Apply (n, List.map replace l)
              | Case (l, o) ->
                let f (x, c) = (x, replace c) in
                Case (List.map f l, replace o)
              | StrVal k ->
                if k = newname then definition
                else StrVal k
              | x -> x
            in
            replace ret
          | _ -> failwith ("Unexpected let: " ^ text)
      )
    | ["_"; "as-array"; name] -> Referral name
    | name :: args ->
      Apply (name, List.map (parse_single_value varname) args)

(* parses the given string into an "output" value *)
and parse_single_value varname line =
  try parse_referral line with _ ->
  try parse_argument line with _ ->
  try parse_basic line with _ ->
  parse_list_value varname [line]
;;

(* parses the given list of strings into an "output" value *)
let parse_value varname lst =
  match lst with
    | [] -> failwith ("Cannot parse an empty value (in var " ^ varname ^ ".")
    | [single] -> parse_single_value varname single
    | _ -> parse_list_value varname lst
;;

(* reads the lines of an SMT-output file, and returns for each variable
assignment a tuple (variable, assignment), where the assignment has the form
(name, output) *)
let rec get_all_values = function
  | [] -> []
  | head :: tail ->
    if head = "" then get_all_values tail else
    let (before, after) =
      try split_arrow head
      with Not_found ->
        failwith ("Don't know what to do with " ^ head ^ " in " ^
                  "SMT output file!")
    in
    if after = "" then failwith ("Variable " ^ before ^ " in SMT output " ^
                                 "file is assigned an empty value!\n") ;
    let (lines, rest) =
      if String.get after 0 = '{' then (
        let remainder = String.sub after 1 ((String.length after) - 1) in
        get_multiline_value before ((trim remainder) :: tail)
      )
      else ([after], tail)
    in
    (before, parse_value before lines) :: get_all_values rest
;;

let print_pair (name, output) =
  let rec print_output = function
    | IntVal x -> string_of_int x
    | StrVal x -> "\"" ^ x ^ "\""
    | Argument -> "ARG"
    | Referral x -> "Ref (" ^ x ^ ")"
    | Case (lst, elsecase) ->
      let printcase (num, op) =
        (string_of_int num) ^ " : " ^ (print_output op)
      in
      (implode printcase " ; " lst) ^ " ; ELSE : " ^
      (print_output elsecase)
    | Apply ("if", [cond;i;e]) | Apply ("ite", [cond;i;e]) ->
      (print_output cond) ^ " ? " ^ "(" ^ (print_output i) ^
      ") : (" ^ (print_output e) ^ ")"
    | Apply (f, args) -> f ^ " @ " ^ (implode print_output " @ " args)
  in
  Printf.printf "%s : %s\n" name (print_output output)
;;

(* reads the value for the given basic (non-array) variables from the
given valuelist (obtaiend from the SMT-output file) *)
let read_basic_value valuelist (varname, sort) =
  try
    match List.assoc varname valuelist with
      | IntVal x -> (varname, string_of_int x)
      | StrVal x -> (varname, x)
      | Apply ("-",[IntVal x]) -> (varname, string_of_int (-x))
      | _ -> failwith ("Variable " ^ varname ^ " assigned to a " ^
                       "non-basic value in SMT-output file!")
  with Not_found ->
    if sort = "Int" then (varname, "0")
    else if sort = "Bool" then (varname, "false")
    else failwith ("Variable of unknown sort " ^ sort ^ ", not " ^
                   "set by SMT-solver!")
;;

(* applies the given function (which is an integer or core symbol)
on the given (string) arguments *)
let handle_underlying_function name args =
  if args = [] then name else
  let fail () = failwith ("Cannot handle pattern: (" ^ name ^ " " ^
                          (implode id " " args) ^ ")") in
  let test_bool_args _ =
    let isbool x = x = "true" || x = "false" in
    if not (forall isbool args) then fail ()
  in
  let test_int_args _ =
    let isint x = try let _ = int_of_string x in true with _ -> false in
    if not (forall isint args) then fail ()
  in
  let handle_int_function f =
    test_int_args () ;
    let rec handle_all start = function
      | [] -> string_of_int start
      | head :: tail ->
        handle_all (f start (int_of_string head)) tail
    in
    match args with
      | [] -> fail ()
      | head :: tail -> handle_all (int_of_string head) tail
  in
  let handle_int_relation f =
    test_int_args () ;
    let rec handle_all a b = function
      | [] -> f a b
      | head :: tail ->
        (f a b) && (handle_all b (int_of_string head) tail)
    in
    match args with
      | [] | [_] -> fail ()
      | a :: b :: tail ->
        string_of_bool (handle_all (int_of_string a) (int_of_string b) tail)
  in
  match (name, args) with
    | ("not", ["true"]) -> "false"
    | ("not", ["false"]) -> "true"
    | ("and", _) ->
      test_bool_args () ;
      string_of_bool (forall (fun x -> x = "true") args)
    | ("or", _) ->
      test_bool_args () ;
      string_of_bool (not (forall (fun x -> x = "false") args))
    | ("xor", args) ->
      test_bool_args () ;
      let c = count (fun x -> x = "true") args in
      string_of_bool (c mod 2 = 1)
    | ("=>", a :: rest) ->
      test_bool_args () ;
      let rec test start = function
        | [] -> a
        | head :: tail ->
          if a = "true" then test head tail else "true"
      in
      test a rest
    | ("=", []) -> "true"
    | ("=", head :: tail) ->
      string_of_bool (forall (fun x -> x = head) tail)
    | ("distinct", []) -> "true"
    | ("distinct", head :: tail) ->
      let rec all_unequal a = function
        | [] -> true
        | [b] -> a <> b
        | b :: tail ->
          (a <> b) && (all_unequal a tail) && (all_unequal b tail)
      in
      string_of_bool (all_unequal head tail)
    | ("ite", ["true";a;b]) | ("if", ["true";a;b]) -> a
    | ("ite", ["false";a;b]) | ("if", ["false";a;b]) -> b
    | ("-", [single]) ->
      ( try let k = int_of_string single in string_of_int (0 - k)
        with _ -> fail ()
      )
    | ("abs", [single]) ->
      ( try let k = int_of_string single in
            if k < 0 then string_of_int (0 - k) else single
        with _ -> fail ()
      )
    | ("-", _) -> handle_int_function (fun x y -> x - y)
    | ("+", _) -> handle_int_function (+)
    | ("*", _) -> handle_int_function ( * )
    | ("div", [_;_]) -> handle_int_function (/)
    | ("mod", [_;_]) -> handle_int_function (mod)
    | (">", _) -> handle_int_relation (>)
    | (">=", _) -> handle_int_relation (>=)
    | ("<", _) -> handle_int_relation (<)
    | ("<=", _) -> handle_int_relation (<=)
    | _ -> fail ()
;;

(* applies an output-function on the given integer *)
let rec apply_function valuelist funct index =
  match funct with
    | Referral str ->
      let other =
        try List.assoc str valuelist
        with Not_found -> failwith ("Referral " ^ str ^ " not defined!")
      in
      apply_function valuelist other index
    | IntVal i -> string_of_int i
    | StrVal s -> s
    | Argument -> string_of_int index
    | Case (lst, other) ->
      ( try apply_function valuelist (List.assoc index lst) index
        with Not_found -> apply_function valuelist other index
      )
    | Apply ("if", [cond;i;e]) ->
      let s = apply_function valuelist cond index in
      if s = "true" then apply_function valuelist i index
      else if s = "false" then apply_function valuelist e index
      else failwith "Bad condition in if-clause."
    | Apply (str, args) ->
      let recurse x = apply_function valuelist x index in
      let argsoutput = List.map recurse args in
      try
        let referred = List.assoc str valuelist in
        if List.length args <> 1 then
          failwith ("Array output applies "^ str ^" on multiple arguments.")
        else (
          let k = try int_of_string (List.hd argsoutput)
                  with _ -> failwith ("Argument of " ^ str ^
                                      " does not reduce to an integer") in
          apply_function valuelist referred k
        )
      with Not_found -> handle_underlying_function str argsoutput
;;

(* reads the value for the given array variable declaration from the
given valuelist (obtained from the SMT-output file) *)
let read_array_value valuelist varname =
  let size = varname ^ "_size" in
  let func = varname ^ "_func" in
  (* find the size *)
  let sizeresult =
    try ( match List.assoc size valuelist with
      | IntVal k -> k
      | _ -> failwith ("SMT-solver sets size variable " ^ size ^
                       " to non-integer (or non-positive integer)!")
      )
    with Not_found -> 1
  in
  (* determine the function core *)
  let rec funcresult name =
    try List.assoc name valuelist
    with Not_found -> IntVal 0
  in
  let funct = funcresult func in
  (* determine the resulting array! *)
  let base = generate sizeresult id in
  let values = List.map (apply_function valuelist funct) base in
  (varname, "{" ^ (implode id ":" values) ^ "}")
;;

let get_array_values nvars avars lst =
  let valuelist = get_all_values (List.map trim lst) in
  let normalvars = List.map (read_basic_value valuelist) nvars in
  let arrayvars = List.map (read_array_value valuelist) avars in
  normalvars @ arrayvars
;;

let read_smt_output normalvars arrayvars text =
  let parts = explode "\n" text in
  let issat x = x = "sat" || x = "unsat" in
  let (result, rest) = List.partition issat parts in
  if result = ["sat"] then
    ("sat", Some (get_array_values normalvars arrayvars rest))
  else if result = ["unsat"] then ("unsat", None)
  else ("unknown", None)
;;

(***************************************************************************)
(*                            manipulating terms                           *)
(***************************************************************************)

(* replaces the arguments of the given term by the new arguments *)
let replace_args problem args =
  let rec nth k = function
    | [] -> failwith ("replace_args called with incorrect argument "^
                      "size; problem is " ^ (tostring_term problem))
    | head :: tail ->
      if k <= 0 then head
      else nth (k-1) tail
  in
  match problem with
    | Var _ | ArrayVal _ -> problem
    | Fun (f, _) -> Fun (f, args)
    | And _ -> And args
    | Size x -> Size (nth 0 args)
    | Allocate _ -> Allocate (nth 0 args, nth 1 args)
    | Select _ -> Select (nth 0 args, nth 1 args)
    | Equal _ -> Equal (nth 0 args, nth 1 args)
    | Store _ -> Store (nth 0 args, nth 1 args, nth 2 args)
    | Ite _ -> Ite (nth 0 args, nth 1 args, nth 2 args)
    | Quantifier _ ->
      failwith "Please do not call replace_args with a quantifier"
;;

(* returns the arguments of the given term *)
let get_args = function
  | Var _ | ArrayVal _ -> []
  | And lst | Fun (_, lst) -> lst
  | Size x -> [x]
  | Select (a,b) | Equal (a,b) | Allocate (a,b) -> [a;b]
  | Store (a,b,c) | Ite (a,b,c) -> [a;b;c]
  | Quantifier _ ->
    failwith "Please do not call get_args with a quantifier"
;;

(* applies f on the arguments of the given term and returns the result *)
let apply_on_args f problem =
  match problem with
    | Quantifier (k, decs, reqs, arg) ->
      let apply_on (x, req) = (x, f req) in
      Quantifier (k, decs, List.map apply_on reqs, f arg)
    | _ -> replace_args problem (List.map f (get_args problem))
;;

(***************************************************************************)
(*                             handling arrays                             *)
(***************************************************************************)

(* splits the variables into normal variables and array variables *)
let splitvars vars =
  let arrayvar (x, sort) = sort = "IntArray" in
  let (arrays, normal) = List.partition arrayvar vars in
  (normal, List.map fst arrays)
;;

(* this pushes all Ites which return an array up in the term, so the
remaining Ites will not interfere with anything; after this, arrays can be
assumed to be allocates, stores, values or variables *)
let rec up_ite term =
  (* make sure ites are moved to the top (where necessary) in all
  children *)
  let term = apply_on_args up_ite term in
  (* move ite upwards if it's right below the top; repeat this on the
  new child, to handle cases like Size(Ite(a, Ite(b, x, y), z)) *)
  let rec up_ite_main = function
    | Size (Ite (cond, a, b)) ->
      Ite (cond, up_ite_main (Size a), up_ite_main (Size b))
    | Select (Ite (cond, a, b), c) ->
      Ite (cond, up_ite_main (Select (a, c)), up_ite_main (Select (b, c)))
    | Store (Ite (cond, a, b), c, d) ->
      Ite (cond, Store (a, c, d), Store (b, c, d))
    | _ -> term
  in
  up_ite_main term
;;

(* this removes all occurrences of Allocate, Store and values, and moves
them as requirements on fresh variables into the quantifier above them;
the return value consists of first the modified problem, second the
requirements on newly introduced variables not yet bound by a quantifier
restriction, third the new list of variable names and fourth the index for
the next array variable to be introduced, if any

Note: after this, array symbols can only occur inside the requirements, and
in the context var1 = Store (var2, n, m) or var1 = Allocate(n, m) or
var1 = ArrayVal arr; the requirements, too, have exactly this form.  This is
because in for instance Store(x, Store(y, a, b), c, d), the inner store will
be replaced by a variable. *)
let rec translate_allocstore problem reqs ds =
  (* creating new variables *)
  let rec unused base i = ( base ^ (string_of_int i), i + 1 ) in
  (* recursively apply the function *)
  let translate_list ds lst =
    let f (sofar, reqs, ds) arg =
      let (arg, reqs, ds) = translate_allocstore arg reqs ds in
      (arg :: sofar, reqs, ds)
    in
    let (newlst, reqs, ds) = List.fold_left f ([], reqs, ds) lst in
    (List.rev newlst, reqs, ds)
  in
  let handle_args problem =
    let args = get_args problem in
    let (lst, reqs, ds) = translate_list ds args in
    (replace_args problem lst, reqs, ds)
  in
  (* handling a store, allocate or value (which we replace! *)
  let rec find_variable = function
    | [] -> raise Not_found
    | (x, prob) :: tail -> if prob = problem then x else find_variable tail
  in
  let handle_store_allocate kind args builder =
    try (Var (find_variable reqs), reqs, ds) with Not_found ->
    let (storevar, ds) = unused kind ds in
    let (newargs, reqs, ds) = translate_list ds args in
    (Var storevar, (storevar, builder newargs) :: reqs, ds)
  in
  (* main part: check all possible forms *)
  match problem with
    | Quantifier (kind, decs, [], arg) ->
      let (newarg, newreqs, ds) = translate_allocstore arg [] ds in
      let newdecs = List.map (fun (x,_) -> (x, "IntArray")) newreqs in
      (Quantifier (kind, newdecs @ decs, newreqs, newarg), reqs, ds)
    | Quantifier _ -> failwith ("translate_allocstore called twice?")
    | Store (arr, n, m) ->
      let builder = function
        | [x;y;z] -> Store (x,y,z)
        | _ -> failwith "something goes wrong with translatelist: store"
      in
      handle_store_allocate "st" [arr;n;m] builder
    | Allocate (n, m) ->
      let builder = function
        | [x;y] -> Allocate (x,y)
        | _ -> failwith "something goes wrong with translatelist: allocate"
      in
      handle_store_allocate "al" [n;m] builder
    | ArrayVal arr ->
      let (storevar, ds) = unused "c" ds in
      (Var storevar, (storevar, problem) :: reqs, ds)
    | Equal (Var x, Allocate (n, m)) | Equal (Allocate (n, m), Var x) ->
      let (lst, reqs, ds) = translate_list ds [n;m] in
      (Equal (Var x, replace_args (Allocate (n,m)) lst), reqs, ds)
    | Equal (Var x, Store (a, n, m)) | Equal (Store (a, n, m), Var x) ->
      let (lst, reqs, ds) = translate_list ds [a;n;m] in
      (Equal (Var x, replace_args (Store (a,n,m)) lst), reqs, ds)
    | Equal (Var x, ArrayVal lst) | Equal (ArrayVal lst, Var x) ->
      (Equal (Var x, ArrayVal lst), reqs, ds)
    | Var _ | Fun _ | And _ | Select _ | Equal _ | Size _ | Ite _ ->
      handle_args problem
;;

(* returns the core requirements for x = ArrayVal lst *)
let valuereqs xfunc lst =
  let intfun k = Fun (string_of_int k, []) in
  let posok i x = Equal (Select (Var xfunc, intfun i), x) in
  mapi posok lst
;;

(* this function replaces all array variables by either the size variable or
the function variable, and returns the result (in which the size function
cannot occur anymore! *)
let rec ditch_sizes depth problem =
  let recurse = ditch_sizes depth in
  let recurse_dec (x, sort) =
    if sort = "IntArray" then
      [(x ^ "_func", "(Array Int Int)"); (x ^ "_size", "Int")]
    else [(x, sort)]
  in
  let recurse_req (x, prob) =
    let (xfunc, xsize) = (x ^ "_func", x ^ "_size") in
    match prob with
      | Allocate (n, m) ->
        let (n, m) = (recurse n, recurse m) in
        (*[ (xfunc, Allocate (n, m)); (xsize, n) ]*)
        [ (xfunc, Allocate (Fun ("0",[]), m)); (xsize, n) ]
      | Store (Var a, n, m) ->
        let (n, m) = (recurse n, recurse m) in
        let (afunc, asize) = (a ^ "_func", a ^ "_size") in
        [ (xfunc, Store (Var afunc, n, m)); (xsize, Var asize) ]
      | ArrayVal lst ->
        let lsize = string_of_int (List.length lst) in
        [ (xfunc, ArrayVal lst); (xsize, Fun (lsize, [])) ]
      | _ -> failwith ("Strange term in recurse_req: " ^
                       (tostring_term prob))
  in
  let is_normal_var x =
    (String.sub x 0 1 = "x") || (String.sub x 0 2 = "?y") in
  match problem with
    | Quantifier (universal, decs, reqs, arg) ->
      let newdecs = flat_map recurse_dec decs in
      let newreqs = flat_map recurse_req reqs in
      let newarg = recurse arg in
      Quantifier (universal, newdecs, newreqs, newarg)
    | Var str -> Var (if is_normal_var str then str else str ^ "_func")
    | Size (Var str) ->
      if not (is_normal_var str) then Var (str ^ "_size")
      else failwith "size of non-array variable requested!"
    | Size _ -> failwith ("uncommon size: " ^ (tostring_term problem))
    | Equal (Var x, Store (Var y, n, m)) ->
      let (xfunc, xsize, yfunc, ysize) =
        (x ^ "_func", x ^ "_size", y ^ "_func", y ^ "_size")
      in
      let (n, m) = (recurse n, recurse m) in
      And [ Equal (Var xsize, Var ysize);
            Equal (Var xfunc, Store (Var yfunc, n, m)) ]
    | Equal (Var x, Allocate (n, m)) ->
      let (xfunc, xsize) = (x ^ "_func", x ^ "_size") in
      let pos = "?i" ^ (string_of_int depth) in
      let (n, m) = (recurse n, ditch_sizes (depth+1) m) in
      And [ Equal (Var xsize, n);
            Quantifier (true, [(pos, "Int")], [],
              Equal (Select (Var xfunc, Var pos), m)) ]
    | Equal (Var x, ArrayVal lst) ->
      let (xfunc, xsize) = (x ^ "_func", x ^ "_size") in
      let funcreqs = valuereqs xfunc lst in
      let lsize = string_of_int (List.length lst) in
      let lenreq = Equal (Var xsize, Fun (lsize, [])) in
      if funcreqs = [] then lenreq
      else And (lenreq :: funcreqs)
    | Equal (Var x, Var y) ->
      if (is_normal_var x) && (is_normal_var y) then problem
      else if (is_normal_var x) || (is_normal_var y) then
        failwith "equality between array and something else!"
      else (
        let (xfunc, xsize, yfunc, ysize) =
          (x ^ "_func", x ^ "_size", y ^ "_func", y ^ "_size")
        in
        And [ Equal (Var xfunc, Var yfunc); Equal (Var xsize, Var ysize) ]
      )
    | Fun _ | And _ | Select _ | Equal _ | Ite _->
      apply_on_args recurse problem
    | Allocate _ | Store _ | ArrayVal _ ->
      failwith "Allocate / Store / ArrayVal occurring in ditch_sizes!"
;;

(* returns the constraint that the variable x is at least 0 *)
let atleast0 x = Fun (">=", [Var x; Fun ("0", [])]);;

(* removes all quantifier requirements which aren't used (for example,
if an array is only used for select, its size variable is useless), and
returns both the resulting problem, and the variables which are used *)
let rec ditch_useless_reqs problem =
  let issize name =
    ( String.length name > 5) &&
    ( restsub name ((String.length name) - 5) = "_size" )
  in
  let atleast0all arg (x,_) =
    match arg with
      | And lst -> And (atleast0 x :: lst)
      | _ -> And [atleast0 x; arg]
  in
  match problem with
    | Var x -> (problem, [x])
    | Quantifier (forall, decs, reqs, arg) ->
      let (newarg, used) = ditch_useless_reqs arg in
      let handlereq (x, req) =
        let (newreq, used) = ditch_useless_reqs req in
        ((x, newreq), used)
      in
      let reqpairs = List.map handlereq reqs in
      let newreqs = List.map fst reqpairs in
      let used = (flat_map snd reqpairs) @ used in
      let reqok (name, _) = List.mem name used in
      let okreqs = List.filter reqok newreqs in
      let okdecs = List.filter (fun (x,_) -> List.mem x used) decs in
      let used = list_diff used (List.map fst okdecs) in
      (* also add the requirement that a size is at least 0! *)
      let sizedecs = List.filter (fun (x,_) -> issize x) okdecs in
      let arg = List.fold_left atleast0all newarg sizedecs in
      ( Quantifier (forall, okdecs, okreqs, arg), used )
    | _ ->
      let args = get_args problem in
      let pairs = List.map ditch_useless_reqs args in
      let newargs = List.map fst pairs in
      let occurring = flat_map snd pairs in
      ( replace_args problem newargs, occurring )
;;

(* moves requirements out of the quantifier tag, and into the formula that is
being quantified over *)
let rec ditch_requirements depth problem =
  match problem with
    | Quantifier (universal, decs, reqs, arg) ->
      (*
      let reqvars = List.map fst reqs in
      let makedec var =
        let len = String.length var in
        let kind = String.sub var (len-4) 4 in
        if kind = "func" then (var, "(Array Int Int)")
        else (var, "Int")
      in
      let adecs = List.map makedec reqvars in
      *)
      let makeconstraints (x, req) =
        match req with
          | Allocate (_, n) ->
            (* FORALL pos: x[pos] = n] *)
            let pos = "?j" ^ (string_of_int depth) in
            let n = ditch_requirements (depth + 1) n in
            let allocarg = Equal (Select (Var x, Var pos), n) in
            [Quantifier (true, [(pos, "Int")], [], allocarg)]
          | ArrayVal lst -> valuereqs x lst
          | _ -> [Equal (Var x, req)]
      in
      let constraints = flat_map makeconstraints reqs in
      let arg = ditch_requirements depth arg in
      let newarg =
        if constraints = [] then arg
        else if universal && (List.tl constraints = []) then
          Fun ("=>", [List.hd constraints; arg])
        else if universal then Fun ("=", [And constraints; arg])
        else And (arg :: constraints)
      in
      Quantifier (universal, decs, [], newarg)
    | _ -> apply_on_args (ditch_requirements depth) problem
;;

(* flattens all conjunctions and disjunctions recursively *)
let rec flatten_junctions = function
  | Quantifier (universal, decs, reqs, arg) ->
    let arg = flatten_junctions arg in
    let flatten_req (x, req) = (x, flatten_junctions req) in
    let reqs = List.map flatten_req reqs in
    Quantifier (universal, decs, reqs, arg)
  | And lst ->
    let lst = List.map flatten_junctions lst in
    let flatten = function | And x -> x | x -> [x] in
    And (flat_map flatten lst)
  | term -> apply_on_args flatten_junctions term
;;

(* removes the topmost Exists (which was introduced to avoid extra
cases) again, and returns the argument below it, as well as the
variables it quantifies over *)
let ditch_top_exists = function
  | Quantifier (false, vars, [], arg) ->
    let split_and = function | And l -> l | x -> [x] in
    (split_and arg, vars)
  | prob -> failwith "Somehow, the problem lost its top Exists!"
;;

(***************************************************************************)
(*                            main functionality                           *)
(***************************************************************************)

let main args =
  (* read input *)
  let (vars, translation, problem) = (
    if Array.length args = 1 then
      failwith "ArraySolver failure: expected file as argument!"
    else if Array.length args >= 3 then
      failwith "ArraySolver failure: can only read one file at a time!"
    else read_smt_file args.(1)
  ) in
  (* make changes *)
  let problem = up_ite problem in
  let (normalvars, arrayvars) = splitvars vars in
  let problem = Quantifier (false, normalvars, [], problem) in
  let (problem, _, _) = translate_allocstore problem [] 0 in
  let problem = ditch_sizes 0 problem in
  let problem = fst (ditch_useless_reqs problem) in
  let problem = ditch_requirements 0 problem in
  let problem = flatten_junctions problem in
  let (problems, topvars) = ditch_top_exists problem in
  (* print the new problem as an SMT-problem *)
  let makefunc x = (x ^ "_func", "(Array Int Int)") in
  let makesize x = (x ^ "_size", "Int") in
  let funcdecs = List.map makefunc arrayvars in
  let sizedecs = List.map makesize arrayvars in
  let decs = topvars @ (funcdecs @ sizedecs) in
  let goodsize (x, _) = atleast0 x in
  let problems = (List.map goodsize sizedecs) @ problems in
  let written = tostring_problem decs problems in
  (* run a real smt-solver *)
  write_file "arraysolver.tmp" written ;
  let _ = Unix.system ("./timeout 5 ./smtsolver arraysolver.tmp > smt_output") in
  let result = file_contents "\n" "smt_output" in
  (* let _ = Unix.system ("rm smt_output arraysolver.tmp") in *)
  match read_smt_output normalvars arrayvars result with
    | ("sat", Some lst) ->
      let translate x = List.assoc x translation in
      let print_pair (x, value) = (translate x) ^ " -> " ^ value in
      Printf.printf "sat\n%s\n" (implode print_pair "\n" lst)
    | (result, _) -> Printf.printf "%s\n" result
;;

let () = main (Sys.argv);;

