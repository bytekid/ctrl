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

(*****************************************************************************)
(* types used for parsing, pre-parsing and result returning                  *)
(* types for interaction with the core are supplied where they are used      *)
(*****************************************************************************)

type renaming = (string * string) list;;
type translation = (string * (string,int) Util.either list) list;;
type possible_results = Smtresults.t = SAT | UNSAT | UNKNOWN;;

type comparison = CGeq | CEqual | CUnequal

type intexp = IValue of int |
              IVar of bool * Variable.t | 
              IPlus of intexp list |
              ITimes of intexp list |
              IDiv of intexp * intexp |
              IMod of intexp * intexp |
              ISize of arrexp |
              ISelect of arrexp * intexp |
              IIte of formula * intexp * intexp |
              IAnonymous of Function.t * string * exp list

and arrexp = AValue of int list |
             AVar of bool * Variable.t |
             AAllocate of intexp * intexp |
             AStore of arrexp * intexp * intexp |
             AIte of formula * arrexp * arrexp |
             AAnonymous of Function.t * string * exp list

and othexp = OVar of bool * Variable.t |
             OIte of formula * othexp * othexp |
             OAnonymous of Function.t * string * exp list

and formula = FTrue | FFalse |
              FVar of bool * Variable.t |
              FAnd of formula list |
              FOr of formula list |
              FXor of formula * formula |
              FEquiv of formula * formula |
              FIte of formula * formula * formula |
              FNegate of formula |
              FCompare of comparison * intexp * intexp |
              FAEqual of arrexp * arrexp |
              FOEqual of othexp * othexp * Sort.t |
              FCorrespond of arrexp * arrexp * intexp * intexp |
              FNonzero of arrexp * intexp * intexp |
              FQuantifier of bool * Variable.t * intexp *
                             intexp * formula |
              FAnonymous of Function.t * string * exp list

and exp = EBool of formula | EInt of intexp |
          EArray of arrexp | EOther of Sort.t * othexp

(*** EXCEPTION **************************************************************)

exception NoInternalProblem of string;;
  (* Although using UnknownPred and UnknownExp we can technically
  handle everything, we cannot really reason freely in the presence
  of unknowns.  Therefore, the actual solving functions are limited
  to logics over integers and arrays.  If any symbols out of the
  ordinary are used in these functions, a NoInternalProblem error will
  be thrown explaining the problem. *)

(*** FUNCTIONS ***************************************************************)

(*****************************************************************************)
(* debug information                                                         *)
(*****************************************************************************)

let tostr_var x = Variable.find_name x;;

let surround brackets arg =
  let bopen = if brackets then "( " else "" in
  let bclose = if brackets then " )" else "" in
  bopen ^ arg ^ bclose
;;

let rec tostr_iexp brackets = function
  | IValue k -> string_of_int k
  | IVar (_, x) -> tostr_var x
  | IPlus lst ->
    surround brackets (List.implode (tostr_iexp true) " + " lst)
  | ITimes lst ->
    surround brackets (List.implode (tostr_iexp true) " * " lst)
  | IDiv (a, b) ->
    surround brackets ((tostr_iexp true a) ^ " / " ^ (tostr_iexp true b))
  | IMod (a, b) ->
    surround brackets ((tostr_iexp true a) ^ " % " ^ (tostr_iexp true b))
  | ISize a -> "size(" ^ (tostr_aexp false a) ^ ")"
  | ISelect (a, i) ->
    (tostr_aexp true a) ^ "[" ^ (tostr_iexp false i) ^ "]"
  | IIte (c, a, b) ->
    surround brackets ((tostr_formula false c) ^ " ? " ^
      (tostr_iexp false a) ^ " : " ^ (tostr_iexp false b))
  | IAnonymous (_, name, lst) ->
    name ^ "(" ^ name ^ (List.implode (tostr_exp false) ", " lst) ^ ")"

and tostr_aexp brackets = function
  | AValue lst -> "{" ^ (List.implode string_of_int "," lst) ^ "}"
  | AVar (_, x) -> tostr_var x
  | AAllocate (a, b) ->
    "allocate(" ^ (tostr_iexp false a) ^ ", " ^ (tostr_iexp false b) ^ ")"
  | AStore (a, x, y) ->
    (tostr_aexp true a) ^ "<" ^ (tostr_iexp false x) ^ " := " ^
    (tostr_iexp false y) ^ ">"
  | AIte (c, a, b) ->
    surround brackets ((tostr_formula false c) ^ " ? " ^
      (tostr_aexp false a) ^ " : " ^ (tostr_aexp false b))
  | AAnonymous (_, name, lst) ->
    name ^ "(" ^ (List.implode (tostr_exp false) ", " lst) ^ ")"

and tostr_oexp brackets = function
  | OVar (_, x) -> tostr_var x
  | OIte (c, a, b) ->
    surround brackets ((tostr_formula false c) ^ " ? " ^
      (tostr_oexp false a) ^ " : " ^ (tostr_oexp false b))
  | OAnonymous (_, name, lst) ->
    name ^ "(" ^ (List.implode (tostr_exp false) ", " lst) ^ ")"

and tostr_formula brackets = function
  | FTrue -> "true"
  | FFalse -> "false"
  | FVar (_, x) -> tostr_var x
  | FAnd lst ->
    surround brackets (List.implode (tostr_formula true) " /\\ " lst)
  | FOr lst ->
    surround brackets (List.implode (tostr_formula true) " \\/ " lst)
  | FXor (a, b) ->
    surround brackets ((tostr_formula true a) ^ " xor " ^
                       (tostr_formula true b))
  | FEquiv (a, b) ->
    surround brackets ((tostr_formula true a) ^ " <-> " ^
                       (tostr_formula true b))
  | FIte (a, b, c) ->
    surround brackets ((tostr_formula true a) ^ " ? " ^
                       (tostr_formula true a) ^ " : " ^
                       (tostr_formula true a))
  | FNegate a -> "not " ^ (tostr_formula true a)
  | FCompare (comparison, a, b) ->
    let rel = match comparison with
      | CGeq -> " >= "
      | CEqual -> " = "
      | CUnequal -> " != "
    in
    surround brackets ((tostr_iexp false a) ^ rel ^ (tostr_iexp false b))
  | FAEqual (a, b) ->
    surround brackets ((tostr_aexp false a) ^ " = " ^ (tostr_aexp false b))
  | FOEqual (a, b, _) ->
    surround brackets ((tostr_oexp false a) ^ " = " ^ (tostr_oexp false b))
  | FCorrespond (a, b, x, y) ->
    "correspond(" ^ (tostr_aexp false a) ^ ", " ^
                    (tostr_aexp false b) ^ ", " ^
                    (tostr_iexp false x) ^ ", " ^
                    (tostr_iexp false y) ^ ")"
  | FNonzero (a, x, y) ->
    "nonzero(" ^ (tostr_aexp false a) ^ ", " ^
                 (tostr_iexp false x) ^ ", " ^
                 (tostr_iexp false y) ^ ")"
  | FQuantifier (universal, x, lower, upper, form) ->
    let varname = tostr_var x in
    let quant = if universal then "ALL" else "EX" in
    quant ^ " " ^ varname ^ " in {" ^ (tostr_iexp true lower) ^
      "..." ^ (tostr_iexp true upper) ^ "} [" ^
      (tostr_formula false form) ^ "]"
  | FAnonymous (_, name, lst) ->
    name ^ "(" ^ (List.implode (tostr_exp false) ", " lst) ^ ")"

and tostr_exp brackets = function
  | EBool form -> tostr_formula brackets form
  | EInt iexp -> tostr_iexp brackets iexp
  | EArray aexp -> tostr_aexp brackets aexp
  | EOther (_, oexp) -> tostr_oexp brackets oexp

(*****************************************************************************)
(* parsing terms into the local shapes of formulas, intexps and so on        *)
(*****************************************************************************)

let parsefail msg = raise (NoInternalProblem msg)

let is_boolsort a sort = sort = Alphabet.boolsort;;

let is_intsort a sort =
  try sort = Alphabet.integer_sort a
  with Not_found -> false
;;

let is_arraysort a sort =
  try sort = Alphabet.array_sort (Alphabet.integer_sort a) a
  with Not_found -> false
;;

let rec parse_iexp tr a e isparam = function
  | Term.Var x -> IVar (not (isparam x), x)
  | Term.Forall _ | Term.Exists _ ->
    parsefail "Quantification with integer sort!"
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    (* get basic data *)
    let fname = Function.find_name f in
    let name = (
      try List.assoc fname tr
      with Not_found -> fname
    ) in
    let name = String.lowercase_ascii name in
    (* recursion data *)
    let pargs = List.map (parse_exp tr a e isparam) args in
    let all_exps kind maker =
      let make_iexp = function
        | EInt e -> e
        | _ -> parsefail (kind ^ " with unexpected input sorts!")
      in
      maker (List.map make_iexp pargs)
    in
    (* parse addition *)
    if name = "+" then all_exps "Addition" (fun lst -> IPlus lst)
    (* parse multiplication *)
    else if name = "*" then all_exps "Multiplication" (fun lst -> ITimes lst)
    (* parse absolute value - we just turn this into an Ite *)
    else if name = "abs" then (
      match pargs with
        | [EInt arg] ->
          IIte (FCompare (CGeq, arg, IValue 0),
                arg,
                ITimes [IValue (-1); arg])
        | _ -> parsefail ("Encountered abs with " ^
            (string_of_int (List.length args)) ^
            " arguments (expected 1, which must be an integer)")
    )
    (* parse binary operators *)
    else if name = "-" || name = "div" || name = "mod" then
      match pargs with
        | [EInt first;EInt second] ->
          if name = "mod" || name = "%" then IMod (first, second)
          else if name = "/" || name = "div" then IDiv (first,second)
          else IPlus [first; ITimes [IValue (-1); second]]
        | _ -> parsefail ("Encountered " ^ name ^ " with " ^
            (string_of_int (List.length args)) ^ " arguments " ^
            "(expected 2, which must be integers)")
    (* parse if-then-else *)
    else if name = "ite" then (
      match pargs with
        | [EBool check;EInt ifval;EInt elseval] ->
          IIte (check, ifval, elseval)
        | _ -> parsefail ("Occurrence of " ^ name ^ " with " ^
            (string_of_int (List.length args)) ^ " arguments, 3 " ^
            "expected, which should be Bool, Int, Int.")
    )
    (* parse values *)
    else if Function.is_integer f then
      IValue (Function.integer_to_int f)
    (* parse anything else as anonymous functions! *)
    else IAnonymous (f, fname, pargs)

and parse_aexp tr a e isparam = function
  | Term.Var x -> AVar (not (isparam x), x)
  | Term.Forall _ | Term.Exists _ ->
    parsefail "Quantification with array sort!"
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    (* get basic data *)
    let fname = Function.find_name f in
    let name = (
      try List.assoc fname tr
      with Not_found -> fname
    ) in
    let name = String.lowercase_ascii name in
    (* recursion data *)
    let pargs = List.map (parse_exp tr a e isparam) args in
    (* parse values *)
    if Function.is_array f then (
      let arr = Function.array_to_array f in
      let elems =
        try List.map Function.integer_to_int (Array.to_list arr)
        with _ -> parsefail "Array with non-integer elements"
      in
      AValue elems
    )
    (* parse allocations *)
    else if name = "allocate" then (
      match pargs with
        | [EInt n; EInt m] -> AAllocate (n, m)
        | _ -> parsefail ("Encountered " ^ name ^ " with erroneous " ^
                          "arguments; should be two integers!")
    )
    (* parse stores *)
    else if name = "store" then (
      match pargs with
        | [EArray a; EInt n; EInt m] -> AStore (a, n, m)
        | _ -> parsefail ("Encountered " ^ name ^ " with erroneous " ^
                          "arguments; should be IntArray, Int, Int!")
    )
    (* parse if-then-else *)
    else if name = "ite" then (
      match pargs with
        | [EBool check;EArray ifval;EArray elseval] ->
          AIte (check, ifval, elseval)
        | _ -> parsefail ("Occurrence of " ^ name ^ " with " ^
            (string_of_int (List.length args)) ^ " arguments, 3 " ^
            "expected, which should be Bool, IntArray, IntArray.")
    )
    (* parse anything else as anonymous functions! *)
    else AAnonymous (f, fname, pargs)

and parse_oexp tr a e isparam = function
  | Term.Var x -> OVar (not (isparam x), x)
  | Term.Forall _ | Term.Exists _ ->
    parsefail "Quantification with unusual sort!"
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    let fname = Function.find_name f in
    let pargs = List.map (parse_exp tr a e isparam) args in
    if fname = "ite" then (
      match pargs with
        | [EBool check;EOther (_,ifval);EOther (_,elseval)] ->
          OIte (check, ifval, elseval)
        | _ -> parsefail ("Occurrence of " ^ fname ^ " with " ^
            (string_of_int (List.length args)) ^ " arguments, 3 " ^
            "expected, which should be Bool, <other>, <other>.")
    )
    else OAnonymous (f, fname, pargs)

and parse_formula tr a e isparam = function
  | Term.Var x -> FVar (not (isparam x), x)
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
    (* get basic data *)
    let fname = Function.find_name f in
    let name = (
      try List.assoc fname tr
      with Not_found -> fname
    ) in
    let name = String.lowercase_ascii name in
    (* recursion data *)
    let pargs = List.map (parse_exp tr a e isparam) args in
    let all_bools kind maker =
      let make_formula = function
        | EBool e -> e
        | _ -> parsefail (kind ^ " with unexpected input sorts!")
      in
      maker (List.map make_formula pargs)
    in
    (* parse truth and falsehood *)
    if name = "true" then FTrue
    else if name = "false" then FFalse
    (* parse conjunction and disjunction *)
    else if name = "and" then all_bools "Conjunction" (fun lst -> FAnd lst)
    else if name = "or" then all_bools "Disjunction" (fun lst -> FOr lst)
    (* parse negation *)
    else if name = "not" then (
      match pargs with
        | [EBool arg] -> FNegate arg
        | _ -> parsefail "Not occurrence with unexpected input sorts or number"
    )
    (* parse all combination operators with two boolean arguments *)
    else if name = "xor" || name = "=>" then (
      match pargs with
        | [EBool u; EBool v] ->
          if name = "and" || name = "/\\" then FAnd [u;v]
          else if name = "or" || name = "\\/" then FOr [u;v]
          else if name = "xor" || name = "^" then FXor (u,v)
          else (* if name = "=>" || name = "implies" then *) FOr [FNegate u;v]
        | _ -> parsefail ("Symbol " ^ name ^ " occurring with " ^
            (string_of_int (List.length args)) ^ " arguments! " ^
            "(2 boolean arguments expected)")
    )
    (* parse integer comparison *)
    else if name = "<=" || name = ">=" || name = "<" || name = ">" then (
      match pargs with
        | [EInt u; EInt v] ->
          if name = "<=" then FCompare (CGeq, v, u)
          else if name = ">=" then FCompare (CGeq, u, v)
          else if name = "<" then FCompare (CGeq, v, IPlus [u; IValue 1])
          else (* if name = ">" then *) FCompare (CGeq, u, IPlus [v; IValue 1])
        | _ -> parsefail ("Symbol " ^ name ^ " occurring with " ^
            (string_of_int (List.length args)) ^ " arguments! " ^
            "(2 integer arguments expected)")
    )
    (* parse equality / equivalence *)
    else if name = "=" then (
      let rec build_equality builder start = function
        | [] -> FTrue
        | [single] -> builder single start
        | first :: second :: rest ->
          FAnd [(builder first second);
                (build_equality builder start (second :: rest))]
      in
      let fail () = parsefail "Encountered = with terms of different sorts." in
      match pargs with
        | (EInt a) :: tail ->
          let builder x y =
            match (x, y) with
              | (EInt u, EInt v) -> FCompare (CEqual, u, v)
              | _ -> fail ()
          in
          build_equality builder (EInt a) tail
        | (EBool a) :: tail ->
          let builder x y =
            match (x, y) with
              | (EBool u, EBool v) -> FEquiv (u, v)
              | _ -> fail ()
          in
          build_equality builder (EBool a) tail
        | (EArray a) :: tail ->
          let builder x y =
            match (x, y) with
              | (EArray u, EArray v) -> FAEqual (u, v)
              | _ -> fail ()
          in
          build_equality builder (EArray a) tail
        | (EOther (sort,a)) :: tail ->
          let builder x y =
            match (x, y) with
              | (EOther (_,u), EOther (_,v)) -> FOEqual (u, v, sort)
              | _ -> fail ()
          in
          build_equality builder (EOther (sort,a)) tail
        | [] -> FTrue
    )
    (* parse inequality *)
    else if name = "distinct" then (
      let unequal = function
        | (EInt x, EInt y) -> FCompare (CUnequal, x, y)
        | (EBool x, EBool y) -> FXor (x, y)
        | (EArray x, EArray y) -> FNegate (FAEqual (x, y))
        | (EOther (sort,x), EOther (_,y)) -> FNegate (FOEqual (x, y, sort))
        | _ -> failwith "Occurrence of distinct with different input sorts."
      in
      let unequal_reqs_from num = List.map (fun x -> unequal (num, x)) in
      let rec all_unequal_reqs = function
        | [] | [_] -> []
        | [x;y] -> [unequal (x, y)]
        | head :: tail -> (unequal_reqs_from head tail) @
                          (all_unequal_reqs tail)
      in
      let allreqs = all_unequal_reqs pargs in
      match allreqs with
        | [] -> FTrue
        | [single] -> single
        | _ -> FAnd allreqs
    )
    (* parse if-then-else *)
    else if name = "ite" then (
      match pargs with
        | [EBool check; EBool ifval; EBool elseval] ->
          FIte (check, ifval, elseval)
        | _ -> parsefail ("Occurrence of boolean-typed ite whose " ^
                          "arguments are not Bool-Bool-Bool.")
    )
    (* parse anything else as anonymous predicates! *)
    else FAnonymous (f, fname, pargs)
  | Term.Forall (x, form) -> parse_quantifier a e tr isparam x form true
  | Term.Exists (x, form) -> parse_quantifier a e tr isparam x form false

and parse_quantifier a e tr isparam x form universal =
  let range =
    if universal then Smtquantifiers.universal_range
    else Smtquantifiers.existential_range
  in
  let ((lower, lstrict), (upper, ustrict), form) =
    try range x a form
    with Smtquantifiers.UnboundedQuantification _ ->
      parsefail ("Encountered quantifier without obvious bounds")
  in
  let newisparam y = if y = x then not universal else isparam x in
  let pargs = List.map (parse_exp tr a e newisparam) [lower;upper;form] in
  match pargs with
    | [EInt l; EInt u; EBool f] ->
      let l = if lstrict then IPlus [l; IValue 1] else l in
      let u = if ustrict then IPlus [u; IValue (-1)] else u in
      FQuantifier (universal, x, l, u, f)
    | _ -> parsefail ("Encountered quantifiers whose parameters " ^
                      "do not have the right form.")

and parse_exp tr a e isparam term =
  let sort = Term.get_sort a e term in
  if is_boolsort a sort then EBool (parse_formula tr a e isparam term)
  else if is_intsort a sort then EInt (parse_iexp tr a e isparam term)
  else if is_arraysort a sort then EArray (parse_aexp tr a e isparam term)
  else EOther (sort, parse_oexp tr a e isparam term)
;;

(*****************************************************************************)
(* returning parsed terms back to the usual shape!                           *)
(*****************************************************************************)

(* returns a symbol which has one of the names in the given list, and a sort
   declaration satisfiying nsortok or ssortok (depending whether it's a normal
   or special sort declaration); if no such symbol is present, a warning is
   given which involves [name], explains of the function of the symbol *)
let rec get_named_symbol alf errmess renamings nsortok ssortok = function
  | [] -> failwith errmess
  | head :: tail ->
    let trs = List.filter (fun (_, x) -> x = head) renamings in
    let headnames =
      if trs = [] then [head]
      else List.map fst trs
    in
    let findfun name  =
      try
        let f = Alphabet.find_fun name alf in
        match Alphabet.find_sortdec f alf with
          | Left sd -> if nsortok sd then [f] else []
          | Right spd -> if ssortok spd then [f] else []
      with Not_found -> []
    in
    let funs = List.flat_map findfun headnames in
    match funs with
      | hd :: _ -> hd
      | _ -> get_named_symbol alf errmess renamings nsortok ssortok tail
;;

(* check whether the given sort declaration has the form:
   a * ... * a => a, where is_kind a holds *)
let pure_sortdec is_kind sd =
  let outp = Sortdeclaration.output_sort sd in
  let inps = Sortdeclaration.input_sorts sd in
  List.for_all is_kind (outp :: inps)
;;

(* check whether the given sort declaration can always be instantiated
   to the form: a * ... * a => a, where is_kind a holds *)
let pure_special_sortdec is_kind spd =
  let outp = Specialdeclaration.output_sort spd in
  let inps = Specialdeclaration.input_sorts spd in
  let mightbe_kind polsort =
    (Specialdeclaration.is_polymorphic polsort) ||
    (is_kind (Specialdeclaration.pol_to_sort polsort))
  in
  List.for_all mightbe_kind (outp :: inps)
;;

(* given a list of terms, creates f(l1, f(l2,... f(l{n-1},ln),...));
   if f takes an arbitrary number of arguments, just f(lst) is made,
   and if lst is empty, default () is returned; if lst has only one
   argument, that argument is returned *)
let unflatten f default a e lst =
  let rec unflatten = function
    | [] -> default ()
    | [single] -> single
    | head :: tail ->
      Term.make_function a e f [head; unflatten tail]
  in
  match Alphabet.find_sortdec f a with
    | Left _ -> unflatten lst
    | Right spd ->
      if Specialdeclaration.known_arity spd then unflatten lst
      else Term.make_function a e f lst
;;

(* helping function for unparse_exp *)
let unparse_fail name =
  ("Using internal solver fails: constructed " ^ name ^ ", which "
    ^ "cannot be reconstructed as a function symbol!")
;;

(* helping function for unparse_exp *)
let sortchecks a inpchecks outcheck sd =
  (outcheck a (Sortdeclaration.output_sort sd)) &&
  (Sortdeclaration.arity sd = List.length inpchecks) &&
  List.for_all (fun (g, s) -> g a s)
    (List.zip inpchecks (Sortdeclaration.input_sorts sd))
;;

let rec unparse_exp a e tr = function
  | EInt i   -> unparse_iexp a e tr i
  | EBool b  -> unparse_bexp a e tr b
  | EArray r -> unparse_aexp a e tr r
  | EOther (sort, o) -> unparse_oexp a e tr sort o

and unparse_iexp a e tr expr =
  let integer_symbol description names def args =
    let isint = is_intsort a in
    let f = get_named_symbol a (unparse_fail description) tr
            (pure_sortdec isint) (pure_special_sortdec isint) names in
    let default () = unparse_iexp a e tr (IValue def) in
    let newargs = List.map (unparse_iexp a e tr) args in
    unflatten f default a e newargs
  in
  let sortcheck inps = sortchecks a inps is_intsort in
  match expr with
    | IValue k ->
      Term.make_function a e (Function.integer_symbol k) []
    | IVar (_, x) -> Term.make_var x
    | IPlus lst ->
      integer_symbol "addition" ["+";"plus";"add"] 0 lst
    | ITimes lst ->
      integer_symbol "multiplication" ["*";"times";"mul"] 1 lst
    | IDiv (a, b) ->
      integer_symbol "division" ["div";"/"] 0 [a;b]
    | IMod (a, b) ->
      integer_symbol "modulo" ["mod";"%"] 0 [a;b]
    | IIte (phi, x, y) ->
      let nsortok = sortcheck [is_boolsort; is_intsort; is_intsort] in
      let f = get_named_symbol a (unparse_fail "if-then-else") tr
              nsortok (const false) ["ite"] in
      let newphi = unparse_bexp a e tr phi in
      let newx = unparse_iexp a e tr x in
      let newy = unparse_iexp a e tr y in
      Term.make_function a e f [newphi; newx; newy]
    | ISize aexp ->
      let nsortok = sortcheck [is_arraysort] in
      let f = get_named_symbol a (unparse_fail "size") tr
              nsortok (const false) ["size"; "length"; "len"] in
      Term.make_function a e f [unparse_aexp a e tr aexp]
    | ISelect (arr, i) ->
      let nsortok = sortcheck [is_arraysort; is_intsort] in
      let f = get_named_symbol a (unparse_fail "select") tr
              nsortok (const false) ["select"; "get"; "query"; "elem"] in
      Term.make_function a e f [unparse_aexp a e tr arr;
                                unparse_iexp a e tr i]
    | IAnonymous (f, _, lst) ->
      let args = List.map (unparse_exp a e tr) lst in
      Term.make_function a e f args

and unparse_bexp a e tr expr =
  let boolean_symbol description names def args =
    let isbool = is_boolsort a in
    let f = get_named_symbol a (unparse_fail description) tr
            (pure_sortdec isbool) (pure_special_sortdec isbool) names in
    let default () = unparse_bexp a e tr def in
    let newargs = List.map (unparse_bexp a e tr) args in
    unflatten f default a e newargs
  in
  let sortcheck inps = sortchecks a inps is_boolsort in
  let relsortcheck = sortcheck [is_intsort; is_intsort] in
  let make_quantifier_var description =
    let intsort =
      try Alphabet.integer_sort a
      with Not_found -> failwith (unparse_fail description)
    in
    let fn = Alphabet.fun_names a in
    Environment.create_sorted_var intsort fn e
  in
  match expr with
    | FTrue ->
      let f =
        try Alphabet.get_top_symbol a
        with Not_found -> 
          get_named_symbol a (unparse_fail "truth") tr
            (sortcheck []) (const false) ["true"; "top"; "truth"]
      in
      Term.make_function a e f []
    | FFalse ->
      let f =
        try Alphabet.get_top_symbol a
        with Not_found -> 
          get_named_symbol a (unparse_fail "falsehood") tr
            (sortcheck []) (const false)
            ["false"; "bottom"; "bot"; "falsehood"]
      in
      Term.make_function a e f []
    | FVar (_, x) -> Term.make_var x
    | FAnd lst -> 
      boolean_symbol "conjunction" ["and";"/\\"] FTrue lst
    | FOr lst -> 
      boolean_symbol "disjunction" ["or";"\\/"] FFalse lst
    | FXor (x, y) ->
      boolean_symbol "xor" ["xor"; "^"] FFalse [x; y]
    | FEquiv (x, y) ->
      boolean_symbol "equivalence" ["<->"; "iff"] FTrue [x;y]
    | FIte (x, y, z) ->
      boolean_symbol "if-then-else" ["ite"] FTrue [x;y;z]
    | FNegate x ->
      boolean_symbol "negation" ["not"; "neg"; "-"] FFalse [x]
    | FCompare (CGeq, x, y) ->
      let (symb, swap, add) =
        try (Alphabet.get_geq_symbol a, false, false) with Not_found ->
        try (Alphabet.get_leq_symbol a, true, false) with Not_found ->
        try (Alphabet.get_greater_symbol a, false, true) with Not_found ->
        try (Alphabet.get_smaller_symbol a, true, true) with Not_found ->
        try (get_named_symbol a "geq" tr relsortcheck (const false)
             [">="; "geq"], false, false) with _ ->
        try (get_named_symbol a "leq" tr relsortcheck (const false)
             ["<="; "leq"], true, false) with _ ->
        try (get_named_symbol a "greater" tr relsortcheck (const false)
             [">"; "greater"], false, true) with _ ->
        try (get_named_symbol a "smaller" tr relsortcheck (const false)
             ["<"; "smaller"], true, true) with _ ->
        failwith (unparse_fail "integer comparison")
      in
      let successor = function
        | IValue k -> IValue (k + 1)
        | IPlus lst ->
          let rec addoneto = function
            | [] -> [IValue 1]
            | (IValue (-1)) :: rest -> rest
            | (IValue k) :: rest -> (IValue (k + 1)) :: rest
            | hd :: tl -> hd :: addoneto tl
          in
          IPlus (addoneto lst)
        | x -> IPlus [IValue 1; x]
      in
      let x = if add then successor x else x in
      let (u, v) = if swap then (y, x) else (x, y) in
      Term.make_function a e symb [unparse_iexp a e tr u; unparse_iexp a e tr v]
    | FCompare (CEqual, x, y) ->
      let u = unparse_iexp a e tr x in
      let v = unparse_iexp a e tr y in
      let f = get_named_symbol a "integer equality" tr relsortcheck
              (const false) ["="; "equal"] in
      Term.make_function a e f [u; v]
    | FCompare (CUnequal, x, y) ->
      let u = unparse_iexp a e tr x in
      let v = unparse_iexp a e tr y in
      ( try
          let f = get_named_symbol a "integer inequality" tr relsortcheck
                  (const false) ["distinct"; "#"; "!="; "<>"] in
          Term.make_function a e f [u; v]
        with _ ->
          let f = get_named_symbol a "integer equality" tr relsortcheck
                  (const false) ["="; "equal"] in
          let negation = get_named_symbol a "negation" tr relsortcheck
                  (const false) ["not"; "neg"; "-"] in
          Term.make_function a e negation [Term.make_function a e f [u; v]]
      )
    | FAEqual (arr1, arr2) ->
      let f = get_named_symbol a "array equality" tr
              (sortcheck [is_arraysort; is_arraysort]) (const false)
              ["="; "equal"] in
      Term.make_function a e f [unparse_aexp a e tr arr1;
                                unparse_aexp a e tr arr2]
    | FOEqual (o1, o2, sort) ->
      let goodsort _ s = (sort = s) in
      let f = get_named_symbol a ((Sort.to_string sort) ^ "equality") tr
              (sortcheck [goodsort; goodsort]) (const false)
              ["="; "equal"] in
      Term.make_function a e f [unparse_oexp a e tr sort o1;
                                unparse_oexp a e tr sort o2]
    | FCorrespond (a1, a2, i, j) ->
      let chk = sortcheck [is_arraysort; is_arraysort; is_intsort;
                           is_intsort] in
      ( try
          let f = get_named_symbol a "array correspondence" tr chk
                  (const false) ["correspond"; "corresponds"] in
          let newa1 = unparse_aexp a e tr a1 in
          let newa2 = unparse_aexp a e tr a2 in
          let newi = unparse_iexp a e tr i in
          let newj = unparse_iexp a e tr j in
          Term.make_function a e f [newa1; newa2; newi; newj]
        with _ ->
          let x = make_quantifier_var "array correspondence" in
          let v = IVar (true, x) in
          let comp = FCompare (CEqual, ISelect (a1, v), ISelect (a2, v)) in
          unparse_bexp a e tr (FQuantifier (true, x, i, j, comp))
      )
    | FNonzero (arr, i, j) ->
      let chk = sortcheck [is_arraysort; is_intsort; is_intsort] in
      ( try
          let f = get_named_symbol a "nonzero" tr chk (const false)
                  ["nonzero"] in
          let newa = unparse_aexp a e tr arr in
          let newi = unparse_iexp a e tr i in
          let newj = unparse_iexp a e tr j in
          Term.make_function a e f [newa; newi; newj]
        with _ ->
          let x = make_quantifier_var "array correspondence" in
          let v = IVar (true, x) in
          let comp = FCompare (CEqual, ISelect (arr, v), IValue 0) in
          unparse_bexp a e tr (FQuantifier (true, x, i, j, comp))
      )
    | FQuantifier (univ, x, n, m, phi) ->
      let i = unparse_iexp a e tr n in
      let j = unparse_iexp a e tr m in
      let p = unparse_bexp a e tr phi in
      if univ then
        Smtquantifiers.universal_quantification x i false j false p a
      else
        Smtquantifiers.existential_quantification x i false j false p a
    | FAnonymous (f, _, lst) ->
      let args = List.map (unparse_exp a e tr) lst in
      Term.make_function a e f args

and unparse_aexp a e tr expr =
  let sortcheck inps = sortchecks a inps is_arraysort in
  match expr with
    | AValue lst ->
      let lst = (List.map Function.integer_symbol lst) in
      let value = Function.array_symbol (Array.of_list lst) in
      Term.make_function a e value []
    | AVar (_, x) -> Term.make_var x
    | AAllocate (i, j) ->
      let f = get_named_symbol a (unparse_fail "allocate") tr
              (sortcheck [is_intsort; is_intsort]) (const false)
              ["allocate"; "alloc"] in
      Term.make_function a e f [unparse_iexp a e tr i; unparse_iexp a e tr j]
    | AStore (arr, i, j) ->
      let f = get_named_symbol a (unparse_fail "store") tr
              (sortcheck [is_arraysort; is_intsort; is_intsort])
              (const false) ["store"; "put"; "set"; "update"] in
      Term.make_function a e f [unparse_iexp a e tr i; unparse_iexp a e tr j]
    | AIte (phi, x, y) ->
      let nsortok = sortcheck [is_boolsort; is_arraysort; is_arraysort] in
      let f = get_named_symbol a (unparse_fail "if-then-else") tr
              nsortok (const false) ["ite"] in
      let newphi = unparse_bexp a e tr phi in
      let newx = unparse_aexp a e tr x in
      let newy = unparse_aexp a e tr y in
      Term.make_function a e f [newphi; newx; newy]
    | AAnonymous (f, _, lst) ->
      let args = List.map (unparse_exp a e tr) lst in
      Term.make_function a e f args

and unparse_oexp a e tr sort = function
  | OVar (_, x) -> Term.make_var x
  | OIte (phi, x, y) ->
    let goodsort a s = sort = s in
    let nsortok = sortchecks a [is_boolsort; goodsort; goodsort] goodsort in
    let f = get_named_symbol a (unparse_fail "if-then-else") tr
            nsortok (const false) ["ite"] in
    let newphi = unparse_bexp a e tr phi in
    let newx = unparse_oexp a e tr sort x in
    let newy = unparse_oexp a e tr sort y in
    Term.make_function a e f [newphi; newx; newy]
  | OAnonymous (f, _, lst) ->
    let args = List.map (unparse_exp a e tr) lst in
    Term.make_function a e f args
;;

(*****************************************************************************)
(* miscellaneous functions                                                   *)
(*****************************************************************************)

(* a list sorting function for mostly ordered lists *)
let rec move_sort compare lst =
  let rec insert x = function
    | [] -> [x]
    | y :: tail ->
      if compare x y > 0 then y :: insert x tail
      else x :: y :: tail
  in
  let rec sorted = function
    | [] -> []
    | x :: tail -> insert x (sorted tail)
  in
  sorted lst
;;

(* applies fe/fb/fi/fa/fo on the direct arguments of the given expression *)
let sub_apply_exp fe fb fi fa fo = function
  | EBool x -> EBool (fb x)
  | EInt x -> EInt (fi x)
  | EArray x -> EArray (fa x)
  | EOther (sort, x) -> EOther (sort, fo x)
;;

(* applies fe/fb/fi/fa/fo on the direct arguments of the given expression *)
let sub_apply_bool fe fb fi fa fo = function
  | FTrue -> FTrue
  | FFalse -> FFalse
  | FVar (univ, x) -> FVar (univ, x)
  | FAnd lst -> FAnd (List.map fb lst)
  | FOr lst -> FOr (List.map fb lst)
  | FXor (a, b) -> FXor (fb a, fb b)
  | FEquiv (a, b) -> FEquiv (fb a, fb b)
  | FIte (a, b, c) -> FIte (fb a, fb b, fb c)
  | FNegate a -> FNegate (fb a)
  | FCompare (cmp, i, j) -> FCompare (cmp, fi i, fi j)
  | FAEqual (a, b) -> FAEqual (fa a, fa b)
  | FOEqual (a, b, sort) -> FOEqual (fo a, fo b, sort)
  | FCorrespond (a, b, i, j) -> FCorrespond (fa a, fa b, fi i, fi j)
  | FNonzero (a, i, j) -> FNonzero (fa a, fi i, fi j)
  | FQuantifier (univ, x, i, j, phi) ->
    FQuantifier (univ, x, fi i, fi j, fb phi)
  | FAnonymous (f, name, lst) -> FAnonymous (f, name, List.map fe lst)
;;

(* applies fe/fb/fi/fa/fo on the direct arguments of the given expression *)
let sub_apply_int fe fb fi fa fo = function
  | IValue k -> IValue k
  | IVar (univ, x) -> IVar (univ, x)
  | IPlus lst -> IPlus (List.map fi lst)
  | ITimes lst -> ITimes (List.map fi lst)
  | IDiv (x, y) -> IDiv (fi x, fi y)
  | IMod (x, y) -> IMod (fi x, fi y)
  | ISize a -> ISize (fa a)
  | ISelect (a, i) -> ISelect (fa a, fi i)
  | IIte (c, x, y) -> IIte (fb c, fi x, fi y)
  | IAnonymous (f, name, lst) -> IAnonymous (f, name, List.map fe lst)
;;

(* applies fe/fb/fi/fa/fo on the direct arguments of the given expression *)
let sub_apply_array fe fb fi fa fo = function
  | AValue lst -> AValue lst
  | AVar (univ, x) -> AVar (univ, x)
  | AAllocate (x, y) -> AAllocate (fi x, fi y)
  | AStore (a, x, y) -> AStore (fa a, fi x, fi y)
  | AIte (c, x, y) -> AIte (fb c, fa x, fa y)
  | AAnonymous (f, name, lst) -> AAnonymous (f, name, List.map fe lst)

(* applies fe/fb/fi/fa/fo on the direct arguments of the given expression *)
let sub_apply_other fe fb fi fa fo = function
  | OVar (univ, x) -> OVar (univ, x)
  | OIte (c, x, y) -> OIte (fb c, fo x, fo y)
  | OAnonymous (f, name, lst) -> OAnonymous (f, name, List.map fe lst)

(*****************************************************************************)
(* pre-parsing                                                               *)
(*****************************************************************************)

(* sort the arguments of a plus or times; helping function for integer
simplification *)
let sort_integer_arguments lst =
  (* find unique identifying arrays for the given pair / triple *)
  let pair_size num a b = (num, List.length a) :: (a @ b) in
  let triple_size num a b c =
    (num, List.length a) :: (a @ [(-num, List.length b)] @ c)
  in
  (* give all expressions a size; we only bother with the non-integer
  expressions to make sure all expressions have a unique identifier *)
  let rec expression_size = function
    | IValue k -> [(0, k)]
    | IVar (univ, x) -> var_size univ x
    | IPlus args ->
      (3, 0) :: List.flat_map id (List.rev_map expression_size args)
    | ITimes args ->
      List.flat_map id (List.rev_map expression_size args)
    | IDiv (a, b) -> pair_size 4 (expression_size a) (expression_size b)
    | IMod (a, b) -> pair_size 5 (expression_size a) (expression_size b)
    | ISize a -> (6, 0) :: (array_size a)
    | ISelect (a, b) -> pair_size 7 (array_size a) (expression_size b)
    | IIte (c, a, b) -> ite_size c (expression_size a) (expression_size b)
    | IAnonymous (f, _, lst) -> anonymous_size f lst
  and array_size = function
    | AValue lst -> (0, 0) :: List.map (fun x -> (x, 0)) lst
    | AVar (univ, x) -> var_size univ x
    | AAllocate (x, y) -> pair_size 3 (expression_size x) (expression_size y)
    | AStore (a, x, y) ->
      triple_size 4 (array_size a) (expression_size x) (expression_size y)
    | AIte (c, a, b) -> ite_size c (array_size a) (array_size b)
    | AAnonymous (f, _, lst) -> anonymous_size f lst
  and bool_size = function
    | FTrue -> [(0, 0)]
    | FFalse -> [(0, 1)]
    | FVar (univ, x) -> var_size univ x
    | FOr args ->
      (3, 0) :: List.flat_map id (List.rev_map bool_size args)
    | FAnd args ->
      List.flat_map id (List.rev_map bool_size args)
    | FXor (a, b) -> pair_size 5 (bool_size a) (bool_size b)
    | FEquiv (a, b) -> pair_size 6 (bool_size a) (bool_size b)
    | FNegate b -> (7, 0) :: bool_size b
    | FAEqual (a, b) -> pair_size 8 (array_size a) (array_size b)
    | FOEqual (a, b, _) -> pair_size 9 (other_size a) (other_size b)
    | FIte (c, a, b) -> ite_size c (bool_size a) (bool_size b)
    | FAnonymous (f, _, lst) -> anonymous_size f lst
    | FCompare (cmp, x, y) ->
      (15, (if cmp == CGeq then 0 else if cmp == CEqual then 1 else 2)) ::
      pair_size 16 (expression_size x) (expression_size y)
    | FCorrespond (a, b, i, j) ->
      let asize = array_size a in
      let bsize = array_size b in
      let isize = expression_size i in
      let jsize = expression_size j in
      [(17, List.length asize)] @ asize @ bsize @
      [(-17, List.length isize)] @ isize @ jsize
    | FNonzero (a, i, j) ->
      triple_size 18 (array_size a) (expression_size i) (expression_size j)
    | FQuantifier (b, x, i, j, c) ->
      let num = 2 * (Variable.to_int x) + (if b then 1 else 0) in
      (19,num) :: triple_size 20 (expression_size i) (expression_size j)
                                 (bool_size c)
  and other_size = function
    | OVar (univ, x) -> var_size univ x
    | OIte (c, a, b) -> ite_size c (other_size a) (other_size b)
    | OAnonymous (f, _, lst) -> anonymous_size f lst
  and exp_size = function
    | EBool b -> bool_size b
    | EInt i -> expression_size i
    | EArray a -> array_size a
    | EOther (_,o) -> other_size o
  and var_size univ x = [((if univ then 2 else 1), Variable.to_int x)]
  and ite_size c asize bsize = triple_size 10 (bool_size c) asize bsize
  and anonymous_size f lst =
      let sizes = List.flat_map exp_size lst in
      if Function.is_standard f then (11, Function.std_to_int f) :: sizes
      else if Function.is_integer f then
        (12, Function.integer_to_int f) :: sizes
      else if Function.is_array f then (
        let arr = Function.array_to_array f in
        let nums = List.map Function.hash (Array.to_list arr) in
        pair_size 13 (List.map (fun x -> (x, 0)) nums) sizes
      )
      else [(14, 0)]
  in
  let comparetuple (a1,b1) (a2,b2) =
    if a1 = a2 then compare b1 b2 else compare a1 a2
  in
  let rec comparelist lst1 lst2 =
    if (lst1 = []) then ( if lst2 = [] then 0 else -1 ) else
    if lst2 = [] then 1 else
    let (hd1, tl1) = (List.hd lst1, List.tl lst1) in
    let (hd2, tl2) = (List.hd lst2, List.tl lst2) in
    let comparison = comparetuple hd1 hd2 in
    if comparison = 0 then compare tl1 tl2 else comparison
  in
  let compare x y =
    comparelist (expression_size x) (expression_size y)
  in
  List.sort compare lst
;;

(* helping function both to spread multiplications over additions and
   conjunctions over disjunctions *)
let explode_subs explodable combine subs =
  let rec recurse sofar = function
    | [] -> [sofar]
    | head :: tail -> (
      match explodable head with
        | None -> recurse (head :: sofar) tail
        | Some args ->
          let explode arg = recurse (arg :: sofar) tail in
          List.flat_map explode args
    )
  in
  List.map combine (recurse [] subs)
;;

(* simplifies integers in an expression (most effective if expressions
are free of anything but variables, values, plus and times) *)
let rec simplify_iexp expression =
  match expression with 
    | IValue _ | IVar _ -> expression
    | IPlus lst -> simplify_plus (List.map simplify_iexp lst)
    | ITimes lst -> simplify_times (List.map simplify_iexp lst)
    | IDiv (x, y) -> IDiv (simplify_iexp x, simplify_iexp y)
    | IMod (x, y) -> IMod (simplify_iexp x, simplify_iexp y)
    | ISize a -> ISize (simplify_ints_in_aexp a)
    | ISelect (a, x) -> ISelect (simplify_ints_in_aexp a, simplify_iexp x)
    | IIte (c, x, y) -> IIte (simplify_ints_in_bexp c, simplify_iexp x,
                              simplify_iexp y)
    | IAnonymous (f, name, lst) ->
      IAnonymous (f, name, List.map simplify_ints_in_expr lst)

and simplify_ints_in_expr e =
  sub_apply_exp simplify_ints_in_expr simplify_ints_in_bexp
                simplify_iexp simplify_ints_in_aexp
                simplify_ints_in_oexp e

and simplify_ints_in_aexp a =
  sub_apply_array simplify_ints_in_expr simplify_ints_in_bexp
                  simplify_iexp simplify_ints_in_aexp
                  simplify_ints_in_oexp a

and simplify_ints_in_bexp b =
  sub_apply_bool simplify_ints_in_expr simplify_ints_in_bexp
                 simplify_iexp simplify_ints_in_aexp
                 simplify_ints_in_oexp b

and simplify_ints_in_oexp o =
  sub_apply_other simplify_ints_in_expr simplify_ints_in_bexp
                  simplify_iexp simplify_ints_in_aexp
                  simplify_ints_in_oexp o

(* simplify an integer expression IPlus args; all elements of args
are already assumed to be simplified *)
and simplify_plus args =
  let flatten_plus = function | IPlus lst -> lst | expr -> [expr] in
  let lst = List.flat_map flatten_plus args in
  let lst = sort_integer_arguments lst in
  let checktimes = function
    | ITimes (IValue 0 :: _) -> []
    | whatever -> [whatever]
  in
  let rec merge_parts = function
    | [] -> []
    | [single] -> [single]
    | (IValue 0) :: rest -> merge_parts rest 
    | (IValue x) :: (IValue y) :: rest ->
      merge_parts ((IValue (x+y)) :: rest)
    | (IValue x) :: rest -> (IValue x) :: merge_parts rest 
    | first :: second :: tail -> ( 
      let isvar = function | IVar _ -> true | _ -> false in
      if (first = second) && (isvar first) then 
        merge_parts ((ITimes [IValue 2; first]) :: tail)
      else let continue _ = first :: merge_parts (second :: tail) in
      match (first, second) with 
        | (ITimes (IValue n :: x), ITimes (IValue m :: y)) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (ITimes (IValue (n+m) :: x))) @ tail)
        | (ITimes x, ITimes (IValue m :: y)) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (ITimes (IValue (m+1) :: y))) @ tail)
        | (x, ITimes [IValue m; y]) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (ITimes [IValue (m+1); x])) @ tail)
        | _ -> continue ()
    )
  in
  match merge_parts lst with
    | [] -> IValue 0
    | [single] -> single
    | lst -> IPlus lst

(* simplify an integer expression Times args; if toponly is true,
then all elements of args are already assumed to be simplified *)
and simplify_times args =
  let rec merge_parts = ( function
    | [] -> []
    | [single] -> [single]
    | (IValue 0) :: rest -> [IValue 0]
    | (IValue 1) :: rest -> merge_parts rest
    | (IValue x) :: (IValue y) :: rest ->
      merge_parts ((IValue (x*y)) :: rest)
    | lst -> lst
  ) in
  (* given a list [a1,...,an] of simplified expressions which may be
  products but not sums, build the resulting multiplication *)
  let finish lst =
    let flatten_times = function | ITimes lst -> lst | expr -> [expr] in
    let lst = List.flat_map flatten_times lst in
    let lst = sort_integer_arguments lst in
    let lst = merge_parts lst in
    match lst with
      | [] -> IValue 1
      | (IValue 0) :: _ -> IValue 0
      | [single] -> single
      | lst -> ITimes lst
  in
  let plustosome = function | IPlus lst -> Some lst | _ -> None in
  let plusparts = explode_subs plustosome finish args in
  ( match plusparts with
    | [single] -> single
    | args -> simplify_plus (List.map simplify_iexp args)
  )

(* given a simplified integer expression x, adds 1 to it; if the
original expression is not simplified, then the result is still x + 1,
but it might not be simplified *)
let successor x = simplify_plus [IValue 1; x];;

(* helping function for up_ite: detects the first occurrence of an
Ite in the given list, and splits the list into two parts, fed into
itebuilder; "builder" turns the lists into an expression of the right
type*)
let handle_ite_list builder itebuilder lst =
  (* detect whether the argument is an anonymised Ite *)
  let isiteparts = function
    | EInt (IIte (c, x, y)) -> Some (c, EInt x, EInt y)
    | EArray (AIte (c, x, y)) -> Some (c, EArray x, EArray y)
    | EOther (sort, OIte (c, x, y)) ->
      Some (c, EOther (sort, x), EOther (sort, y))
    | _ -> None
  in
  (* find the first Ite, and split accordingly *)
  let rec handle sofar = function
    | [] -> builder lst
      (* we couldn't find one; just return the full list *)
    | hd :: tl ->
      match isiteparts hd with
        | None -> handle (hd :: sofar) tl
        | Some (c, x, y) ->
          let lst1 = List.rev_append sofar (x :: tl) in
          let lst2 = List.rev_append sofar (y :: tl) in
          itebuilder c (builder lst1) (builder lst2)
  in
  handle [] lst
;;

(* moves any occurrence of Ite up in the given expression; only FItes
are not moved further upwards *)
let rec up_ite exp =
  sub_apply_exp up_ite up_ite_bool up_ite_int up_ite_array up_ite_other exp

and up_ite_bool exp =
  let exp = sub_apply_bool up_ite up_ite_bool up_ite_int up_ite_array
            up_ite_other exp in
  let rec recurse exp = match exp with
    | FCompare (cmp, IIte (c, x, y), i) ->
      FIte (c, recurse (FCompare (cmp, x, i)),
               recurse (FCompare (cmp, y, i)))
    | FCompare (cmp, x, IIte (c, i, j)) ->
      FIte (c, recurse (FCompare (cmp, x, i)),
               recurse (FCompare (cmp, x, j)))
    | FAEqual (AIte (c, a, b), d) ->
      FIte (c, recurse (FAEqual (a, d)), recurse (FAEqual (b, d)))
    | FAEqual (a, AIte (c, b, d)) ->
      FIte (c, recurse (FAEqual (a, b)), recurse (FAEqual (a, d)))
    | FOEqual (OIte (c, a, b), d, sort) ->
      FIte (c, recurse (FOEqual (a, d, sort)),
               recurse (FOEqual (b, d, sort)))
    | FOEqual (a, OIte (c, b, d), sort) ->
      FIte (c, recurse (FOEqual (a, b, sort)),
               recurse (FOEqual (a, d, sort)))
    | FCorrespond (AIte (c, a, b), d, i, j) ->
      FIte (c, recurse (FCorrespond (a, d, i, j)),
               recurse (FCorrespond (b, d, i, j)))
    | FCorrespond (a, AIte (c, b, d), i, j) ->
      FIte (c, recurse (FCorrespond (a, b, i, j)),
               recurse (FCorrespond (b, d, i, j)))
    | FCorrespond (a, b, IIte (c, n, m), i) ->
      FIte (c, recurse (FCorrespond (a, b, n, i)),
               recurse (FCorrespond (a, b, m, i)))
    | FCorrespond (a, b, n, IIte (c, i, j)) ->
      FIte (c, recurse (FCorrespond (a, b, n, i)),
               recurse (FCorrespond (a, b, n, j)))
    | FNonzero (AIte (c, a, b), n, i) ->
      FIte (c, recurse (FNonzero (a, n, i)),
               recurse (FNonzero (b, n, i)))
    | FNonzero (a, IIte (c, n, m), i) ->
      FIte (c, recurse (FNonzero (a, n, i)),
               recurse (FNonzero (a, m, i)))
    | FNonzero (a, n, IIte (c, i, j)) ->
      FIte (c, recurse (FNonzero (a, n, i)),
               recurse (FNonzero (a, n, j)))
    | FAnonymous (f, name, lst) ->
      let builder l = FAnonymous (f, name, l) in
      let itebuilder c x y = FIte (c, recurse x, recurse y) in
      handle_ite_list builder itebuilder lst
    | _ -> exp
  in
  recurse exp

and up_ite_int exp =
  let exp = sub_apply_int up_ite up_ite_bool up_ite_int up_ite_array
            up_ite_other exp in
  (* now IIte occurs only directly below the root *)
  let rec listhandle builder sofar = function
    | [] -> builder (List.rev sofar)
    | (IIte (c, a, b)) :: tl ->
      let lst1 = List.rev_append sofar (a :: tl) in
      let lst2 = List.rev_append sofar (b :: tl) in
      IIte (c, recurse (builder lst1),
               recurse (builder lst2))
    | hd :: tl -> listhandle builder (hd :: sofar) tl
  and listtopair user lst =
    user (List.hd lst) (List.hd (List.tl lst))
  and recurse exp =
    match exp with
      | IPlus lst -> listhandle (fun x -> IPlus x) [] lst
      | ITimes lst -> listhandle (fun x -> ITimes x) [] lst
      | IDiv (a, b) -> listhandle (listtopair (fun x y -> IDiv (x, y))) [] [a;b]
      | IMod (a, b) -> listhandle (listtopair (fun x y -> IDiv (x, y))) [] [a;b]
      | ISize (AIte (c, a, b)) ->
        IIte (c, recurse (ISize a), recurse (ISize b))
      | ISelect (AIte (c, a, b), x) ->
        IIte (c, recurse (ISelect (a, x)),
                 recurse (ISelect (b, x)))
      | ISelect (a, IIte (c, x, y)) ->
        IIte (c, recurse (ISelect (a, x)),
                 recurse (ISelect (a, y)))
      | IAnonymous (f, name, lst) ->
        let builder l = IAnonymous (f, name, l) in
        let itebuilder c x y =
          IIte (c, recurse x, recurse y) in
        handle_ite_list builder itebuilder lst
      | IValue _ | IVar _ | ISize _ | IIte _ | ISelect _ -> exp
  in
  recurse exp

and up_ite_array exp =
  let exp = sub_apply_array up_ite up_ite_bool up_ite_int up_ite_array
            up_ite_other exp in
  let rec recurse exp = match exp with
    | AAllocate (IIte (c, n, m), i) ->
      AIte (c, recurse (AAllocate (n, i)),
               recurse (AAllocate (m, i)))
    | AAllocate (n, IIte (c, i, j)) ->
      AIte (c, recurse (AAllocate (n, i)),
               recurse (AAllocate (n, j)))
    | AStore (AIte (c, a, b), i, j) ->
      AIte (c, recurse (AStore (a, i, j)),
               recurse (AStore (b, i, j)))
    | AStore (a, IIte (c, i, k), j) ->
      AIte (c, recurse (AStore (a, i, j)),
               recurse (AStore (a, k, j)))
    | AStore (a, i, IIte (c, j, k)) ->
      AIte (c, recurse (AStore (a, i, j)),
               recurse (AStore (a, i, k)))
    | AAnonymous (f, name, lst) ->
      let builder l = AAnonymous (f, name, l) in
      let itebuilder c x y =
        AIte (c, recurse x, recurse y) in
      handle_ite_list builder itebuilder lst
    | AValue _ | AVar _ | AIte _ | AAllocate _ | AStore _ -> exp
  in
  recurse exp

and up_ite_other exp =
  let exp = sub_apply_other up_ite up_ite_bool up_ite_int up_ite_array
            up_ite_other exp in
  let rec recurse exp = match exp with
    | OVar _ | OIte _ -> exp
    | OAnonymous (f, name, lst) ->
      let builder l = OAnonymous (f, name, l) in
      let itebuilder c x y =
        OIte (c, recurse x, recurse y) in
      handle_ite_list builder itebuilder lst
  in
  recurse exp
;;

(* handles negation; if the given formula has simplified integers,
then the same holds for its negation *)
let rec negate formula =
  match formula with
    | FTrue -> FFalse
    | FFalse -> FTrue
    | FNegate x -> x
    | FAnd args -> FOr (List.map negate args)
    | FOr args -> FAnd (List.map negate args)
    | FCompare (CGeq, a, b) -> FCompare (CGeq, b, successor a)
    | FCompare (CEqual, a, b) -> FCompare (CUnequal, a, b)
    | FCompare (CUnequal, a, b) -> FCompare (CEqual, a, b)
    | FQuantifier (universal, x, lower, upper, form) ->
      FQuantifier (not universal, x, lower, upper, negate form)
    | _ -> FNegate formula
;;



(*
let ditch_ite formula =
  (* move all ite occurrences up *)
  let formula = up_it formula in
  (* handle Ites at a top! *)
  let rec handle_subs inand formula = match formula with
    | FTrue | FFalse | FVar _ -> formula
    | FAnd lst -> FAnd (List.map (handle_subs true) lst)
    | FOr lst -> FOr (List.map (handle_subs false) lst)
    | FXor (a, b) ->
      FXor (handle_subs (not inand) a, handle_subs (not inand) b)
    | FNegate a -> FNegate (handle_subs (not inand) a)
    | FCompare (cmp, IIte (c, n, m), i) ->
      if inand then
        FAnd [FOR [handle_subs true 
      else
      
  | FCompare (cmp, i, j) -> FCompare (cmp, fi i, fi j)
  | FAEqual (a, b) -> FAEqual (fa a, fa b)
  | FOEqual (a, b, sort) -> FOEqual (fo a, fo b, sort)
  | FCorrespond (a, b, i, j) -> FCorrespond (fa a, fa b, fi i, fi j)
  | FNonzero (a, i, j) -> FNonzero (fa a, fi i, fi j)
  | FQuantifier (univ, x, i, j, phi) ->
    FQuantifier (univ, x, fi i, fi j, fb phi)
  | FAnonymous (f, name, lst) -> FAnonymous (f, name, List.map fe lst)
  in
  handle_subs formula
;;
*)














(*
(* removes any occurrence of Ite from the given formula *)
let rec ditch_ite formula =
  let isite = function | IIte _ -> true | _ -> false in
  let parts = function
    | IIte (cond, cif, celse) -> (cond, cif, celse)
    | _ -> failwith "ite occurrence not actually ite!"
  in
  let replacement iteexpr maker =
    let (cond, cif, celse) = parts iteexpr in
    let ifform = maker cif in
    let elseform = maker celse in
    let form = FOr [FAnd [cond; ifform]; FAnd [FNegate cond; elseform]] in
    ditch_ite form
  in
  match formula with
    | FTrue | FFalse | FVar _ -> formula
    | FAnd args -> FAnd (List.map ditch_ite args)
    | FOr args -> FOr (List.map ditch_ite args)
    | FNegate arg -> FNegate (ditch_ite arg)
    | FXor (a,b) -> FXor (ditch_ite a, ditch_ite b)
    | FCompare (cmp, a, b) ->
      ( match find_sub_iexp isite false a with
        | Some (pos, expr) ->
          let maker nexpr = FCompare (cmpd, replace_sub_iexp pos nexpr a, b) in
          replacement expr maker
        | None -> match find_sub_iexp isite false b with
          | Some (pos, expr) -> 
          | None -> formula
      )
              (*
              FCompare of comparison * intexp * intexp |
              FAEqual of arrexp * arrexp |
              FOEqual of othexp * othexp * Sort.t |
              FCorrespond of arrexp * arrexp * intexp * intexp |
              FNonzero of arrexp * intexp * intexp |
              FQuantifier of bool * Variable.t * intexp *
                             intexp * formula |
              FAnonymous of Function.t * string * exp list
              *)
  (*
    | Geq (a,b) | Equal (a, b) | Unequal (a, b) ->
      let builder x y =
        match formula with
          | Geq _ -> Geq (x,y)
          | Equal _ -> Equal (x,y)
          | _ -> Unequal (x,y)
      in
      expression_pair a b builder
  let expression_pair a b builder =
    match find_sub_expr isite false a with
      | None -> ( match find_sub_expr isite false b with
      | Some (pos, expr) ->
        let maker nexpr = builder (replace_sub_expr pos nexpr a) b in
        replacement expr maker
  in
  match formula with
    | UnknownPred (cond, exprs, forms) ->
      let forms = List.map ditch_ite forms in
      let rec first i = function
        | [] -> None
        | hd :: tl -> match find_sub_expr isite false hd with
          | None -> first (i+1) tl
          | Some (pos, expr) -> Some (i, pos, expr)
      in
      ( match first 0 exprs with
        | None -> UnknownPred (cond, exprs, forms)
        | Some (i, pos, expr) ->
          let maker nexpr =
            let (a, b) = List.split_at i exprs in
            let (q, c) = (List.hd b, List.tl b) in
            let newexpr = replace_sub_expr pos nexpr q in
            let newexprs = a @ (newexpr :: c) in
            UnknownPred (cond, newexprs, forms)
          in
          replacement expr maker
      )
    | Quantifier (universal, x, lower, upper, form) ->
      let builder y z = Quantifier (universal, x, y, z, ditch_ite form) in
      expression_pair lower upper builder
    | AndWithDefs _ | OrWithUndefs _ ->
      failwith "ditch_ite should not be called when deep simplifying"
    | _ -> formula
  *)
;;

(* helping function for find_sub_exp, separate only for polymorphism;
   finds the first argument where f returns something other than
   None, and updates its position accordingly
*)
let find_first f =
  let rec recurse i = function
    | [] -> None
    | head :: tail -> (
      match f head with
        | None -> recurse (i+1) tail
        | Some (pos, expr) -> Some (i::pos, expr)
    )
  in
  recurse 0
;;

(* returns the first position and subexpression at this position
   where checker is satisfied, or None if there is no such position;
   if "deep" is set to true, then this position must be as deep
   inside the expression as possible, otherwise it must be as low
   inside the expression as possible *)
let rec find_sub_exp checker deep = function
  | EBool x      -> find_sub_bexp checker deep x
  | EInt x       -> find_sub_iexp checker deep x
  | EArray x     -> find_sub_aexp checker deep x
  | EOther (_,x) -> find_sub_oexp checker deep x

and find_sub_bexp checker deep bexp =
  let brecurse lst = find_first (find_sub_bexp checker deep) lst in
  match bexp with
  | FTrue | FFalse | FVar _ -> None
  | FAnd lst | FOr lst -> brecurse lst
  | FXor (x, y) -> brecurse [x;y]
  | FNegate x -> brecurse [x]
  | FCompare (_, i, j) ->
    find_first (find_sub_iexp checker deep) [i; j]
  | FAEqual (a, b) -> find_first (find_sub_aexp checker deep) [a;b]
  | FOEqual (a, b, _) -> find_first (find_sub_oexp checker deep) [a;b]
  | FCorrespond (a, b, i, j) ->
    find_first (find_sub_exp checker deep) [EArray a; EArray b; EInt i; EInt j]
  | FNonzero (a, i, j) ->
    find_first (find_sub_exp checker deep) [EArray a; EInt i; EInt j]
  | FQuantifier (_, _, i, j, p) ->
    find_first (find_sub_exp checker deep) [EInt i; EInt j; EBool p]
  | FAnonymous (_, _, lst) ->
    find_first (find_sub_exp checker deep) lst

and find_sub_iexp checker deep iexp =
  let checkargs args =
    match find_first (find_sub_exp checker deep) args with
      | None ->
        if deep && (checker iexp) then Some ([], iexp)
        else None
      | answer -> answer
  in
  let checkiargs args = checkargs (List.map (fun x -> EInt x) args) in
  if (not deep) && (checker iexp) then Some ([], iexp)
  else match iexp with
    | IValue _ | IVar _ -> checkargs []
    | IPlus args | ITimes args -> checkiargs args
    | IDiv (x, y) | IMod (x, y) -> checkiargs [x;y]
    | IIte (cond, cif, celse) ->
      checkargs [EBool cond; EInt cif; EInt celse]
    | ISize aexp -> checkargs [EArray aexp]
    | ISelect (aexp, iexp) -> checkargs [EArray aexp; EInt iexp]
    | IAnonymous (_, _, lst) -> checkargs lst

and find_sub_aexp checker deep = function
  | AValue _ | AVar _ -> None
  | AAllocate (a, b) ->
    find_first (find_sub_iexp checker deep) [a;b]
  | AStore (aexp, i, j) ->
    find_first (find_sub_exp checker deep) [EArray aexp; EInt i; EInt j]
  | AAnonymous (_, _, lst) ->
    find_first (find_sub_exp checker deep) lst

and find_sub_oexp checker deep = function
  | OVar _ -> None
  | OAnonymous (_, _, lst) ->
    find_first (find_sub_exp checker deep) lst
;;
*)













(** TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO
 * From this point onward, the code has not yet been adapted for separating the
 * input parsing and prepocessing, and the core reasoning parts. *)

(** MODULES ******************************************************************)

module Possibilities = struct
  type t = int list

  let compare = compare
  let fprintf = List.fprintf (fun f -> Format.fprintf f "%d") ", "
  let rec from_range a b = if a <= b then a :: from_range (a+1) b else []
end

module VarMap = Replacement.Make(Variable)(Possibilities);;
  (* Possibility maps are used for universal satisfiability: we simply
  consider all possible combinations for the ways to fill the quantified
  variables *)

(*** TYPES *******************************************************************)

(*****************************************************************************)
(* types used to interact with the solver core                               *)
(*****************************************************************************)

type othercontext = Func of string * othercontext list |
                    OtherVar of bool * Variable.t |
                    IntExp of int | BoolExp of int

type intexpression = Value of int | Plus of intexpression list |
                     Times of intexpression list |
                     Div of intexpression * intexpression |
                     Mod of intexpression * intexpression |
                     Ite of intformula * intexpression * intexpression |
                     IntVar of bool * Variable.t |
                     UnknownExp of othercontext * intexpression list *
                                   intformula list

and  intformula = And of intformula list | Or of intformula list |
                  Geq of intexpression * intexpression |
                  Equal of intexpression * intexpression |
                  Unequal of intexpression * intexpression |
                  BoolVar of bool * Variable.t |
                  True | False |
                  Negate of intformula | Xor of intformula * intformula |
                  AndWithDefs of int * intformula list |
                  OrWithUndefs of int * intformula list |
                  UnknownPred of othercontext * intexpression list *
                                 intformula list |
                  Quantifier of bool * Variable.t * intexpression *
                                intexpression * intformula

(* NOTE: unknown predicates cannot be present in deep analysis, as we
don't know what properties to expect for them.  However, they may
serve a purpose in for instance rewriting constraints.  Thus, we
support them in those functions where their presence does not lead to
any conflict.
TODO: investigate exactly what we can do with them in the solver
core! *)

(*** FUNCTIONS ***************************************************************)

(*****************************************************************************)
(* debug information                                                         *)
(*****************************************************************************)

let rec tostr_each printer between = function
  | [] -> ""
  | [single] -> printer single
  | head :: tail -> (printer head) ^ " " ^ between ^ " " ^
                    (tostr_each printer between tail)
;;

let tostr_pair printer between (x, y) =
  (printer x) ^ " " ^ between ^ " " ^ (printer y)
;;

let rec tostr_expression brackets expression =
  match expression with
    | Value k -> string_of_int k
    | Plus args -> surround brackets
                   (tostr_each (tostr_expression true) "+" args)
    | Times args -> surround brackets
                   (tostr_each (tostr_expression true) "*" args)
    | Div (top, bottom) -> (tostr_expression true top) ^ " / " ^
                           (tostr_expression true bottom)
    | Mod (top, bottom) -> (tostr_expression true top) ^ " % " ^
                           (tostr_expression true bottom)
    | Ite (cond,ci,ce) ->
      let combination =
        (tostr_formula false cond) ^ " ? " ^
        (tostr_expression false ci) ^ " : " ^
        (tostr_expression false ce)
      in
      surround brackets combination
    | UnknownExp (context, earr, farr) ->
      tostr_context earr farr false context
    | IntVar (_, x) -> tostr_var x

and tostr_formula brackets formula =
  match formula with
    | And args ->
      surround brackets (tostr_each (tostr_formula true) "/\\" args)
    | AndWithDefs (_, args) ->
      surround brackets (tostr_each (tostr_formula true) "&&" args)
    | Or args ->
      surround brackets (tostr_each (tostr_formula true) "\\/" args)
    | OrWithUndefs (_, args) ->
      surround brackets (tostr_each (tostr_formula true) "||" args)
    | Geq (x,y) -> tostr_pair (tostr_expression false) ">=" (x,y)
    | Equal (x,y) -> tostr_pair (tostr_expression false) "=" (x,y)
    | Unequal (x,y) -> tostr_pair (tostr_expression false) "!=" (x,y)
    | True -> "Top"
    | False -> "Bottom"
    | Negate cond -> surround brackets ("not " ^ (tostr_formula true cond))
    | Xor (x,y) -> tostr_pair (tostr_formula true) "xor" (x,y)
    | UnknownPred (context, earr, farr) ->
      tostr_context earr farr false context
    | Quantifier (universal, x, lower, upper, form) ->
      let varname = tostr_var x in
      let quant = if universal then "ALL" else "EX" in
      quant ^ " " ^ varname ^ " in {" ^ (tostr_expression true lower) ^
      "..." ^ (tostr_expression true upper) ^ "} [" ^
      (tostr_formula false form) ^ "]"
    | BoolVar (_, x) -> tostr_var x

and tostr_context elst flst printint = function
  | Func (name, lst) -> name ^ "(" ^
      (List.implode (tostr_context elst flst printint) ", " lst) ^ ")"
  | IntExp i -> if printint then "[i" ^ (string_of_int i) ^ "]"
                else tostr_expression false (List.nth elst i)
  | BoolExp i -> if printint then "[b" ^ (string_of_int i) ^ "]"
                 else tostr_formula false (List.nth flst i)
  | OtherVar (_, x) -> tostr_var x
;;

let print_formula f = Printf.printf "%s\n" (tostr_formula false f);;

(*****************************************************************************)
(* making sure we get only relevant stuff here                               *)
(*****************************************************************************)

let acceptable_logic logic =
  logic = "QF_NIA" || logic = "QF_LIA" || logic = "QF_IDL"
;;

(*****************************************************************************)
(* parsing terms into the local shapes of intformulas and -expressions       *)
(*****************************************************************************)

let rec parse_context a e i j isparam term =
  let rec translate_list i j = function
    | [] -> []
    | hd :: tl ->
      let sort = Term.get_sort a e hd in
      let isort =
        try Alphabet.integer_sort a
        with Not_found ->parsefail "integer sort not even set!"
      in
      if sort = isort then
        ((IntExp i), [hd], []) :: translate_list (i + 1) j tl
      else if sort = Alphabet.boolsort then
        ((BoolExp j), [], [hd]) :: translate_list i (j + 1) tl
      else (
        let (context, es, fs) = parse_context a e i j isparam hd in
        let newi = i + List.length es in
        let newj = j + List.length fs in
        (context, es, fs) :: translate_list newi newj tl
      )
  in
  match term with
    | Term.Var x -> (OtherVar (not (isparam x), x), [], [])
    | Term.Forall _ | Term.Exists _ ->
      failwith "Quantifiers occurring in context which should be functional!"
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      let targs = translate_list i j args in
      ( Func (Function.find_name f, List.map (fun (x,_,_) -> x) targs),
        List.flat_map (fun (_,y,_) -> y) targs,
        List.flat_map (fun (_,_,z) -> z) targs
      )
;;

(* translates an smt-expression to a term, if possible; fails if not *)
let rec translate_smt makesub a e rens lst =
  let make_term name args =
    let f = get_named_symbol a ("Unknown symbol: " ^ name) rens
            (const true) (const true) [name] in
    Term.make_function a e f args
  in
  let rec split_identifier txt i len =
    if i >= len then (txt, "")
    else if List.mem (String.get txt i) [' '; '('; ')'] then
      (String.sub txt 0 i, String.chop (String.sub txt i (len - i)))
    else split_identifier txt (i + 1) len
  in
  let rec translate_args sofar l =
    match translate_smt makesub a e rens l with
      | (None, rest) -> (List.rev sofar, rest)
      | (Some term, rest) -> translate_args (term :: sofar) rest
  in
  match lst with
    | [] -> failwith "unmatched brackets!"
    | (Right i) :: tail -> (Some (makesub i), tail)
    | (Left txt) :: tail ->
      let txt = String.chop txt in
      let len = String.length txt in
      (* Empty string? Just continue with the rest of the list. *)
      if len = 0 then translate_smt makesub a e rens tail
      (* if this is a ), then we're at the end of an expression *)
      else if String.get txt 0 = ')' then (
        let rest = String.chop (String.sub txt 1 (len - 1)) in
        if rest = "" then (None, tail)
        else (None, Left rest :: tail)
      )
      (* if the expression doesn't start with (, then we'll simply
      read to the next space *)
      else if String.get txt 0 <> '(' then (
        let (ident, rest) = split_identifier txt 0 len in
        let term = make_term ident [] in
        if rest = "" then (Some term, tail)
        else (Some term, Left rest :: tail)
      )
      (* if it does, read on until the matching closing bracket! *)
      else (
        let txt = String.chop (String.sub txt 1 (len - 1)) in
        let (ident, rest) = split_identifier txt 0 (String.length txt) in
        let (args, remainder) = translate_args [] (Left rest :: tail) in
        (Some (make_term ident args), remainder)
      )
;;

let rec translate_int ren tra a e isparam = function
  | Term.Var x -> IntVar (not (isparam x), x)
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) as term ->
    let name = Function.find_name f in
    let name = (
      try List.assoc name ren
      with Not_found -> name
    ) in
    let name = String.lowercase_ascii name in
    let newargs =
      if name = "ite" then []
      else List.map (translate_int ren tra a e isparam) args
    in
    if name = "+" || name = "plus" || name = "add" then Plus newargs
    else if name = "*" || name = "times" || name = "mul" then Times newargs
    else if name = "abs" then (
      match newargs with
        | [arg] -> Ite (Geq (arg, Value 0), arg, Times [Value (-1); arg])
        | _ -> parsefail ("Encountered abs with " ^
            (string_of_int (List.length args)) ^ " arguments (expected 1)")
    )
    else if name = "-" || name = "minus" ||
            name = "/" || name = "div" || name = "mod" || name = "%" then
      match newargs with
        | [first;second] ->
          if name = "mod" || name = "%" then Mod (first, second)
          else if name = "/" || name = "div" then Div (first,second)
          else Plus [first; Times [Value (-1); second]]
        | _ -> parsefail ("Encountered " ^ name ^ " with " ^
            (string_of_int (List.length args)) ^ " arguments " ^
            "(expected 2)")
    else if name = "ite" then (
      match args with
        | [check;ifval;elseval] ->
          let ccheck = translate_bool ren tra a e isparam check in
          let cif = translate_int ren tra a e isparam ifval in
          let celse = translate_int ren tra a e isparam elseval in
          Ite (ccheck, cif, celse)
        | _ -> parsefail ("Occurrence of " ^ name ^ " with " ^
            (string_of_int (List.length args)) ^ " arguments, 3 expected")
    )
    else if Function.is_integer f then Value (Function.integer_to_int f)
    else (
      let (context, exprs, forms) = parse_context a e 0 0 isparam term in
      let es = List.map (translate_int ren tra a e isparam) exprs in
      let fs = List.map (translate_bool ren tra a e isparam) forms in
      UnknownExp (context, es, fs)
    )
  | Term.Forall _ | Term.Exists _ ->
    parsefail "Quantification marked as integer!"

and translate_bool ren tra a e isparam = function
  | Term.Var x -> BoolVar (not (isparam x), x)
  | Term.Fun (f, args) | Term.InstanceFun (f, args, _) as term ->
    let name = Function.find_name f in
    let name = (
      try List.assoc name ren
      with Not_found -> name
    ) in
    (* handle custom function symbols *)
    let (istranslation, t) =
      try
        let trans = List.assoc name tra in
        let makesub i = List.nth args i in
        match translate_smt makesub a e ren trans with
          | (Some s, []) -> (true, s)
          | _ -> (false, term)
      with _ -> (false, term)
    in
    if istranslation then translate_bool ren tra a e isparam t
    (* truth and falsehood *)
    else if name = "true" || name = "top" then True
    else if name = "false" || name = "bot" || name = "bottom" then False
    (* negation *)
    else if name = "not" || name = "neg" then (
      match args with
        | [arg] -> Negate (translate_bool ren tra a e isparam arg)
        | _ -> parsefail "Not occurrence with unexpected number of arguments!"
    )
    (* all combination operators with two arguments *)
    else if name = "and" || name = "/\\" || name = "or" ||
        name = "\\/" || name = "xor" || name = "^" || name = "=>" ||
        name = "implies" then (
      match args with
        | [first;second] ->
          let u = translate_bool ren tra a e isparam first in
          let v = translate_bool ren tra a e isparam second in
          if name = "and" || name = "/\\" then And [u;v]
          else if name = "or" || name = "\\/" then Or [u;v]
          else if name = "xor" || name = "^" then Xor (u,v)
          else (* if name = "=>" || name = "implies" then *) Or [Negate u;v]
        | _ -> parsefail ("Symbol " ^ name ^ " occurring with " ^
            (string_of_int (List.length args)) ^ " arguments! " ^
            "(2 expected)")
    )
    (* integer comparison *)
    else if name = "<=" || name = ">=" || name = "<" || name = ">" then (
      match args with
        | [first;second] ->
          let u = translate_int ren tra a e isparam first in
          let v = translate_int ren tra a e isparam second in
          if name = "<=" then Geq (v,u)
          else if name = ">=" then Geq (u,v)
          else if name = "<" then Geq (v, Plus [u; Value 1])
          else (* if name = ">" then *) Geq (u, Plus [v; Value 1])
        | _ -> parsefail ("Symbol " ^ name ^ " occurring with " ^
            (string_of_int (List.length args)) ^ " arguments! " ^
            "(2 expected)")
    )
    (* equality / equivalence *)
    else if name = "=" || name = "<=>" then (
      let rec build_equality builder start = function
        | [] -> True
        | [single] -> builder single start
        | first :: second :: rest ->
          And [builder first second;
               build_equality builder start (second :: rest)]
      in
      (*let geq x y = Geq (x,y) in *)
      (*let equality u = build_equality geq (List.hd u) u in*)
      let eq x y = Equal (x,y) in
      let equality = function | [] -> True | [x;y] -> Equal (x,y)
                              | hd :: tl -> build_equality eq hd tl
      in
      let impl x y = Or [Negate x;y] in
      let equivalence u = build_equality impl (List.hd u) u in
      match args with
        | [] -> True
        | head :: tail ->
          let sort = Sort.to_string (Term.get_sort a e head) in
          if sort = "Int" then
            equality (List.map (translate_int ren tra a e isparam) args)
          else if sort = "Bool" then
            equivalence (List.map (translate_bool ren tra a e isparam) args)
          else (
            (*parsefail ("Occurrence of " ^ name ^ " with unexpected sort!")*)
            let (context, exprs, forms) = parse_context a e 0 0 isparam term in
            let es = List.map (translate_int ren tra a e isparam) exprs in
            let fs = List.map (translate_bool ren tra a e isparam) forms in
            UnknownPred (context, es, fs)
          )
    )
    (* unequal *)
    else if name = "#" || name = "distinct" || name = "!=" || name = "<>" then (
      let unequal x y = Unequal (x,y) in
      let rec unequal_from num = function
        | [] -> True
        | [single] -> unequal num single
        | head :: tail -> And [unequal num head; unequal_from num tail]
      in
      let rec all_unequal = function
        | [] -> True
        | [single] -> True
        | [first;second] -> unequal first second
        | head :: tail ->
          And [unequal_from head tail; all_unequal tail]
      in
      match args with
        | [] -> True
        | head :: tail ->
          let sort = Sort.to_string (Term.get_sort a e head) in
          if sort = "Int" then
            all_unequal (List.map (translate_int ren tra a e isparam) args)
          else if sort = "Bool" then (
            match tail with
              | [] -> True
              | [single] -> Xor (translate_bool ren tra a e isparam head,
                                 translate_bool ren tra a e isparam single)
              | _ -> False
          )
          else (
            (*parsefail ("Occurrence of " ^ name ^ " with unexpected sort!")*)
            let (context, exprs, forms) = parse_context a e 0 0 isparam term in
            let es = List.map (translate_int ren tra a e isparam) exprs in
            let fs = List.map (translate_bool ren tra a e isparam) forms in
            UnknownPred (context, es, fs)
          )
    )
    (* if then else *)
    else if name = "ite" then (
      match args with
        | [check;ifval;elseval] ->
          let ccheck = translate_bool ren tra a e isparam check in
          let cif = translate_bool ren tra a e isparam ifval in
          let celse = translate_bool ren tra a e isparam elseval in
          And [Or [ccheck;celse]; Or [Negate ccheck; cif]]
        | _ -> parsefail ("Occurrence of " ^ name ^ " with " ^
            (string_of_int (List.length args)) ^ " arguments, 3 expected")
    )
    else (
      let (context, exprs, forms) = parse_context a e 0 0 isparam term in
      let es = List.map (translate_int ren tra a e isparam) exprs in
      let fs = List.map (translate_bool ren tra a e isparam) forms in
      UnknownPred (context, es, fs)
    )
  | Term.Forall (x, form) ->
    let ((lower, lstrict), (upper, ustrict), form) =
      Smtquantifiers.universal_range x a form in
    let l = translate_int ren tra a e isparam lower in
    let l = if lstrict then Plus [l; (Value 1)] else l in
    let u = translate_int ren tra a e isparam upper in
    let u = if lstrict then Plus [u; (Value (-1))] else u in
    let newisparam y = if y = x then false else isparam x in
    Quantifier (true, x, l, u, translate_bool ren tra a e newisparam form)
  | Term.Exists (x, form) ->
    let ((lower, lstrict), (upper, ustrict), form) =
      Smtquantifiers.existential_range x a form in
    let l = translate_int ren tra a e isparam lower in
    let l = if lstrict then Plus [l; (Value 1)] else l in
    let u = translate_int ren tra a e isparam upper in
    let u = if lstrict then Plus [u; (Value (-1))] else u in
    let newisparam y = if y = x then false else isparam x in
    Quantifier (false, x, l, u, translate_bool ren tra a e newisparam form)
;;

(*****************************************************************************)
(* interfacing with a real SMT-solver                                        *)
(*****************************************************************************)

(* makes an SMT-input style description of the given intexpression *)
let rec make_smt_expression = function
  | Value k -> string_of_int k
  | Plus lst -> "(+ " ^ (List.implode make_smt_expression " " lst) ^ ")"
  | Times lst -> "(* " ^ (List.implode make_smt_expression " " lst) ^ ")"
  | Ite (form, expr1, expr2) ->
    ("(ite " ^ (make_smt_formula form) ^ " " ^
               (make_smt_expression expr1) ^ " " ^
               (make_smt_expression expr2) ^ ")") 
  | Div (x, y) -> "(div " ^ (make_smt_expression x) ^ " " ^
                            (make_smt_expression y) ^ ")"
  | Mod (x, y) -> "(mod " ^ (make_smt_expression x) ^ " " ^
                            (make_smt_expression y) ^ ")"
  | IntVar (_, x) -> tostr_var x
  | UnknownExp (context, exprs, forms) ->
    make_smt_context exprs forms context

(* makes an SMT-input style description of the given intformula *)
and make_smt_formula = function
  | And lst | AndWithDefs (_, lst) ->
    "(and " ^ (List.implode make_smt_formula " " lst) ^ ")"
  | Or lst | OrWithUndefs (_, lst) ->
    "(or " ^ (List.implode make_smt_formula " " lst) ^ ")"
  | Geq (x,y) -> "(>= " ^ (make_smt_expression x) ^ " " ^
                          (make_smt_expression y) ^ ")"
  | Equal (x,y) -> "(= " ^ (make_smt_expression x) ^ " " ^
                           (make_smt_expression y) ^ ")"
  | Unequal (x,y) -> "(not (= " ^ (make_smt_expression x) ^ " " ^
                                  (make_smt_expression y) ^ "))"
  | BoolVar (true, _)  -> failwith ("Error in validity solver, " ^
             "global variables should be removed *before* make_smt!")
  | BoolVar (false, x) -> tostr_var x
  | Negate f -> "(not " ^ (make_smt_formula f) ^ ")"
  | Xor (f,g) -> "(xor " ^ (make_smt_formula f) ^ " " ^
                           (make_smt_formula g) ^ ")"
  | True -> "true"
  | False -> "false"
  | UnknownPred (context, exprs, forms) ->
    make_smt_context exprs forms context
  | Quantifier (universal, x, lower, upper, form) ->
    let vname = tostr_var x in
    let (quant, andor, c1, c2) =
      if universal then ("forall", "or", ">", "<")
      else ("exists", "and", "<=", ">=")
    in
    "(" ^ quant ^ " ((" ^ vname ^ " Int)) (" ^ andor ^ " (" ^ c1 ^
    " " ^ (make_smt_expression lower) ^ " " ^ vname ^ ") (" ^ c2 ^
    " " ^ (make_smt_expression upper) ^ " " ^ vname ^ ") " ^
    (make_smt_formula form) ^ "))"

(* makes an SMT-input style description of the given context *)
and make_smt_context exprs forms = function
  | OtherVar (false, x) -> tostr_var x
  | OtherVar (true, _) -> failwith ("Error in validity solver, global " ^
                    "variables should be removed *before* make_smt!")
  | Func (f, lst) ->
    let recurse = make_smt_context exprs forms in
    if lst = [] then f
    else "(" ^ f ^ " " ^ (List.implode recurse " " lst) ^ ")"
  | IntExp i -> make_smt_expression (List.nth exprs i)
  | BoolExp i -> make_smt_formula (List.nth forms i)
;;

(* returns all intparams or intvars satisfying f, boolvars and
boolparams satisfying g and other parameters satisfying h in the
given formula *)
let rec get_vars f g h formula =
  let rec unique_sorted = function
    | first :: second :: tail ->
      if first = second then unique_sorted (second :: tail)
      else first :: unique_sorted (second :: tail)
    | lst -> lst
  in
  let unique lst = unique_sorted (move_sort compare lst) in
  let rec get_vars_context context =
    match context with
      | OtherVar (_, x) -> if h context then [x] else []
      | Func (f, lst) -> unique (List.flat_map get_vars_context lst)
      | IntExp _ | BoolExp _ -> []
  in
  let rec get_vars_int expression =
    match expression with
      | IntVar (_, x) -> if f expression then [x] else []
      | Plus args -> unique (List.flat_map get_vars_int args)
      | Times args -> unique (List.flat_map get_vars_int args)
      | Ite (a,b,c) -> unique (List.append (get_vars f g h a)
          (List.append (get_vars_int b) (get_vars_int c)))
      | Div (x, y) | Mod (x, y) ->
        unique (List.flat_map get_vars_int [x;y])
      | Value _ -> []
      | UnknownExp (context, exprs, forms) ->
        (unique (get_vars_context context)) @
        (unique (List.flat_map get_vars_int exprs)) @
        (unique (List.flat_map (get_vars f g h) forms))
  in
  match formula with
    | BoolVar (_,x) -> if g formula then [x] else []
    | And args | AndWithDefs (_, args) ->
      unique (List.flat_map (get_vars f g h) args)
    | Or args | OrWithUndefs (_, args) ->
      unique (List.flat_map (get_vars f g h) args)
    | Negate arg -> get_vars f g h arg
    | Xor (a, b) -> unique (List.flat_map (get_vars f g h) [a;b])
    | Geq (a, b) | Equal (a, b) | Unequal (a, b) ->
      unique (List.flat_map get_vars_int [a;b])
    | True | False -> []
    | UnknownPred (context, exprs, forms) ->
      (unique (get_vars_context context)) @
      (unique (List.flat_map get_vars_int exprs)) @
      (unique (List.flat_map (get_vars f g h) forms))
    | Quantifier (universal, x, lower, upper, form) ->
      let v1 = get_vars_int lower in
      let v2 = get_vars_int upper in
      let f t = match t with
        | IntVar (_, y) -> (x != y) && (f t)
        | _ -> false
      in
      let v3 = get_vars f g h form in
      unique (v1 @ v2 @ v3)
;;

(* returns whether the given integer expression has the given integer
variable *)
let rec has_ivar x expr =
  let getvars = get_vars (const true) (const false) (const false) in
  match expr with
    | IntVar (_, y) -> x = y
    | Plus args | Times args -> List.exists (has_ivar x) args
    | Div (a, b) | Mod (a, b) -> List.exists (has_ivar x) [a;b]
    | Value _ -> false
    | Ite (a,b,c) ->
      (List.exists (has_ivar x) [b;c]) || (List.mem x (getvars a))
    | UnknownExp (context, exprs, forms) ->
      (List.exists (has_ivar x) exprs) ||
      (List.mem x (List.flat_map getvars forms))
;;

(* makes an SMT-input file for the given list of formulas *)
let make_smt_file env parameters formulas logic =
  Externalsolver.create_smt_file env parameters formulas make_smt_formula logic
;;

(* given a satisfiability problem (so no IntVar and BoolVar
occurrences!), passes it on to the given external SMT-solver to
determine the answer *)
let solve_externally env alf satproblem nonlinear quant solvername =
  let params = get_vars (const true) (const true) (const true) satproblem in
  let problems = ( match satproblem with
    | And lst | AndWithDefs (_, lst) -> lst
    | _ -> [satproblem]
  ) in
  let logic =
    if nonlinear then (
      if quant then "UFNIA"  (* non-linear, quantifiers *)
      else "QF_NIA"          (* non-linear, no quantifiers *)
    )
    else (
      if quant then "AUFLIA" (* linear, quantifiers *)
      else "QF_LIA"          (* linear, no quantifiers *)
    )
  in
  let text = make_smt_file env params problems logic in
  Externalsolver.check_smt_file_and_parse text solvername env alf
;;

(*****************************************************************************)
(* calculating expressions and formulas                                      *)
(*****************************************************************************)

let rec calculate_expression subst expression =
  let recurse = calculate_expression subst in
  match expression with
    | Value k -> k
    | Plus exprs -> List.fold_left (+) 0 (List.map recurse exprs)
    | Times exprs -> List.fold_left ( * ) 1 (List.map recurse exprs)
    | Div (a, b) -> (recurse a) / (recurse b)
    | Mod (a, b) -> (recurse a) mod (recurse b)
    | Ite (c, a, b) -> if calculate_formula subst c then recurse a
                       else recurse b
    | IntVar (univ, x) ->
      ( try List.assoc x subst
        with Not_found ->
          if not univ then 0 else
          failwith ("Cannot calculate expression containing " ^
                    "universally quantified variables!")
      )
    | UnknownExp _ -> failwith ("Cannot calculate expression containing " ^
                                "anonymous functions!")

and calculate_formula subst formula =
  let recurse = calculate_formula subst in
  let erecurse = calculate_expression subst in
  match formula with
    | True -> true
    | False -> false
    | And forms | AndWithDefs (_, forms) ->
      List.for_all id (List.map recurse forms)
    | Or forms | OrWithUndefs (_, forms) ->
      List.exists id (List.map recurse forms)
    | Geq (a, b) -> (erecurse a) >= (erecurse b)
    | Equal (a, b) -> (erecurse a) = (erecurse b)
    | Unequal (a, b) -> (erecurse a) != (erecurse b)
    | Xor (a, b) -> if recurse a then not (recurse b) else recurse b
    | Negate form -> not (recurse form)
    | BoolVar (false,_) -> false
    | BoolVar (true,_) -> failwith ("Cannot calculate formula containing " ^
                             "universally quantified (boolean) variables!")
    | UnknownPred _ -> failwith ("Cannot calculate expression containing " ^
                                 "anonymous predicates!")
    | Quantifier (universal, x, lower, upper, form) ->
      let l = erecurse lower in
      let u = erecurse upper in
      let checkval k = calculate_formula ((x,k) :: subst) form in
      let ran = List.range l (u + 1) in
      if universal then List.for_all checkval ran
      else List.exists checkval ran
;;

let calculate term rens transes a e =
  let sort = Sort.to_string (Term.get_sort a e term) in
  if sort = "Bool" then (
    let formula = translate_bool rens transes a e (const true) term in
    let f =
      if calculate_formula [] formula then Alphabet.get_top_symbol
      else Alphabet.get_bot_symbol
    in
    try Term.make_function a e (f a) []
    with Not_found -> failwith ("Top and bottom symbols must be " ^
      "marked as specific symbols in the alphabet to use internal " ^
      "calculation!")
  )
  else if sort = "Int" then (
    let expr = translate_int rens transes a e (const true) term in
    let k = Function.integer_symbol (calculate_expression [] expr) in
    Term.make_function a e k []
  )
  else parsefail ("integer solver cannot handle sort " ^ sort)
;;

let trivial_test term rens transes a e =
  let formula = translate_bool rens transes a e (const true) term in
  calculate_formula [] formula
;;

let get_value sort alf =
  let sortstring = Sort.to_string sort in
  let isort =
    try Sort.to_string (Alphabet.integer_sort alf)
    with Not_found -> ""
  in
  if sortstring = isort then (
    let k = Random.int (Random.int 1000000) in
    let mk = if Random.bool () then k else -k in
    let f = Function.integer_symbol mk in
    Term.make_fun f []
  )
  else if sortstring = Sort.to_string Alphabet.boolsort then (
    let f =
      try
        if Random.bool () then Alphabet.get_top_symbol alf
        else Alphabet.get_bot_symbol alf
      with Not_found -> failwith ("Cannot use internal get_value " ^
                                  "if top/bottom symbol is not set!")
    in
    Term.make_fun f []
  )
  else parsefail ("Cannot find a value of sort " ^ sortstring)
;;

(*****************************************************************************)
(* simplifying formulas                                                      *)
(*****************************************************************************)

(* helping function for find_sub_exp, separate only for polymorphism;
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
  let rec find_sub_expr_in = function
    | And args | Or args | AndWithDefs (_, args) | OrWithUndefs (_, args) ->
      find_first find_sub_expr_in 0 args
    | Geq (arg1, arg2) | Equal (arg1, arg2) | Unequal (arg1, arg2) ->
      find_first (find_sub_expr checker deep) 0 [arg1;arg2]
    | Negate arg ->
      find_first find_sub_expr_in 0 [arg]
    | Xor (arg1, arg2) ->
      find_first find_sub_expr_in 0 [arg1;arg2]
    | UnknownPred (_, arg1, arg2) -> handle_unknown arg1 arg2
    | Quantifier (universal, x, lower, upper, form) ->
      let answer = find_first (find_sub_expr checker deep) 0 [lower;upper] in
      if answer <> None then answer
      else find_first find_sub_expr_in 2 [form]
    | _ -> None
  and handle_unknown arg1 arg2 =
    let answer = find_first (find_sub_expr checker deep) 0 arg1 in
    if answer <> None then answer
    else find_first find_sub_expr_in (List.length arg1) arg2
  in
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
    | Div (x, y) | Mod (x, y) -> checkargs [x;y]
    | Ite (cond, cif, celse) -> (
      match find_first (find_sub_expr checker deep) 1 [cif;celse] with
        | None -> (
            match find_sub_expr_in cond with
              | None ->
                if deep && (checker expression) then
                  Some ([], expression)
                else None
              | Some (pos, expr) -> Some (0::pos, expr)
          )
        | result -> result
    )
    | UnknownExp (_, arg1, arg2) -> handle_unknown arg1 arg2
    | _ ->
      if deep && (checker expression) then Some ([], expression)
      else None
;;

(* replaces the sub-expression at the given position *)
let rec replace_sub_expr pos replacement expression =
  let replace_num_expr i j arg restpos =
    if i = j then replace_sub_expr restpos replacement arg else arg
  in
  let rec replace_num_form i j arg restpos =
    if i = j then replace_sub_expr_in arg restpos else arg
  and replace_sub_expr_in formula pos =
    let (hd,tl) = match pos with
      | [] -> parsefail "asked to replace expression at formula position"
      | hd :: tl -> (hd, tl)
    in
    let repf j arg = replace_num_form hd j arg tl in
    let repe j arg = replace_num_expr hd j arg tl in
    match formula with
      | And args -> And (List.mapi repf args)
      | Or args -> Or (List.mapi repf args)
      | Negate arg -> Negate (repf 0 arg)
      | Xor (arg1, arg2) -> Xor (repf 0 arg1, repf 1 arg2)
      | Geq (arg1, arg2) -> Geq (repe 0 arg1, repe 1 arg2)
      | Equal (arg1, arg2) -> Equal (repe 0 arg1, repe 1 arg2)
      | Unequal (arg1, arg2) -> Unequal (repe 0 arg1, repe 1 arg2)
      | AndWithDefs _ | OrWithUndefs _ ->
        failwith "replace_sub_expr should not be called when deep simplifying!"
      | UnknownPred (c, arg1, arg2) ->
        let len = List.length arg1 in
        let repfplus j arg = replace_num_form hd (j + len) arg tl in
        UnknownPred (c, List.mapi repe arg1, List.mapi repfplus arg2)
      | Quantifier (universal, x, lower, upper, form) ->
        Quantifier (universal, x, repe 0 lower, repe 1 upper,
                    repf 2 form)
      | _ -> formula
  in
  let mpair maker = function
    | [x;y] -> maker x y
    | _ -> failwith "mpair with not a pair!"
  in
  match pos with
    | [] -> replacement
    | i :: tail -> (
      let repf j arg = replace_num_form i j arg tail in
      let repe j arg = replace_num_expr i j arg tail in
      match expression with
        | Plus args -> Plus (List.mapi repe args)
        | Times args -> Times (List.mapi repe args)
        | Div (a, b) -> mpair (fun x y -> Div (x,y)) (List.mapi repe [a;b])
        | Mod (a, b) -> mpair (fun x y -> Mod (x,y)) (List.mapi repe [a;b])
        | Ite (cond, cif, celse) ->
          Ite (repf 0 cond, repe 1 cif, repe 1 celse)
        | UnknownExp (c, arg1, arg2) ->
          let len = List.length arg1 in
          let repfplus j arg = replace_num_form i (j + len) arg tail in
          UnknownExp (c, List.mapi repe arg1, List.mapi repfplus arg2)
        | _ -> expression
    )
;;

(* removes any occurrence of Ite from the given formula *)
let rec ditch_ite formula =
  let isite = function | Ite _ -> true | _ -> false in
  let parts = function
    | Ite (cond, cif, celse) -> (cond, cif, celse)
    | _ -> failwith "ite occurrence not actually ite!"
  in
  let replacement iteexpr maker =
    let (cond, cif, celse) = parts iteexpr in
    let ifform = maker cif in
    let elseform = maker celse in
    let form = Or [And [cond; ifform]; And [Negate cond; elseform]] in
    ditch_ite form
  in
  let expression_pair a b builder =
    match find_sub_expr isite false a with
      | None -> ( match find_sub_expr isite false b with
        | None -> builder a b
        | Some (pos, expr) ->
          let maker nexpr = builder a (replace_sub_expr pos nexpr b) in
          replacement expr maker
        )
      | Some (pos, expr) ->
        let maker nexpr = builder (replace_sub_expr pos nexpr a) b in
        replacement expr maker
  in
  match formula with
    | And args -> And (List.map ditch_ite args)
    | Or args -> Or (List.map ditch_ite args)
    | Negate arg -> Negate (ditch_ite arg)
    | Xor (a,b) -> Xor (ditch_ite a, ditch_ite b)
    | UnknownPred (cond, exprs, forms) ->
      let forms = List.map ditch_ite forms in
      let rec first i = function
        | [] -> None
        | hd :: tl -> match find_sub_expr isite false hd with
          | None -> first (i+1) tl
          | Some (pos, expr) -> Some (i, pos, expr)
      in
      ( match first 0 exprs with
        | None -> UnknownPred (cond, exprs, forms)
        | Some (i, pos, expr) ->
          let maker nexpr =
            let (a, b) = List.split_at i exprs in
            let (q, c) = (List.hd b, List.tl b) in
            let newexpr = replace_sub_expr pos nexpr q in
            let newexprs = a @ (newexpr :: c) in
            UnknownPred (cond, newexprs, forms)
          in
          replacement expr maker
      )
    | Geq (a,b) | Equal (a, b) | Unequal (a, b) ->
      let builder x y =
        match formula with
          | Geq _ -> Geq (x,y)
          | Equal _ -> Equal (x,y)
          | _ -> Unequal (x,y)
      in
      expression_pair a b builder
    | Quantifier (universal, x, lower, upper, form) ->
      let builder y z = Quantifier (universal, x, y, z, ditch_ite form) in
      expression_pair lower upper builder
    | AndWithDefs _ | OrWithUndefs _ ->
      failwith "ditch_ite should not be called when deep simplifying"
    | _ -> formula
;;

(* removes any occurrence of div and mod from the formula, replacing
it by fresh variables which come with their own constraints; returns
both the variables which were introduced and the new formula;
satisfiability is set to true if the nearest quantifier above the
formula is existential; or, if there is no quantifier above, we are
only trying to make a satisfiability problem (so no universally
quantified variables occur) *)
let rec ditch_division formula env alf satisfiability =
  let recurse lst builder =
    let recursion f = ditch_division f env alf satisfiability in
    let args = List.map recursion lst in
    let vars = List.flat_map fst args in
    let newargs = List.map snd args in
    (vars, builder newargs)
  in
  let fn = Alphabet.fun_names alf in
  let intsort = Sort.from_string "Int" in
  let freshvar _ = Environment.create_sorted_var intsort fn env in
  let varmaker x = IntVar (not satisfiability, x) in
  (* IF y <> 0,
     THEN x = y * (x div y) + (x mod y)
     AND 0 <= x mod y < abs y *)
  let fix_division = function
    | Div (x, y) ->
      (* for division, this means that:
      z = x div y <==>
      y * z <= x < y * z + abs(y) <==>
      y * z <= x /\ (y > 0 => x < y * z + y) /\ (y < 0 => x < y * z - y) *)
      let z = freshvar () in
      let zvar = varmaker z in
      let (form1, form2, form3) =
        if satisfiability then
          ( Geq (x, Times [zvar; y]),
            Or [Geq (Value 0, y); Geq (Plus [Times [y;zvar];y;Value (-1)], x)],
            Or [Geq (y, Value 0); Geq (Times [y;zvar], Plus [x;y;Value 1])]
          )
        else
          ( Geq (Times [y;zvar], Plus [x;Value 1]),
            And [Geq (y, Value 1); Geq (x, Plus [Times [y;zvar];y])],
            And [Geq (Value (-1), y); Geq (Plus [x;y], Times [y;zvar])]
          )
      in
      ([z], [form1; form2; form3], zvar)
    | Mod (x, y) ->
      (* for modulo, we implement division as well: w and z are the
      unique values such that x = y * w + z and 0 <= z < abs(y) *)
      let w = freshvar () in
      let z = freshvar () in
      let wvar = varmaker w in
      let zvar = varmaker z in
      let (form1, form2, form3, form4) =
        if satisfiability then
          ( Equal (x, Plus [Times [y;wvar]; zvar]),
            Geq (zvar, Value 0),
            Or [Geq (Value 0, y); Geq (y, Plus [zvar; Value 1])],
            Or [Geq (y, Value 0); Geq (Value (-1), Plus [y;zvar])]
          )
        else
          ( Unequal (x, Plus [Times [y;wvar]; zvar]),
            Geq (Value (-1), zvar),
            And [Geq (y, Value 1); Geq (zvar, y)],
            And [Geq (Value (-1), y); Geq (Plus [y;zvar], Value 0)]
          )
      in
      ([w;z], [form1;form2;form3], zvar)
    | other -> ([], [], other)
  in
  let expression_pair a b builder =
    let isdivision = function
      | Div _ | Mod _ -> true
      | _ -> false
    in
    let repeat newvars newform =
      let (nv, final) = ditch_division newform env alf satisfiability in
      (newvars @ nv, final)
    in
    let fullform cforms formula =
      if satisfiability then And (formula :: cforms)
      else Or (formula :: cforms)
    in
    match find_sub_expr isdivision true a with
      | None -> ( match find_sub_expr isdivision true b with
          | None -> ([], builder a b)
          | Some (pos, expr) ->
            let (newvars, newforms, newexpr) = fix_division expr in
            let newform = builder a (replace_sub_expr pos newexpr b) in
            repeat newvars (fullform newforms newform)
        )
      | Some (pos, expr) ->
        let (newvars, newforms, newexpr) = fix_division expr in
        let newform = builder (replace_sub_expr pos newexpr a) b in
        repeat newvars (fullform newforms newform)
  in
  match formula with
    | And args -> recurse args (fun l -> And l)
    | Or args -> recurse args (fun l -> Or l)
    | Negate arg -> recurse [arg] (fun l -> Negate (List.hd l))
    | Xor (a,b) -> recurse [a;b]
      (fun l -> Xor (List.hd l, List.hd (List.tl l)))
    | Geq (a,b) | Equal (a,b) | Unequal (a,b) ->
      let builder x y =
        match formula with
          | Geq _ -> Geq (x,y)
          | Equal _ -> Equal (x,y)
          | _ -> Unequal (x,y)
      in
      expression_pair a b builder
    | Quantifier (universal, x, lower, upper, form) ->
      let (vars, newform) = ditch_division form env alf (not universal) in
      if (vars <> []) && (satisfiability = universal) then
        failwith ("Cannot currently handle division or modulo below " ^
                  "a quantifier.  Please alter the formula.") ;
        (* The problem being, this would lead to a quantification over
        the new variable which isn't necessarily bounded; Mod is
        actually not a problem, but Div is.  To handle this, we would
        need to treat Div in a different way, taking all its possible
        contexts into account. *)
      let builder l u = Quantifier (universal, x, l, u, newform) in
      let (vs, result) = expression_pair lower upper builder in
      (vars @ vs, result)
    | UnknownPred (cond, _, _) ->
      parsefail ("Occurrence of unknown symbol in predicate; " ^
                 "should not get to ditch_division given an " ^
                 "unusual logic!")
        (* there is actually no reason not to do this, but at the
        moment we don't need to do this *)
    | AndWithDefs _ | OrWithUndefs _ ->
      failwith "ditch_division should not be called when deep simplifying"
    | _ -> ([], formula)
;;

(* replaces all boolean variables by integer variables, so we have
fewer cases (they are easily converted back) *)
let rec ditch_boolvars formula =
  match formula with
    | BoolVar (univ, x) -> Unequal (IntVar (univ, x), Value 0)
    | And lst -> And (List.map ditch_boolvars lst)
    | Or lst -> Or (List.map ditch_boolvars lst)
    | Negate x -> Negate (ditch_boolvars x)
    | Xor (x, y) -> Xor (ditch_boolvars x, ditch_boolvars y)
    | Quantifier (universal, x, lower, upper, form) ->
      Quantifier (universal, x, lower, upper, ditch_boolvars form)
    | UnknownPred (cond, exprs, forms) ->
      UnknownPred (cond, exprs, List.map ditch_boolvars forms)
    | AndWithDefs _ | OrWithUndefs _ ->
      failwith "ditch_boolvars should not be called when deep simplifying"
    | _ -> formula
;;

(* removes all occurrences of Xor from the given formula, replacing
them by conjunctions if conj is true, or disjunctions otherwise *)
let rec ditch_xor conj formula =
  let translation = match formula with
    | Xor (x, y) ->
      if conj then And [Or [x; y]; Or [Negate x; Negate y]]
      else Or [And [x; Negate y]; And [Negate x; y]]
    | _ -> formula
  in
  match translation with
    | And lst -> And (List.map (ditch_xor conj) lst)
    | Or lst -> Or (List.map (ditch_xor conj) lst)
    | Negate x -> Negate (ditch_xor (not conj) x)
    | UnknownPred (cond, exprs, forms) ->
      UnknownPred (cond, exprs, List.map (ditch_xor conj) forms)
    | Quantifier (universal, x, lower, upper, form) ->
      Quantifier (universal, x, lower, upper, ditch_xor conj form)
    | AndWithDefs _ | OrWithUndefs _ ->
      failwith "ditch_xor should not be called when deep simplifying"
    | _ -> translation
;;

(* sort the arguments of a plus or times *)
let sort_integer_arguments lst =
  let rec expression_size = function
    | Value k -> [(0, k)]
    | IntVar (univ, x) -> [((if univ then 2 else 1), Variable.to_int x)]
    | Plus args ->
      (3, 0) :: List.flat_map id (List.rev_map expression_size args)
    | Times args ->
      List.flat_map id (List.rev_map expression_size args)
    | _ -> [(4, 0)]
  in
  let comparetuple (a1,b1) (a2,b2) =
    if a1 = a2 then compare b1 b2 else compare a1 a2
  in
  let rec comparelist lst1 lst2 =
    if (lst1 = []) then ( if lst2 = [] then 0 else -1 ) else
    if lst2 = [] then 1 else
    let (hd1, tl1) = (List.hd lst1, List.tl lst1) in
    let (hd2, tl2) = (List.hd lst2, List.tl lst2) in
    let comparison = comparetuple hd1 hd2 in
    if comparison = 0 then compare tl1 tl2 else comparison
  in
  let compare x y =
    comparelist (expression_size x) (expression_size y)
  in
  List.sort compare lst
;;

(* simplifies an integer expression (not particularly efficient
unless ite-, div-, mod- and unknown-free *)
let rec simplify_int expression =
  match expression with 
    | Plus lst -> simplify_plus (List.map simplify_int lst)
    | Times lst -> simplify_times (List.map simplify_int lst)
    | Div (a, b) -> Div (simplify_int a, simplify_int b)
    | Mod (a, b) -> Mod (simplify_int a, simplify_int b)
    | Ite (c, a, b) -> Ite (simplify_ints_in c, simplify_int a,
                            simplify_int b)
    | UnknownExp (cond, exprs, forms) ->
      UnknownExp (cond, List.map simplify_int exprs,
                  List.map simplify_ints_in forms)
    | Value _ | IntVar _ -> expression

(* simplify an integer expression Plus args; all elements of args
are already assumed to be simplified *)
and simplify_plus args =
  let flatten_plus = function | Plus lst -> lst | expr -> [expr] in
  let lst = List.flat_map flatten_plus args in
  let lst = sort_integer_arguments lst in
  let checktimes = function
    | Times (Value 0 :: _) -> []
    | whatever -> [whatever]
  in
  let rec merge_parts = ( function
    | [] -> []
    | [single] -> [single]
    | (Value 0) :: rest -> merge_parts rest 
    | (Value x) :: (Value y) :: rest ->
      merge_parts ((Value (x+y)) :: rest)
    | (Value x) :: rest -> (Value x) :: merge_parts rest 
    | first :: second :: tail -> ( 
      let isvar = function | IntVar _ -> true | _ -> false in
      if (first = second) && (isvar first) then 
        merge_parts ((Times [Value 2; first]) :: tail)
      else let continue _ = first :: merge_parts (second :: tail) in
      match (first, second) with 
        | (Times (Value n :: x), Times (Value m :: y)) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (Times (Value (n+m) :: x))) @ tail)
        | (Times x, Times (Value m :: y)) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (Times (Value (m+1) :: y))) @ tail)
        | (x, Times [Value m; y]) ->
          if x <> y then continue ()
          else merge_parts ((checktimes (Times [Value (m+1); x])) @ tail)
        | _ -> continue ()
    )
  ) in
  match merge_parts lst with
    | [] -> Value 0
    | [single] -> single
    | lst -> Plus lst

(* simplify an integer expression Times args; if toponly is true,
then all elements of args are already assumed to be simplified *)
and simplify_times args =
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
  let finish lst =
    let flatten_times = function | Times lst -> lst | expr -> [expr] in
    let lst = List.flat_map flatten_times lst in
    let lst = sort_integer_arguments lst in
    let lst = merge_parts lst in
    match lst with
      | [] -> Value 1
      | (Value 0) :: _ -> Value 0
      | [single] -> single
      | lst -> Times lst
  in
  let plustosome = function | Plus lst -> Some lst | _ -> None in
  let plusparts = explode_subs plustosome finish args in
  ( match plusparts with
    | [single] -> single
    | args -> simplify_plus (List.map simplify_int args)
  )

(* simplifies all integer expressions in a formula *)
and simplify_ints_in formula =
  match formula with
    | And args -> And (List.map simplify_ints_in args)
    | AndWithDefs (i, args) -> AndWithDefs (i, List.map simplify_ints_in args)
    | Or args -> Or (List.map simplify_ints_in args)
    | OrWithUndefs (i, args) -> OrWithUndefs (i, List.map simplify_ints_in args)
    | Xor (arg1, arg2) -> Xor (simplify_ints_in arg1, simplify_ints_in arg2)
    | Negate arg -> Negate (simplify_ints_in arg)
    | Geq (x,y) -> Geq (simplify_int x, simplify_int y)
    | Equal (x,y) -> Equal (simplify_int x, simplify_int y)
    | Unequal (x,y) -> Unequal (simplify_int x, simplify_int y)
    | UnknownPred (cond, exprs, forms) ->
      UnknownPred (cond, List.map simplify_int exprs,
                   List.map simplify_ints_in forms)
    | Quantifier (universal, x, lower, upper, form) ->
      Quantifier (universal, x, simplify_int lower,
                  simplify_int upper, simplify_ints_in form)
    | _ -> formula
;;

(* handles negation; if the given formula has simplified integers,
then the same holds for its negation *)
let rec negate formula =
  let add_one_to x = simplify_plus [Value 1; x] in
  match formula with
    | Negate x -> x
    | And args -> Or (List.map negate args)
    | AndWithDefs (i, args) -> OrWithUndefs (i, List.map negate args)
    | Or args -> And (List.map negate args)
    | OrWithUndefs (i, args) -> AndWithDefs (i, List.map negate args)
    | True -> False
    | False -> True
    | Geq (a, b) -> Geq (b, add_one_to a)
    | Equal (a, b) -> Unequal (a, b)
    | Unequal (a, b) -> Equal (a, b)
    | Quantifier (universal, x, lower, upper, form) ->
      Quantifier (not universal, x, lower, upper, negate form)
    | _ -> Negate formula
;;

(* returns the product of the given list of terms, which we assume to
already be in simplified and correctly ordered form (so simplify_times
is *not* necessary) *)
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
      if n = 0 then build_is0 equality (Times ((Value k) :: lst))
      else if k = 0 then notequal (* n + 0 = 0 can't hold when n != 0 *)
      else if n mod k <> 0 then notequal
      else build_is0 equality (simplify_plus [Value (n / k); times])
        (* m * k + k x = 0 <=> m + x = 0 *)
    | _ ->
      if equality then Equal (x, Value 0)
      else Unequal (x, Value 0)
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
      else Geq (Times (Value (-1) :: lst), Value 0)
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
      else Geq (x, Value 0)
    | _ -> Geq (x, Value 0)
;;

let make_negative expr = simplify_times [Value (-1); expr];;

(* assuming that a and b are both simplified expressions, returns an
expression representing a - b *)
let subtract a b = simplify_plus [a; make_negative b];;

(* handles very basic simplifications: removing Nots and moving
everything into Geq, Equal and Unqueal to the left-hand side *)
let rec basic_simplify substitution formula =
  let flatten f args =
    List.flat_map f (List.map (basic_simplify substitution) args)
  in
  let handleandor flatt f block empty builder x =
    let lst = flatt f x in
    if List.mem block lst then block
    else if lst = [] then empty
    else if List.tl lst = [] then List.hd lst
    else builder lst
  in
  let recurse = basic_simplify substitution in
  let rec instantiate_expression = function
    | IntVar (_, x) as exp ->
      ( try List.assoc x substitution
        with Not_found -> exp
      )
    | Plus lst -> Plus (List.map instantiate_expression lst)
    | Times lst -> Times (List.map instantiate_expression lst)
    | Div (a,b) -> Div (instantiate_expression a, instantiate_expression b)
    | Mod (a,b) -> Mod (instantiate_expression a, instantiate_expression b)
    | Ite (c,a,b) -> Ite (recurse c, instantiate_expression a,
                          instantiate_expression b)
    | UnknownExp (c, es, fs) ->
        UnknownExp (c, List.map instantiate_expression es,
                       List.map recurse fs)
    | Value k -> Value k
  in
  let handle_compare x y build =
    let x = instantiate_expression x in
    let y = instantiate_expression y in
    build (subtract x y)
  in
  match formula with
    | Negate (BoolVar _) | Negate (Xor _)
    | True | False
    | BoolVar _ -> formula
    | Negate (UnknownPred (cond, exprs, forms)) ->
      let es = List.map instantiate_expression exprs in
      let fs = List.map recurse forms in
      Negate (UnknownPred (cond, es, fs))
    | Negate x -> recurse (negate x)
    | Xor (x, y) -> Xor (recurse x, recurse y)
    | And x ->
      let f = function | And y -> y | True -> [] | z -> [z] in
      handleandor flatten f False True (fun lst -> And lst) x
    | Or x ->
      let f = function | Or y -> y | False -> [] | z -> [z] in
      handleandor flatten f True False (fun lst -> Or lst) x
    | AndWithDefs _ | OrWithUndefs _ ->
      failwith "Unexpected use of basic_simplify when deep simplifying"
    | Geq (x, y) -> handle_compare x y build_geq0
    | Equal (x, y) -> handle_compare x y (build_is0 true)
    | Unequal (x, y) -> handle_compare x y (build_is0 false)
    | UnknownPred (cond, exprs, forms) ->
      let es = List.map instantiate_expression exprs in
      let fs = List.map recurse forms in
      UnknownPred (cond, es, fs)
    | Quantifier (universal, x, lower, upper, form) ->
      let lower = instantiate_expression lower in
      let upper = instantiate_expression upper in
      match (lower, upper) with
        | (Value l, Value u) ->
          let instance k =
            basic_simplify ((x, Value k) :: substitution) form in
          let instances = List.map_range instance l u in
          let flatten f args = List.flat_map f args in
          if universal then (
            let splitter = function | And y -> y | True -> [] | z -> [z] in
            handleandor flatten splitter False True
                        (fun lst -> And lst) instances
          )
          else (
            let splitter = function | Or y -> y | False -> [] | z -> [z] in
            handleandor flatten splitter True False
                        (fun lst -> Or lst) instances
          )
        | _ -> Quantifier (universal, x, lower, upper, recurse form)
;;

(* given a preferably-already-simplified expression, replaces
occurences of x >= y / z by an equivalent div-free statement *)
let rec safe_ditch_division inconj = function
  | True | False | BoolVar _ | Equal _ | Unequal _ as form -> form
  | And lst -> And (List.map (safe_ditch_division true) lst)
  | Or lst -> Or (List.map (safe_ditch_division false) lst)
  | Negate x -> Negate (safe_ditch_division (not inconj) x)
  | Xor (x, y) -> Xor (safe_ditch_division (not inconj) x,
                       safe_ditch_division (not inconj) y)
  | UnknownPred (c, is, fs) ->
    UnknownPred (c, is, List.map (safe_ditch_division true) fs)
  | Quantifier (univ, x, lower, upper, form) ->
    Quantifier (univ, x, lower, upper, safe_ditch_division univ form)
  | AndWithDefs _ | OrWithUndefs _ ->
    failwith "ditch_division should not be called when deep simplifying"
  | Geq (exp, Value 0) ->
    (* note: om the euclidean definition, y div (-z) = - (y div z) *)
    let rec split_divisions divs rest = function
      | [] -> (divs, rest)
      | Div (a,b) :: tail ->
        split_divisions ((a,make_negative b) :: divs) rest tail
      | Times [Value (-1); Div (a,b)] :: tail
      | Times [Div (a,b); Value (-1)] :: tail ->
        split_divisions ((a,b) :: divs) rest tail
      | x :: tail -> split_divisions divs (x :: rest) tail
    in
    let get_single_division = function
      | Div (a,b) -> Some (Value 0, a, make_negative b)
      | Times [Value (-1); Div (a,b)] | Times [Div (a,b); Value (-1)] ->
        Some (Value 0, a, b)
      | Plus lst -> (
          let (divs, rest) = split_divisions [] [] lst in
          match divs with
            | [(a,b)] ->
              Some (simplify_plus (List.rev rest), a, b)
            | _ -> None
        )
      | _ -> None
    in
    ( match get_single_division exp with
      | None -> Geq (exp, Value 0)
      | Some (x, y, z) -> (* expression is: x >= y div z *)
        (* if z = 0, then y div z = 0, so x >= y div z <==> x >= 0 *)
        let zis0 = Geq (x, Value 0) in
        (* if z > 0, then x >= y div z <==> x * z + z - 1 >= y *)
        let xz = simplify_times [x;z] in
        let gexp = simplify_plus [xz; z; Value (-1); make_negative y] in
        let zgreater0 = Geq (gexp, Value 0) in
        (* if z < 0, then x >= y div z <==> x * z <= y *)
        let minxz = simplify_times [Value (-1); x; z] in
        let zsmaller0 = Geq (simplify_plus [y; minxz], Value 0) in
        (* Conjunction? We make the three implications *)
        if inconj then
          And [ Or [ Unequal (z, Value 0); zis0 ];
                Or [ Geq (make_negative z, Value 0); zgreater0 ];
                Or [ Geq (z, Value 0); zsmaller0 ]
              ]
        (* Disjunction? Then, we make three conjunctions *)
        else
          Or [ And [ Equal (z, Value 0); zis0 ];
               And [ Geq (simplify_plus [z; Value (-1)], Value 0);
                     zgreater0 ];
               And [ Geq (subtract (Value (-1)) z, Value 0);
                     zsmaller0 ]
             ]
    )
  | Geq _ as form -> form
;;

(* puts a basically simplified formula without xors, quantifiers,
unknowns or negation (other than perhaps negated boolvars) into
conjunctive normal form; this will not introduce new variables, so
may explode - use with care! *)
let rec conjunctive_form formula =
  match formula with
    | And lst ->
      let args = List.map conjunctive_form lst in
      let flatten_and = function | And lst -> lst | form -> [form] in
      And (List.flat_map flatten_and args)
    | Or lst ->
      let args = List.map conjunctive_form lst in
      let andtosome = function | And lst -> Some lst | _ -> None in
      let finishor args = Or args in
      let andparts = explode_subs andtosome finishor args in
      ( match andparts with
        | [single] -> single
        | parts -> And parts
      )
    | _ -> formula
;;

(* puts a basically simplified formula without xors, quantifiers,
unknowns or negation (other than perhaps negated boolvars) into
disjunctive normal form; this will not introduce new variables, so
may explode - use with care! *)
let rec disjunctive_form formula =
  match formula with
    | Or args ->
      let newargs = List.map disjunctive_form args in
      let flatten_or = function | Or lst -> lst | form -> [form] in
      And (List.flat_map flatten_or newargs)
    | And args ->
      let newargs = List.map disjunctive_form args in
      let ortosome = function | Or lst -> Some lst | _ -> None in
      let finishand args = And newargs in
      let orparts = explode_subs ortosome finishand args in
      ( match orparts with
        | [single] -> single
        | parts -> Or parts
      )
    | _ -> formula
;;

(*****************************************************************************)
(* instantiating (simplified) formulas and expressions                       *)
(*****************************************************************************)

(*
(* applies the given int-substitution (a list of variable / value
mappings) and formula-substitution (similar, but mapping to
intformulas) to the given expression or formula; if param is true,
then parameters only are instantiated, otherwise variables only *)
let rec instantiate_expression param isub fsub expression =
  let induction e = instantiate_expression param isub fsub e in
  match expression with
    | Value k -> expression
    | Plus lst -> Plus (List.map induction lst)
    | Times lst -> Times (List.map induction lst)
    | Div (expr1, expr2) -> Div (induction expr1, induction expr2)
    | Mod (expr1, expr2) -> Mod (induction expr1, induction expr2)
    | Ite (formula, expr1, expr2) ->
      Ite (instantiate_formula param isub fsub formula,
           induction expr1, induction expr2)
    | IntVar x ->
      if param then expression else
      ( try List.assoc x isub
        with Not_found -> expression
      )
    | IntParam x ->
      if (not param) then expression else
      try List.assoc x isub
      with Not_found -> expression

and instantiate_formula param isub fsub formula =
  let induction f = instantiate_formula param isub fsub f in
  let einduction e = instantiate_expression param isub fsub e in
  match formula with
    | True | False -> formula
    | And lst -> And (List.map induction lst)
    | Or lst -> Or (List.map induction lst)
    | Geq (x,y) -> Geq (einduction x, einduction y)
    | Equal (x,y) -> Equal (einduction x, einduction y)
    | Unequal (x,y) -> Unequal (einduction x, einduction y)
    | Negate f -> Negate (induction f)
    | Xor (f,g) -> Xor (induction f, induction g)
    | BoolVar x ->
      if param then formula else
      ( try List.assoc x fsub
        with Not_found -> formula
      )
    | BoolParam x ->
      if (not param) then formula else
      try List.assoc x fsub
      with Not_found -> formula
;;
*)

(* helping function for instantiate_expression and instantiate_formula *)
let instantiate_all induction builder lst =
  let instantiated = List.map induction lst in
  let newargs = List.map fst instantiated in
  let changed = List.exists snd instantiated in
  (builder newargs changed, changed)
;;

(* applies the given int-substitution (a list of variable / value
mappings) and formula-substitution (similar, but mapping to
intformulas) to the given expression or formula; we assume that the
expression and the output of all substitutions are in simplified
form, and return an expression which is also simplified *)
let rec instantiate_expression isub fsub expression repeat =
  let induction e = instantiate_expression isub fsub e repeat in
  let finduction form = instantiate_formula isub fsub form repeat in
  let substituted answer =
    if repeat then (fst (induction answer), true)
    else (answer, true)
  in
  match expression with
    | Value k -> (expression, false)
    | IntVar (_, x) ->
      ( try substituted (List.assoc x isub)
        with Not_found -> (expression, false)
      )
    | Plus lst ->
      let builder args changed =
        if changed then simplify_plus args
        else Plus args
      in
      instantiate_all induction builder lst
    | Times lst ->
      let builder args changed =
        if changed then simplify_times args
        else Times args
      in
      instantiate_all induction builder lst
    | Div (x, y) ->
      let builder args _ =
        match args with
          | [Value n; Value m] ->
            if m <> 0 then Value (n / m)
            else Div (List.hd args, List.hd (List.tl args))
          | _ -> Div (List.hd args, List.hd (List.tl args))
      in
      instantiate_all induction builder [x;y]
    | Mod (x, y) ->
      let builder args _ =
        match args with
          | [Value n; Value m] ->
            if m <> 0 then Value (n mod m)
            else Mod (List.hd args, List.hd (List.tl args))
          | _ -> Mod (List.hd args, List.hd (List.tl args))
      in
      instantiate_all induction builder [x;y]
    | Ite (c, x, y) ->
      ( match finduction c with
          | (True, _) -> let (a, _) = induction x in (a, true)
          | (False, _) -> let (a, _) = induction y in (a, true)
          | (whatever, c1) ->
            let (a, c2) = induction x in
            let (b, c3) = induction y in
            (Ite (whatever, a, b), c1 || c2 || c3)
      )
    | UnknownExp (c, es, fs) ->
      let esind = List.map induction es in
      let fsind = List.map finduction fs in
      let changed = (List.exists snd esind) || (List.exists snd fsind) in
      (UnknownExp (c, List.map fst esind, List.map fst fsind), changed)

and instantiate_formula isub fsub formula repeat =
  let induction f = instantiate_formula isub fsub f repeat in
  let einduction e = instantiate_expression isub fsub e repeat in
  let handle_comparison x builder =
    let (instantiated, changed) = einduction x in
    if changed then (builder instantiated, true)
    else (formula, false)
  in
  let rec make_andor block trivial n k sofar flatten builder = function
    | [] -> builder n (List.rev sofar)
    | head :: tail ->
      if head = block then block
      else if k < n then (
        if head = trivial then
          make_andor block trivial (n-1) k sofar flatten builder tail
        else make_andor block trivial n (k+1) (head :: sofar) flatten
                                      builder tail
      ) else
      let sofar = List.rev_append (flatten head) sofar in
      make_andor block trivial n k sofar flatten builder tail
  in
  let handle_and i lst makeand =
    let flatten = function
      | And x -> x | AndWithDefs (_, x) -> x | True -> [] | x -> [x]
    in
    let builder args changed =
      if changed then make_andor False True i 0 [] flatten makeand args
      else makeand i args
    in
    instantiate_all induction builder lst
  in
  let handle_or i lst makeor =
    let flatten = function
      | Or x -> x | OrWithUndefs (_, x) -> x | False -> [] | x -> [x]
    in
    let builder args changed =
      if changed then make_andor True False i 0 [] flatten makeor args
      else makeor i args
    in
    instantiate_all induction builder lst
  in
  let substituted answer =
    if repeat then (fst (induction answer), true)
    else (answer, true)
  in
  match formula with
    | True | False -> (formula, false)
    | BoolVar (_, x) ->
      ( try substituted (List.assoc x fsub)
        with Not_found -> (formula, false)
      )
    | Geq (x, Value 0) -> handle_comparison x build_geq0
    | Equal (x, Value 0) -> handle_comparison x (build_is0 true)
    | Unequal (x, Value 0) -> handle_comparison x (build_is0 false)
    | AndWithDefs (i, lst) -> handle_and i lst (fun k x -> AndWithDefs (k, x))
    | And lst -> handle_and 0 lst (fun _ x -> And x)
    | OrWithUndefs (i, lst) -> handle_or i lst (fun k x -> OrWithUndefs (k, x))
    | Or lst -> handle_or 0 lst (fun _ x -> Or x)
    | Negate f ->
      let (instantiated, changed) = induction f in
      if changed then (negate instantiated, true)
      else (formula, false)
    | Xor (f, g) ->
      let (fin, chf) = induction f in
      let (gin, chg) = induction g in
      (Xor (fin, gin), chf || chg)
    | Quantifier (universal, x, lower, upper, form) ->
      let (ll, c1) = einduction lower in
      let (uu, c2) = einduction upper in
      ( match (ll, uu) with
        | (Value l, Value u) ->
          let instance k = fst (instantiate_formula ((x, Value k) ::
                                isub) fsub form repeat) in
          let instances = List.map_range instance l u in
          if universal then (
            let flatten = function
              | And x -> x | AndWithDefs (_, x) -> x | True -> [] | x -> [x]
            in
            let makeand _ lst = And lst in
            ( make_andor False True 0 0 [] flatten makeand instances, true )
          )
          else (
            let flatten = function
              | Or x -> x | OrWithUndefs (_, x) -> x | False -> [] | x -> [x]
            in
            let makeor _ lst = Or lst in
            ( make_andor True False 0 0 [] flatten makeor instances, true )
          )
        | _ ->
          let (iform, c3) = induction form in
          (Quantifier (universal, x, ll, uu, iform), c1 || c2 || c3)
      )
    | UnknownPred (c, es, fs) ->
      let esind = List.map einduction es in
      let fsind = List.map induction fs in
      let changed = (List.exists snd esind) || (List.exists snd fsind) in
      (UnknownPred (c, List.map fst esind, List.map fst fsind), changed)
    (* unusual (basic_simplify SHOULD have taken care of this) *)
    | Geq (x, y) -> handle_comparison (subtract x y) build_geq0
    | Equal (x, y) -> handle_comparison (subtract x y) (build_is0 true)
    | Unequal (x, y) -> handle_comparison (subtract x y) (build_is0 false)
;;

(*****************************************************************************)
(* solving problem represented as intformulae                                *)
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

(* calculates positive + negative - extra *)
let calculate_triple (positive, negative, extra) =
  let make_negative expression = simplify_times [Value (-1); expression] in
  let posargs = if extra = 0 then positive else (Value extra) :: positive in
  let negargs = List.map make_negative negative in
  let args = List.append posargs negargs in
  simplify_plus args
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
  | Negate (BoolVar _) -> true
  | And _ | AndWithDefs _ | Or _ | OrWithUndefs _ | Xor _ | Negate _
    | UnknownPred _ | Quantifier _ -> false
  | _ -> true
;;

(* checks whether the first given formula implies the second (this
obviously admits false negatives) *)
let implies form1 form2 =
  match (form1, form2) with
    | (Unequal (x, Value 0), Unequal (y, Value 0)) ->
      x = y
        (* x <> 0 ==> x <> 0 *)
    | (Geq (x, Value 0), Geq (y, Value 0)) -> atleast0 ([y],[x],0)
        (* x >= 0 ==> y >= 0 certainly if y >= x, so if y-x >= 0 *)
    | (Geq (x, Value 0), Unequal (y, Value 0)) ->
        atmost0 ([y;x],[],1) || atmost0 ([x],[y],1)
        (* x >= 0 /\ y = 0 cannot hold together if x+y or x-y < 0 *)
    | (Equal (x, Value 0), Geq (y, Value 0)) ->
      atleast0 ([y],[x],0) || atleast0 ([y;x],[],0)
        (* x = k ==> y >= 0 if y + N * x >= 0 *)
    | (Equal (x, Value 0), Equal (y, Value 0)) ->
      exactly0 ([y],[x],0) || exactly0 ([y;x],[],0)
        (* x = 0 ==> y = 0 if x = y, or y + N * x = 0 *)
    | (Equal (x, Value 0), Unequal (y, Value 0)) ->
      notexactly0 ([y],[x],0) || notexactly0 ([y;x],[],0)
        (* x = 0 ==> y != 0 if y + N * x != 0 *)
    | _ -> false
;;

(* checks whether the given formula together imply falsehood *)
let inconsistent form1 form2 =
  match form1 with
    | Equal (x, Value 0) -> implies form2 (Unequal (x, Value 0))
    | Geq (x, Value 0) ->
      let negx = simplify_times [Value (-1); x] in
      let negated = Geq (simplify_plus [Value (-1); negx], Value 0) in
      implies form2 negated
    | Unequal (x, Value 0) -> implies form2 (Equal (x, Value 0))
    | _ -> false
;;

(* checks whether the given formulas together always hold *)
let alwaystogether form1 form2 =
  match (form1, form2) with
    | (Unequal (x, Value 0), form) | (form, Unequal (x, Value 0)) ->
      implies (Equal (x, Value 0)) form
    | (Geq (x, Value 0), Geq (y, Value 0)) -> atleast0 ([x;y],[],1)
    | _ -> false
;;

(* returns a list of formulas, one of which must be satisfied for
form1 and form2 to be always true together (has false negatives) *)
let always_together_formula form1 form2 =
  (* helping function for equality_implication *)
  let compare f x y =
    [f (calculate_triple ([y],[x],0), Value 0);
     f (calculate_triple ([y;x],[],0), Value 0)
    ]
  in
  (* equality_impliciation x form returns the requirements for
  x = 0 ==> form *)
  let equality_implication x = function
    | Geq (y, Value 0) -> compare (fun (a,b) -> Geq (a,b)) x y
    | Equal (y, Value 0) -> compare (fun (a,b) -> Equal (a,b)) x y
    | Unequal (y, Value 0) -> compare (fun (a,b) -> Unequal (a,b)) x y
    | _ -> []
  in
  (* main part *)
  match (form1, form2) with
    | (Unequal (x, Value 0), form) | (form, Unequal (x, Value 0)) ->
      equality_implication x form
    | (Geq (x, Value 0), Geq (y, Value 0)) ->
      [Geq (calculate_triple ([x;y],[],1), Value 0)]
    | _ -> []
;;

(* given both form1 and form2, find a simpler formula that implies
both *)
let improve_conjunction form1 form2 =
  match (form1, form2) with
    | (Geq (x, Value 0), Geq (y, Value 0)) ->
      if exactly0 ([x;y],[],0) then Some (build_is0 true x)
      else None
        (* x + y = 0 ==> x >= 0 /\ y >= 0 <=> x = 0 *)
    | (Unequal (x, Value 0), Geq (y, Value 0)) |
      (Geq (y, Value 0), Unequal (x, Value 0)) ->
      if x = y then
        Some (Geq (simplify_plus [Value (-1); y], Value 0))
        (* a != 0 /\ a >= 0 => a > 0 *)
      else if exactly0 ([x],[y],0) then
        Some (Geq (simplify_plus [Value (-1); y], Value 0))
        (* -a != 0 /\ a >= 0 => a > 0 *)
      else None
    | _ -> None
;;

(* given either form1 or form2, find a simpler formula that implies
the disjunction *)
let improve_disjunction form1 form2 =
  match (form1, form2) with
    | (Geq (x, Value 0), Geq (y, Value 0)) ->
      if exactly0 ([x;y],[],2) then
        Some (build_is0 false (simplify_plus [Value 1; x]))
      else None
        (* x + y = -2 ==> x >= 0 \/ y >= 0 <=> x != -1 *)
    | (Equal (x, Value 0), Geq (y, Value 0)) |
      (Geq (y, Value 0), Equal (x, Value 0)) ->
      if exactly0 ([y],[x],1) then Some (Geq (x, Value 0))
        (* y = x - 1 ==> x = 0 \/ y >= 0 <=> x >= 0 *)
      else if exactly0 ([y;x],[],1) then
        Some (Geq (simplify_plus [Value 1; y], Value 0))
        (* y = -x - 1 ==> -x = 0 \/ y >= 0 <=> y + 1 >= 0 *)
      else None
    | _ -> None
;;

(* given that all statements in assumptions can be assumed true, and
all statements in antiassumptions can be assumed false, finds a
replacement for the given formula which is either as strong as
possible (if strong is true) or as weak as possible (if strong is
false) *)
let improve formula assumptions antiassumptions strong =
  (* checks whether formula can be simplified using any of the
  formulas in assumptions *)
  let rec assimprove formula = function
    | [] -> formula
    | head :: tail -> ( match improve_conjunction formula head with
        | Some f -> f
        | None -> assimprove formula tail
      )
  in
  (* checks whether formula can be simplified using any of the
  formulas in antiassumptions *)
  let rec antiimprove formula = function
    | [] -> formula
    | head :: tail -> ( match improve_disjunction formula head with
        | Some f -> f
        | None -> antiimprove formula tail
      )
  in
  (* runs f until formula doesn't change anymore *)
  let rec repeat f formula count =
    let newform = f formula in
    if formula = newform || count <= 0 then formula
    else repeat f newform (count - 1)
  in
  (* decide how to do the improvements *)
  if not (is_basic formula) then formula
  else if strong then repeat (fun x -> assimprove x assumptions) formula 3
  else repeat (fun x -> antiimprove x antiassumptions) formula 3
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

(** given a formula free of Div, Mod, Xor and Negate other than for
boolean variables, tries to find more advanced simplifications than
the basics; we may assume that all assumptions are satisfied,
that the antiassumptions are not be satisfied, and that the
replacements in defs should be done to any basic formula.
Returned are a pair with the simplified formula and a boolean
indicating whether anything was changed in it *)
let rec deep_simplify defs assumptions antiassumptions formula changed =
  (* check the given formula against the list of assumptions and
  antiassumptions *)
  let check formula ass antiass =
    if List.exists (fun x -> implies x formula) ass then True
    else if List.exists (implies formula) antiass then False
    else if List.exists (inconsistent formula) ass then False
    else if List.exists (alwaystogether formula) antiass then True
    else formula
  in
  (* applies the def substitution to all basic formulas in the given list *)
  let apply_defs (isub, fsub) formulas =
    let apply_on formula =
      match formula with
        | BoolVar _ | Negate _ | Equal _ | Unequal _ | Geq _ ->
          fst (instantiate_formula isub fsub formula false)
        | _ -> formula
    in
    List.map apply_on formulas
  in
  (* find a substitution corresponding to the given formula, or return
  something with first element false if no such substitution exists *)
  let (isub, fsub) = defs in
  let check_nodef x sub iadd fadd =
    if List.mem_assoc x sub then (false, [], [])
    else (true, iadd, fadd)
  in
  let find_substitution = function
      | BoolVar (_, x) ->
        check_nodef x fsub [] [(x, True)]
      | Negate (BoolVar (_, x)) ->
        check_nodef x fsub [] [(x, False)]
      | Equal (IntVar (_, x), Value 0) ->
        check_nodef x isub [(x, Value 0)] []
      | Equal (Plus [Value k; IntVar (_, x)], Value 0) ->
        check_nodef x isub [(x, Value (-k))] []
      | _ -> (false, [], [])
  in
  let anti_substitution = function
    | BoolVar _ -> find_substitution (Negate formula)
    | Negate x -> find_substitution x
    | Unequal (x, y) -> find_substitution (Equal (x, y))
    | _ -> (false, [], [])
  in
  (* working with the format returned by find_substitution and
  anti_substitution *)
  let check_definition def = (def, find_substitution def) in
  let check_antidefinition def = (def, anti_substitution def) in
  let is_definition (def, (isdef, isub, fsub)) = isdef in
  let get_isub (def, (isdef, isub, fsub)) = isub in
  let get_fsub (def, (isdef, isub, fsub)) = fsub in
  (* split a list of definitions / anti-definitions with a given
  definition length into the definition part and the rest; the
  definition part is immediately instantiated using [defs] *)
  let (isub, fsub) = defs in
  let rec split trivial block i n sofar lst =
    if i >= n then (sofar, n, lst)
    else match lst with
      | [] -> failwith "more definitions than arguments!"
      | head :: tail ->
        let head = fst (instantiate_formula isub fsub head false) in
        if head = trivial then split trivial block i (n-1) sofar tail
        else if head = block then ([], 0, [False])
        else split trivial block (i+1) n (head :: sofar) tail
  in
  (* finds all definitions x = k or anti-definitions (depending on
  whether check is check_definition or check_antidefinition, and on
  the trivial and block parameters), and all boolean variables x or
  not x in the given list, and returns:
  - the updated list of definitions (items 0..k-1 were already assumed
    to be definitions of variables not otherwise occurring in args),
    with defs already applied on it
  - the size of the updated definition list
  - the remaining arguments, which are not definitions, but which have
    both the old definitions and the new ones applied to basic
    formulas
  - the new definition list
  - whether any new definitions were added, or changed = true
  *)
  let get_definitions trivial block check changed k args =
    let (start, k, finish) = split trivial block 0 k [] args in
    let information = List.map check finish in
    let (definitions, rest) = List.partition is_definition information in
    let newdefs = List.map fst definitions in
    let remainder = List.map fst rest in
    let newisub = List.flat_map get_isub definitions in
    let newfsub = List.flat_map get_fsub definitions in
    let newsub = (newisub @ isub, newfsub @ fsub) in
    let remainder = apply_defs newsub remainder in
    let c = (newisub <> []) || (newfsub <> []) in
    (newdefs @ start, k + (List.length newdefs), remainder, newsub,
     changed || c)
  in
  (* modify ass, antiass and forms under the assumption that the
  given formula holds *)
  let assume formula (ass, antiass, forms) =
    if is_basic formula then (formula :: ass, antiass, forms)
    else (ass, antiass, forms)
  in
  let antiassume formula (ass, antiass, forms) =
    if is_basic formula then (ass, formula :: antiass, forms)
    else (ass, antiass, forms)
  in
  (* removes all elements e from the given list such that f e x holds
  for an earlier element x in the list, and reverses the list in the
  process; also returns whether anything changed *)
  let rec prune_andor_arguments f sofar ch = function
    | [] -> (sofar, ch)
    | head :: tail ->
      let (newsofar, newch) =
        if List.exists (f head) sofar then (sofar, true)
        else (head :: sofar, ch)
      in
      prune_andor_arguments f newsofar newch tail
  in
  (* find a (simplified) list of requirements indicating that each of
  (if strong is true) or one of (if strong is false) the given
  formulas is false) *)
  let rec update_andor_arguments ch ds ass antiass sofar strong = function
    | [] ->
      (* everything is simplified; now just make all claims as strong
      or weak as we can, by comparing all pairs in the direction they
      haven't been compared yet: during the recursion we have replaced
      A /\ B with A /\ B <--> C by A /\ C, and now have sofar = C, A;
      we can remove A because C -> A (and similar for \/) *)
      let f = if strong then (fun e x -> implies x e) else implies in
      prune_andor_arguments f [] ch sofar
    | arg :: tail ->
      (* to simplify arg, first check whether we can reduce it to
      truth or falsehood given what we already know *)
      let (formula, ch) = deep_simplify ds ass antiass arg ch in
      ( match (check formula ass antiass, strong) with
          | (True, true) | (False, false) ->
            (* We can! This is either a true statement inside a
            conjunction, or a false statement inside a disjunction,
            and can be removed *)
            update_andor_arguments ch ds ass antiass sofar strong tail
          | (True, false) | (False, true) as result ->
            (* We can! This is however a false statement inside a
            conjunction, or a true statement inside a disjunction,
            so the entire conjunction / disjunction is decided *)
            ([fst result], true)
          | _ ->
            (* Nope, we can't.  But maybe we *can* put it in a
            stronger / weaker form, at least, both using what we knew
            from assumptions / antiassumptions and from the previous
            elements in the list *)
            let form = improve formula ass antiass strong in
            (* assume that the current statement is true (in And) or
            false (in Or), and continue with the next! *)
            let newsofar = form :: sofar in
            let info = (ass, antiass, tail) in
            let (ass, antiass, rest) =
              if is_basic form then (
                if strong then assume form info
                else antiassume form info
              )
              else info
            in
            update_andor_arguments ch ds ass antiass newsofar strong rest
      )
  in
  (* check for each of the likely forms! *)
  match formula with
    | AndWithDefs (i, lst) ->
      let (defpart, n, argpart, subst, ch) =
        get_definitions True False check_definition changed i lst in
      let (args, ch) = update_andor_arguments ch subst
                   assumptions antiassumptions [] true argpart in
      let fullargs = defpart @ args in
      if args = [False] then (False, true)
      else if fullargs = [] then (True, true)
      else if List.tl fullargs = [] then (List.hd fullargs, true)
      else (AndWithDefs (n, fullargs), ch)
    | OrWithUndefs (i, lst) ->
      let (defpart, n, argpart, subst, ch) =
        get_definitions False True check_antidefinition changed i lst
      in
      let (args, ch) = update_andor_arguments ch subst
                   assumptions antiassumptions [] false argpart in
      let fullargs = defpart @ args in
      if args = [True] then (True, true)
      else if fullargs = [] then (False, true)
      else if List.tl fullargs = [] then (List.hd fullargs, true)
      else (OrWithUndefs (n, fullargs), ch)
    | And lst ->
      let form = AndWithDefs (0, lst) in
      deep_simplify defs assumptions antiassumptions form true
    | Or lst ->
      let form = OrWithUndefs (0, lst) in
      deep_simplify defs assumptions antiassumptions form true
    | Quantifier (universal, x, lower, upper, form) ->
      let (ll, c1) = instantiate_expression isub fsub lower false in
      let (uu, c2) = instantiate_expression isub fsub upper false in
      ( match (ll, uu) with
        | (Value l, Value u) ->
          let (f, _)  = instantiate_formula isub fsub formula false in
          deep_simplify defs assumptions antiassumptions f true
        | _ ->
          let (f, c3) = deep_simplify defs assumptions antiassumptions
                                      form (c1 || c2) in
          ( Quantifier (universal, x, ll, uu, f), c3)
      )
    | _ -> (formula, changed)
;;

(* instantiates "definitions" where possible, taking occurrences
x = yz and replacing x everywhere by yz *)
let rec blunt_simplify substitutions formula changed =
  (* split a list of definitions / anti-definitions with a given
  definition length into the definition part and the rest *)
  let split n lst =
    let rec recurse i sofar lst =
      if i >= n then (sofar, lst)
      else match lst with
        | [] -> failwith "more definitions than arguments!"
        | head :: tail ->
          recurse (i+1) (head :: sofar) tail
    in
    recurse 0 [] lst
  in
  (* substitute the given list of basic formulas, and partition by
  those which were unaffected by the substitution and those which
  were not *)
  let substitute_definitions lst =
    let rec recurse k realdefs notrealdefs = function
      | [] -> (realdefs, k, notrealdefs)
      | head :: tail ->
        let (subhead, changed) = blunt_simplify substitutions head false in
        if changed then recurse k realdefs (subhead :: notrealdefs) tail
        else recurse (k + 1) (subhead :: realdefs) notrealdefs tail
    in
    recurse 0 [] [] lst
  in
  (* test whether the given formula is a variable definition, and
  returns the corresponding replacement if so *)
  let test_posnegvar = function
    | IntVar (_, x) -> Some (x, 1)
    | Times [Value -1; IntVar (_, x)] -> Some (x, -1)
    | _ -> None
  in
  let test_0def = function
    | Plus lst ->
      let addinfo a = (a, test_posnegvar a) in
      let lstinfo = List.rev_map addinfo lst in
        (* reversed so negative variables will come first *)
      let vars = List.filter (Option.is_some <.> snd) lstinfo in
      let rec bestvar = function
        | (a, Some (x, orientation)) :: tail ->
          let totalmina = simplify_plus (List.diff lst [a]) in
          if has_ivar x totalmina then bestvar tail
          else if orientation = 1 then
            Some (x, simplify_times [Value (-1); totalmina])
          else Some (x, totalmina)
        | _ -> None
      in
      bestvar vars
    | _ -> None
  in
  let test_definition eq = function
    | Equal (expr, Value 0) -> if eq then test_0def expr else None
    | Unequal (expr, Value 0) -> if eq then None else test_0def expr
    | _ -> None
  in
  (* partition a list into potential blunt-definitions and others *)
  let maybe_definition eq form =
    let goodexpr = function
      | Plus lst -> List.exists (fun x -> test_posnegvar x <> None) lst
      | _ -> false
    in
    match form with
      | Equal (expr, _) -> eq && (goodexpr expr)
      | Unequal (expr, _) -> (not eq) && (goodexpr expr)
      | _ -> false
  in
  let find_blunt_definitions eq lst =
    List.partition (maybe_definition eq) lst
  in
  (* substitute what may be blunt definitions with the substitution,
  and then parse them and perhaps update the substitution! *)
  let rec substitute_bluntdefs sofar subst eq lst changed =
    match lst with
      | [] -> (sofar, changed, subst)
      | head :: tail ->
        let (head, changed) = blunt_simplify subst head changed in
        match test_definition eq head with
          | None -> substitute_bluntdefs (head :: sofar) subst eq tail changed
          | Some pair ->
            substitute_bluntdefs (head :: sofar) (pair :: subst) eq tail changed
  in
  (* handle an AndWithDefs or an OrWithUndefs *)
  let handle_andor k args makeand =
    (* separate definitions x = k from the rest baddefs @ rest *)
    let (defs, rest) = split k args in
    let (defs, n, baddefs) = substitute_definitions defs in
    let rest = baddefs @ rest in
    let changed = changed || (k <> n) in
    (* separate remaining formulas into potential definitions,
    basic formulas and non-basic formulas, so we'll do everything in
    the right order *)
    let (bluntdefs, rest) = find_blunt_definitions makeand rest in
    let (basics, nonbasics) = List.partition is_basic rest in
    (* substitute the potential definitions and then, when we're
    done and have updated the substitutions, all other formulas *)
    let (bluntdefs, changed, subst) = substitute_bluntdefs []
                      substitutions makeand bluntdefs changed in
    let info = List.map (fun x -> blunt_simplify subst x changed)
                        (basics @ nonbasics) in
    let remainder = List.map fst info in
    let changed = List.exists snd info in
    let args = defs @ bluntdefs @ remainder in
    (*let (remainder, changed) = handle_instantiations remainder in*)
    if makeand then (AndWithDefs (n, args), changed)
    else (OrWithUndefs (n, args), changed)
  in
  (* cases for each of the likely forms! *)
  match formula with
    | AndWithDefs (k, args) -> handle_andor k args true
    | OrWithUndefs (k, args) -> handle_andor k args false
    | Quantifier (universal, x, lower, upper, form) ->
      let (f, c) = blunt_simplify substitutions form changed in
      ( Quantifier (universal, x, lower, upper, f), c )
    | _ ->
      let (f, c) = instantiate_formula substitutions [] formula true in
      (f, changed || c)
;;

(* replaces all occurrences of And by AndWithDefs and Or by
OrWithUndefs; here, the formula is assumed to already be simplified,
so no Ites or Xors occurs, and no defcounts are assumed to be
present yet *)
let rec add_def_counts = function
  | And lst -> AndWithDefs (0, List.map add_def_counts lst)
  | Or lst -> OrWithUndefs (0, List.map add_def_counts lst)
  | Quantifier (universal, x, lower, upper, form) ->
    Quantifier (universal, x, lower, upper, add_def_counts form)
  | formula -> formula
;;

(* global function, handles integer and formula simplifications *)
let advanced_simplify formula timeout =
  let timeout = timeout * 10 in
  let time = truncate ((Unix.time ()) *. 10.0) in
  let rec repeat formula count =
    if count < 0 then formula
    else if (truncate ((Unix.time ()) *. 10.0) >= time + timeout) then formula
    else (
      let (simplified, changed) = deep_simplify ([],[]) [] [] formula false in
      if changed then repeat simplified (count - 1)
      else (
        let (blunt, changed) = blunt_simplify [] formula false in
        if changed then repeat blunt (count - 1)
        else formula
      )
    )
  in
  repeat (add_def_counts formula) 10
;;

(*****************************************************************************)
(* creating intformulas from problem statements                              *)
(*****************************************************************************)

(* makes an intproblem ip such that:
- if [satisfiability] is true, then
  EXISTS <vars>.ip <=> EXISTS <vars>.forms_1 /\ ... forms_n
- if [satisfiability] is false, then
  FORALL <vars>.ip <=> FORALL <vars>.forms_1 /\ ... forms_n
Note here that existentially quantified variables are replaced by
parameters, and universally quantified variables by vars.
*)
let makeproblem forms rens transes a e satisfiability =
  let makeparam x = satisfiability in
  let translate = translate_bool rens transes a e makeparam in
  let translated = List.map translate forms in
  let intsimped = List.map simplify_ints_in translated in
  let xorfree = List.map (ditch_xor true) intsimped in
  let simped = basic_simplify [] (And xorfree) in
  let itefree = ditch_ite simped in
  let divmodfree = safe_ditch_division true itefree in
  let ditch_divmod formula =
    snd (ditch_division formula e a satisfiability)
  in
  let final = ditch_divmod divmodfree in
  basic_simplify [] final
;;

let satisfiability_problem forms renamings translations a e =
  makeproblem forms renamings translations a e true
;;

let validity_problem forms renamings translations a e =
  makeproblem forms renamings translations a e false
;;

(*****************************************************************************)
(* dealing with existential validity queries                                 *)
(*****************************************************************************)

(* returns all integer values in the given list of pairs of lists of
formulas *)
let integer_values_in formulas =
  let ints term = List.filter Function.is_integer (Term.funs term) in
  let allints = List.flat_map ints formulas in
  let around x =
    let k = Function.integer_to_int x in 
    if k = 0 then []
    else [k-1;k;k+1;-k-1;-k;-k+1]
  in
  let all = (-1) :: 0 :: 1 :: List.flat_map around allints in
  let rec prune = function
    | first :: second :: tail ->
      if first = second then prune (second :: tail)
      else first :: prune (second :: tail)
    | lst -> lst
  in
  prune (List.sort compare all) 
;;

(* turns a sequence of variables with ranges into a varmap *)
let make_varmap env varswithrange norange =
  let base = VarMap.empty in
  let make_list i j = Possibilities.from_range i j in
  let add_elem rest = function
    | (x, Some (b,t)) -> VarMap.add x (make_list b t) rest
    | (x, None) ->
      let sort = Environment.find_sort x env in
      if Sort.to_string sort = "Int" then VarMap.add x norange rest
      else VarMap.add x (make_list 0 1) rest
  in
  List.foldl add_elem base varswithrange
;;

(* makes a parameter constraint for the given variable with range *)
let make_range_constraint = function
  | (x, None) -> []
  | (x, Some (a, b)) ->
    if a = b then [Equal (IntVar (false, x), Value a)]
    else [Geq (IntVar (false, x), Value a);
          Geq (Value b, IntVar (false, x))]
;;

(* returns all parameters occurring in a given formula *)
let get_params =
  let f = function | IntVar (univ, _) -> not univ | _ -> false in
  let g = function | BoolVar (univ, _) -> not univ | _ -> false in
  let h = function | OtherVar (univ, _) -> not univ | _ -> false in
  get_vars f g h
;;

let get_univars =
  let f = function | IntVar (univ, _) -> univ | _ -> false in
  let g = function | BoolVar (univ, _) -> univ | _ -> false in
  let h = function | OtherVar (univ, _) -> univ | _ -> false in
  get_vars f g h
;;

(* sorts a sequence of formulas by how many parameters occur in them;
returns a list with entries (parameters, number of parameters,
formula) *)
let sort_formulas formulas =
  let varsforform form =
    let params = get_params form in
    (params, List.length params, form)
  in
  let compare (_,i,_) (_,j,_) = compare i j in
  List.sort compare (List.map varsforform formulas)
;;

(* makes a problem of the form: find x1,...,xn such that forms are valid *)
let make_existsvalid forms varswithrange renamings translations a e =
  (* build the basic problem *)
  let parameters = List.map fst varswithrange in
  let makeparam x = List.mem x parameters in
  let translate = translate_bool renamings translations a e makeparam in
  let translated = List.map translate forms in
  let intsimped = List.map simplify_ints_in translated in
  let xorfree = List.map (ditch_xor true) intsimped in
  (* add constraints for the variable ranges *)
  let rangeconstraints = List.flat_map make_range_constraint varswithrange in
  let simped = basic_simplify [] (And (xorfree @ rangeconstraints)) in
  (* get rid of problematic symbols *)
  let itefree = ditch_ite simped in
  let divmodfree = safe_ditch_division true itefree in
  let ditch_divmod formula =
    snd (ditch_division formula e a false)
  in
  ditch_divmod divmodfree
;;

(* checks whether the given varmap contains the given combination *)
let rec matches varmap combination =
  match combination with
    | [] -> true
    | (var, value) :: tail ->
      let possibilities = VarMap.find var varmap in
      if List.mem value possibilities
      then matches varmap tail
      else false
;;

(* removes a combination from the list of possibilities *)
let remove_combination combination possibilities =
  let rec splitoff varmap = function
    | [] -> []
    | (var, value) :: tail ->
      let possibilities = VarMap.find var varmap in
      if possibilities = [value] then splitoff varmap tail
      else (
        let possible1 = List.diff possibilities [value] in
        let possible2 = [value] in
        (VarMap.replace var possible1 varmap) ::
        splitoff (VarMap.replace var possible2 varmap) tail
      )
  in
  let doremove varmap =
    if matches varmap combination
    then splitoff varmap combination
    else [varmap]
  in
  List.flat_map doremove possibilities
;;

(* alters the given list of combinations by removing all variables
for which only one choice is possible, and additionally returns a
list of these variables along with their desired value *)
let clean_combinations combinations =
  (* returns whether varmap maps x to [k] *)
  let goodcand varmap (x,k) =
    try VarMap.find x varmap = [k]
    with Not_found -> false
  in
  (* tests whether the given list of (variable,value) pairs is
  enforced by all varmaps in the given list *)
  let rec test candidates = function
    | [] -> candidates
    | varmap :: tail ->
      let newcandidates = List.filter (goodcand varmap) candidates in
      if newcandidates = [] then []
      else test newcandidates tail
  in
  (* figures out whether there's a variable in the list of
  combinations for which there is only one choice; returns
  all such variables, with their admitted values *)
  let single_choices combinations =
    let singlelist lst = (lst <> []) && (List.tl lst = []) in
    match combinations with
      | [] -> []
      | varmap :: tail ->
        let combis = VarMap.to_list varmap in
        let getsingle (x,l) =
          if singlelist l then [(x, List.hd l)]
          else []
        in
        let candidates = List.flat_map getsingle combis in
        test candidates combinations
  in
  (* main functionality *)
  let determined : (Variable.t * int) list = single_choices combinations in
  let clean varmap (x,_) : VarMap.t = VarMap.remove x varmap in
  let cleanall varmap : VarMap.t = List.fold_left clean varmap determined in
  let cleaned_combis = List.map cleanall combinations in
  (cleaned_combis, determined)
;;

let remove_validity_checks env acceptablevalues formswithvars =
  (* returns all lists of (variable, value) pairs where the variable
  is in the given list, and the value is in the acceptable values for
  that variable *)
  let rec all_combinations = function
    | [] -> [[]]
    | var :: tail ->
      let values =
        try VarMap.find var acceptablevalues
        with Not_found -> failwith ("Error in all_combinations (" ^
                                    (Variable.to_string var) ^ ")")
      in
      let varcombs = List.map (fun v -> (var, v)) values in
      let restcombs = all_combinations tail in
      let combinations = List.product varcombs restcombs in
      List.map (fun (x,y) -> x :: y) combinations
  in
  (* tries whether the given combination of variable / value
  instantiations will make phi valid; if true, nothing
  much is done, if false, we register (both in validcombis and
  in the returned constraints) that this combination is not
  allowed *)
  let make_int_value (x,k) = (x, Value k) in
  let make_bool_value (x,k) =
    if k = 0 then (x, False) else (x, True) in
  let isbool (x, _) =
    Sort.to_string (Environment.find_sort x env) = "Bool"
  in
  let try_combination phi (validcombis, problemssofar) combi =
    (* abort if we already rejected this combination *)
    let matching varmap = matches varmap combi in
    if not (List.exists matching validcombis)
    then (validcombis, problemssofar) else
    (* let's instantiate the constraint with this combi *)
    let (bools, ints) = List.partition isbool combi in
    let sub1 = List.map make_int_value ints in
    let sub2 = List.map make_bool_value bools in
    let newphi = fst (instantiate_formula sub1 sub2 phi false) in
    let (psi, c) = deep_simplify ([], []) [] [] newphi false in
    let psi =
      if c then fst (deep_simplify ([], []) [] [] psi false)
      else psi
    in
    (* check whether the instantiated constraint is valid, and
    update the combinations list and sequence of constraints on the
    parameters accordingly! *)
    let unequal (x, value) = Unequal (IntVar (false, x), value) in
    let unequiv (x, value) =
      if value = True then Negate (BoolVar (false, x))
      else BoolVar (false, x)
    in
    match psi with
      | True -> (validcombis, problemssofar)
      | _ ->
        let valid = remove_combination combi validcombis in
        let unequals = List.map unequal sub1 in
        let unequivs = List.map unequiv sub2 in
        (valid, match unequals @ unequivs with
          | [] -> [False]
          | [single] -> single :: problemssofar
          | lst -> Or lst :: problemssofar
        )
  in
  (* applies the given substitution on the given constraint,
  changing numbers of parameters while we're at it*)
  let single_param_substitution (gamma1, gamma2) (params, k, phi) =
    let keys = (List.map fst gamma1) @ (List.map fst gamma2) in
    let ingamma x = List.mem x keys in
    if List.exists ingamma params then (
      let substituted = fst (instantiate_formula gamma1 gamma2 phi false) in
      let newparams = get_params substituted in
      (newparams, List.length params, substituted)
    )
    else (params, k, phi)
  in
  (* updates the given list with the given parameter substitution *)
  let param_substitution gamma lst =
    let newlist = List.map (single_param_substitution gamma) lst in
    let compare (_,i,_) (_,j,_) = compare i j in
    move_sort compare newlist
  in
  (* test whether the satisfiability part of this formula is free
  from any universally quantified variables *)
  let split_satisfiability_parts = function
    | Or lst | OrWithUndefs (_, lst) ->
      let is_satisfiability_problem form = get_params form <> [] in
      List.partition is_satisfiability_problem lst
    | x -> ([x], [])
  in
  let make_satisfiability_problem formula =
    let (satparts, restparts) = split_satisfiability_parts formula in
    let makeor = function | [] -> False | hd :: [] -> hd | l -> Or l in
    if List.exists (fun f -> get_univars f <> []) satparts then None
    else Some (makeor satparts, makeor restparts)
  in
  (* iterates over the given lists of constraints, obtaining
  requirements on the parameters *)
  let rec handleform validcombis sofar = function
    | [] -> sofar
    | (params, n, phi) :: tail ->
      (* can we separate the satisfiability part from the validity
      part? *)
      let satsplit =
        if n = 0 then Some (False, phi) 
        else make_satisfiability_problem phi 
      in   
      match satsplit with
        | None -> try_combis_for validcombis sofar params phi tail
            (* if we can't, just try out all combinations *)
        | Some (satpart, restpart) ->
            (* we can! continue only with the satisfiability part;
            if we haven't proved validity of restpart so far, we
            aren't going to (not without external calls, anyway, and
            we're trying to avoid those in this function) *)
          if satpart = False then (
            (* no satisfiability part? not likely going to work then *)
            if restpart = True then handleform validcombis sofar tail
            else [False]
          )
          else if n = 1 then (
            (* checking this "combination" out won't hurt, but will
            probably eliminate some combinations *)
            let combis = all_combinations params in
            let (newcombis, _) = List.fold_left
              (try_combination satpart) (validcombis, []) combis in
            handleform newcombis (satpart :: sofar) tail
          )
          else handleform validcombis (satpart :: sofar) tail
  and try_combis_for validcombis sofar params phi rest =
    let combis = all_combinations params in
    let (newcombis, newsofar) = List.fold_left
      (try_combination phi) (validcombis, sofar) combis
    in   
    let (newcombis, determined) = clean_combinations newcombis in
    if determined = [] then handleform newcombis newsofar rest 
    else (
      let (bdet, idet) = List.partition isbool determined in
      let substitution =
        (List.map make_int_value idet,
         List.map make_bool_value bdet
        )
      in
      let newrest = param_substitution substitution rest in
      handleform newcombis newsofar newrest
    )
  in
  (* main functionality, gets constraints on the parameters that will
  make all the given problems valid when satisfied, and additionally
  creates constraints that the variables should be in thir option
  range *)
  let combinations = [acceptablevalues] in
  let problems = handleform combinations [] formswithvars in
  And problems
;;

(* given a list of problems with mixed parameters and universal
variables, where each problem has the form <basic> OR ... OR <basic>,
returns Some lst, where lst contains items ([partswithoutparams],
[partswithparams], paramsinvolved); if problems does not have this
form, returns None *)
let simple_exists_valid_problem lst =
  let isintparam = function | IntVar (univ,_) -> not univ | _ -> false in
  let isboolparam = function | BoolVar (univ,_) -> not univ | _ -> false in
  let isotherparam = function | OtherVar (univ,_) -> not univ | _ -> false in
  let getparams x = (x, get_vars isintparam isboolparam isotherparam x) in
  let orchildren = function
    | Or lst | OrWithUndefs (_, lst) -> lst
    | x -> [x]
  in
  let split lst =
    let (without, withh) = List.partition (fun (_, l) -> l = []) lst in
    let params = List.unique (List.flat_map snd withh) in
    (List.map fst without, List.map fst withh, params)
  in
  let info = List.map orchildren lst in
  if not (List.for_all (List.for_all is_basic) info) then None else
  let infowithvars = List.map (List.map getparams) info in
  Some (List.map split infowithvars)
;;

(* like remove_validity_checks, but focused on simple requirements
of the form A1 OR ... OR An OR B1 OR ... OR bk with all Ai and Bi
basic and parameters only occurring in the Bi *)
let simple_remove_validity_checks env reqs =
  (* step 1: replace all formulas by a single or of basic formulas
  which indicates that this OR can be handled with always_together;
  we assume that if some Ai \/ Aj part always holds, we would have
  figured that out already! *)
  let rec self_product = function
    [] | [_] -> []
    | head :: tail ->
      (List.map (fun x -> (head, x)) tail) @ (self_product tail)
  in
  let requirements (partswithout, partswith, _) =
    let combinations1 = List.product partswithout partswith in
    let combinations2 = self_product partswith in
    let combinations = combinations2 @ combinations1 in
    let atf (x, y) = always_together_formula x y in
    partswith @ (List.flat_map atf combinations)
  in
  let atreqs = List.map requirements reqs in
  (* step 2: replace every basic formula by a list of IntVar/BoolVar-
  free requirements, using absolute positiveness *)
  let rec split_by_variables expr = match expr with
    | Value k -> [(Value k, [])]
    | IntVar (false, x) -> [(IntVar (false, x), [])]
    | Plus lst -> List.flat_map split_by_variables lst
    | IntVar (true, x) -> [(Value 1, [x])]
    | Times lst ->
      let getintvar = function | IntVar (true, x) -> [x] | _ -> [] in
      let isintvar e = getintvar e <> [] in
      let (varparts, remainder) = List.partition isintvar lst in
      let varlist = List.flat_map getintvar varparts in
      ( match remainder with
          | [] -> [(Value 1, varlist)]
          | [single] -> [(single, varlist)]
          | lst -> [Times lst, varlist]
      )
    | _ -> failwith ("Encountered unexpected non-simplified expression: " ^
                     (tostr_expression false expr))
  in
  let group_by_var expr =
    let c (_, l1) (_, l2) = compare l1 l2 in
    let groups = List.group_fully ~c:c (split_by_variables expr) in
    let constantgroup = List.exists (fun (_,x) -> x = []) in
    let cleangrouplist lst = (List.map fst lst, constantgroup lst) in
    let grouped = List.map cleangrouplist groups in
    let makesum (elist, isconst) = (simplify_plus elist, isconst) in
    List.map makesum grouped
  in
  let absolute_positiveness expr =
    let groups = group_by_var expr in
    let build_geq (x, base) =
      if base then build_geq0 x
      else build_is0 true x
    in
    List.map build_geq groups
  in
  let absolute_zeroness expr =
    let groups = group_by_var expr in
    List.map ((build_is0 true) <.> fst) groups
  in
  let absolute_nonzeroness expr =
    let groups = group_by_var expr in
    let (base, rest) = List.partition snd groups in
    match base with
      | [] -> [False]
      | _ :: _ :: _ -> failwith "more than one constant?!?"
      | [(expr, _)] ->
        (* for non-zeroness of n*x + m, it suffices if not n | m *)
        if rest = [] then [Unequal (expr, Value 0)] else
        let intsort = Sort.from_string "Int" in
        let fv _ = IntVar (false, Environment.create_sorted_var intsort [] env) in
        let divver = fv () in
        (* divver * <some var> = <part of n*x> *)
        let handle_part p = Equal (simplify_times [divver; fv ()], fst p) in
        let main = List.map handle_part rest in
        (* expr mod divver != 0, so divver * x < expr < divver * x + divver *)
        let divrest = fv () in
        let divvertimesrest = simplify_times [divver;divrest] in
        let smaller =
          Geq (simplify_plus [Value (-1);
                 divver;
                 divvertimesrest;
                 simplify_times [Value (-1); expr]],
               Value 0) in
        let greater =
          Geq (simplify_plus [Value (-1);
                 expr;
                 simplify_times [Value (-1); divvertimesrest]],
               Value 0) in
        smaller :: greater :: main
  in
  let absoluteness = function
    | Geq (x, Value 0) -> absolute_positiveness x
    | Equal (x, Value 0) -> absolute_zeroness x
    | Unequal (x, Value 0) -> absolute_nonzeroness x
    | _ -> [False]
  in
  let absreqs = List.map (List.map absoluteness) atreqs in
  (* step 3: put it all back together into a big formula again *)
  let makeand = function
    | [] -> True
    | [single] -> single
    | lst -> if List.mem False lst then False else And lst
  in
  let makeor = function
    | [] -> False
    | [single] -> single
    | lst -> if List.mem True lst then True else Or lst
  in
  let formreqs = List.map (List.map makeand) absreqs in
  let formreqs = List.map makeor formreqs in
  makeand formreqs
;;

(*****************************************************************************)
(* rewriting smt-problems to equivalent problems                             *)
(*****************************************************************************)

(* changes a comparison x R y into x' R y' where all negative terms
   are moved to the right-hand side and positive terms to the left *)
let prettify_comparison x y =
  let make_negative expr = simplify_times [Value (-1); expr] in
  if y <> Value 0 then (x, y)
  else match x with
    | Plus lst ->
      let isnegative = function
        | Value k -> k < 0
        | Times ((Value k) :: _) -> k < 0
        | _ -> false
      in
      let (negatives, positives) = List.partition isnegative lst in
      let otherside = List.map make_negative negatives in
      let sum = function
        | [] -> Value 0
        | [single] -> single
        | lst -> Plus lst
      in
      (sum positives, sum otherside)
    | exp -> (exp, Value 0)
;;

(* given a context and functions [efun] and [ffun] which supply the
   integer and boolean expressions indexed in the context, returns
   the term represented by the context *)
let rec translate_context_back alf env efun ffun = function
  | Func (fname, lst) ->
    let f = Alphabet.find_fun fname alf in
    let args = List.map (translate_context_back alf env efun ffun) lst in
    Term.make_function alf env f args
  | OtherVar (_, x) -> Term.Var x
  | IntExp i -> efun i
  | BoolExp i -> ffun i
;;

(* given a list [xn;...;x2;x1], returns (...f (f x1 x2) x3 ... xn) *)
let rec associative a e f = function
  | [] -> failwith "Associative not given any arguments!"
  | [single] -> single
  | [first;second] -> Term.make_function a e f [second;first]
  | head :: tail ->
    Term.make_function a e f [associative a e f tail; head]

(* given an integer_expression, tries to find the corresponding term
   again *)
let rec translate_expression_back tr alf env exp =
  let errfor name = "Cannot simplify formula: cannot determine " ^
                    "suitable symbol for " ^ name ^ "." in
  let get_symbol n = get_named_symbol alf (errfor n) tr (const true)
                                          (const true) in
  let recurse = translate_expression_back tr alf env in
  match exp with
    | Value k ->
      let num = Function.integer_symbol k in
      Term.make_function alf env num []
    | Plus lst ->
      let plus = get_symbol "addition" ["+";"plus";"add"] in
      associative alf env plus (List.rev_map recurse lst)
    | Times lst ->
      let times = get_symbol "multiplication" ["*";"times";"mul"] in
      associative alf env times (List.rev_map recurse lst)
    | Div (x, y) ->
      let div = get_symbol "division" ["/";"div"] in
      Term.make_function alf env div [recurse x; recurse y]
    | Mod (x, y) ->
      let md = get_symbol "modulo" ["%";"mod"] in
      Term.make_function alf env md [recurse x; recurse y]
    | Ite (c, x, y) ->
      let ite = get_symbol "if-then-else" ["ite"] in
      let cterm = translate_formula_back tr alf env c in
      Term.make_function alf env ite [cterm; recurse x; recurse y]
    | IntVar (_, x) -> Term.Var x
    | UnknownExp (c, esubs, fsubs) ->
      let efun i = translate_expression_back tr alf env (List.nth esubs i) in
      let ffun i = translate_formula_back tr alf env (List.nth fsubs i) in
      translate_context_back alf env efun ffun c

(* given an integer_formula, tries to find the corresponding term again *)
and translate_formula_back tr alf env formula =
  let erecurse = translate_expression_back tr alf env in
  let frecurse = translate_formula_back tr alf env in
  let get_symbol name func =
    try func alf
    with Not_found -> failwith ("Cannot simplify formula: cannot determine " ^
                                "suitable symbol for " ^ name ^ ".")
  in
  let negation term =
    let n = get_symbol "negation" Alphabet.get_not_symbol in
    Term.make_function alf env n [term]
  in
  match formula with
    | And lst | AndWithDefs (_, lst) ->
      let f = get_symbol "conjunction" Alphabet.get_and_symbol in
      associative alf env f (List.rev_map frecurse lst)
    | Or lst | OrWithUndefs (_, lst) ->
      let f = get_symbol "disjunction" Alphabet.get_or_symbol in
      associative alf env f (List.rev_map frecurse lst)
    | Xor (x, y) ->
      let xorerr = "Cannot simplify formula: cannot determine " ^
                   "suitable symbol for xor." in
      let xor = get_named_symbol alf xorerr tr
                (const true) (const true) ["xor";"^"] in
      Term.make_function alf env xor [frecurse x; frecurse y]
    | Geq (x, y) ->
      let (x, y) = prettify_comparison x y in
      let f = get_symbol "greater-equal" Alphabet.get_geq_symbol in
      Term.make_function alf env f [erecurse x; erecurse y]
    | Equal (x, y) ->
      let (x, y) = prettify_comparison x y in
      let f = get_symbol "equality" Alphabet.get_equal_symbol in
      Term.make_function alf env f [erecurse x; erecurse y]
    | Unequal (x, y) ->
      let (x, y) = prettify_comparison x y in
      let f = get_symbol "equality" Alphabet.get_equal_symbol in
      let sub = Term.make_function alf env f [erecurse x; erecurse y] in
      negation sub
    | BoolVar (_, x) -> Term.Var x
    | True ->
      let f = get_symbol "truth" Alphabet.get_top_symbol in
      Term.make_function alf env f []
    | False ->
      let f = get_symbol "falsehood" Alphabet.get_bot_symbol in
      Term.make_function alf env f []
    | Negate f -> negation (frecurse f)
    | UnknownPred (c, esubs, fsubs) ->
      let efun i = translate_expression_back tr alf env (List.nth esubs i) in
      let ffun i = translate_formula_back tr alf env (List.nth fsubs i) in
      translate_context_back alf env efun ffun c
    | Quantifier (universal, x, lower, upper, phi) ->
      let l = erecurse lower in
      let u = erecurse upper in
      let form = frecurse phi in
      if universal then
        Smtquantifiers.universal_quantification x l false u false form alf
      else
        Smtquantifiers.existential_quantification x l false u false form alf
;;

(* Just a helping function for abstract_expressions and abstract_formulas *)
let combine_and_number_lists start lst1 lst2 =
  List.mapi (fun i (x,y) -> (i+start,x,y)) (List.zip lst1 lst2)
;;

(* abstract_expressions and abstract_formulas return either None, if
the two given expressions / formulas cannot be seen as instances of
the same unary predicate, or Some (posses, exps) if they can be; in
this case, posses lists all positions where the expressions / formulas
disagree, and exps lists pairs (expression in given1 at that position,
expression in given2 at that position).  This is a list because 1
position higher up in the expression / formula there may still be a
suitable position. Here, positions are reversed lists indicating the
position in the term. *)
let rec abstract_expressions exp1 exp2 others parent_expressions pos =
  (* exp1 != exp2, so we need to add this position to the list of bad
  positions, provided the expressions match with expressions already
  in the list! *)
  let expchain = (exp1, exp2) :: parent_expressions in
  let rec equal_len = function
    | ([], _) | (_, []) -> 0
    | (hd1 :: tl1, hd2 :: tl2) ->
      if hd1 = hd2 then 1 + equal_len (tl1, tl2) else 0
  in
  let rec another_difference posses = function
    | [] -> None
    | head :: tail as exps ->
      if head <> (exp1, exp2) then
        another_difference (List.map List.tl posses) tail
      else (
        let goodlen = equal_len (exps, expchain) in
        let exps = List.take goodlen exps in
        Some (pos :: posses, exps)
      )
  in
  let different () =
    let (posses, exps) = others in
    if exps = [] then Some ([pos], expchain)
    else another_difference posses exps
  in
  (* exp1 = exp2, so the only differences are the ones we have found
  before *)
  let not_different () = Some others in
  (* exp1 and exp2 have the same outer shape; consider their
  children! *)
  let compare_lists others lst =
    abstract_lists different lst [] others expchain pos in
  let handle_list lst1 lst2 =
    try compare_lists others (combine_and_number_lists 0 lst1 lst2)
    with Invalid_argument _ -> different ()
  in
  (* main functionality: check how the given expressions compare *)
  match (exp1, exp2) with
    | (Value n, Value m) ->
      if n <> m then different () else not_different ()
    | (Plus lst1, Plus lst2) | (Times lst1, Times lst2) ->
      handle_list lst1 lst2
    | (Div (x1,y1), Div (x2,y2)) | (Mod (x1,y1), Mod (x2,y2)) ->
      handle_list [x1;y1] [x2;y2]
    | (IntVar (_,x), IntVar (_,y)) ->
      if x <> y then different () else not_different ()
    | (Ite (c1, i1, e1), Ite (c2, i2, e2)) ->
      abstract_lists different [(1,i1,i2);(2,e1,e2)] [(0,c1,c2)]
                     others expchain pos
    | (UnknownExp (c1, es1, fs1), UnknownExp (c2, es2, fs2)) ->
      if c1 <> c2 then different () else
      let elen = List.length es1 in
      ( try
          let es = combine_and_number_lists 0 es1 es2 in
          let fs = combine_and_number_lists elen fs1 fs2 in
          abstract_lists different es fs others expchain pos
        with Invalid_argument _ -> different ()
      )
    | _ -> different ()

and abstract_formulas form1 form2 others pos =
  (* if the root shape of form1 and form2 is not the same, then they
  cannot possibly be the same expression-context! *)
  let different () = None in
  (* if form1 = form2, then the only differences we return are the
  ones we have found before *)
  let not_different () = Some others in
  (* main functionality: check how the given formulas compare *)
  let recurse_lists elst flst =
    abstract_lists different elst flst others [] pos in
  match (form1, form2) with
    | (And lst1, And lst2) | (Or lst1, Or lst2) |
      (AndWithDefs (_, lst1), AndWithDefs (_, lst2)) |
      (OrWithUndefs (_, lst1), OrWithUndefs (_, lst2)) ->
      ( try recurse_lists [] (combine_and_number_lists 0 lst1 lst2 )
        with Invalid_argument _ -> different ()
      )
    | (Geq (a1,b1), Geq (a2, b2)) | (Equal (a1,b1), Equal (a2,b2)) |
      (Unequal (a1,b1), Unequal (a2,b2)) ->
      recurse_lists [(0,a1,a2);(1,b1,b2)] []
    | (Xor (a1, b1), Xor (a2, b2)) ->
      recurse_lists [] [(0,a1,a2);(1,b1,b2)]
    | (BoolVar (_,x), BoolVar (_,y)) ->
      if x <> y then different() else not_different ()
    | (True, True) | (False, False) -> not_different ()
    | (Negate form1, Negate form2) ->
      abstract_formulas form1 form2 others (0 :: pos)
    | (UnknownPred (c1, es1, fs1), UnknownPred (c2, es2, fs2)) ->
      if c1 <> c2 then different () else
      let elen = List.length es1 in
      ( try
          let es = combine_and_number_lists 0 es1 es2 in
          let fs = combine_and_number_lists elen fs1 fs2 in
          recurse_lists es fs
        with Invalid_argument _ -> different ()
      )
    | (Quantifier (univ1, x1, lower1, upper1, main1),
       Quantifier (univ2, x2, lower2, upper2, main2)) ->
      if form1 = form2 then not_different()
      else different ()
        (* yes, this gives lots of false negatives - but false
        negatives don't lead to problems, and we don't accidentally
        want to get a position containing a binder! (This can be
        solved with more advanced code should it ever be needed.) *)
    | _ -> different ()

and abstract_lists different elst flst others parents pos =
  let handle_check rest1 rest2 = function
    | None -> different ()
    | Some others ->
      abstract_lists different rest1 rest2 others parents pos
  in
  match (elst, flst) with
    | ([], []) -> Some others
    | ([], (i, form1, form2) :: tail) ->
      handle_check [] tail
        (abstract_formulas form1 form2 others (i :: pos))
    | ((i, exp1, exp2) :: tail, _) ->
      handle_check tail flst
        (abstract_expressions exp1 exp2 others parents (i :: pos))
;;

(* returns Some 0 if [pos1] = [pos2], Some 1 if [pos2] is the start of
[pos1] and Some -1 if it's the other way around (so it gives a partial
comparison) *)
let rec corresponding_positions pos1 pos2 =
  match (pos1, pos2) with
    | ([], []) -> Some 0
    | ([], _) -> Some (-1)
    | (_, []) -> Some 1
    | (hd1 :: tl1, hd2 :: tl2) ->
      if hd1 = hd2 then corresponding_positions tl1 tl2
      else None
;;

(* Puts the given replacement expression in the given formula or
   expression position, and returns the result of the replacement. *)
let rec replace_at_position pos formula replacement =
  (* do a replacement inside form IF n = phead *)
  let freplace_if_equal phead ptail n form =
    if n = phead then replace_at_position ptail form replacement
    else form
  in
  (* do a replacemenet in the given list *)
  let rec freplace_list phead ptail n = function
    | [] -> []
    | hd :: tl ->
      freplace_if_equal phead ptail n hd ::
      freplace_list phead ptail (n+1) tl
  in
  (* do an expression replacement IF n = phead *)
  let rec ereplace_if_equal phead ptail n expression =
    if n = phead then replace_in_expression ptail expression
    else expression
  (* do an expression replacement in the given list *)
  and ereplace_list phead ptail n = function
    | [] -> []
    | hd :: tl ->
      ereplace_if_equal phead ptail n hd ::
      ereplace_list phead ptail (n+1) tl
  (* given an expression, does a replacement in a sub=expression *)
  and replace_in_expression pos expression =
    match pos with | [] -> replacement | phead :: ptail ->
    match expression with
      | Plus lst -> Plus (ereplace_list phead ptail 0 lst)
      | Times lst -> Times (ereplace_list phead ptail 0 lst)
      | Div (x, y) -> Div (ereplace_if_equal phead ptail 0 x,
                           ereplace_if_equal phead ptail 1 y)
      | Mod (x, y) -> Mod (ereplace_if_equal phead ptail 0 x,
                           ereplace_if_equal phead ptail 1 y)
      | Ite (c, x, y) -> Ite (freplace_if_equal phead ptail 0 c,
                              ereplace_if_equal phead ptail 1 x,
                              ereplace_if_equal phead ptail 2 y)
      | UnknownExp (c, es, fs) ->
        let elen = List.length es in
        let nes = ereplace_list phead ptail 0 es in
        let nfs = freplace_list phead ptail elen fs in
        UnknownExp (c, nes, nfs)
      | _ -> failwith "No such expression position to replace at"
  in
  let fail _ = failwith "Position in replace_at gives a formula!" in
  match pos with | [] -> fail () | phead :: ptail ->
  match formula with
    | And lst | AndWithDefs (_, lst) ->
      And (freplace_list phead ptail 0 lst)
    | Or lst | OrWithUndefs (_, lst) ->
      Or (freplace_list phead ptail 0 lst)
    | Geq (x, y) -> Geq (ereplace_if_equal phead ptail 0 x,
                         ereplace_if_equal phead ptail 1 y)
    | Equal (x, y) -> Equal (ereplace_if_equal phead ptail 0 x,
                             ereplace_if_equal phead ptail 1 y)
    | Unequal (x, y) -> Unequal (ereplace_if_equal phead ptail 0 x,
                                 ereplace_if_equal phead ptail 1 y)
    | Negate form -> Negate (freplace_if_equal phead ptail 0 form)
    | Xor (a, b) -> Xor (freplace_if_equal phead ptail 0 a,
                         freplace_if_equal phead ptail 1 b)
    | UnknownPred (c, es, fs) ->
      let elen = List.length es in
      let nes = ereplace_list phead ptail 0 es in
      let nfs = freplace_list phead ptail elen fs in
      UnknownPred (c, nes, nfs)
    | Quantifier _ (* NOTE: deliberately omitted, as in formula_differences *)
    | _ -> failwith "No such formula position to replace at!"
;;

(* tests whether the [exp] evaluates an integer, assuming that the
expressions in [nuls] all evaluate to 0; if so, Some (that integer)
is returned, otherwise None *)
let evaluates_to_int nuls exp =
  (* check whether the given expression is a value, and which one *)
  let check_value = function
    | (_, _, Value k) -> [k]
    | _ -> []
  in
  (* get the variables occurring inside an expression, not counting
  anything inside silly structures that aren't going to get affected
  by adding and subtracting anyway *)
  let rec get_vars_in_times = function
    | IntVar (_,x) -> [x]
    | Times lst ->
      let get_var = function | IntVar (_,x) -> [x] | _ -> [] in
      List.flat_map get_var lst
    | _ -> []
  in
  let rec get_vars_in_plus = function
    | Plus lst -> List.flat_map get_vars_in_times lst
    | whatever -> get_vars_in_times whatever
  in
  let get_vars_for exp =
    List.sort_unique (get_vars_in_plus exp)
  in
  (* helping function: combine an expression with the non-forbidden
  variables occurring accessibly inside it *)
  let combine_with_vars forbidden exp =
    let vs = get_vars_for exp in
    let vs = List.diff vs forbidden in
    (vs, List.length vs, exp)
  in
  (* find out all ways in which x is defined in [nuls] *)
  let rec check_instantiation x = function
    | Plus lst as plus ->
      let is_x exp = (exp = IntVar (true,x)) || (exp = IntVar (false,x)) in
      let is_x_neg exp =
        (exp = Times [Value (-1); IntVar (true,x)]) ||
        (exp = Times [Value (-1); IntVar (false,x)])
      in
      ( try
          let xvar = List.find is_x lst in
          [subtract xvar plus]
        with Not_found -> (
          try
            let xvar = List.find is_x_neg lst in
            [subtract plus xvar]
          with Not_found -> []
        )
      )
    | IntVar (_,y) -> if x = y then [Value 0] else []
    | _ -> []
  in
  let find_instantiations x = List.flat_map (check_instantiation x) in
  (* given a list of expressions, all equal to [exp], tries to find
  one which evaluates to an expression by instantiating variables not
  in [forbidden] *)
  let rec find_replacement forbidden exps =
    (* if any of them is already a value, we're done!*)
    let values = List.flat_map check_value exps in
    if values <> [] then Some (List.hd values) else
    (* we can't do anything for expressions without accessible
    variables, so toss those out *)
    let useful (_, k, _) = k > 0 in
    let usefuls = List.filter useful exps in
    (* let's not grow too large, otherwise this will be inefficient *)
    let cmp (_, n, _) (_, m, _) = compare n m in
    let exps =
      if List.length exps > 10 then
        List.take 10 (List.sort cmp usefuls)
      else usefuls
    in
    (* if there are no expressions in the list, we give up; otherwise,
    choose a variable to instantiate *)
    if exps = [] then None else
    let (vs, _, _) = List.hd exps in
    let x = List.hd vs in
    let instantiations = find_instantiations x nuls in
    (* instantiate x by each of the possibilities (and itself) in
    every element of exps, and forbid x in the result *)
    let instantiate_everywhere (vars, k, exp) =
      if not (List.mem x vars) then [(vars, k, exp)] else
      let try_instance inst =
        let subst = [(x, inst)] in
        let nexp = fst (instantiate_expression subst [] exp false) in
        combine_with_vars (x :: forbidden) nexp
      in
      let instances = List.map try_instance instantiations in
      (List.diff vars [x], k - 1, exp) :: instances
    in
    let newexps = List.flat_map instantiate_everywhere exps in
    find_replacement (x :: forbidden) newexps
  in
  find_replacement [] [combine_with_vars [] exp]

  (* SIMPLER SOLUTION: add and subtract all definitions
  (* is [exp + 0] a value? *)
  let add_to_exp nul = simplify_plus [exp;nul] in
  let chk2 = List.flat_map check_value (List.map add_to_exp nuls) in
  if chk2 <> [] then Some (List.hd chk2) else
  (* is [exp - 0] a value? *)
  let sub_from_exp nul = subtract exp nul in
  let chk3 = List.flat_map check_value (List.map sub_from_exp nuls) in
  if chk3 <> [] then Some (List.hd chk3) else
  (* damn, no good *)
  None
  *)
;;

(* given a formula, tries to find elements of the list which combine
to be turned into a quantifier; returns either (formula, lst) (if this
failed), or (newform, rest) where newform is a quantifier implying
formula, and rest those elements of lst which are not obviously
implied by newform. *)
let seek_quantifier_combination freshvar univ nuls jnuls formula lst =
  (* find those elements in lst which actually correspond to formula
  in all but one subexpression, plus some data *)
  let position_compare (i, form) =
    match abstract_formulas formula form ([],[]) [] with
      | None | Some (_,[]) -> []
      | Some (posses, exps) ->
        let rec up_arithmetic posses = function
          | _ :: (Plus lst1, Plus lst2) :: rest |
            _ :: (Times lst1, Times lst2) :: rest ->
            let newposses = List.map List.tl posses in
            let tail = (Plus lst1, Plus lst2) :: rest in
            up_arithmetic newposses tail
          | (e1, e2) :: _ -> (posses, e1, e2)
          | _ -> failwith "up_arithmetic_posses with empty list?"
        in
        let (posses, e1, e2) = up_arithmetic posses exps in
        [(i, posses, e1, e2)]
  in
  let info = List.flat_map position_compare lst in
  (* group these relevant elements by the positions they disagree with
  formula: to make a useful quantification, we'll need at least two
  different items to get a length-3-or-more quantification! *)
  let cmp (_,pos1,_,_) (_,pos2,_,_) = compare pos1 pos2 in
  let allgroups = List.group_fully ~c:cmp info in
  let large_enough group = List.length group >= 2 in
  let groups = List.filter large_enough allgroups in
  let get_info group =
    let (_,pos,e,_) = List.hd group in
    let make_info (i, _, e1, e2) = (i, e2, subtract e2 e1) in
    ((pos, e), List.map make_info group)
  in
  let groupinfo = List.map get_info groups in
  (* we are only interested in positions where the expression is a
  known integer away from the corresponding expression in formula *)
  let restrict_to_integer (i, exp, diff) =
    let legal_nul (j, nul) = if i = j then [] else [nul] in
    let allnuls = (List.flat_map legal_nul jnuls) @ nuls in
    match evaluates_to_int allnuls diff with
      | None -> []
      | Some k -> [(i, exp, k)]
  in
  let restrict_group (info, group) =
    (info, List.flat_map restrict_to_integer group) in
  let restricted = List.map restrict_group groupinfo in
  let goodgroups = List.filter (large_enough <.> snd) restricted in
  (* for that matter, we should be able to make a sequence; the
  following functions make sure that this can be done, and limit
  interest to groups with the required property *)
  let rec successive_sequence step start = function
    | [] -> []
    | hd :: tl ->
      let (_,_,k) = hd in
      if k = start + step then hd :: successive_sequence step k tl
      else if k = start then successive_sequence step k tl
      else []
  in
  let get_last_of default l =
    if l = [] then default
    else let (_, exp, _) = List.last l in exp
  in
  let check_group ((pos, exp), data) =
    (* data has elements (index in lst, expression at position pos of
    lst[i], diff between this expression and exp *)
    let (positives, negatives) =
      List.partition (fun (_,_,k) -> k > 0) data in
    let cmp (_,_,s) (_,_,t) = compare s t in
    let poss = List.sort cmp positives in
    let negs = List.sort (fun x y -> cmp y x) negatives in
    let poss = successive_sequence 1 0 poss in
    let negs = successive_sequence (-1) 0 negs in
    if (List.length poss) + (List.length negs) < 2 then None else
    let lowest = get_last_of exp negs in
    let highest = get_last_of exp poss in
    let index_of (i,_,_) = i in
    let involved = (List.map index_of negs) @
                   (List.map index_of poss) in
    Some (pos, lowest, highest, involved)
  in
  (* take the first group which is suitable and turn it into a
  quantifier, or fail and continue with the rest of the list *)
  let rec try_each_group = function
    | [] -> (formula, lst)
    | hd :: tail ->
      match check_group hd with
        | None -> try_each_group tail
        | Some (pos, lowest, highest, involved) ->
          let notinvolved (i, _) = not (List.mem i involved) in
          let lst = List.filter notinvolved lst in
          (* special cases for ?Q x in {...} [x >= k] and [x <= k] *)
          let specialcase =
            match formula with
              | Geq _ ->
                if (pos = [[0]]) && univ then Some lowest
                else if (pos = [[1]]) && univ then Some highest
                else if pos = [[0]] then Some highest
                else if pos = [[1]] then Some lowest
                else None
              | _ -> None
          in
          match specialcase with
            | None ->
              let x = freshvar () in
              let xvar = IntVar (univ, x) in
              let replace form pos =
                replace_at_position (List.rev pos) form xvar in
              let body = List.fold_left replace formula pos in
              (Quantifier (univ, x, lowest, highest, body), lst)
            | Some sub -> (replace_at_position (List.hd pos) formula sub, lst)
  in
  try_each_group goodgroups
;;

(* given And lst (if [universal] is true) or Or lst (if [universal is
false), tries to combine elements of [lst] into a universal or
existential quantification; the result is turned into a formula again
and returned. *)
let create_quantifiers_junction freshvar universal nuls jnuls lst =
  (* give all elements of lst an index, so as to refer more easily to
  them in the helping functions (note: the order doesn't matter, just
  that the index are unique) *)
  let args = List.mapi pair lst in
  (* iterate over the indexed list, trying to combine every item into
  a quantifier if we can *)
  let rec update_list = function
    | [] -> []
    | (i, form) :: tail ->
      let (base, rest) = seek_quantifier_combination freshvar
                                    universal nuls jnuls form tail in
      base :: update_list rest
  in
  match update_list args with
    | [] -> if universal then True else False
    | [single] -> single
    | l -> if universal then And l else Or l
;;

(* replaces instances of Ite in an expression by either subterm, if
it's easy to tell which side we should choose *)
let rec handle_obvious_ite nuls exp =
  let recurse = handle_obvious_ite nuls in
  let compare_to_nul x comparison a b c =
    match evaluates_to_int nuls x with
      | Some k -> if comparison k 0 then a else b
      | None -> Ite (c, a, b)
  in
  match exp with
    | Value _ | IntVar _ -> exp
    | Plus lst -> Plus (List.map recurse lst)
    | Times lst -> Times (List.map recurse lst)
    | Div (a, b) -> Div (recurse a, recurse b)
    | Mod (a, b) -> Mod (recurse a, recurse b)
    | UnknownExp (c, es, fs) ->
      UnknownExp (c, List.map recurse es, fs)
    | Ite (c, a, b) ->
      let a = recurse a in
      let b = recurse b in
      match c with
        | True -> a
        | False -> b
        | Geq (x, Value 0) -> compare_to_nul x (>=) a b c
        | Equal (x, Value 0) -> compare_to_nul x (=) a b c
        | Unequal (x, Value 0) -> compare_to_nul x (<>) a b c
        | _ -> Ite (c, a, b)
;;

(* creates quantifiers wherever this seems clever everywhere in
formula *)
let rec create_quantifiers nuls freshvar formula =
  let recurse = create_quantifiers nuls freshvar in
  match formula with
    | And lst | AndWithDefs (_, lst) ->
      let get_nuls i = function
        | Equal (x, Value 0) -> [(i, x)]
        | _ -> []
      in
      let newnuls = List.flat_mapi get_nuls lst in
      let combined = (List.map snd newnuls) @ nuls in
      let updatedlst = List.map (create_quantifiers combined freshvar) lst in
      create_quantifiers_junction freshvar true nuls newnuls updatedlst
    | Or lst | OrWithUndefs (_, lst) ->
      let get_nuls i = function
        | Unequal (x, Value 0) -> [(i, x)]
        | _ -> []
      in
      let newnuls = List.flat_mapi get_nuls lst in
      let combined = (List.map snd newnuls) @ nuls in
      let updatedlst = List.map (create_quantifiers combined freshvar) lst in
      create_quantifiers_junction freshvar false nuls newnuls updatedlst
    | Negate x -> Negate (recurse x)
    | Xor (x, y) -> Xor (recurse x, recurse y)
    | UnknownPred (c, elist, flist) ->
      UnknownPred (c, List.map (handle_obvious_ite nuls) elist,
                      List.map recurse flist)
    | Quantifier (universal, x, lower, upper, phi) ->
      Quantifier (universal, x, lower, upper, recurse phi)
    | Geq (a, b) -> Geq (handle_obvious_ite nuls a,
                         handle_obvious_ite nuls b)
    | Equal (a, b) -> Equal (handle_obvious_ite nuls a,
                             handle_obvious_ite nuls b)
    | Unequal (a, b) -> Unequal (handle_obvious_ite nuls a,
                                 handle_obvious_ite nuls b)
    | form -> form
;;

(* makes a term x = x *)
let make_equality a e x =
  let sort = Environment.find_sort x e in
  if sort = Alphabet.boolsort then Or [BoolVar (true, x); Negate (BoolVar (true, x))]
  else if sort = Alphabet.integer_sort a then
    Equal (IntVar (true, x), IntVar (true, x))
  else (
    let eq =
      try Alphabet.get_equal_symbol a
      with Not_found ->
        try Alphabet.find_fun "=" a
        with Not_found -> failwith ("No equality symbol set for " ^
          "variables of sort " ^ (Sort.to_string sort) ^ ".")
    in
    (* check whether we can type this properly! *)
    let test = ( match Alphabet.find_sortdec eq a with
      | Left sd ->
        sd = Sortdeclaration.create [sort;sort] Alphabet.boolsort
      | Right spd ->
        let input_okay polsort =
          (Specialdeclaration.is_polymorphic polsort) ||
          (Specialdeclaration.sort_to_pol sort = polsort)
        in
        ( Specialdeclaration.output_sort spd =
          Specialdeclaration.sort_to_pol Alphabet.boolsort ) &&
        ( ( not (Specialdeclaration.known_arity spd) ) ||
          ( Specialdeclaration.arity spd = 2 ) ) &&
        List.for_all input_okay (Specialdeclaration.input_sorts spd)
    ) in
    if not test then failwith ("Cannot create equality of sort " ^
                               (Sort.to_string sort) ^ "!") ;
    UnknownPred (Func (Function.find_name eq,
                       [OtherVar (true, x); OtherVar (true, x)]), [], [])
  )
;;

(* TODO: this really ought to be done on the new formula type which
natively handles arrays; the same holds for the rleated functions *)
let rec stores_in formula =
  match formula with
    | And lst | AndWithDefs (_, lst) -> List.flat_map stores_in lst
    | UnknownPred (Func ("=", [OtherVar (true, x); Func ("store",
                [OtherVar (false, y); IntExp 0; IntExp 1])]), [n;m], []) |
      UnknownPred (Func ("=", [Func ("store", [OtherVar (false, y);
                 IntExp 0; IntExp 1]); OtherVar (true, x)]), [n;m], []) ->
      (* x = store(y, n, m) or store(y, n, m) = x *)
      [(x, (y, n, m))]
    | _ -> []
;;

let rec remove_storage_variable freshvar original update position
                                newval oldval form =
  let recurse = remove_storage_variable freshvar original update
                                        position newval oldval in
  let rec safe_context = function
    | Func (_, lst) -> List.for_all safe_context lst
    | OtherVar (_, x) -> x <> original
    | IntExp _ | BoolExp _ -> true
  in
  let is_positive = function
    | Value k -> k > 0
    | _ -> false
  in
  let is_nonzero = function | Value k -> k <> 0 | _ -> false in
  let rec replace_inside = function
    | Value k -> Value k
    | IntVar (univ, v) -> IntVar (univ, v)
    | Div (a, b) -> Div (replace_inside a, replace_inside b)
    | Mod (a, b) -> Mod (replace_inside a, replace_inside b)
    | Plus lst -> Plus (List.map replace_inside lst)
    | Times lst -> Times (List.map replace_inside lst)
    | Ite (c, a, b) ->
      Ite (recurse c, replace_inside a, replace_inside b)
    | UnknownExp (c, es, fs) ->
      let es = List.map replace_inside es in
      let fs = List.map recurse fs in
      if safe_context c then UnknownExp (c, es, fs)
      else match (c, es) with
        | (Func ("size", [OtherVar (false, _)]), []) ->
          UnknownExp (Func ("size", [OtherVar (true, update)]), [], [])
        | (Func ("select", [OtherVar (false, _); IntExp 0]), [pos]) ->
          ( match subtract pos position with
              | Value 0 -> oldval
              | Value _ -> UnknownExp (Func ("select", [OtherVar
                  (true, update); IntExp 0]), [pos], [])
              | whatever ->
                Ite (Equal (whatever, Value 0), oldval,
                  UnknownExp (Func ("select", [OtherVar (true,
                  update); IntExp 0]), [pos], []))
          )
        | _ -> failwith "nope"
  in
  match form with
    | And lst | AndWithDefs (_, lst) -> And (List.map recurse lst)
    | Or lst | OrWithUndefs (_, lst) -> Or (List.map recurse lst)
    | Xor (a, b) -> Xor (recurse a, recurse b)
    | Negate a -> Negate (recurse a)
    | True | False | BoolVar _ -> form
    | Geq (a, b) -> Geq (replace_inside a, replace_inside b)
    | Equal (a, b) -> Equal (replace_inside a, replace_inside b)
    | Unequal (a, b) -> Unequal (replace_inside a, replace_inside b)
    | Quantifier (univ, x, l, u, f) ->
      Quantifier (univ, x, replace_inside l, replace_inside u, recurse f)
    | UnknownPred (c, es, fs) ->
      let es = List.map replace_inside es in
      let fs = List.map recurse fs in
      if safe_context c then UnknownPred (c, es, fs)
      else match (c, es) with
        | (* x = store (y, n, m) *)
          (Func ("=", [OtherVar (true, x); Func ("store",
            [OtherVar (false, y); IntExp 0; IntExp 1])]), [n;m]) |
          (Func ("=", [Func ("store", [OtherVar (false, y);
            IntExp 0; IntExp 1]); OtherVar (true, x)]), [n;m]) ->
          if (y = original) && (x = update) then (
            let left = UnknownExp (Func ("select",
              [OtherVar (true, x); IntExp 0]), [position], []) in
            Equal (left, newval)
          )
          else failwith "nope"
        | (* correspond (x, y, n, m) *)
          (Func ("correspond", [OtherVar (xval, x); OtherVar (yval, y);
            IntExp 0; IntExp 1]), [n;m]) ->
            let (other, oval) =
              if x = original then (y, yval)
              else (x, xval)
            in
            if (is_positive (subtract position m)) ||
               (is_positive (subtract n position)) ||
               (m = newval) then (
              UnknownPred (Func ("correspond",
                [OtherVar (true, update); OtherVar (oval, other);
                 IntExp 0; IntExp 1]), [n;m], [])
            ) (*
            else (
              let bv = freshvar () in
              let select_in
              Quantifier (true, bv, n, m, corresponding)
            )
            *)
            else failwith "nope"
        | (* nonzero (x, n, m) *)
          (Func ("nonzero", [OtherVar (false, _); IntExp 0; IntExp 1]),
            [n;m]) ->
            if (is_positive (subtract position m)) ||
               (is_positive (subtract n position)) ||
               (is_nonzero newval) then (
              UnknownPred (Func ("nonzero", [OtherVar (true, update);
                IntExp 0; IntExp 1]), [n;m], [])
            )
            else failwith "nope"
        | _ -> failwith "nope"
;;

(* if a universally quantified variable x is defined as store(y, n, m)
and y is an existentially quantified variable, then we try to remove y
altogether, and instead use at most a variable for y[n] *)
let ditch_array_stores alf env formula =
  let stores = stores_in formula in
  let rec ditch_duplicates = function
    | [] -> []
    | (x, v) :: tail ->
      if List.mem_assoc x tail then ditch_duplicates tail
      else (x, v) :: ditch_duplicates tail
  in
  let stores = ditch_duplicates stores in
  if stores = [] then formula else
  let isort =
    try Alphabet.integer_sort alf
    with Not_found -> parsefail "Integer sort unset!"
  in
  let fn = Alphabet.fun_names alf in
  let freshvar _ = Environment.create_sorted_var isort fn env in
  let handle_storage form (x, (y, n, m)) =
    let yn = IntVar (false, freshvar ()) in
    try remove_storage_variable freshvar y x n m yn form
    with Failure "nope" -> form
  in
  let formula = List.fold_left handle_storage formula stores in
  formula
;;

(* appearances is a list of (parameter variable, indicator pairs, where
indicator is one of the following:
- None: we have not encountered this variable so far
- Some 0: we have encountered this variable in an equality
- Some 1: we have encountered this variable in the form x >= ...
- Some -1: we have encountered this variable in the form ... >= x
Variables not in the list have been in different ways, and are not
guaranteed to be possible to fill in in a satisfying way *)
(*
let rec update_appearances appearances formula =
  let update_in_all = List.fold_left update_appearances appearances in
  let update_single x kind (y, at) =
    if x <> y then [(y, at)]
    else match at with
      | None -> [(y, Some kind)]
      | Some 0 -> []
      | Some k -> if k = kind then [(y, at)] else []
  in
  let update_all_in x kind = List.flat_map (update_single x kind) in
  let remove_from_appearances x = List.filter (fun (y,_) -> x <> y) in
  match formula with
    | And lst | AndWithDefs (_, lst) | Or lst | OrWithUndefs (_, lst) ->
      update_in_all lst
    | Xor (a, b) -> update_in_all [a;b]
    | Negate a -> update_appearances appearances a
    | True | False | BoolVar (true, _) -> appearances
    | BoolVar (false, x) -> update_all_in x 0 appearances
    | Geq (a, b) ->
      let diff = subtract a b in
      let sign k = if k > 0 then 1 else if k < 0 then (-1) else 0 in
      let rec test_occurrence_list x = function
        | [] -> 0
        | (IntVar (_, y)) :: tail ->
          if x <> y then test_occurrence_list x tail
          else if occurs_in y tail then 42 else 1
        | (Times [Value k; IntVar (_, y)]) :: tail ->
          if (x <> y) || (k = 0) then test_occurrence_list x tail
          else if occurs_in x (Plus tail) then 42
          else sign k
        | head :: tail ->
          if occurs_in x head then 42
          else test_occurrence_list x tail
      in
      let test_occurrence x = function
        | Plus lst -> test_occurrence_list x lst
        | single -> test_occurence_list x [single]
      in
      let check_dangerous apps x =
        let test = test_occurrence x diff in
        if test = 1 then update_all_in x 1 apps (* positive occurrence *)
        else if test = -1 then update_all_in x (-1) apps
        else if test = 0 then apps (* does not occur *)
        else remove_from_appearances x apps
          (* does not obviously occur positively or negatively *)
      in
      List.fold_left check_dangerous appearances (get_params formula)
    (*
                  Geq of intexpression * intexpression |
                  Equal of intexpression * intexpression |
                  Unequal of intexpression * intexpression |
                  UnknownPred of othercontext * intexpression list *
                                 intformula list |
                  Quantifier of bool * Variable.t * intexpression *
                                intexpression * intformula
    *)
;;
*)

let ditch_unnecessary_parameters formula =
  (*
  let vs = get_params formula in
  let appearances = List.map (fun x -> (x,None)) vs in
  let appearances = update_appearances appearances formula in
  *)
  formula
;;

let simplify_constraint ren tr a e vs phi =
  let vs = List.intersect vs (Term.vars phi) in
  (* get the formula in a standard format *)
  let isparam x = not (List.mem x vs) in
  let formula = translate_bool ren tr a e isparam phi in
  let formula = ditch_xor true (ditch_ite formula) in
  (* ditch array updates and unnecessary variables where possible *)
  let formula = ditch_array_stores a e formula in
  let formula = ditch_unnecessary_parameters formula in
  let formula = basic_simplify [] (simplify_ints_in formula) in
  (* turn conjunctions with the same formula over successive numbers
  (e.g. C[x] /\ C[x+1] /\ C[x+2]) into universal quantifications, and
  disjunctions into existential quantifications *)
  let fn = Alphabet.fun_names a in
  let isort =
    try Alphabet.integer_sort a
    with Not_found -> parsefail "integer sort not even set!"
  in
  let makefresh () = Environment.create_sorted_var isort fn e in
  let updated = create_quantifiers [] makefresh formula in
  (* make sure we haven't forgotten any variables (for instance x = x
  occurrences which are added to force a variable to be instantiated
  by a value *)
  let vars = get_univars updated in
  let forgotten = List.diff vs vars in
  let equalities = List.map (make_equality a e) forgotten in
  let form =
    if equalities = [] then updated
    else match updated with
      | And lst -> And (lst @ equalities)
      | _ -> And (updated :: equalities)
  in
  (* translate the adapted formula back to a term! *)
  try translate_formula_back ren a e form
  with _ -> phi
;;

(*****************************************************************************)
(* solving smt-problems: main functionality                                  *)
(*****************************************************************************)

(* returns whether there are any occurrences of BoolVar true or IntVar true *)
let rec hasvars bound form =
  let ehasvars exp =
    let checker = function
      | IntVar (true, var) -> not (List.mem var bound)
      | _ -> false
    in
    find_sub_expr checker false exp <> None
  in
  match form with
    | And lst | Or lst | AndWithDefs (_, lst) | OrWithUndefs (_, lst) ->
      List.exists (hasvars bound) lst
    | BoolVar (true, var) -> not (List.mem var bound)
    | Negate x -> hasvars bound x
    | Xor (x, y) -> (hasvars bound x) || (hasvars bound y)
    | True | False | BoolVar (false, _) -> false
    | Geq (x, y) | Equal (x, y) | Unequal (x, y) ->
      (ehasvars x) || (ehasvars y)
    | UnknownPred (_, es, fs) ->
      (List.exists (hasvars bound) fs) || (List.exists ehasvars es)
    | Quantifier (universal, x, lower, upper, subform) ->
      (ehasvars lower) || (ehasvars upper) ||
      (hasvars (x :: bound) subform)
;;

(* returns whether there are any occurrences of Mul, not counting
Value * variable *)
let rec hasmuls form =
  let badmul = function
    | Times [Value _; IntVar _] -> false
    | Times _ -> true
    | _ -> false
  in
  let ehasmuls e = find_sub_expr badmul false e <> None in
  match form with
    | And lst | Or lst | AndWithDefs (_, lst) | OrWithUndefs (_, lst) ->
      List.exists hasmuls lst
    | Negate x -> hasmuls x
    | Xor (x, y) -> (hasmuls x) || (hasmuls y)
    | Geq (x, y) | Equal (x, y) | Unequal (x, y) ->
      (ehasmuls x) || (ehasmuls y)
    | UnknownPred (_, es, fs) ->
      (List.exists ehasmuls es) || (List.exists hasmuls fs)
    | Quantifier (universal, x, lower, upper, form) ->
      (ehasmuls lower) || (ehasmuls upper) || (hasmuls form)
    | True | False | BoolVar _ -> false
;;

(* returns whether there are any occurrences of Quantifier *)
let rec hasquantifiers form =
  let rec check_expression = function
    | Value _ | IntVar _ -> false
    | Plus lst | Times lst -> List.exists check_expression lst
    | Div (a,b) | Mod (a,b) -> (check_expression a) || (check_expression b)
    | Ite (form, a, b) -> (hasquantifiers form) || (check_expression a) ||
                          (check_expression b)
    | UnknownExp (_, es, fs) ->
      (List.exists hasquantifiers fs) || (List.exists check_expression es)
  in
  match form with
    | Quantifier _ -> true
    | And lst | Or lst | AndWithDefs (_, lst) | OrWithUndefs (_, lst) ->
      List.exists hasquantifiers lst
    | Negate x -> hasquantifiers x
    | Xor (x, y) -> (hasquantifiers x) || (hasquantifiers y)
    | UnknownPred (_, es, fs) ->
      (List.exists hasquantifiers fs) || (List.exists check_expression es)
    | Geq (a,b) | Equal (a,b) | Unequal (a,b) ->
      (check_expression a) || (check_expression b)
    | True | False | BoolVar _ -> false
;;

(* given a validity problem, find a satisfiability problem such that
validity of original <--> unsatisfiability of created *)
let transform_validity_problem problem e =
  let negated = basic_simplify [] (negate problem) in
  let vars = get_vars (const true) (const true) (const true) negated in
  let isint x =
    let sort = Sort.to_string (Environment.find_sort x e) in
    sort = "Int"
  in
  let (intvars, boolvars) = List.partition isint vars in
  let isub = List.map (fun x -> (x,IntVar (false,x))) intvars in
  let fsub = List.map (fun x -> (x,BoolVar (false,x))) boolvars in
  fst (instantiate_formula isub fsub negated false)
;;

let solve_satisfiability formulas solver renamings translations alf env =
  let vars = List.flat_map Term.vars formulas in
  let varsorts = List.map (fun x -> Environment.find_sort x env) vars in
  let problem = satisfiability_problem formulas renamings translations alf env in
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
  (* TODO: try a straightforward satisfying instantiation *)
  else if solver = "" then (UNKNOWN, Substitution.empty)
  else (
    let nonlinear = hasmuls remainder in
    let quant = hasquantifiers remainder in
    solve_externally env alf remainder nonlinear quant solver
  )
;;

let solve_validity formulas solver renamings translations alf env =
  let problem = validity_problem formulas renamings translations alf env in
  let remainder = advanced_simplify problem 3 in
  (*
  Printf.printf "Before: " ;
  print_formula env problem ;
  Printf.printf "\n" ;
  Printf.printf "After: " ;
  print_formula env remainder ;
  Printf.printf "\n" ;
  *)
  if remainder = True then SAT
  else if remainder = False then UNSAT
  else if solver = "" then UNKNOWN
  else (
    let transformed = transform_validity_problem problem env in
    let nonlinear = hasmuls transformed in
    let quant = hasquantifiers remainder in
    let (inverseanswer, _) =
      solve_externally env alf transformed nonlinear quant solver
    in
    if inverseanswer = SAT then UNSAT
    else if inverseanswer = UNSAT then SAT
    else UNKNOWN
  )
;;

let get_ranged_value sort alf start ending =
  let chosen =
    if (start <= 0) && (0 <= ending) then 0
    else if start < 0 then ending
    else start
  in
  let sortstring = Sort.to_string sort in
  if sortstring = "Int" then
    Term.make_fun (Function.integer_symbol chosen) []
  else if sortstring = "Bool" then (
    let f =
      try
        if chosen = 1 then Alphabet.get_top_symbol alf
        else Alphabet.get_bot_symbol alf
      with Not_found -> failwith ("Cannot use internal set_value " ^
                                  "if top/bottom symbol is not set!")
    in
    Term.make_fun f []
  )
  else raise (NoInternalProblem ("Cannot find a value of sort " ^ sortstring))
;;

let solve_existential_validity formulas varswithrange solvername
                               renamings translations alf env =
  if varswithrange = [] then
    (solve_validity formulas solvername renamings translations alf env,
    Substitution.empty)
  else
  let problem = make_existsvalid formulas varswithrange renamings translations alf env in
  (*let remainder = advanced_simplify problem 3 in*)
  let remainder = add_def_counts problem in
  if remainder = False then (UNSAT, Substitution.empty) else
  if remainder = True then (
    let addvarchoice (x, range) =
      let sort = Environment.find_sort x env in
      match range with
        | None -> (x, get_ranged_value sort alf 0 0)
        | Some (a, b) -> (x, get_ranged_value sort alf a b)
    in
    let choices = List.map addvarchoice varswithrange in
    let makesubst gamma (x, value) = Substitution.add x value gamma in
    (SAT, List.fold_left makesubst Substitution.empty choices)
  ) else
  (* okay, it's not -obvious-; we'll go and transform the formulas
  into a satisfiability problem one by one then *)
  let forms = (match remainder with
    | And lst | AndWithDefs (_,lst) -> lst
    | x -> [x])
  in
  (*
  Printf.printf "Formulas:\n" ;
  List.iter print_formula forms ;
  Printf.printf "Vars with range:\n" ;
  let print_varwithrange = function
    | (x, None) -> Printf.printf "  %s : anything\n" (Variable.to_string x)
    | (x, Some (i,j)) -> Printf.printf "  %s : (%d,%d)\n" (Variable.to_string x) i j
  in
  List.iter print_varwithrange varswithrange ;
  *)
  let satprob = (
    match simple_exists_valid_problem forms with
      | Some lst ->
        simple_remove_validity_checks env lst
      | None ->
        let rangelessoptions = integer_values_in formulas in
        let acceptablevalues = make_varmap env varswithrange rangelessoptions in
        let formswithvars = sort_formulas forms in
        remove_validity_checks env acceptablevalues formswithvars
  ) in
  let nonlinear = hasmuls satprob in
  let quant = hasquantifiers remainder in
  (*Printf.printf "about to solve externally, satprob = %s\n" (tostr_formula false env satprob) ;*)
  match solve_externally env alf satprob nonlinear quant solvername with
    | (UNSAT, gamma) -> (UNKNOWN, gamma)
    | pair -> pair
;;

