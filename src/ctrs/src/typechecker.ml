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
open Prelude;;
open Util;;

(*** TYPES *******************************************************************)
type fakesort = RealSort of Sort.t | FakeSort of int
type func = Function.t
type sd = Sortdeclaration.t
type term = Term.t = Var of Variable.t | Fun of Function.t * term list |
                     InstanceFun of Function.t * term list * Sortdeclaration.t|
                     Forall of Variable.t * term | Exists of Variable.t * term
type rule = Rule.t

(*** MODULES *****************************************************************)

module FakeSort = struct
  type t = fakesort

  let compare a b =
    match a with
      | RealSort aa -> (
        match b with
          | RealSort bb -> compare aa bb
          | FakeSort _ -> -1
        )
      | FakeSort aa -> (
        match b with
          | RealSort _ -> 1
          | FakeSort bb -> compare aa bb
        )

  let to_string a =
    match a with
      | RealSort b -> Sort.to_string b
      | FakeSort b -> string_of_int b

  let fprintf fmt a =
    Format.fprintf fmt "%s" (to_string a)
end;;

module FakeSortDeclaration = struct
  type t = fakesort list * fakesort

  let compare x y =
    let rec comparelists a b =
      match a with
        | [] -> (
          match b with
            | [] -> 0
            | head :: tail -> -1
          )
        | head :: tail -> (
          match b with
            | [] -> 1
            | hd :: tl ->
              let cmp = FakeSort.compare head hd in
              if cmp != 0 then cmp
              else comparelists tail tl
          )
    in
    comparelists ((snd x) :: (fst x)) ((snd y) :: (fst y))

  let to_string a =
    let rec listify_help lst =
      match lst with
        | [] -> "]"
        | head :: [] -> (FakeSort.to_string head) ^ "]"
        | head :: tail -> (FakeSort.to_string head) ^ " * " ^ (listify_help tail)
    in
    "[" ^ (listify_help (fst a)) ^ " ==> " ^ (FakeSort.to_string (snd a))

  let fprintf fmt a =
    Format.fprintf fmt "%s" (to_string a)
end;;

module EnvVar = struct
  type t = Variable.t * Environment.t

  let compare = compare
  let fprintf fmt (x,e) = Variable.fprintf fmt x ; Environment.fprintf fmt e
end;;

module FakeSortMap = Map.Make (EnvVar) (FakeSort);;
module FakeDeclarationMap = Map.Make (Function) (FakeSortDeclaration);;

(*** FUNCTIONS ***************************************************************)

(** general accessing functions *)
let alf = ref None;;

let get_alphabet _ =
  match !alf with
    | None -> failwith "alphabet unset, shouldn't happen"
    | Some a -> a
;;

(** initialising the type derivation: fake declarations **)

(* recreates a real sort declaration as a fake declaration *)
let recreate declaration =
  let rec make_real_list i m dec =
    if i <= m then
      (RealSort (Sortdeclaration.input_sort dec i)) ::
      (make_real_list (i+1) m dec)
    else []
  in
  let n = Sortdeclaration.arity declaration in
  let lst = make_real_list 1 n declaration in
  (lst, RealSort (Sortdeclaration.output_sort declaration))
;;

(* fake_declarations is given a list of function symbols and a
starting number (typically 0), and returns a pair.  The first element
of this pair is the main return value: a list of pairs (symbol, "sort
declaration"), where the sort declaration uses fresh integers for all
input sorts and the output sort if they aren't already known.  The
second element is an int which indicates how many fake "sorts" were
used (and thereby automatically the first unused number).
*)
let rec fake_declarations lst k sofar =
  let alphabet = get_alphabet () in
  let rec make_fake_list i m =
    if m = 0 then []
    else (FakeSort i) :: make_fake_list (i+1) (m-1)
  in
  match lst with
    | [] -> (sofar, k)
    | f :: tail ->
      if (Alphabet.mem_sortdec f alphabet) then (
        let esd = Alphabet.find_sortdec f alphabet in
        let updated = ( match esd with
          | Left sd -> FakeDeclarationMap.add f (recreate sd) sofar
          | Right _ -> sofar
        ) in
        fake_declarations tail k updated
      )
      else if (Alphabet.mem_ari f alphabet) then (
        let n = Alphabet.find_ari f alphabet in
        let updated = FakeDeclarationMap.add f
                      (make_fake_list k n, FakeSort (k+n)) sofar in
        fake_declarations tail (n+k+1) updated
      )
      else failwith ("Trying to derive sorts of a TRS without " ^
                     "having an arity for all function symbols.")
;;

(* fake_varsorts is given a list of rules with environments, and
returns a mapping (var, env) -> fake sort, where the "sort" uses a fresh
integer, or the sort of the variable in the given environment if
declared *)
let rec fake_varsorts rulelist k sofar =
  let rec fake_varsorts_single varlist e j sofar =
    match varlist with
      | [] -> (sofar, j)
      | x :: tail ->
        let sort, i =
          if (Environment.has_sort x e)
          then (RealSort (Environment.find_sort x e), j)
          else (FakeSort j, j+1)
        in
        fake_varsorts_single tail e i (FakeSortMap.add (x,e) sort sofar)
  in
  match rulelist with
    | [] -> (sofar, k)
    | (rule, env) :: tail ->
      let (newsofar, j) =
        fake_varsorts_single (Rule.allvars rule) env k sofar
      in
      fake_varsorts tail j newsofar
;;

(** fake_posses is given a term, and finds all positions which have
a normal function with a symbol that is declared with a special
declaration; the result consists of triples (function symbol,
position of occurrence, arity of the occurrence) *)
let rec fake_posses term =
  let a = get_alphabet () in
  let addimain i (f, j, ar) = (f, Position.add_first i j, ar) in
  let addi i = List.map (addimain i) <.> fake_posses in
  match term with
  | Var _ -> []
  | InstanceFun (_,ts,_) -> List.flat_mapi addi ts
  | Fun (f,ts) ->
    if not (Alphabet.mem_sortdec f a) then List.flat_mapi addi ts
    else (
      match Alphabet.find_sortdec f a with
        | Left _ -> List.flat_mapi addi ts
        | Right _ -> (f, Position.root, List.length ts) :: List.flat_mapi addi ts
    )
  | Forall (_,s) | Exists (_,s) -> List.flat_mapi addi [s]
;;

(** [fake_sortdec_instance f ar k] creates a fake sort declaration
for an occurrence of the symbol [f] (which is declared with an instance
declaration), assuming it occurs with arity [ar]. The number [k]
indicates the first unused integer to use for fake sort declarations. *)
let fake_sortdec_instance f ar k =
  let a = get_alphabet () in
  let special = match Alphabet.find_sortdec f a with
    | Left _ -> failwith "fake sortdec instance"
    | Right sd -> sd
  in
  let rec fakesortlist fakes k = function
    | [] -> ([], k)
    | polsort :: tail ->
      let srt, updatedfakes, i = (
        if Specialdeclaration.is_polymorphic polsort then (
          let str = Specialdeclaration.pol_to_string polsort in
          try (FakeSort (List.assoc str fakes), fakes, 0)
          with Not_found -> (FakeSort k, (str,k) :: fakes, 1)
        )
        else (RealSort (Specialdeclaration.pol_to_sort polsort), fakes, 0)
      ) in
      let (rest, newk) = fakesortlist updatedfakes (k+i) tail in
      (srt :: rest, newk)
  in
  let relevantpolsorts = (
    if Specialdeclaration.known_arity special then (
      let rec inputs i n =
        if i > n then []
        else (Specialdeclaration.input_sort i special) :: (inputs (i+1) n)
      in
      let inps = inputs 1 (Specialdeclaration.arity special) in
      if ar <> List.length inps then
        failwith ("Symbol " ^ (Function.find_name f) ^
                  " occurs with arity " ^ (string_of_int ar) ^
                  " but was declared with arity " ^
                  (string_of_int (List.length inps)) ^ ".")
      else (Specialdeclaration.output_sort special) :: inps
    )
    else (
      let rec repeat sort n =
        if n = 0 then [] else sort :: repeat sort (n-1)
      in
      (Specialdeclaration.output_sort special) ::
      (repeat (Specialdeclaration.input_sort 0 special) ar)
    )
  ) in
  let (fakesorts, updatedk) = fakesortlist [] k relevantpolsorts in
  ((List.tl fakesorts, List.hd fakesorts), updatedk)
;;

(** creates a list of positions in the term where a sort declaration
(for an instance) should be added, along with the fake sort
declaration used in that spot *)
let fake_termsorts term k start sofar =
  let rec runthroughlist k sofar = function
    | [] -> (sofar, k)
    | (f, pos, ar) :: tail ->
      let dec, k = fake_sortdec_instance f ar k in
      runthroughlist k ((Position.append start pos, dec) :: sofar) tail
  in
  runthroughlist k sofar (fake_posses term)
;;

(** gets a list of position => fake sort declaration entries for all
positions anywhere in the rule which should be turned into an
instance declaration *)
let rec fake_positionsorts rulelist k sofar i =
  let rulepos = Position.add_first i (Position.root) in
  let pos i = (Position.add_last i rulepos) in
  let rec fake_constraints_sorts k j sofar = function
    | [] -> (sofar, k)
    | c :: tail ->
      let sofar, k = fake_termsorts c k (pos j) sofar in
      fake_constraints_sorts k (j+1) sofar tail
  in
  let fake_rulepossorts rule =
    let sofar, k = fake_termsorts (Rule.lhs rule) k (pos 0) sofar in
    let sofar, k = fake_termsorts (Rule.rhs rule) k (pos 1) sofar in
    fake_constraints_sorts k 2 sofar (Rule.constraints rule)
  in
  match rulelist with
    | [] -> (sofar, k)
    | (rule, _) :: tail ->
      let (newsofar, j) = fake_rulepossorts rule in
      fake_positionsorts tail j newsofar (i+1)
;;

(* goes through the list of position sorts, and for all positions
[id p], adds [p] to the result *)
let sub_position_sorts id possorts =
  let lower_pos (pos, dec) = (snd (Position.split_first pos), dec) in
  let right_pos (pos, dec) = Position.is_head id pos in
  List.map lower_pos (List.filter right_pos possorts)
;;

(** checking and updating the equalitymapping *)

(* the equality mapping is an array with entries FakeSort -1
(indicating that this fake sort is not known to be equal to any
smaller sorts), or [a] = b, with 0 <= b < a (indicating that
FakeSort a and b are equal); this function returns the smallest
sort "equal" to the given sort
*)
let rec trace_main_sort sort equalitymapping =
  match sort with
    | RealSort s -> sort
    | FakeSort s ->
    match equalitymapping.(s) with
      | RealSort a -> equalitymapping.(s)
      | FakeSort a ->
        if a < 0 then sort
        else trace_main_sort equalitymapping.(s) equalitymapping
;;

(* prints the main sort of s for debug information *)
let to_string_main_sort s equalitymapping =
  let smain = trace_main_sort s equalitymapping in
  match smain with
    | RealSort t -> Sort.to_string t
    | FakeSort t -> "{" ^ Int.to_string t ^ "}"
;;

(* add a new equality to the equality mapping, making sure to add
the equality to the *main* sorts, so no equalities are lost; if two
real different real sorts are attempted to be unified, this leads
to a non-empty string being returned
*)
let add_sort_equality s t equalitymapping =
  let smain = trace_main_sort s equalitymapping in
  let tmain = trace_main_sort t equalitymapping in
  match smain with
    | RealSort ss -> (
      match tmain with
        | RealSort tt ->
          if Sort.equal ss tt then ""
          else "Type checking error: cannot unify " ^
            (Sort.to_string ss) ^ " with " ^
            (Sort.to_string tt)
        | FakeSort tt ->
          equalitymapping.(tt) <- smain ; ""
      )
    | FakeSort ss -> (
      match tmain with
        | RealSort tt ->
          equalitymapping.(ss) <- tmain ; ""
        | FakeSort tt ->
          if ss < tt then (equalitymapping.(tt) <- smain ; "")
          else (
            if tt < ss then (equalitymapping.(ss) <- tmain ; "")
            else ""
          )
      )
;;

(* returns the (main) fake sort of the given term *)
let get_fake_sort term pos env funsorts varsorts possorts equalitymapping =
  match term with
    | Var x -> trace_main_sort (FakeSortMap.find (x,env) varsorts) equalitymapping
    | InstanceFun (f, _, sd) ->
      RealSort (Sortdeclaration.output_sort sd)
    | Fun (f, _) -> (
      try
        trace_main_sort
          (snd (FakeDeclarationMap.find f funsorts)) equalitymapping
      with Not_found ->
        trace_main_sort (snd (List.assoc pos possorts)) equalitymapping
      )
    | Forall _ | Exists _ -> RealSort Alphabet.boolsort
;;

let force_equal_types term1 pos1 term2 pos2 env funsorts varsorts possorts equalitymapping =
  let a = get_fake_sort term1 pos1 env funsorts varsorts possorts equalitymapping in
  let b = get_fake_sort term2 pos2 env funsorts varsorts possorts equalitymapping in
  let msg = add_sort_equality a b equalitymapping in
  if msg <> "" then (
    let term1str = Term.to_string term1 in
    let term2str = Term.to_string term2 in
    "Type checking error: cannot unify types of " ^ term1str ^
      " (" ^ (to_string_main_sort a equalitymapping) ^ ") and " ^ term2str ^
      " (" ^ (to_string_main_sort b equalitymapping) ^ ")"
  )
  else ""
;;

(** enforcing fake sort equalities as required by the rules *)

(* saves sort equalities induced by a term, and throws a failure if
this gives any problems! *)
let rec parse_term_sorts term env funsorts varsorts possorts equalitymapping =
  let pos i = (Position.add_first i Position.root) in
  let rec parse_args args i declaration =
    match args with
      | [] -> None
      | arg :: restargs ->
        let sort1 = get_fake_sort arg (pos i) env funsorts varsorts possorts equalitymapping in
        let sort2 = List.hd declaration in
        let a = add_sort_equality sort1 sort2 equalitymapping in
        if a <> "" then Some (a, arg)
        else (
          parse_term_sorts arg env funsorts varsorts
                (sub_position_sorts i possorts) equalitymapping ;
          parse_args restargs (i+1) (List.tl declaration)
        )
  in
  match term with
    | Var _ -> ()
    | Fun (_, args) | InstanceFun (_, args, _) -> (
      let argssorts = fst (
        match term with
          | Var _ | Forall _ | Exists _ -> failwith "meh"
          | InstanceFun (_,_,dec) -> recreate dec
          | Fun (f,_) ->
            try FakeDeclarationMap.find f funsorts
            with Not_found -> List.assoc Position.root possorts
      ) in
      match (parse_args args 0 argssorts) with
        | None -> ()
        | Some (msg, arg) ->
          failwith (msg ^ ". Type of " ^
            (Term.to_string arg) ^ " in " ^ (Term.to_string term))
    )
    | Forall (_, arg) | Exists (_, arg) ->
      let sort = get_fake_sort arg (pos 0) env funsorts varsorts possorts equalitymapping in
      let a = add_sort_equality sort (RealSort Alphabet.boolsort) equalitymapping in
      if a <> "" then failwith (a ^ ". Type of " ^
        (Term.to_string arg) ^ " below quantifier.")
;;

let parse_constraint_sorts c env funsorts varsorts possorts equalitymapping =
  let boolsort = RealSort Alphabet.boolsort in
  let add_constraint_info msg =
    msg ^ " in constraint [" ^ (Term.to_string c) ^ "]"
  in
  try
    let sort = get_fake_sort c Position.root env funsorts varsorts possorts equalitymapping in
    let msg = add_sort_equality sort boolsort equalitymapping in
    if msg <> "" then (
      let srt = to_string_main_sort sort equalitymapping in
      failwith ("Type checking error: logical constraints should have " ^
        "sort Bool, but [" ^ (Term.to_string c) ^ "] has sort " ^ srt)
    )
    else parse_term_sorts c env funsorts varsorts possorts equalitymapping
  with Failure s -> failwith (add_constraint_info s)
;;

(* saves sort equalities induced by a rule and returns a non-empty
string if this gives problems *)
let parse_rule_sorts rule env funsorts varsorts possorts equalitymapping =
  let lhs = Rule.lhs rule in
  let rhs = Rule.rhs rule in
  let constraints = Rule.constraints rule in
  let add_rule_info msg =
    msg ^ " in rule " ^ (Rule.to_string rule) ^ ".  " ^
          "{note that debug representations of terms are given}"
  in
  let pos i = Position.add_first i Position.root in
  try
    parse_term_sorts lhs env funsorts varsorts
                     (sub_position_sorts 0 possorts) equalitymapping ;
    parse_term_sorts rhs env funsorts varsorts
                     (sub_position_sorts 1 possorts) equalitymapping;
    let rec parse_constraints_sorts j = function
      | [] -> ()
      | head :: tail ->
        parse_constraint_sorts head env funsorts varsorts
                               (sub_position_sorts j possorts)
                               equalitymapping ;
        parse_constraints_sorts (j+1) tail
    in
    parse_constraints_sorts 2 constraints ;
    let msg = force_equal_types lhs (pos 0) rhs (pos 1) env funsorts
                                varsorts possorts equalitymapping in
    if msg <> "" then
      failwith ("different sides of rules should have the same type; " ^ msg)
    else ()
  with Failure s -> failwith (add_rule_info s)
;;

(* saves sort equalities induced by a number of rules *)
let rec parse_rules_sorts rules funsorts varsorts possorts equalitymapping id =
  match rules with
    | [] -> ()
    | (rule, env) :: tail ->
      let ps = sub_position_sorts id possorts in
      parse_rule_sorts rule env funsorts varsorts ps equalitymapping ;
      parse_rules_sorts tail funsorts varsorts possorts equalitymapping (id+1)
;;

(** deriving conclusions from the equality mapping *)

let realify_sortdec (args, outp) equalitymapping =
  let realify fs =
    match fs with
      | RealSort s -> s
      | FakeSort _ -> Sort.from_string "Unit"
  in
  let rec lookup_and_realify_args args =
    match args with
      | [] -> []
      | head :: tail ->
        realify (trace_main_sort head equalitymapping) ::
          lookup_and_realify_args tail
  in
  let o = realify (trace_main_sort outp equalitymapping) in
  let a = lookup_and_realify_args args in
  Sortdeclaration.create a o
;;

(* having derived a number of sort equalities and not run into
contradictions, this function fixes a sort declaration for every function
symbol, choosing Unit for non-fixed sorts; the return value is a list of
new sort declarations which should get declared *)
let make_derived_function_declarations funsorts equalitymapping =
  let alphabet = get_alphabet () in
  let declare key (args, outp) sofar =
    match outp with
      | RealSort s -> sofar
      | FakeSort s ->
        let sortdec = realify_sortdec (args, outp) equalitymapping in
        Alphabet.add_normal_sortdec key sortdec alphabet ;
        s :: sofar
  in
  List.unique (FakeDeclarationMap.fold declare funsorts [])
;;

let make_derived_variable_declarations varsorts equalitymapping units =
  let declare (var, env) sort =
    match sort with
      | RealSort _ -> ()
      | FakeSort _ ->
        let sort = trace_main_sort sort equalitymapping in
        let realsort = (  match sort with
          | RealSort s -> s
          | FakeSort u ->
            if List.mem u units then Sort.from_string "Unit"
            else Sort.from_string "Bool"
        ) in
        Environment.add_sort var realsort env
  in
  FakeSortMap.iter declare varsorts
;;

let rec make_term_derivations possorts equalitymapping term =
  let alphabet = get_alphabet () in
  let rec fix_args i = function
    | [] -> []
    | arg :: rest ->
      (make_term_derivations (sub_position_sorts i possorts) equalitymapping arg) ::
      fix_args (i+1) rest
  in
  match term with
    | Var x -> Var x
    | Forall (x, s) ->
      let lower_pos (pos, dec) = (Position.tail pos, dec) in
      let subsorts = List.map lower_pos possorts in
      Forall (x, make_term_derivations subsorts equalitymapping s)
    | Exists (x, s) ->
      let lower_pos (pos, dec) = (Position.tail pos, dec) in
      let subsorts = List.map lower_pos possorts in
      Exists (x, make_term_derivations subsorts equalitymapping s)
    | InstanceFun (f, args, dec) -> InstanceFun (f, fix_args 0 args, dec)
    | Fun (f, args) ->
      let args = fix_args 0 args in
      match Alphabet.find_sortdec f alphabet with
        | Left _ -> Fun (f, args)
        | Right _ ->
          let fakesd = List.assoc Position.root possorts in
          InstanceFun (f, args, realify_sortdec fakesd equalitymapping)
;;

let rec make_position_derivations possorts equalitymapping i rules =
  let make_term term possorts = make_term_derivations possorts equalitymapping term in
  let rec make_constraints j possorts = function
    | [] -> []
    | c :: tail ->
      (make_term c (sub_position_sorts j possorts)) ::
      (make_constraints (j+1) possorts tail)
  in
  let make_rule rule possorts =
    let lhs = make_term (Rule.lhs rule) (sub_position_sorts 0 possorts) in
    let rhs = make_term (Rule.rhs rule) (sub_position_sorts 1 possorts) in
    let cs = make_constraints 2 possorts (Rule.constraints rule) in
    Rule.create lhs rhs cs
  in
  match rules with
    | [] -> []
    | (rule, e) :: tail ->
      (make_rule rule (sub_position_sorts i possorts), e) ::
      (make_position_derivations possorts equalitymapping (i+1) tail)
;;

(** main functionality *)

let type_derivation rules a polyallowed =
  alf := Some a ;
  let funs = List.foldr (List.union <.> Rule.funs) [] (List.map fst rules) in
  let funsorts, k = fake_declarations funs 0 FakeDeclarationMap.empty in
  let varsorts, k = fake_varsorts rules k FakeSortMap.empty in
  let possorts, k = fake_positionsorts rules k [] 0 in
  let equalitymapping = Array.make k (FakeSort (-1)) in
  parse_rules_sorts rules funsorts varsorts possorts equalitymapping 0 ;
  let units = make_derived_function_declarations funsorts equalitymapping in
  make_derived_variable_declarations varsorts equalitymapping units ;
  if possorts = [] then rules
  else make_position_derivations possorts equalitymapping 0 rules
;;

(* type-checks rules, and makes declarations in a if necessary *)
let type_check rules a =
  let _ = type_derivation rules a false in ()
;;

(* type-checks all rules, and makes declarations if necessary *)
let type_check_trs t = type_check (Trs.get_rules t) (Trs.get_alphabet t);;

let type_derive t =
  let newrules = type_derivation (Trs.get_rules t) (Trs.get_alphabet t) true in
  Trs.replace_rules newrules t
;;

let type_derive_term term trs =
  let a = Trs.get_alphabet trs in
  let e = Trs.get_main_environment trs in
  let rule = Rule.of_terms term term in
  match type_derivation [(rule,e)] a false with
    | [(newrule,_)] -> Rule.lhs newrule
    | _ -> failwith "Type derivation gives an unexpected result"
;;

let type_derive_rules rules a = type_derivation rules a false;;

