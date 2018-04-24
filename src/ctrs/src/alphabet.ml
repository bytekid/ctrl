(* Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
 * and 2014, 2015 Cynthia Kop
 * GNU Lesser General Public License
 *
 * This file is part of CTRL (and originates in TTT2).
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

(*** OPENS ********************************************************************)
open Prelude;;
open Util;;

(*** TYPES *******************************************************************)
type t = int;;
type sort = Sort.t;;
type sd = Sortdeclaration.t;;
type spd = Specialdeclaration.t;;
type func = Function.t;;
type symbolkind = Terms | Logical | Both;;
 
(*** MODULES ******************************************************************)
module SKind = struct
  type t = symbolkind

  let compare = compare
  let hash = Hashtbl.hash
  let copy = id
  let fprintf fmt = function
    | Terms -> Format.fprintf fmt "Terms"
    | Logical -> Format.fprintf fmt "Logical"
    | Both -> Format.fprintf fmt "Both"
end;;

module Declaration = struct
  type t = (sd, spd) either

  let compare = compare
  let hash = Hashtbl.hash
  let copy = id
  let fprintf fmt = function
    | Left sd -> Sortdeclaration.fprintf fmt sd
    | Right spd -> Specialdeclaration.fprintf fmt spd
end;;

module Symbols = Index.Isomorphic (Int) (String);;
module Arities = Index.Make (Int) (Int);;
module Declarations = Index.Make (Int) (Declaration);;
module SymbolKinds = Index.Make (Int) (SKind);;

(*** MORE TYPES **************************************************************)
type alphabet = {symbs : Symbols.t;
                 arity : Arities.t;
                 sorts : Declarations.t;
                 kinds : SymbolKinds.t;
                 has_integers : Sort.t option;  (* None = no integers *)
                 has_arrays : (Sort.t * Sort.t) list;
                 has_mixed : (string * string * Sort.t) list;
                 core_symbols : func option array;
                 wellfounded_symbols : (Sort.t * (Function.t list)) list
                };;

(** STATE VARIABLES **********************************************************)

type internal = { mutable alfs : alphabet array };;
let state = { alfs = [| |]  };;
let valalf = ref (-1);;

(*** FUNCTIONS ***************************************************************)

(* general accessing function *)

let get a = state.alfs.(a);;
let update a alf = state.alfs.(a) <- alf;;
let names a = (get a).symbs;;
let arity a = (get a).arity;;
let sorts a = (get a).sorts;;
let kinds a = (get a).kinds;;
let ints a = (get a).has_integers;;
let arrays a = (get a).has_arrays;;
let mixeds a = (get a).has_mixed;;
let core a = (get a).core_symbols;;
let wfs a = (get a).wellfounded_symbols;;

let intsort a =
  match (get a).has_integers with
    | None -> failwith "Asked for int sort when not supporting ints.\n"
    | Some sort -> sort
;;

let boolsort = Sort.from_string "Bool";;
let default_intsort = Sort.from_string "Int";;

(* Distinguishing between Standard symbols and Integer / Array symbols *)

let is_integer str a =
  if (ints a = None) then false else
  (
    try let _ = int_of_string str in true
    with _ -> false
  )
;;

let is_array str a =
  if (arrays a = []) then false else
  if str = "" then false else
  (String.get str 0 = '{') &&
  (String.get str ((String.length str) - 1) = '}')
;;

let split_mixed str a =
  let lst = mixeds a in
  let bracket_match (o, c, n) =
    let slen = String.length str in
    let olen = String.length o in
    let clen = String.length c in
    if slen < olen + clen then []
    else if (String.sub str 0 olen <> o) then []
    else if (String.sub str (slen - clen) clen <> c) then []
    else [(String.sub str olen (slen - olen - clen), o, c, n)]
  in
  match List.flat_map bracket_match lst with
    | [] -> None
    | [data] -> Some data
    | (a,_,_,_) :: (b,_,_,_) :: _ ->
      failwith ("Error: symbol " ^ str ^ " matches multiple kinds " ^
                "of mixed symbol (" ^ a ^ ", " ^ b ^ ")")
;;

let is_mixed str a = split_mixed str a <> None;;

(* splits a given array in the corresponding substrings, taking
nested arrays into account *)
let split_array_parts str a =
  if (not (is_array str a)) then
    failwith "split_array_parts may only be called with a string" else
  let sub = String.trim (String.sub str 1 ((String.length str) - 2)) in
  (* finds an occurrence of : in s not occurring between {brackets} *)
  let rec find_unnested_splitter s i num_open =
    if i >= String.length s then (
      if num_open = 0 then i
      else failwith "Given an array with badly nested brackets."
    )
    else if String.get s i = '{' then
      find_unnested_splitter s (i+1) (num_open+1)
    else if String.get s i = '}' then (
      if num_open = 0 then
        failwith "Given an array with badly nested brackets."
      else find_unnested_splitter s (i+1) (num_open-1)
    )
    else if (String.get s i = ':') && (num_open = 0) then i
    else find_unnested_splitter s (i+1) num_open
  in
  (* split in parts separated by : *)
  let rec split_parts s =
    let k = find_unnested_splitter s 0 0 in
    if k >= String.length s then [s] else
    let start = String.trim (String.sub s 0 k) in
    let ending = String.sub s (k+1) ((String.length s) - k - 1) in
    start :: split_parts ending
  in
  split_parts sub
;;

(* return either std <index of f> (if f is a standard symbol) or i *)
let choose std i f =
  if Function.is_standard f then std (Function.std_to_int f) else i
;;

(* execute std <index of f if f is a standard symbol>, intg <f cast
   to integer if it's an integer symbol>, arrg <f cast to an array if
   it's an array symbol> or mixedg <((open,close),name) of f if it's
   a mixed symbol> *)
let choose2 std intg arrg mixedg f =
  if Function.is_standard f then std (Function.std_to_int f)
  else if Function.is_integer f then intg (Function.integer_to_int f)
  else if Function.is_mixed f then
    mixedg (Function.mixed_brackets f, Function.mixed_to_string f)
  else arrg (Function.array_to_array f)
;;

(* Search Functions *)

let integer_sort a = intsort a;;
let arraysorts a = List.map (fun (_,x) -> x) (get a).has_arrays;;
let arraysorts_of a = List.map (fun (x,_) -> x) (get a).has_arrays;;
let mixedsorts a = List.map (fun (_,_,x) -> x) (get a).has_mixed;;

let test_mixed sort a =
  let f sofar (o,c,s) =
    if s = sort then Some (o,c)
    else sofar
  in
  List.fold_left f None (get a).has_mixed
;;

let array_sort sort a =
  let goodinput (y, _) = y = sort in
  let (_, x) = List.find goodinput (get a).has_arrays in x
;;

let mixed_sort (o,c) a =
  let (_, _, sort) = List.find (fun (u, v, _) -> u = o && v = c) (mixeds a) in
  sort
;;

let rec find_fun n a =
  if is_integer n a then Function.integer_symbol (int_of_string n)
  else if is_array n a then (
    let parts = split_array_parts n a in
    let funcs = List.map (fun s -> find_fun s a) parts in
    Function.array_symbol (Array.of_list funcs)
  )
  else match split_mixed n a with
    | Some (str, o, c, _) -> Function.mixed_symbol str o c
    | None -> Function.standard_symbol (Symbols.find_key n (names a)) n
;;

let find_ari f a = choose (flip Arities.find (arity a)) 0 f;;
let mem_sortdec f a = choose (flip Declarations.mem (sorts a)) true f;;

(* finds the sortdeclaration of a given function symbol *)
let rec find_sortdec f a = choose2
  (flip Declarations.find (sorts a))
  (fun _ -> Left (Sortdeclaration.create [] (intsort a)))
  (fun arr -> Left (Sortdeclaration.create [] (sort_of_array arr a)))
  (fun ((o,c),_) -> Left (Sortdeclaration.create [] (mixed_sort (o,c) a)))
  f

(* given an array symbol, tries to determine its sort *)
and sort_of_array arr a =
  let warning x = "Sort of array symbol " ^
                  (Function.to_string (Function.array_symbol arr)) ^
                  "requested, but " ^ x in
  let lst = (get a).has_arrays in
  if lst = [] then failwith (warning "no array sorts are set.")
  else if List.tl lst = [] then
    let (_, osort) = List.hd lst in osort
  else if Array.length arr = 0 then
    failwith (warning "there are multiple array sorts that could apply!")
  else (
    let first = arr.(0) in
    let ot =
      try Sortdeclaration.output_sort (Either.left (find_sortdec first a))
      with _ -> failwith (warning "first symbol has an unknown sort!")
    in
    try List.assoc ot lst
    with Not_found -> failwith (warning ("arrays of " ^
                      (Sort.to_string ot) ^ " are not declared."))
  )
;;

let find_symbol_kind f a = choose (flip SymbolKinds.find (kinds a)) Both f;;

let funs ?(p = const true) a =
  let lst = Symbols.to_list (names a) in
  let makesymb (index, name) = Function.standard_symbol index name in
  let converted = List.map makesymb lst in
  List.filter p converted
;;

let fun_names a = Symbols.elements (names a);;

let get_sorts filter includespecial a =
  let update_sofar sofar = function
    | Left sortdec ->
      (Sortdeclaration.output_sort sortdec) ::
      List.append (Sortdeclaration.input_sorts sortdec) sofar
    | Right shakydec ->
      let srts = (Specialdeclaration.output_sort shakydec) ::
                 (Specialdeclaration.input_sorts shakydec) in
      let rec goodsorts ret = function
        | [] -> ret
        | s :: tail ->
          if Specialdeclaration.is_polymorphic s then
            goodsorts ret tail
          else Specialdeclaration.pol_to_sort s :: goodsorts ret tail
      in
      goodsorts sofar srts
  in
  let rec most_sorts sofar = function
    | [] -> sofar
    | f :: tail ->
      if (mem_sortdec f a) && (filter f) then
        most_sorts (update_sofar sofar (find_sortdec f a)) tail
      else most_sorts sofar tail
  in
  let all_sorts lst = (
    if not includespecial then most_sorts [] lst
    else (arraysorts a) @ (mixedsorts a) @ (
      match (get a).has_integers with
        | None -> most_sorts [] lst
        | Some sort -> most_sorts [sort] lst
    )
  )
  in
  List.unique (all_sorts (funs a))
;;

let find_sorts a = get_sorts (fun f -> true) true a;;

let find_logical_sorts a =
  let is_logical f = find_symbol_kind f a <> Terms in
  get_sorts is_logical true a
;;

let find_symbols_with_sort a sort =
  let sd_okay = function
    | Left sd -> (Sortdeclaration.output_sort sd) = sort
    | Right sd ->
      let out = Specialdeclaration.output_sort sd in
      if Specialdeclaration.is_polymorphic out then true
      else (Specialdeclaration.pol_to_sort out) = sort
  in
  let sort_okay f =
    if mem_sortdec f a then sd_okay (find_sortdec f a)
    else false
  in
  List.filter sort_okay (funs a)
;;

(* Scan Functions *)

let mem_ari f = catch Not_found (const true <.> find_ari f) false;;
let mem_symbol_kind f = catch Not_found (const true <.> find_symbol_kind f) false;;

let mem_fun_name n a =
  if (is_integer n a) || (is_array n a) || (is_mixed n a) then true
  else Symbols.mem_elt n (names a)
;;

let is_ari n f = catch Not_found ((=) n <.> find_ari f) false;;
let is_defined_fun f a = mem_ari f a || mem_sortdec f a;;

let is_value f a =
  let problem_with unset =
    failwith (unset ^ " of " ^ (Function.find_name f) ^ " is not set.")
  in
  if not (mem_ari f a) then false
  else if (find_ari f a > 0) then false
  else if not (mem_symbol_kind f a) then problem_with "Symbol kind"
  else if (find_symbol_kind f a = Terms) then false
  else try
    match find_sortdec f a with
      | Left _ -> true
      | Right _ -> false
    with Not_found -> problem_with "Sort declaration "
;;

let is_sort s f a =
  try
    match find_sortdec f a with
      | Left sortdec ->
        Some (Sort.equal (Sortdeclaration.output_sort sortdec) s)
      | Right shakydec ->
        let outp = Specialdeclaration.output_sort shakydec in
        if (Specialdeclaration.is_polymorphic outp) then None
        else Some (Sort.equal (Specialdeclaration.pol_to_sort outp) s)
  with Not_found -> None
;;

let is_argument_sort i s f a =
  try
    match find_sortdec f a with
      | Left sortdec ->
        Some (Sort.equal (Sortdeclaration.input_sort sortdec i) s)
      | Right shakydec ->
        let inp = Specialdeclaration.input_sort i shakydec in
        if (Specialdeclaration.is_polymorphic inp) then None
        else Some (Sort.equal (Specialdeclaration.pol_to_sort inp) s)
  with Not_found -> None
;;

let has_integers a = (ints a) <> None;;
let has_arrays a = (arrays a) <> [];;
let has_arrays_of sort a =
  try let _ = array_sort sort a in true with Not_found -> false;;
let has_mixeds a = (mixeds a) <> [];;

let logical_sorts_inhabited a =
  let logical_sorts = find_logical_sorts a in
  let lsorts =
    match (get a).has_integers with
      | None -> logical_sorts
      | Some t -> List.diff logical_sorts [t]
  in
  let lsorts = List.diff lsorts (arraysorts a) in    
  let lsorts = List.diff lsorts (mixedsorts a) in
  let is_val f = is_value f a in
  let values = funs ~p:is_val a in
  let getsort c = match find_sortdec c a with
    | Left sd -> Sortdeclaration.output_sort sd
    | Right spd -> failwith "Inconsistency in logical_sorts_inhabited!"
  in
  let valsorts = List.map getsort values in
  let badsorts = List.diff lsorts valsorts in
  badsorts = []
;;

(* Constructors and Destructors *)

let update_arity upd f k a = update a {(get a) with arity = upd f k (arity a)};;
let update_symbs upd f n a = update a {(get a) with symbs = upd f n (names a)};;
let update_sorts upd f d a = update a {(get a) with sorts = upd f d (sorts a)};;
let update_kinds upd f d a = update a {(get a) with kinds = upd f d (kinds a)};;

let force_zero k a =
  if k <> 0 then
    failwith ("cannot assign non-zero arity to integer, array or " ^
              "mixed symbol (these are required to be values).")
  else ()
;;
let add_ari = choose (update_arity Arities.add) force_zero;;
let replace_ari = choose (update_arity Arities.replace) force_zero;;

let check_special_sort desc expected f d a =
  match d with
    | Right _ -> failwith (desc ^ " symbols must have a normal, " ^
                           "non-polymorphic sort (problem: " ^
                           (Function.find_name f) ^ ").")
    | Left dec ->
      if Sortdeclaration.arity dec <> 0 then
        failwith (desc ^ " symbols cannot take arguments!")
      else (
        let s = Sortdeclaration.output_sort dec in
        if s <> expected then failwith (desc ^ " symbol " ^
          (Function.find_name f) ^ " with sort " ^ (Sort.to_string s) ^
          ", originally had sort " ^ (Sort.to_string expected) ^ ".")
      )
;;

let force_int f _ d a = check_special_sort "Integer" (intsort a) f d a;;
let force_array f arr d a = check_special_sort "Array" (sort_of_array arr a) f d a;;
let force_mixed f (p,_) d a = check_special_sort "Mixed" (mixed_sort p a) f d a;;

let add_sortdec f = choose2 (update_sorts Declarations.add)
                      (force_int f) (force_array f) (force_mixed f) f
;;

let add_normal_sortdec f sd a =
  add_sortdec f (Left sd) a ;
  add_ari f (Sortdeclaration.arity sd) a
;;

let add_special_sortdec f spd a =
  add_sortdec f (Right spd) a ;
  if Specialdeclaration.known_arity spd then
    add_ari f (Specialdeclaration.arity spd) a
;;

let replace_sortdec f = choose2 (update_sorts Declarations.replace)
                      (force_int f) (force_array f) (force_mixed f) f
;;

let replace_normal_sortdec f sd a =
  replace_sortdec f (Left sd) a ;
  replace_ari f (Sortdeclaration.arity sd) a
;;

let replace_special_sortdec f spd a =
  replace_sortdec f (Right spd) a ;
  if Specialdeclaration.known_arity spd then
    replace_ari f (Specialdeclaration.arity spd) a
;;

let set_symbol_kind = choose (update_kinds SymbolKinds.replace) (fun k a -> ())

let add_symbol_kind f k a =
  try
    match (find_symbol_kind f a, k) with
      | (Both, _) | (Logical, Logical) | (Terms, Terms) -> ()
      | (_, Both) | (Logical, Terms) | (Terms, Logical) ->
        set_symbol_kind f Both a
  with Not_found -> set_symbol_kind f k a
;;

let empty n =
  let new_alf = {
    symbs = Symbols.empty n;
    arity = Arities.empty;
    sorts = Declarations.empty;
    kinds = SymbolKinds.empty;
    has_integers = None;
    has_arrays = [];
    has_mixed = [];
    core_symbols = [| None; None; None; None; None; None; None; None; None; None; None |];
    wellfounded_symbols = [];
  } in
  let len = Array.length state.alfs in
  state.alfs <- Array.append state.alfs [| new_alf |] ;
  len
;;

(* Fresh Symbols *)

let fresh_fun n a =
  let (f, fs) = Symbols.fresh (names a) in
  let fs = Symbols.add f n fs in
  update a {(get a) with symbs = fs} ;
  Function.standard_symbol f n
;;

let create_unsorted_fun k n a =
  try
    let f = find_fun n a in
    if find_ari f a = k then f
    else failwith "incorrect arity"
  with Not_found ->
    let f = fresh_fun n a in
    add_ari f k a; f
;;

let create_fun d n a =
  let add_arity f k =
    if mem_ari f a then (
      if find_ari f a != k then failwith "incorrect arity"
    )
    else add_ari f k a
  in
  let f =
    try find_fun n a
    with Not_found -> fresh_fun n a
  in
  let k = Sortdeclaration.arity d in
  add_arity f k ;
  try
    match find_sortdec f a with
      | Left sd -> if Sortdeclaration.equal sd d then f
                   else failwith "incorrect sort declaration"
      | Right sd -> failwith "incorrect sort declaration"
  with Not_found -> ( add_normal_sortdec f d a ; f )
;;

let add_instance_fun f d n a =
  if Specialdeclaration.known_arity d then (
    let k = Specialdeclaration.arity d in
    add_ari f k a ;
    add_special_sortdec f d a
  )
  else (
    if mem_ari f a then
      failwith ("Cannot assign variable sort declaration to " ^
        "a symbol which already has an arity!")
    else (
      add_special_sortdec f d a
    )
  )
;;

let create_instance_fun d n a =
  let add_arity f k =
    if mem_ari f a then (
      if find_ari f a != k then failwith "incorrect arity"
    )
    else if k <> -1 then add_ari f k a
  in
  try
    let f = find_fun n a in
    add_arity f ( if Specialdeclaration.known_arity d
                  then Specialdeclaration.arity d
                  else -1
                ) ;
    try
      match find_sortdec f a with
        | Left sd -> failwith "incorrect sort declaration"
        | Right sd -> if Specialdeclaration.equal sd d then f
                      else failwith "incorrect sort declaration"
    with Not_found -> ( add_special_sortdec f d a ; f )
  with Not_found ->
    let f = fresh_fun n a in
    add_instance_fun f d n a ; f
;;

let include_integers s a = update a {(get a) with has_integers = Some s};;

let include_arrays isort osort a =
  let s = (get a).has_arrays in
  update a {(get a) with has_arrays = (isort, osort) :: s}
;;

let include_mixed openbracket closebracket osort a =
  let s = (get a).has_mixed in
  update a {(get a) with has_mixed = (openbracket, closebracket, osort) :: s}
;;

let value_alphabet _ =
  if !valalf <> -1 then !valalf
  else (
    let a = empty 2 in
    let sd = Sortdeclaration.create [] boolsort in
    let _ = create_fun sd "true" a in
    let _ = create_fun sd "false" a in
    include_integers default_intsort a ;
    include_arrays default_intsort (Sort.from_string "(Array Int Int)") a ;
    valalf := a ;
    a
  )
;;

(* Special (Core) Logical Symbols *)

let corename n =
  if n = 0 then "conjunction"
  else if n = 1 then "disjunction"
  else if n = 2 then "implication"
  else if n = 3 then "negation"
  else if n = 4 then "truth"
  else if n = 5 then "falsehood"
  else if n = 6 then "equality"
  else if n = 7 then "greater-equal"
  else if n = 8 then "smaller-equal"
  else if n = 9 then "greater"
  else if n = 10 then "smaller"
  else failwith "Name requested of an illegal core symbol."
;;

(** note: negative arity -i means: at least i arguments *)
let do_core_checks num expected_arity func a =
  let err = "Attempting to set function for " ^
    (corename num) ^ " which " in
  let sortdec = (
    try find_sortdec func a
    with Not_found -> failwith (err ^ "has no sort declaration!")
  ) in
  let check_arity ar =
    if ar <> expected_arity then (
      if (expected_arity >= 0) || (ar < -expected_arity) then
        failwith (err ^ "has arity " ^ (string_of_int ar) ^ ".")
    )
  in
  match sortdec with
    | Left sd -> check_arity (Sortdeclaration.arity sd)
    | Right spd ->
      let ar = (
        try Specialdeclaration.arity spd
        with _ ->
          if expected_arity >= 0 then
            failwith (err ^ "has variable arity (should be 2).")
          else -expected_arity
      ) in
      let osrt = Specialdeclaration.output_sort spd in
      if Specialdeclaration.is_polymorphic osrt then
        failwith (err ^ "has a polymorphic output sort.")
      else check_arity ar
;;

let update_core num expected_arity func a =
  do_core_checks num expected_arity func a ;
  let full = (get a) in
  let symbs = full.core_symbols in
  symbs.(num) <- Some func ;
  update a {full with core_symbols = symbs}
;;

let get_core num a =
  match (core a).(num) with
    | None -> raise Not_found
    | Some x -> x
;;

let set_and_symbol = update_core 0 (-2);;
let set_or_symbol = update_core 1 (-2);;
let set_imply_symbol = update_core 2 2;;
let set_not_symbol = update_core 3 1;;
let set_top_symbol = update_core 4 0;;
let set_bot_symbol = update_core 5 0;;
let set_equal_symbol = update_core 6 (-2);;
let set_geq_symbol = update_core 7 2;;
let set_leq_symbol = update_core 8 2;;
let set_greater_symbol = update_core 9 2;;
let set_smaller_symbol = update_core 10 2;;
let get_and_symbol = get_core 0;;
let get_or_symbol = get_core 1;;
let get_imply_symbol = get_core 2;;
let get_not_symbol = get_core 3;;
let get_top_symbol = get_core 4;;
let get_bot_symbol = get_core 5;;
let get_equal_symbol = get_core 6;;
let get_geq_symbol = get_core 7;;
let get_leq_symbol = get_core 8;;
let get_greater_symbol = get_core 9;;
let get_smaller_symbol = get_core 10;;

let add_wellfounded sort f a =
  let allwfs = wfs a in
  let rec addf = function
    | [] -> [(sort, [f])]
    | (s,fs) :: tl ->
      if s <> sort then (s,fs) :: addf tl
      else if List.mem f fs then (s,fs) :: tl
      else (s,f::fs) :: tl
  in
  update a {(get a) with wellfounded_symbols = addf allwfs}
;;

let get_wellfounded sort a =
  try List.assoc sort (wfs a)
  with Not_found -> []
;;

let sorts_with_wellfounded_relations a = List.map fst (wfs a);;

(* Miscellaneous *)

let copy a =
  let cp = {
    symbs = Symbols.copy (names a);
    arity = Arities.copy (arity a);
    sorts = Declarations.copy (sorts a);
    kinds = SymbolKinds.copy (kinds a);
    has_integers = ints a;
    has_arrays = arrays a;
    has_mixed = mixeds a;
    core_symbols = core a;
    wellfounded_symbols = wfs a;
  } in
  let len = Array.length state.alfs in
  state.alfs <- Array.append state.alfs [| cp |] ;
  len
;;

let hash = id;;

(* Printers *)

let fprintf fmt a =
  Format.fprintf fmt
    "@[Alphabet:@[<1>@\n%a@]@\nArities:@[<1>@\n%a@]@\nSorts:@[<1>@\n%a@]%s%s%s@]@\n"
    Symbols.fprintf (names a)
    Arities.fprintf (arity a)
    Declarations.fprintf (sorts a)
    ( if has_integers a then
        "\nAll integers are also included with sort " ^
        (Sort.to_string (intsort a))
      else ""
    )
    ( if has_arrays a then
        let printkind (isort, osort) =
          "arrays of sort " ^ (Sort.to_string isort) ^ " with sort "
                            ^ (Sort.to_string osort)
        in
        "and " ^ (List.implode printkind ", " (get a).has_arrays)
      else ""
    )
    ( if has_mixeds a then
        let printkind (ob, cb, sort) =
          "mixed symbols with brackets " ^ ob ^ " and " ^ cb ^
          "with sort " ^ (Sort.to_string sort)
        in
        "and " ^ (List.implode printkind ", " (get a).has_mixed) ^ "."
      else "."
    )
;;

let to_string = Format.flush_str_formatter <.> fprintf Format.str_formatter;;
 
