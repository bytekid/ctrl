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
open Util;;
open Io;;
open Smt;;
open Rewriting;;

(*** TYPES *******************************************************************)

type sortcheck = Either | Values | Terms;;

(*** MODULES *****************************************************************)

(*** FUNCTIONS ***************************************************************)

(* returns whether only values occur in both Sigma_theory and Sigma_terms *)
let test_welldefined a = 
  let kind f = 
    try Alphabet.find_symbol_kind f a 
    with Not_found -> failwith ("Could not check standardness: " ^
      "symbol kind for function symbol " ^
      (Function.find_name f) ^ " is unset.")
  in  
  let is_constant f = 
    try Alphabet.find_ari f a = 0 
    with Not_found -> false
  in  
  let is_illegal f = (kind f = Alphabet.Both) && not (is_constant f) in
  let illegal = Alphabet.funs ~p:is_illegal a in
  illegal = []
;;

(* returns whether sorts which contain values do not additionally
contain other constructors *)
let check_value_safe trs =
  let a = Trs.get_alphabet trs in
  let lsorts = Alphabet.find_logical_sorts a in
  let dangerous = List.flat_map (Alphabet.find_symbols_with_sort a) lsorts in
  let really_dangerous = List.diff dangerous (Trs.def_symbols trs) in
  let logical f = Alphabet.find_symbol_kind f a <> Alphabet.Terms in
  List.for_all logical really_dangerous
;;

(* returns first all the logical sorts which contain only values and
constructors, second all the sorts which contain both values and
other constructors *)
let split_safe_sorts constructors trs =
  let a = Trs.get_alphabet trs in
  let lsorts = Alphabet.find_logical_sorts a in
  let safe sort =
    let dangerous = Alphabet.find_symbols_with_sort a sort in
    List.intersect dangerous constructors = []
  in
  List.partition safe lsorts
;;

(* returns whether all logical sorts contain values *)
let check_value_sound trs =
  let a = Trs.get_alphabet trs in
  Alphabet.logical_sorts_inhabited a
;;

(* returns whether the left-hand sides in the TRS do not contain
values *)
let check_left_value_free trs =
  let a = Trs.get_alphabet trs in
  let lfun = Trs.left_funs trs in
  let notavalue f =
    if not (Alphabet.mem_ari f a) then true
    else if not (Alphabet.mem_symbol_kind f a) then (
      failwith ("Error calculating value safety: symbol " ^
        (Function.find_name f) ^ " has no symbol " ^
        "kind set!")
    )
    else ( (Alphabet.find_ari f a > 0) ||
           (Alphabet.find_symbol_kind f a = Alphabet.Terms)
         )
  in
  List.for_all notavalue lfun
;;

(* makes the given trs left-value-free *)
let make_left_value_free trs =
  let rules = Trs.get_rules trs in
  let a = Trs.get_alphabet trs in
  let makebetter (rule, e) = (Rule.left_value_free a e rule, e) in
  let newrules = List.map makebetter rules in
  Trs.set_rules newrules trs
;;

(* returns whether all left-hand sides in the TRS are linear *)
let check_left_linear = Trs.is_left_linear;;

(* returns whether the given sort is inhabited by constructor terms;
   the list goodones contains sorts which are definitely inhabited,
   and info maps every sort to all triples (f, inps, sort) where f is
   a constructor of sorts inps => sort (with sort the relevant sort);
   badones are sorts we should not consider (to avoid recursion)

   also (sort, relevant) has this form, and the return value is a
   tuple, with the first element being inhabitation status and the
   second the sorts which we proved good by doing this
*)
let rec check_inhabited goodones badones info (sort, relevant) =
  (* checks recursively whether the given sort is inhabited *)
  let check_recursively goodones newsort =
    if List.mem newsort goodones then (goodones, true)
    else if List.mem newsort badones then (goodones, false)
    else try
      let newrelevant = List.assoc newsort info in
      check_inhabited goodones (sort :: badones) info (newsort, newrelevant)
    with Not_found -> (goodones, false)
  in
  (* true if all elements of the given sort list are inhabited *)
  let rec try_inputs_inhabited goodones = function
    | [] -> (goodones, true)
    | srt :: tail ->
      let (newgood, answer) = check_recursively goodones srt in
      if answer then try_inputs_inhabited newgood tail
      else (newgood, false)
  in
  (* true if some element of the given constructor list can be inhabited *)
  let rec check_inhabitation goodones = function
    | [] -> (goodones, false)
    | (f, inps, _) :: tail ->
      let (newgood, answer) = try_inputs_inhabited goodones inps in
      if answer then (newgood, true)
      else check_inhabitation newgood tail
  in
  let (goodones, success) = check_inhabitation goodones relevant in
  if success then (sort :: goodones, true)
  else (goodones, false)
;;

(* returns whether all sorts admit ground constructor terms *)
let check_constructor_sound trs =
  let a = Trs.get_alphabet trs in
  if not (Alphabet.logical_sorts_inhabited a) then false
  else (
    let allsorts = Alphabet.find_sorts a in
    let goodsorts = Alphabet.find_logical_sorts a in
    let badsorts = List.diff allsorts goodsorts in
    let constructors = List.diff (Alphabet.funs a) (Trs.def_symbols trs) in
    let addsort f =
      if not (Alphabet.mem_sortdec f a) then []
      else match Alphabet.find_sortdec f a with
        | Left sd -> 
          let inps = Sortdeclaration.input_sorts sd in
          let outp = Sortdeclaration.output_sort sd in
          [(f, inps, outp)]
        | Right _ -> [] (* should only happen for theory symbols! *)
    in
    let csorts = List.flat_map addsort constructors in
    let addconstructor sort =
      let sortokay (f, i, o) = (o = sort) in
      let relevant = List.filter sortokay csorts in
      let cmp (_, lst1, _) (_, lst2, _) =
        compare (List.length lst1) (List.length lst2)
      in
      let ordered = List.sort cmp relevant in
      (sort, ordered)
    in
    let info = List.map addconstructor badsorts in
      (* now info contains pairs (sort, list of constructors) *)
    let rec all_inhabited goodsorts = function
      | [] -> true
      | (sort, relevant) :: tail ->
        if List.mem sort goodsorts then true
        else (
          let (goodsorts, ok) =
            check_inhabited goodsorts [] info (sort, relevant)
          in
          if not ok then false
          else all_inhabited goodsorts tail
        )
    in
    all_inhabited goodsorts info
  )
;;

let precheck trs =
  if not (check_left_linear trs) then Some "TRS is not left-linear!"
  else if not (check_value_sound trs) then
    Some "TRS is not value-sound!"
  else if not (check_constructor_sound trs) then
    Some "TRS is not constructor-sound!"
  else ( make_left_value_free trs ; None )
;;

(** creates a conjunction or disjunction out of a list of constraints *)
let rec create_junction a conj = function
  | [] ->
    let symb =
      if conj then get_symbol Alphabet.get_top_symbol a "top"
      else get_symbol Alphabet.get_bot_symbol a "bottom"
    in
    Term.make_fun symb []
  | last :: [] -> last
  | first :: tail ->
    let symb =
      if conj then get_symbol Alphabet.get_and_symbol a "and"
      else get_symbol Alphabet.get_or_symbol a "or"
    in
    Term.make_fun symb [first; create_junction a conj tail]

and get_symbol getter a name =
  try getter a
  with Not_found ->
    failwith ("Standard symbol " ^ name ^ " should be set to " ^
              "enable quasi-reductivity.")
;;

(* calculates the OK function as described in completeness.tex *)
let rec test_reductivity constructors a e sortcheck ls x pairs =
  (* if there are no suitable shapes to reduce anything, we clearly fail *)
  if pairs = [] then false
  (* if elements of pairs have the form ([], phi), we must see that the
  union of all phis is satisfiable *)
  else if fst (List.hd pairs) = [] then (
    let phis = List.map snd pairs in
    let disjunction = create_junction a false phis in
    let vars = List.diff (Term.vars disjunction) x in
    let smt = Rewriter.smt_solver (Rewriter.get_current ()) in
    Solver.exists_valid vars disjunction smt e
  )
  (* otherwise, we have a sequence of patterns to check; determine
  whether we want to look for logical or non-logical terms *)
  else (
    let dosplit (lst, phi) = (List.hd lst, List.tl lst, phi) in
    let splitpairs = List.map dosplit pairs in
    let first = List.hd (fst (List.hd pairs)) in
    match sortcheck with
      | Values -> test_reductivity_values constructors a e ls x splitpairs
      | Terms -> test_reductivity_terms constructors a e ls x splitpairs
      | Either ->
        let sort = Term.get_sort a e first in
        if List.mem sort (fst ls) then
          test_reductivity_values constructors a e ls x splitpairs
        else if not (List.mem sort (snd ls)) then
          test_reductivity_terms constructors a e ls x splitpairs
        else (
          let variable_head (s, _, _) = Term.is_var s in
          let nophi_head (s, _, phi) =
            if not (Term.is_var s) then true else
            let x = List.hd (Term.vars s) in
            not (List.mem x (Term.vars phi))
          in
          let vs = List.filter variable_head splitpairs in
          let ts = List.filter nophi_head splitpairs in
          if vs = [] || ts = [] then false else
          (test_reductivity_values constructors a e ls x vs) &&
          (test_reductivity_terms constructors a e ls x ts)
        )
  )

(* calculates the OK function as described in completeness.tex, for
b = term and m > 0 *)
and test_reductivity_terms constructors a e ls x pairs =
  let variable_head (x, _, _) = Term.is_var x in
  if List.for_all variable_head pairs then (
    let remainder (_, lst, phi) = (lst, phi) in
    test_reductivity constructors a e Either ls x (List.map remainder pairs)
  )
  else (
    let (first, _, _) = List.hd pairs in
    let osort = Term.get_sort a e first in
    let goodsort (_, dec) = Sortdeclaration.output_sort dec = osort in
    let goodcons = List.filter goodsort constructors in
    let adapt_for (f, dec) (start, rest, phi) = match start with
      | Term.Var y ->
        let inps = Sortdeclaration.input_sorts dec in
        let makefresh sort =
          let z = Environment.create_sorted_var sort [] e in
          Term.make_var z
        in
        let zs = List.map makefresh inps in
        let gamma = Substitution.of_list [(y, Term.make_fun f zs)] in
        [(List.append zs rest, Substitution.apply_term gamma phi)]
      | Term.Fun (g, args) ->
        if g = f then [(List.append args rest, phi)]
        else []
      | Term.InstanceFun _ -> failwith "unexpected constructor form"
      | Term.Forall _ | Term.Exists _ ->
        failwith ("System has a quantifier in the left-hand side " ^
                  "side of a rule!  Should have been caught before.")
    in
    let make_group c = List.flat_map (adapt_for c) pairs in
    let groups = List.map make_group goodcons in
      List.for_all (test_reductivity constructors a e Either ls x) groups
  )

(* calculates the OK function as described in completeness.tex, for
b = value and m > 0 *)
and test_reductivity_values constructors a e ls x pairs =
  let variable_head (x, _, _) = Term.is_var x in
  if not (List.for_all variable_head pairs) then
    failwith ("In test_reductivity_values and not all list heads " ^
              "variables!  Left-value-freeness should have " ^
              "avoided this!")
  else (
    let (first, _, _) = List.hd pairs in
    let z = List.hd (Term.vars first) in
    let update (start, rest, phi) =
      let y = List.hd (Term.vars start) in
      let sub = Substitution.of_list [(y, first)] in
      let newphi = Substitution.apply_term sub phi in
      (*let newrest = List.map (Substitution.apply_term sub) rest in*)
      (rest, newphi)
    in
    let updated = List.map update pairs in
    test_reductivity constructors a e Either ls (z :: x) updated
  )
;;

(* does the main work for both quasi_reductive and
completely_reducible: checks preconditions and whether each of the
given symbols is completely reducible, returning the name of an
offending symbol if not *)
let check_reductivity trs symbolswithdecs relterms =
  (* check whether the basic conditions are satisfied *)
  ( match precheck trs with
    | None -> ()
    | Some msg -> failwith ("Pre-condition for quasi-" ^
                            "reductivity fails: " ^ msg)
  ) ;
  (* get all the rules, renamed to one shared environment *)
  let a = Trs.get_alphabet trs in
  let fn = Alphabet.fun_names a in
  let rulepairs = Trs.get_rules trs in
  let e = Environment.empty 100 in
  let rename (r, oldenv) = Rule.environment_transfer r oldenv e fn in
  let rules = List.map rename rulepairs in
  (* list various symbols *)
  let cons =                            (* non-value constructors *)
    let base = Trs.used_con_symbols relterms trs in
    let ok f =
      (Alphabet.find_symbol_kind f a = Alphabet.Terms) &&
      (Alphabet.mem_sortdec f a)
    in
    List.filter ok base
  in
  let conswithdec =
    let getdec f =
      try match Alphabet.find_sortdec f a with
        | Left sd -> (f, sd)
        | Right _ -> failwith "Strange declaration for term symbol!"
      with Not_found ->
        failwith ("Declaration for " ^ (Function.find_name f) ^ " unset.")
    in
    List.map getdec cons
  in
  (* limit interest to constructor rules *)
  let constructorrule rule =
    let args = Term.args (Rule.lhs rule) in
    let quantifierfree arg = Term.quantifier_pos arg = [] in
    (List.for_all (Term.is_build cons) args) &&
    (List.for_all quantifierfree args)
  in
  let crules = List.filter constructorrule rules in
  (* test whether the rules for a given symbol are okay, that is,
  that each term f(s1,...,sn) with all si ground constructor term
  (including values) reduces! *)
  let goodroot f rule = (Rule.left_root rule = f) in
  let (value_safe, value_unsafe) = split_safe_sorts cons trs in
  let freshvar sort = Environment.create_sorted_var sort fn e in
  let calcrule f dec =
    let inps = Sortdeclaration.input_sorts dec in
    let outp = Sortdeclaration.output_sort dec in
    let args = List.map (Term.make_var <.> freshvar) inps in
    let lhs = Term.make_function a e f args in
    let rhs = Term.make_var (freshvar outp) in
    let equal =
      try Alphabet.get_equal_symbol a
      with Not_found -> failwith "No equality symbol set in the theory!"
    in
    let constr = Term.make_function a e equal [rhs;lhs] in
    (args, constr)
  in
  let symbol_ok (f, dec, defined) =
    let relevant = List.filter (goodroot f) crules in
    let make_tuple rule =
      let args = Term.args (Rule.lhs rule) in
      let constraints = Rule.constraints rule in
      (args, create_junction a true constraints)
    in
    (*let safe sort = List.mem sort value_safe in*)
    try
      let parts = List.map make_tuple relevant in
      let parts =
        if defined then parts
        (*else if List.for_all safe (Sortdeclaration.input_sorts dec) then parts*)
        else (calcrule f dec) :: parts
      in
      if test_reductivity conswithdec a e Either
                          (value_safe, value_unsafe) [] parts then []
      else [Function.find_name f]
    with Rule.Not_an_lctrs -> failwith "The given system is not an LCTRS!"
  in
  let results = List.flat_map symbol_ok symbolswithdecs in
  Environment.drop e ;
  if results = [] then None
  else Some (List.hd results)
;;

let quasi_reductive trs =
  let a = Trs.get_alphabet trs in
  let defs = Trs.def_symbols trs in
  let getinfo f =
    match Alphabet.find_sortdec f a with
      | Left sd -> (f, sd, true)
      | Right _ -> failwith "Defined symbols must have a standard declaration!"
  in
  let valuesafe = check_value_safe trs in
  valuesafe && (check_reductivity trs (List.map getinfo defs) [] = None)
  (*****
  TODO: it is not exactly required that the system is value-safe; we
  *could* check whether theory symbols satisfy the requirements.
  However, it will fail if there are symbols with special
  declarations that allow an arbitrary number of children (such as
  =): this would require an infinite number of rules
  *****)
;;

let completely_reducible trs terms =
  let a = Trs.get_alphabet trs in
  let cons = Trs.con_symbols trs in
  let is_constructor f = List.mem f cons in
  (* figure out the defined and calculation symbols used in a term,
  together with their sort declaration *)
  let rec symbols_with_dec a term =
    let children args = List.flat_map (symbols_with_dec a) args in
    let handle_function f args sd =
      let kind = Alphabet.find_symbol_kind f a in
      if kind = Alphabet.Terms then (
        if is_constructor f then children args
        else (f, sd, true) :: children args
      )
      else if kind = Alphabet.Logical then (
        if args = [] then []
        else (f, sd, false) :: children args
      )
      else (* kind = Alphabet.Both Both *) (
        if args <> [] then
          failwith "Symbol occurring in both alphabets not a value!" ;
        []
      )
    in
    match term with
      | Term.Var _ -> []
      | Term.Forall (_, arg) | Term.Exists (_, arg) ->
        symbols_with_dec a arg
      | Term.Fun (f, args) ->
        let sd = ( match Alphabet.find_sortdec f a with
          | Left sd -> sd
          | Right _ -> failwith ("Instance function symbol occurs " ^
                                 "without its instantiation!")
        ) in
        handle_function f args sd
      | Term.InstanceFun (f, args, sd) -> handle_function f args sd
  in
  let rhss = List.map Rule.rhs (Trs.get_plain_rules trs) in
  let symbols = List.flat_map (symbols_with_dec a) (terms @ rhss) in
  let symbols = List.unique symbols in
  check_reductivity trs symbols terms
;;

