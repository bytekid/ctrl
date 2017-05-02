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

(*** OPENS *******************************************************************)
open Prelude;;
open Util;;

(*** MODULES *****************************************************************)

(*** TYPES *******************************************************************)
type func = Function.t;;
type sort = Sort.t;;
type rule = Rule.t;;
type term = Term.t = Var of Variable.t | Fun of func * term list |
                     InstanceFun of func * term list * Sortdeclaration.t |
                     Forall of Variable.t * term |
                     Exists of Variable.t * term;;

type trs = { alphabet : Alphabet.t ;
             environment: Environment.t ;
             rules : (rule * Environment.t) list ;
             csmapping : Csmapping.t
           }
type t = int;;

(** STATE VARIABLES **********************************************************)
type internal = { mutable ts : trs array ; mutable cur : int };;
let state = { ts = [| |] ; cur = -1 };;

(*** FUNCTIONS ***************************************************************)

(* general accessing function *)

let get t = state.ts.(t);;
let update t trs = state.ts.(t) <- trs;;
let update_rules t newrules = update t { (get t) with rules = newrules };;
let update_alphabet t newalf = update t { (get t) with alphabet = newalf };;

(* Constructors and Destructors *)

let empty _ =
  let new_trs = { 
    alphabet = Alphabet.empty 10 ;
    environment = Environment.empty 10 ;
    rules = [] ;
    csmapping = Csmapping.empty ()
  } in
  let len = Array.length state.ts in
  state.ts <- Array.append state.ts [| new_trs |] ;
  len 
;;

let create_contextsensitive a e cs =
  let new_trs = {
    alphabet = a ;
    environment = e ;
    rules = [] ;
    csmapping = cs
  } in
  let len = Array.length state.ts in
  state.ts <- Array.append state.ts [| new_trs |] ;
  len
;;

let create a e = create_contextsensitive a e (Csmapping.empty ());;

let get_alphabet t = (get t).alphabet;;
let get_main_environment t = (get t).environment;;
let get_rules t = (get t).rules;;
let get_plain_rules t = List.map fst (get_rules t);;
let get_context_sensitivity t = (get t).csmapping;;

let add rule e t = update_rules t ((rule, e) :: get_rules t);;
let set_rules rules t = update_rules t rules;;
let set_alphabet alf t = update_alphabet t alf;;
let lhs t = List.map (fun p -> Rule.lhs (fst p)) (get_rules t);;
let rhs t = List.map (fun p -> Rule.rhs (fst p)) (get_rules t);;

(* Iterators *)

let flat_map f = List.flat_map (Pair.uncurry f) <.> get_rules;;
let fold f a = List.foldr (Pair.uncurry f) a <.> get_rules;;
let iter f = List.iter (Pair.uncurry f) <.> get_rules;;
let map f = List.map (Pair.uncurry f) <.> get_rules;;
let project f s = let f1 r e = (f r e, e) in update_rules s (map f1 s);;
let count_fun f = List.foldr ((+) <.> (Rule.count_fun f)) 0 <.> get_plain_rules;;

(** {3 Search Functions} *)

let choose = (List.hd <?> "empty TRS") <.> get_rules;;
let filter f t = update_rules t (List.filter (Pair.uncurry f) (get_rules t));;
let find f t = List.find (Pair.uncurry f) (get_rules t);;
let find_option f t = List.find_option (Pair.uncurry f) (get_rules t);;
let find_all f t = List.filter (Pair.uncurry f) (get_rules t);;

(* Scan Functions *)

let exists f = List.exists (Pair.uncurry f) <.> get_rules;;
let exists_rule f = List.exists f <.> get_plain_rules;;
let for_all f = List.for_all (Pair.uncurry f) <.> get_rules;;
let for_all_rule f = List.for_all f <.> get_plain_rules;;

(* TRS Symbols *)

let compute_symbols f = List.foldr (List.union <.> f) [] <.> get_plain_rules;;
let cons = compute_symbols Rule.cons;;
let funs r = Alphabet.funs (get_alphabet r);;
let symbols = compute_symbols Rule.symbols;;
let vars = compute_symbols Rule.vars;;
let left_cons r = compute_symbols Rule.left_cons r;;
let left_funs r = compute_symbols Rule.left_funs r;;
let left_symbols r = compute_symbols Rule.left_symbols r;;
let left_vars r = compute_symbols Rule.left_vars r;;
let right_cons r = compute_symbols Rule.right_cons r;;
let right_funs r = compute_symbols Rule.right_funs r;;
let right_symbols r = compute_symbols Rule.right_symbols r;;
let right_vars r = compute_symbols Rule.right_vars r;;

let roots f =
  List.unique_hash <.>
    List.foldr (fun r fs -> try (f r) :: fs with Failure _ -> fs) [] <.> get_plain_rules
;;

let left_roots r = roots Rule.left_root r;;
let right_roots r = roots Rule.right_root r;;
let roots = List.unique_hash <.> List.foldr (List.rev_append <.> Rule.roots) [] <.> get_plain_rules
let def_symbols = left_roots;;
let notcalc r f = try Alphabet.find_symbol_kind f (get_alphabet r) <> Alphabet.Logical
                  with Not_found -> true;; (* default *)
let con_symbols r = List.filter (notcalc r) (List.diff (funs r) (def_symbols r));;
let left_con_symbols r = List.diff (left_funs r) (def_symbols r);;
let right_con_symbols r = List.diff (right_funs r) (def_symbols r);;

let used_con_symbols terms r =
  let termfuns = List.flat_map Term.funs terms in
  let rulefuns = List.flat_map Rule.funs (get_plain_rules r) in
  let usedfuns = List.unique (termfuns @ rulefuns) in
  List.intersect (con_symbols r) usedfuns
;;

let calc_symbols t =
  let a = get_alphabet t in
  let iscalculation f =
    try
      if not (Alphabet.find_symbol_kind f a = Alphabet.Logical) then false
      else if not (Alphabet.mem_ari f a) then true
      else Alphabet.find_ari f a > 0
    with Not_found -> false
  in
  Alphabet.funs ~p:iscalculation a
;;

(* Properties *)

let is_build fs = for_all_rule (Rule.is_build fs);;
let is_collapsing = exists_rule Rule.is_collapsing;;
let is_dummy = for_all_rule Rule.is_dummy;;
let is_duplicating = exists_rule Rule.is_duplicating;;
let is_erasing = exists_rule Rule.is_erasing;;
let is_empty = List.is_empty <.> get_rules
let is_flat = for_all_rule Rule.is_flat;;
let is_ground = for_all_rule Rule.is_ground;;
let is_growing = for_all_rule Rule.is_growing;;
let is_linear = for_all_rule Rule.is_linear;;
let is_shallow = for_all_rule Rule.is_shallow;;
let is_size_preserving = for_all_rule Rule.is_size_preserving;;
let is_left_build fs r = for_all_rule (Rule.is_left_build fs) r;;
let is_left_dummy = for_all_rule Rule.is_left_dummy;;
let is_left_flat = for_all_rule Rule.is_left_flat;;
let is_left_ground = for_all_rule Rule.is_left_ground;;
let is_left_linear = for_all_rule Rule.is_left_linear;;
let is_left_shallow = for_all_rule Rule.is_left_shallow;;
let is_right_build fs = for_all_rule (Rule.is_right_build fs);;
let is_right_dummy = for_all_rule Rule.is_right_dummy;;
let is_right_flat = for_all_rule Rule.is_right_flat;;
let is_right_ground = for_all_rule Rule.is_right_ground;;
let is_right_linear = for_all_rule Rule.is_right_linear;;
let is_right_shallow = for_all_rule Rule.is_right_shallow;;

let is_variant r s =
  let is_variant r s = for_all_rule (flip exists_rule s <.> Rule.is_variant) r in
  is_variant r s && is_variant s r
;;

let is_constructor f r =
  let cs = con_symbols r in
  for_all_rule (List.for_all (Term.is_build cs) <.> Term.args <.> f) r
;;

let is_left_constructor = is_constructor Rule.lhs;;
let is_right_constructor = is_constructor Rule.rhs;;
let is_constructor = is_left_constructor;;
let is_redex t = exists_rule (Rule.is_redex t);;
let is_normal_form t = for_all_rule (Rule.is_normal_form t);;

let is_constructor_term term r =
  let ds = def_symbols r in
  let termfuns = Term.funs term in
  List.intersect ds termfuns = []
;;

let is_applicative r =
  let alphabet = get_alphabet r in
  let rec check_sig b = function
    | [] -> b
    | f::fs ->
      let a = Alphabet.find_ari f alphabet in
      if a = 0 then check_sig b fs
      else if a = 2 && not b then check_sig true fs
      else false
  in
  check_sig false (funs r)
;;

let is_overlapping r =
  let rec check_overlap rule = function
    | [] -> false
    | head :: tail ->
      (Rule.are_overlapping rule head) && (check_overlap rule tail)
  in
  let rec check_all = function
    | [] -> false
    | head :: tail -> (check_overlap head tail) && (check_all tail)
  in
  check_all (get_plain_rules r)
;;

let is_overlay r =
  let is_root (_,p,_) = Position.is_root p in
  let check r1 r2 = List.for_all is_root (Rule.overlaps r1 r2) in
  for_all_rule (flip for_all_rule r <.> check) r
;;

let is_trs r =
  let constraintfree rule = (Rule.constraints rule = []) in
  for_all_rule constraintfree r
;;

(* Miscellaneous *)

let rename t =
  let a = get_alphabet t in
  let e = get_main_environment t in
  let rename_rule (rule, env) = (Rule.rename_fully rule a e, e) in
  update_rules t (List.map rename_rule (get_rules t))
;;

let copy r = 
  let cp = { 
    alphabet = Alphabet.copy (get_alphabet r); 
    environment = Environment.copy (get_main_environment r); 
    rules = get_rules r ;
    csmapping = get_context_sensitivity r
  } in
  let len = Array.length state.ts in
  state.ts <- Array.append state.ts [| cp |] ;
  len 
;;

let depth = List.foldr (max <.> Rule.depth) 0 <.> get_plain_rules;;

let hash r =
  let hashpair (rule, env) = (Rule.hash rule, Environment.hash env) in
  Hashtbl.hash (List.rev_map hashpair (get_rules r),
                Environment.hash (get_main_environment r),
                Alphabet.hash (get_alphabet r));;

let size = List.length <.> get_rules;;

let rule_overlaps func r =
  let ignore_env f r e = f r in
  let overlap r1 r2 _ = func r1 r2 in
  flat_map (ignore_env (flip (flat_map <.> overlap) r)) r;;

let overlaps = rule_overlaps Rule.overlaps;;
let var_overlaps = rule_overlaps Rule.var_overlaps;;

let replace_rules = flip update_rules;;

(* Validity (not type checking) *)

(* tests whether var1 is contained in var2, returns None if so,
and returns Some x if not, where x is a variable that is in var1
but not in var2 *)
let test_var_inclusion var1 var2 =
  if (List.is_subset var1 var2) then None
  else Some (List.hd (List.diff var1 var2))
;;

(* test whether x is an "input" variable *)
let test_input x =
  let name = Variable.find_name x in
  String.sub (name ^ "   ") 0 3 = "inp"
;;

(* test whether x in a "random" variable *)
let test_random x =
  let name = Variable.find_name x in
  String.sub (name ^ "   ") 0 3 = "rnd"
;;

(* tests whether the variables of the given constraint are included
in vars where necessary, and returns both a string indicating whether
there was a problem (the empty string if no problems) and an updated
set of variables *)
let test_constraint_variables c vars rule alphabet env regular =
  let test_vars_inclusion lst =
    match (test_var_inclusion lst vars) with
      | None -> ""
      | Some x ->
        let rulestr = Rule.to_stringm rule in
        let consstr = Term.to_stringm c in
        let illegal = Variable.find_name x in
        "Constraint [" ^ consstr ^ "] of rule [" ^ rulestr ^ "] " ^
          "contains a variable [" ^ illegal ^ "] which does not " ^
          "occur in the left-hand side of the rule or any previous " ^
          "constraints."
  in
  let test_input_inclusion s =
    let svars = Term.vars s in
    let badvars = List.filter test_input svars in
    match (test_var_inclusion badvars vars) with
      | None -> ""
      | Some x ->
        let rulestr = Rule.to_stringm rule in
        let consstr = Term.to_stringm c in
        let illegal = Variable.find_name x in
        "Constraint [" ^ consstr ^ "] of rule [" ^ rulestr ^ "] " ^
          "contains an input variable [" ^ illegal ^ "], which is " ^
          "not allowed."
  in
  let checklist lst = (test_vars_inclusion lst, vars) in
  if regular then checklist (Term.vars c)
  else (test_input_inclusion c, List.union vars (Term.vars c))
;;

(* tests validity of all constraints, and returns the set of variables
occurring in them alongside an answer (if anything but the empty string
is returned, the set may be incomplete) *)
let rec test_constraints_variables lst vars rule alphabet env regular =
  match lst with
    | [] -> ("", vars)
    | head :: tail ->
      let (msg, newvars) =
        test_constraint_variables head vars rule alphabet env regular in
      if msg <> "" then (msg, newvars)
      else test_constraints_variables tail newvars rule alphabet env regular
;;

(* checks whether the given rule satisfies variable conditions,
returning a helpful string if not *)
let test_rule_variables alphabet regular (rule, env) rest =
  if rest <> "" then rest else (
    let lvars = Rule.left_vars rule in
    let (msg, vars) =
      test_constraints_variables (Rule.constraints rule)
                                 lvars rule alphabet env regular
    in
    if msg <> "" then msg else (
      let rvars = Rule.right_vars rule in
      match (test_var_inclusion rvars vars) with
        | None -> ""
        | Some x -> (
          let name = Variable.find_name x in
          if (test_input x) || (test_random x) then ""
          else (
            let rulestr = Rule.to_stringm rule in
            Printf.printf "%s" ("Right-hand side of rule [" ^ rulestr
              ^ "] contains a variable [" ^ name ^ "] which does " ^
              "not occur in the left-hand side or any of the " ^
              "constraints.  To indicate user input or randomness, "
              ^ "please use a variable whose name starts with " ^
              "\"inp\" or \"rnd\"."
            ) ;
            failwith "Illegal rule."
          )
        )
    )
  )
;;

let test_variables t regular =
  List.foldr (test_rule_variables (get_alphabet t) regular) "" (get_rules t)
;;

let test_reasonable t =
  let a = get_alphabet t in
  let f i str (rule, e) =
    if str <> "" then str else
    try
      if not (Rule.test_reasonable rule a e) then
        ("Rule " ^ (string_of_int i) ^ " reduces a logical term " ^
         "which we don't allow, because value should be retained!")
      else ""
    with Failure msg -> msg ^ " (rule " ^ (string_of_int i) ^ ")"
  in
  List.fold_lefti f "" (get_rules t)
;;

let test_values t =
  let a = get_alphabet t in
  let isboth f = (Alphabet.find_symbol_kind f a = Alphabet.Both) in
  let funs = Alphabet.funs ~p:isboth a in
  let isconstant f = Alphabet.is_ari 0 f a in
  let isbad f = not (isconstant f) in
  let badfuns = List.filter isbad funs in
  if badfuns = [] then ""
  else (
    let f = List.hd badfuns in
    let name = Function.find_name f in
    "Symbol " ^ name ^ " occurs both in the terms and logical " ^
    "alphabet, so should be a value, but it is not a constant."
  )
;;

let test_regular t =
  let rec test_all = function
    | [] -> ""
    | (rule, e) :: tail ->
      if Rule.is_regular rule then test_all tail
      else "Rule " ^ (Rule.to_stringm rule) ^ " is not regular"
  in
  test_all (get_rules t)
;;

let test_standard t =
  let a = get_alphabet t in
  let rec test_all = function
    | [] -> ""
    | (rule, e) :: tail ->
      if Rule.is_standard rule a then test_all tail
      else "Rule " ^ (Rule.to_stringm rule) ^ " is not standard"
  in
  test_all (get_rules t)
;;

let test_safe_sort t sort =
  let a = get_alphabet t in
  let dangerous = Alphabet.find_symbols_with_sort a sort in
  let really_dangerous = List.diff dangerous (def_symbols t) in
  let logical f = Alphabet.find_symbol_kind f a <> Alphabet.Terms in
  List.for_all logical really_dangerous
;;

(* tests whether it is possible to form terms f(...,err,...) with f a
constructor; returns either None or Some f if this can be done *)
(*
let test_error_constructors t =
  let a = get_alphabet t in
  let errsorts = Alphabet.sorts_with_errors a in
  let symbs = List.diff (funs t) (def_symbols t) in
  let term_symbol f =
    try Alphabet.find_symbol_kind f a = Alphabet.Terms
    with Not_found ->
      if Alphabet.mem_fun f a then failwith
        ("Symbol kind unset for function " ^ (Alphabet.find_fun_name f a))
      else failwith "Symbol kind and name unset for some symbol."
  in
  let relevant_non_constant f =
    try
      match Alphabet.find_sortdec f a with
        | Left sd -> Sortdeclaration.arity sd > 0
        | _ -> failwith "Term symbol with special declaration!"
    with Not_found -> false (* we only consider declared / used symbols *)
  in
  let error_input sofar f =
    match Alphabet.find_sortdec f a with
      | Left sd ->
        let sorts = Sortdeclaration.input_sorts sd in
        if List.intersect sorts errsorts <> [] then Some f
        else sofar
      | _ -> failwith "Meh?!?"
  in
  let constructors = List.filter term_symbol symbs in
  let relevants = List.filter relevant_non_constant constructors in
  List.fold_left error_input None relevants
;;

let test_no_error_catching t =
  let a = get_alphabet t in
  let errsorts = Alphabet.sorts_with_errors a in
  let errsymbs = List.map (Alphabet.error_fun a) errsorts in
  (* make sure the left-hand sides do not contain any error symbols *)
  let constants = left_cons t in
  if List.intersect constants errsymbs <> [] then
    ("The left-hand sides of the given rules contain error symbols; " ^
     "this should only happen in the pre-defined ERROR rules!")
  (* make sure subterms f(...,err,...) with f a constructor cannot occur *)
  else ""
;;

let test_right_errors t =
  let a = get_alphabet t in
  let rules = get_rules t in
  let check_rhs msg (rule, e) =
    let fs = Rule.right_funs rule in
    if List.exists (Alphabet.is_error a) fs then (
      match Rule.rhs rule with
        | Fun (_, []) | InstanceFun (_, [], _) -> msg
        | _ ->
          "RHS of rule contains error below root: " ^
          (Rule.to_stringm a e rule)
    )
    else msg
  in
  List.fold_left check_rhs "" rules
;;
*)

(* Current Environment *)

let set_current k =
  if k < 0 || k >= Array.length state.ts
  then failwith "Trying to set a current TRS which doesn't exist!"
  else state.cur <- k
;;

let has_current _ = state.cur >= 0;;

let get_current _ =
  if state.cur < 0 then failwith "No current TRS has been set!"
  else state.cur
;;

(* Printers *)

let to_string t =
  let alphabet = (get_alphabet t) in
  let to_string_rule (r, e) = Rule.to_stringm r in
  let astring = Alphabet.to_string alphabet in
  let rstring = List.to_string to_string_rule "\n" (get_rules t) in
  astring ^ "\n" ^ rstring
;;

let fprintf fmt t = Format.fprintf fmt "%s" (to_string t)
;;

(*let fprintf fmt t =
  let alphabet = (get_alphabet t) in
  let print_rule fmt (r, e) = Rule.fprintfm alphabet e fmt r in
  Alphabet.fprintf fmt alphabet ;
  Format.fprintf fmt "@[%a\n@]" (List.fprintf print_rule "@\n") (get_rules t)
;;*)

