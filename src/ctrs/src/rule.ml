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

(*** MODULES *****************************************************************)
module Pos = Position;;
module L = struct end;;
module Sub = Substitution.Make(L);;

(*** OPENS *******************************************************************)
open Prelude;;
open Util;;

(*** TYPES *******************************************************************)
type substitution = Sub.t;;
type func = Function.t;;
type term = Term.t = Var of Variable.t | Fun of func * term list |
                     InstanceFun of func * term list * Sortdeclaration.t |
                     Forall of Variable.t * term |
                     Exists of Variable.t * term;;
type t = Term.t * Term.t * Term.t list;;

exception Not_an_lctrs;;
 
(*** FUNCTIONS ***************************************************************)

(* Constructors and Destructors *)

let ditch_constraints (l, r, c) = (l, r);;
let invert (l, r, c) = (r, l, c);;
let lhs (l, r, c) = l;;
let rhs (l, r, c) = r;;
let constraints (l, r, c) = c;;
let create l r c = (l, r, c);;
let of_terms l r = (l, r, []);;

(* Iterators *)

let apply f g h ( (l, r, c) : t ) = (f l, g r, h c);;
let fold f d ( (l, r, c) : t ) = f r (f l d);;
let map f = apply f f (List.map f);;
let project = map;;
let uncurry f (l, r, c) = f l r c;;

let uncurry_main f ( (a, b, c) : t ) = f a b;;
let map_main f ( (l, r, c) : t ) = (f l, f r);;

(* Rule Symbols *)

let symbols f (l, r, c) =
  let symbs term rest = List.union (f term) rest in
  List.foldr symbs [] (l :: r :: c)
;;

(* let symbols f = Pair.uncurry List.union <.> map_main f;; *)

let cons = symbols Term.cons;;
let funs = symbols Term.funs;;
let vars = symbols Term.vars;;
let allvars = symbols Term.allvars;;
let symbols = symbols Term.symbols;;
let left_cons r = Term.cons (lhs r);;
let left_funs r = Term.funs (lhs r);;
let left_vars r = Term.vars (lhs r);;
let left_symbols r = Term.symbols (lhs r);;
let right_cons r = Term.cons (rhs r);;
let right_funs r = Term.funs (rhs r);;
let right_vars r = Term.vars (rhs r);;
let right_symbols r = Term.symbols (rhs r);;
 
let left_root r =
  (Option.the <.> Term.root <.> lhs <?> "left-hand side is not a function") r
;;
 
let right_root r =
  (Option.the <.> Term.root <.> rhs <?> "right-hand side is not a function") r
;;
 
let roots r =
  let root g = try [Option.the (Term.root (g r))] with Failure _ -> [] in
  let f = root lhs and g = root rhs in if f = g then f else List.rev_append f g
;;
 
(* Compare Functions *)

let compare = compare;;
let equal r r' = compare r r' = 0;;
 
(* Rewriting *)

let rewrite t p r = 
  let s = Elogic.match_term (Term.subterm p t) (lhs r) in
  Term.replace p (Sub.apply_term s (rhs r)) t
;;

let rewrites s p r t = 
  try rewrite s p r = t with Elogic.Not_matchable -> false
;; 

let reducts t r = 
  let f rs p = try (rewrite t p r :: rs) with Elogic.Not_matchable -> rs in
  (List.foldl f [] <.> flip Term.fun_pos t <.> Option.the <.> Term.root <.> lhs <?>
    "left-hand side is not a function") r
;;
 
let redex_pos t r =
  let f p = Elogic.matches (Term.subterm p t) (lhs r) in
  List.filter f (Term.fun_pos (left_root r) t)
;;
 
let accessible_redex_pos t mu r =
  let f p = Elogic.matches (Term.subterm p t) (lhs r) in
  List.filter f (Term.accessible_fun_pos (left_root r) mu t)
;;
 
(* Properties *)

let for_both f ( (l, r, c) : t ) = (f l) && (f r);;
 
let is_build = for_both <.> Term.is_build;;
let is_collapsing r = Term.is_var (rhs r);;
let is_dummy = for_both Term.is_dummy;;
 
let is_duplicating r =
  let rec count c x = function
    | Var y -> if x = y then c + 1 else c
    | Fun (_,ts) | InstanceFun (_,ts,_) -> List.foldl (flip count x) c ts
    | Forall (y, t) | Exists (y, t) ->
      if x = y then 0 else count c x t
  in
  match r with | (l,r,c) ->
  List.exists (fun x -> count 0 x l < count 0 x r) (Term.vars r)
;;

(*
let is_proper_embedded r =
  List.exists (Term.is_embedded (rhs r)) (Term.subterms (lhs r))
;;
let is_embedded = uncurry_main (flip Term.is_embedded);;
*)

let is_flat = for_both Term.is_flat;;
let is_ground = for_both Term.is_ground;;
let is_linear = for_both Term.is_linear;;
let is_shallow = for_both Term.is_shallow;;
let is_string = for_both Term.is_string;;

let is_size_preserving r =
  let check = Term.size (lhs r) >= Term.size (rhs r) in
  if check then not (is_duplicating r)
  else check
;;

let is_left_build fs = Term.is_build fs <.> lhs;;
let is_left_dummy r = Term.is_dummy (lhs r);;
let is_left_flat r = Term.is_flat (lhs r);;
let is_left_ground r = Term.is_ground (lhs r);;
let is_left_linear r = Term.is_linear (lhs r);;
let is_left_shallow r = Term.is_shallow (lhs r);;
let is_left_string r = Term.is_string (lhs r);;
let is_right_build fs = Term.is_build fs <.> rhs;;
let is_right_dummy r = Term.is_dummy (rhs r);;
let is_right_flat r = Term.is_flat (rhs r);;
let is_right_ground r = Term.is_ground (rhs r);;
let is_right_linear r = Term.is_linear (rhs r);;
let is_right_shallow r = Term.is_shallow (rhs r);;
let is_right_string r = Term.is_string (rhs r);;

let is_growing r =
  let l = lhs r in
  let check x = List.for_all ((>=) 1 <.> Pos.length) (Term.var_pos x l) in
  List.for_all check (List.intersect (Term.vars l) (Term.vars (rhs r)))
;;
 
let matches r r' =
  try const true (Elogic.match_problem [(lhs r,lhs r');(rhs r,rhs r')])
  with Elogic.Not_matchable -> false
;;

let is_variant r r' = matches r r' && matches r' r;;
let subsumes (l, r, c) = matches (r, l, c);;
let is_erasing = not <.> Pair.uncurry List.is_subset <.> map_main Term.vars;;
let is_contained = uncurry_main (flip Elogic.contains);;
let is_left_erasing = Pair.uncurry List.is_supset <.> map_main Term.vars;;
let is_rewrite_rule r = Term.is_fun (lhs r) && is_left_erasing r && List.is_empty (constraints r);;
let is_normal_form t r = try reducts t r = [] with Failure _ -> false;;
let is_redex t r = Elogic.matches t (lhs r);;

let is_standard r a = Term.check_proper_term a (lhs r) = None;;

let is_regular r =
  let cvars = List.flat_map Term.vars (constraints r) in
  let lvars = left_vars r in
  List.is_subset cvars lvars
;;
 
let is_overlap r1 p r2 =
  let group = Elogic.environment_oblivious_renaming [lhs r1; Term.subterm p (lhs r2)] in
  match group with
    | term1 :: term2 :: [] -> (
      let unif = try Elogic.are_unifiable term1 term2
                 with Failure _ -> false
      in
      unif && (not (Pos.is_root p) || not (is_variant r1 r2))
    )
    | _ -> failwith "error in is_overlap, shouldn't happen"
;;

let ols_p r1 p r2 = if (is_overlap r1 p r2) then [(r1,p,r2)] else [];;

let rec ols r1 r2 = function
  | [] -> []
  | p :: tail -> List.append (ols_p r1 p r2) (ols r1 r2 tail)
;;

let overlaps r1 r2      = ols r1 r2 (Term.funs_pos (lhs r1));;
let var_overlaps r1 r2  = ols r1 r2 (Term.vars_pos (lhs r1));;
let are_overlapping s t = (overlaps s t) <> [];;

(* Equational Logic *)

let apply_sub s rule = map (Sub.apply_term s) rule;;

(* Miscellaneous *)

let count_fun f = fold ((+) <.> Term.count_fun f) 0;;
(*let reflect = apply Term.reflect Term.reflect id;;*)
let reverse = apply Term.reverse Term.reverse id <?> "term is not a string";;
let to_terms (l, r, c) = (l, r);;
let copy = id;;
let hash r = Hashtbl.hash (map Term.hash r);;
let depth = Pair.uncurry max <.> map_main Term.depth;;

let rename_avoid r a e =
  let cterms = constraints r in
  let gamma = Elogic.renaming (List.append [lhs r;rhs r] cterms) a e in
  apply_sub gamma r
;;

let rename r = rename_avoid r [];;
let rename_fully r e a = rename_avoid r (Alphabet.fun_names a) e;;

let fresh_renaming rule oldenv newenv funnames =
  let vars = List.unique (allvars rule) in
  let create_fresh x =
    let y = Environment.create_var_like x oldenv funnames newenv in
    (x, Term.make_var y)
  in
  let replacement = List.map create_fresh vars in
  let substitution = Sub.of_list replacement in
  apply_sub substitution rule
;;

let environment_transfer rule oldenv newenv funnames =
  let vars = List.unique (allvars rule) in
  let replacement x = Environment.create_var_like x oldenv funnames newenv in
  let subst x = (x, Term.make_var (replacement x)) in
  let sub = Sub.of_list (List.map subst vars) in
  apply_sub sub rule
;;

(* helping function for calculation_free and full_calculation_free *)
let logical_free a e r all_logical : t =
  (* we're going to need an equality symbol to use in constraints *)
  let equal = (
    try Alphabet.get_equal_symbol a
    with Not_found -> failwith ("Cannot create a calculation-free " ^
      "version of this LCTRS: no equality symbol = has been set.")
  ) in
  (* and for creating fresh variables, we need to know which names
     already occur in the alphabet *)
  let funnames = Alphabet.fun_names a in
  (* this returns a calculation-free version of term, together with a
     list of equalities of the form variable = term
  *)
  let getsort term =
    try Term.get_sort a e term
    with Not_found -> failwith ("Finding calculation-free " ^
      "version of term failed because types have not been " ^
      "set up properly.")
  in
  let replace term =
    let sort = getsort term in
    let var = Environment.create_sorted_var sort funnames e in
    let x = Term.make_var var in
    (x, [Term.make_function a e equal [x;term]])
  in
  let symbol_kind f =
    try Alphabet.find_symbol_kind f a 
    with Not_found -> failwith ("Alphabet contains a function " ^
      "symbol whose kind (theory versus term signature) is not " ^
      "set!")
  in
  let list_logical lst =
    let funs = List.flat_map Term.funs lst in
    let is_logical f = symbol_kind f <> Alphabet.Terms in
    List.for_all is_logical funs
  in
  let rec calc_free term = match term with
    | Var _ -> (term, [])
    | Fun (f, args) -> calc_free_function Term.make_fun term f args
    | InstanceFun (f, args, sd) ->
      calc_free_function (fun f a -> Term.make_instance f a sd) term f args
    | Forall _ | Exists _ -> replace term
  and calc_free_function create term f args =
    let kind = symbol_kind f in
    if ((kind = Alphabet.Logical) ||
       ((kind = Alphabet.Both) && (all_logical))) &&
       (list_logical args) then replace term
    else (
      let arguments = List.map calc_free args in
      let children = List.map fst arguments in
      let equalities = List.flat_map snd arguments in
      (create f children, equalities)
    )
  in
  (* main functionality *)
  let (right, equalities) = calc_free (rhs r) in
  create (lhs r) right (List.append (constraints r) equalities)
;;

let calculation_free a e r = logical_free a e r false;;
let full_calculation_free a e r = logical_free a e r true;;

let add_constraint c cs andsymb =
  let rec add_extra a = function
    | [] -> [c]
    | head :: tail ->
      ( Term.make_fun a [head; c] ) :: tail
  in
  match andsymb with
    | None -> c :: cs
    | Some a -> add_extra a cs
;;

let left_value_free a e (l, r, cs) =
  let equal = (
    try Alphabet.get_equal_symbol a
    with Not_found -> failwith ("Cannot create a left-value-free " ^
      "version of this LCTRS: no equality symbol = has been set.")
  ) in
  let conj = (
    try Some (Alphabet.get_and_symbol a)
    with Not_found -> None
  ) in
  let recreate_function f args somesd =
    let (newargs, newcs) = List.split args in
    let newcs = List.flatten newcs in
    match somesd with
      | None -> (Term.make_fun f newargs, newcs)
      | Some sd -> (Term.make_instance f newargs sd, newcs)
  in
  let varfun x = (Term.make_var x, []) in
  let instancefun f args sd = recreate_function f args (Some sd) in
  let funnames = Alphabet.fun_names a in
  let funfun f args =
    let (term, cs) = recreate_function f args None in
    if (args <> []) || (Alphabet.find_symbol_kind f a = Alphabet.Terms) then
      (term, cs)
    else (
      let sort = Term.get_sort a e term in
      let y = Environment.create_sorted_var sort funnames e in
      let yterm = Term.make_var y in
      let eq = Term.make_function a e equal [yterm; term] in
      (yterm, [eq])
    )
  in
  let allfun x (arg, lst) = (Forall (x, arg), lst) in
  let exfun x (arg, lst) = (Exists (x, arg), lst) in
  let (newl, newcs) = Term.recurse varfun funfun instancefun allfun exfun l in
  let rec update_constraints cs = function
    | [] -> cs
    | head :: tail -> update_constraints (add_constraint head cs conj) tail
  in
  (newl, r, update_constraints cs newcs)
;;

(* Printers *)

let to_string (l, r, c) =
  match c with
    | [] -> Printf.sprintf "%s -> %s" (Term.to_string l) (Term.to_string r)
    | _  -> Printf.sprintf "%s -> %s [%s]" (Term.to_string l)
        (Term.to_string r) (List.to_string Term.to_string ", " c)
;;

let to_stringm (l, r, c) =
  match c with
    | [] -> Printf.sprintf "%s -> %s" (Term.to_stringm l) (Term.to_stringm r)
    | _  -> Printf.sprintf "%s -> %s [%s]" (Term.to_stringm l)
        (Term.to_stringm r) (List.to_string Term.to_stringm ", " c)
;;

let fprintf fmt rule = Format.fprintf fmt "%s" (to_string rule);;
let fprintfm fmt rule = Format.fprintf fmt "%s" (to_stringm rule);;

(*let fprintf fmt (l, r, c) =
  match c with
    | [] -> Format.fprintf fmt "%a -> %a" Term.fprintf l Term.fprintf r
    | _ -> Format.fprintf fmt "%a -> %a <-- %a" Term.fprintf l
        Term.fprintf r (List.fprintf Constraint.fprintf ",") c
;;

let fprintfm a e fmt (l, r, c) =
  match c with
    | [] -> Format.fprintf fmt "%a -> %a" (Term.fprintfm a e) l
            (Term.fprintfm a e) r
    | _ -> Format.fprintf fmt "%a -> %a <-- %a" (Term.fprintfm a e) l
            (Term.fprintfm a e) r (List.fprintf (Constraint.fprintfm a e) ", ")
            c

let to_string = Format.flush_str_formatter <.> fprintf Format.str_formatter;;
let to_stringm a e = Format.flush_str_formatter <.> (fprintfm a e Format.str_formatter);;*)

(* Validity Checking *)

let test_reasonable (l,r,c) a e =
  let errorcheck place desc = function
    | None -> ()
    | Some pos -> failwith ("Symbol error at position " ^
      (Pos.to_string pos) ^ " of " ^ place ^ " in rule " ^
      (to_string (l,r,c)) ^ ": " ^ desc)
  in
  let logical = Term.check_logical_term a in
  let check_constraint i c =
    errorcheck ("constraint " ^ (string_of_int i))
      "logical constraints should be logical terms" (logical c)
  in
  let rec check_constraints i = function
    | [] -> ()
    | head :: tail ->
      check_constraint i head ;
      check_constraints (i+1) tail
  in
  let functions = funs (l, r, c) in
  let badfun f = (not (Alphabet.mem_symbol_kind f a)) in
  let bads = List.filter badfun functions in
  if bads <> [] then (
    let f = List.hd bads in
    failwith ("Function symbol " ^ (Function.find_name f) ^
              " has no symbol kind set.")
  ) ;
  check_constraints 1 c ;
  if Term.is_value a l then failwith "Left-hand side of rule is a value"
  else if logical l = None then false
  else true
;;

