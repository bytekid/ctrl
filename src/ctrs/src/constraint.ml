(* Copyright 2014 Cynthia Kop
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

(*** MODULES ******************************************************************)
module Fun = Function;;
module Var = Variable;;

(*** OPENS ********************************************************************)
open Prelude;;
open Util;;

(*** TYPES ********************************************************************)
type term = Term.t (*= Var of Var.t | Fun of Fun.t * term list |
                     InstanceFun of Fun.t * term list * Sortdeclaration.t |
                     Forall of Var.t * term | Exists of Var.t * term*);;
type t = ReduceCondition                 of term * term |
         JoinCondition                   of term * term |
         ConstructorFormConstraint       of Variable.t list |
         GroundConstructorFormConstraint of Variable.t list |
         LogicalConstraint               of term;;

(*** FUNCTIONS ***************************************************************)

(* Constructors *)

let reduce_condition s t = ReduceCondition (s, t);;
let join_condition s t = JoinCondition (s, t);;
let constructor_form_constraint s = ConstructorFormConstraint s;;
let ground_constructor_form_constraint s = GroundConstructorFormConstraint s;;
let logical_constraint s = LogicalConstraint s;;

(* Miscellaneous *)

let hash = Hashtbl.hash;;

let modify_terms f = function
  | ReduceCondition (a, b) -> ReduceCondition (f a, f b)
  | JoinCondition (a, b) -> JoinCondition (f a, f b)
  | LogicalConstraint a -> LogicalConstraint (f a)
  | nfconstr -> nfconstr
;;

let run f1 f2 f3 f4 f5 = function
  | ReduceCondition (a, b) -> f1 a b
  | JoinCondition (a, b) -> f2 a b
  | ConstructorFormConstraint a -> f3 a
  | GroundConstructorFormConstraint a -> f4 a
  | LogicalConstraint a -> f5 a
;;

let underlying_terms c =
  let f a b = [a;b] in
  let g a = List.map Term.make_var a in
  let h a = [a] in
  run f f g g h c
;;

let is_nf_constraint = function
  | ConstructorFormConstraint a -> Some (false, a)
  | GroundConstructorFormConstraint a -> Some (true, a)
  | _ -> None
;;

let is_logical_constraint = function
  | LogicalConstraint a -> Some a
  | _ -> None
;;

let list_vars b lst =
  let all_terms = List.flat_map underlying_terms lst in
  let varsfun = if b then Term.allvars else Term.vars in
  let all_variables = List.map varsfun all_terms in
  let rec uvars unique = function
    | [] -> unique
    | head :: tail ->
      if unique = [] then uvars head tail (* optimisation *)
      else (
        let uhead = List.diff head unique in
        uvars (List.append uhead unique) tail
      )
  in
  uvars [] all_variables
;;

let vars c = list_vars false [c];;
let allvars c = list_vars true [c];;

(* Printers *)

let to_string_help maybe c =
  let (to_string_term, to_string_var) =
    match maybe with
      | Some (a, e) ->
        let fn = Alphabet.fun_names a in
        (Term.to_stringm a e,
         fun x -> Environment.to_string_var x fn e)
      | None -> (Term.to_string, Variable.to_string)
  in
  let to_string_vars lst = List.implode to_string_var "," lst in
  match c with
    | ReduceCondition (a, b) -> 
      (to_string_term a) ^ " ->* " ^ (to_string_term b)
    | JoinCondition (a, b) -> 
      (to_string_term a) ^ " ->*<- " ^ (to_string_term b)
    | ConstructorFormConstraint a ->
      (to_string_vars a) ^ " in CNF"
    | GroundConstructorFormConstraint a ->
      (to_string_vars a) ^ " in GCNF"
    | LogicalConstraint a ->
      "[" ^ (to_string_term a) ^ "]"
;;

let to_string = to_string_help None;;
let to_stringm a e = to_string_help (Some (a, e));;
let fprintf fmt c = Format.fprintf fmt "%s" (to_string c);;
let fprintfm a e fmt c = Format.fprintf fmt "%s" (to_stringm a e c);;

(*let fprintf_help maybe fmt c =
  let termprint fmt t =
    match maybe with
      | Some (a, e) -> Term.fprintfm a e fmt t
      | None -> Term.fprintf fmt t
  in
  match c with
    | ReduceCondition (a, b) -> 
      F.fprintf fmt "@[%a@ ->*@ %a@]" termprint a termprint b
    | JoinCondition (a, b) -> 
      F.fprintf fmt "@[%a@ ->*<-@ %a@]" termprint a termprint b
    | NormalFormConstraint a ->
      F.fprintf fmt "@[%a@ in NF@]" termprint a
    | ConstructorFormConstraint a ->
      F.fprintf fmt "@[%a@ in CNF@]" termprint a
    | GroundConstructorFormConstraint a ->
      F.fprintf fmt "@[%a@ in GCNF@]" termprint a
    | LogicalConstraint a ->
      F.fprintf fmt "@[[%a]@]" termprint a
;;

let fprintf = fprintf_help None;;
let fprintfm a e fmt = fprintf_help (Some (a, e)) fmt;;
let to_string = Format.flush_str_formatter <.> fprintf Format.str_formatter;;
let to_stringm a e = Format.flush_str_formatter <.> (fprintfm a e Format.str_formatter);;*)

