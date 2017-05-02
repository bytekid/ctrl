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

(*** MODULES ******************************************************************)
module F = Format;;
module Var = Variable;;

(*** OPENS ********************************************************************)
open Prelude;;
open Util;;

(**
  A Functor is used here to allow the packaging system to deal with complex
  terms.  This is explained in rewriting.ml
*)
module Make (MM : MAKEMODULE) = struct

(*** TYPES *******************************************************************)
type func = Function.t;;
type term = Term.t = Var of Var.t | Fun of Function.t * term list |
                     InstanceFun of Function.t * term list * Sortdeclaration.t |
                     Forall of Var.t * term | Exists of Var.t * term;;
type context = Context.t = Hole | More of Function.t * term list * context * term list;;
 
(*** INCLUDES ****************************************************************)
include Replacement.Make (Var) (Term);;
 
(*** FUNCTIONS ***************************************************************)

(* Apply Substitutions *)

let apply_term s t =
  (* gives a failure message if term contains a bound variable,
  unless it is the variable x is bound to *)
  let check_bad x bound term =
    if bound = [] then term else
    let vs = Term.vars term in
    let assoc y =
      try [List.assoc y bound]
      with Not_found -> []
    in
    let bads = List.flat_map assoc vs in
    if bads = [] then term
    else if (bads = [x]) && (Term.is_var term) then term
    else failwith "Substitution replaces a bound variable!"
  in
  (* returns the variable substitued for x, if any, and gives a
  failure if x is substituted by anything other than a variable *)
  let check_var x =
    if mem x s then (
      match find x s with
        | Term.Var z -> z
        | x -> failwith ("Cannot substitute binder variables by " ^
                         "anything but a variable (trying " ^
                         (Term.to_string x) ^ ").")
    )
    else x
  in
  (* recursively apply the substitution on the term *)
  let rec apply_main bound = function
    | Var x as q ->
      let result = apply x q s in
      check_bad x bound result
    | Fun (f,ts) -> Fun (f,List.map (apply_main bound) ts)
    | InstanceFun (f,ts,d) ->
      InstanceFun (f,List.map (apply_main bound) ts,d)
    | Forall (x, q) ->
      let y = check_var x in
      Forall (y, apply_main ((y,x) :: bound) q)
    | Exists (x, q) ->
      let y = check_var x in
      Exists (y, apply_main ((y,x) :: bound) q)
  in
  apply_main [] t
;;
 
let rec apply_context s = function
  | Hole -> Hole
  | More (f,us,c,vs) ->
    let g = List.map (apply_term s) in More (f,g us,apply_context s c,g vs)
;;

(* Properties *)

let is_surjective s =
  let dom = domain s in
  List.for_all (fun x ->
    not (List.mem ~c:Var.compare x dom)
      || exists (fun _ t -> Term.equal (Var x) t) s
  ) dom
;;
 
let is_bijective s = is_injective s && is_surjective s;;
let is_renaming = is_bijective

(* Printers *)

let to_stringm s =
  let f x t rest =
    (Variable.find_name x) ^ " -> " ^ (Term.to_stringm t) ^ "\n" in
  fold f s ""
;;

let fprintfm fmt s = Format.fprintf fmt "%s" (to_stringm s);;

end

