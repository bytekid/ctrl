(* Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
 * and 2014, Cynthia Kop.
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

(*** OPENS ********************************************************************)
open Util;;

(*** TYPES ********************************************************************)
type sort = Sort.t
type polsort = Mono of string | MonoIndexed of string * int | SVar of string;;
type t = Known of polsort list * polsort | Unknown of polsort * polsort;;
type sd = Sortdeclaration.t

(*** FUNCTIONS ****************************************************************)
(* Miscellaneous *)
let copy = id;;
let hash = Hashtbl.hash;;

(* Compare Functions *)
let compare = compare;;
let equal f g = compare f g = 0;;

let pol_to_string = function
  | Mono s -> s
  | SVar s -> "?" ^ s
;;

(* Printers *)
let to_string s =
  let str = pol_to_string in
  let rec print_list lst =
    match lst with
      | [] -> "]"
      | a :: [] -> (str a) ^ "]"
      | a :: b :: tail -> (str a) ^ " * " ^ (print_list (b :: tail))
  in
  match s with
    | Known (inp, outp) -> "[" ^ (print_list inp) ^ " ==> " ^ (str outp)
    | Unknown (inp, outp) -> "<" ^ (str inp) ^ "> ==> " ^ (str outp)
;;

let fprintf fmt f = Format.fprintf fmt "@[%s@]" (to_string f);;

(* Creation and Recovery *)

let polymorphic_declaration inps outp = Known (inps, outp);;
let variable_declaration inp outp = Unknown (inp, outp);;

let known_arity = function
  | Known _ -> true
  | Unknown _ -> false
;;

let arity = function
  | Known (lst, _) -> List.length lst
  | Unknown _ -> failwith "Arity requested of symbol with variable arity"
;;

let input_sort i = function
  | Unknown (inp, _) -> inp
  | Known (lst, _) ->
    let rec checklist num = function
      | [] -> (*raise Not_found*) failwith "input_sort in special declaration"
      | head :: tail ->
        if num = 1 then head
        else checklist (num-1) tail
    in
    checklist i lst
;;

let input_sorts = function
  | Unknown (inp, _) -> [inp]
  | Known (inps, _) -> inps
;;

let output_sort = function
  | Unknown (_, outp) -> outp
  | Known (_, outp) -> outp
;;

(* Manipulating polymorphic sorts *)

let is_polymorphic = function
  | SVar _ -> true
  | _ -> false
;;

let pol_to_sort = function
  | Mono str -> Sort.from_string str
  | MonoIndexed (str, n) -> Sort.from_indexed str n
  | SVar str -> failwith "Sort conversion requested for sort variable!"
;;

let sort_to_pol sort = Mono (Sort.to_string sort);;

let make_polsort str ?(index = None) =
  let len = String.length str in
  if str.[0] = '?' then SVar (String.sub str 1 (len - 1))
  else
    match index with
      None -> Mono str
    | Some i -> MonoIndexed(str,i)
;;

(* Comparing to / turning into monomorphic fixed declarations *)

let is_normal_sortdec sd =
  let rec all_monomorphic = function
    | [] -> true
    | head :: tail ->
      if is_polymorphic head then false
      else all_monomorphic tail
  in
  match sd with
    | Unknown _ -> false
    | Known (inp, outp) -> all_monomorphic (outp :: inp)
;;

let make_normal_sortdec sd =
  match sd with
    | Unknown _ -> failwith ("Conversion to Sortdeclaration.t " ^
        "requested for declaration with variable arity!")
    | Known (inp, outp) ->
      let lst = List.map pol_to_sort (outp :: inp) in
      Sortdeclaration.create (List.tl lst) (List.hd lst)
;;

