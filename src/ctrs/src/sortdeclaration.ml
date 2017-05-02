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

(*** OPENS ********************************************************************)
open Util;;

(*** TYPES ********************************************************************)
type sort = Sort.t
type t = { input : Sort.t array ; output : Sort.t };;

(*** FUNCTIONS ****************************************************************)
(* Miscellaneous *)
let copy s = { input = Array.copy s.input ; output = s.output };;
let hash = Hashtbl.hash;;

(* Compare Functions *)
let compare = compare;;
let equal f g = compare f g = 0;;

(* Printers *)
let to_string s =
  let rec print_list lst =
    match lst with
      | [] -> "]"
      | a :: [] -> Sort.to_string a ^ "]"
      | a :: tail -> Sort.to_string a ^ " * " ^ (print_list tail)
  in
  let ss = Array.to_list s.input in
  "[" ^ (print_list ss) ^ " ==> " ^ (Sort.to_string s.output);;

let fprintf fmt f = Format.fprintf fmt "@[%s@]" (to_string f);;

(* Creation and Recovery *)
let create lst a = {input = Array.of_list lst ; output = a};;

let input_sort s i =
  if i > 0 && i <= Array.length s.input
  then s.input.(i-1)
  else failwith ("Trying to access input sort " ^
    (string_of_int i) ^ " of sort declaration " ^
    (to_string s));;

let input_sorts s = Array.to_list s.input;;

let output_sort s = s.output;;

let arity s = Array.length s.input;;

