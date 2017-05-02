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
open Util;;

(*** TYPES ********************************************************************)
type t = Std of int * string | Integer of int | Arr of t array |
         Mixed of string * string * string;;

(*** FUNCTIONS ****************************************************************)
(* Miscellaneous *)

let standard_symbol i name = Std (i, name);;
let integer_symbol i = Integer i;;
let array_symbol arr = Arr arr;;
let mixed_symbol name openb closeb = Mixed (name, openb, closeb);;

let copy = id;;

let is_standard = function
  | Std _ -> true
  | _ -> false
;;

let is_integer = function
  | Integer _ -> true
  | _ -> false
;;

let is_array = function
  | Arr _ -> true
  | _ -> false
;;

let is_mixed = function
  | Mixed _ -> true
  | _ -> false
;;

let std_to_int = function
  | Std (i,_) -> i
  | _ -> failwith "Only standard functions can be converted to ints"
;;

let integer_to_int = function
  | Integer i -> i
  | _ -> failwith "Function symbol is not an integer"
;;

let array_to_array = function
  | Arr arr -> arr
  | _ -> failwith "Function symbol is not an array"
;;

let mixed_to_string = function
  | Mixed (name, _, _) -> name
  | _ -> failwith "Function symbol is not a mixed"

let array_from_list f lst = Arr (Array.of_list (List.map f lst));;

let mixed_brackets = function
  | Mixed (_, ob, cb) -> (ob, cb)
  | _ -> failwith "Brackets requested of non-mixed symbol"

(* Compare Functions *)

let compare a b =
  match (a, b) with
    | (Std (aa,_), Std (bb,_)) -> compare aa bb
    | (Integer aa, Integer bb) -> compare aa bb
    | (Arr aa, Arr bb) -> compare aa bb
    | (Mixed (an, ao, ac), Mixed (bn, bo, bc)) ->
      compare (an, ao, ac) (bn, bo, bc)
    | (Std _, Integer _) | (Std _, Arr _) | (Std _, Mixed _) |
      (Integer _, Arr _) | (Integer _, Mixed _) | (Arr _, Mixed _) -> -1
    | (Mixed _, Arr _) | (Mixed _, Integer _) | (Mixed _, Std _) |
      (Arr _, Integer _) | (Arr _, Std _) | (Integer _, Std _) -> 1
;;

let equal f g = compare f g = 0;;

(* Printers *)

let rec to_string ?(debug = true) = function
  | Std (_,name) -> (if debug then "$" else "") ^ name
  | Integer i -> (if debug then "I" else "") ^ (string_of_int i)
  | Arr x -> (if debug then "A" else "") ^ stringify_array debug x
  | Mixed (n, o, c) -> (if debug then "M" else "") ^ o ^ n ^ c

and stringify_array debug arr =
  let recurse = to_string ~debug:debug in
  "{" ^ (List.implode recurse ":" (Array.to_list arr)) ^ "}"
;;

let find_name = to_string ~debug:false;;

let fprintf fmt = function
  | Std (_,n) -> Format.fprintf fmt "@[%s@]" n
  | Integer i -> Format.fprintf fmt "@[i%i@]" i
  | Arr x -> Format.fprintf fmt "@[{%s}@]"
             (List.implode to_string ":" (Array.to_list x))
  | Mixed (n,o,c) -> Format.fprintf fmt "@[%s%s%s@]" o n c
;;

(* Hash Function *)

let hash = function
  | Std (i,_) -> i*5
  | Integer i -> if i < 0 then (-i)*5+1 else i*5+2
  | Arr arr -> 5 * (String.hash (stringify_array true arr)) + 3
  | Mixed (n,_,_) -> 5 * (String.hash n) + 4
;;

