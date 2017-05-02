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
type t = Fixed of string | Indexed of string * int;;

(*** FUNCTIONS ****************************************************************)
(* Miscellaneous *)
let copy = id;;
let hash = Hashtbl.hash;;

(* Compare Functions *)
let compare = compare;;
let equal f g = compare f g = 0;;

let is_indexed = function Fixed _ -> false | _ -> true;;

let index = function
    Indexed (_ , i) -> i
  | _ -> failwith "Index requested for unindexed sort has no index"
;;

(* Printers *)
let to_string = function
    Fixed s -> s
  | Indexed(s,i) ->
    let j = if i < 0 then 8 else i in
    "(_ " ^ s ^ " " ^ (string_of_int j) ^ ")"
;;

let fprintf fmt f = Format.fprintf fmt "@[%s@]" (to_string f);;

let from_string s = Fixed s;;
let from_indexed s i = Indexed (s, i);;
