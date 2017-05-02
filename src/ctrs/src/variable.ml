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
type t = int * string;;

(*** FUNCTIONS ****************************************************************)
(* Miscellaneous *)
let create i x = (i,x);;
let copy = id;;
let hash (i,_) = i;;
let to_int ((i,_) : t) = i;;
let find_name (_,x) = x;;

(* Compare Functions *)
let compare (i,_) (j,_) = compare i j;;
let equal x y = compare x y = 0;;

(* Printers *)
let to_string (i,x) = x;;
let fprintf fmt (i,x) = Format.fprintf fmt "@[%s@]" x;;

