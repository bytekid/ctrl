(* Copyright 2012 Simon Legner, Christian Sternagel, Harald Zankl
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
open Prelude;;
open Int64;;

(*** TYPES ********************************************************************)
type t = int64;;

(*** FUNCTIONS ****************************************************************)

(* Constructors *)
let zero, one, minus_one = zero, one, minus_one;;
let max_int, min_int = max_int, min_int;;

let of_int, of_float, of_int32 = of_int, of_float, of_int32;;
let of_nativeint, of_string, of_float = of_nativeint, of_string, of_float;;
let to_int, to_float, to_int32 = to_int, to_float, to_int32;;
let to_nativeint, to_string = to_nativeint, to_string;;

(* Integer Operators *)
let succ, add, pred, neg, sub = succ, add, pred, neg, sub;;
let mul, div, rem, abs = mul, div, rem, abs;;
let rec pow base = function
 | x when x < Int64.zero -> failwith "negative exponent"
 | x when x = Int64.zero -> Int64.one
 | x -> mul base (pow base (pred x))
;;

(* Bit Operators *)
let bit_max_int n =
 Int64.of_string (Big_int.string_of_big_int (Int.bit_max_big_int n))
;;
let float_of_bits, bits_of_float = float_of_bits, bits_of_float;;

(* Logical Operators *)
let logand, logor, logxor, lognot = logand, logor, logxor, lognot;;
let shift_right_logical = shift_right_logical;;

(* Compare Functions *)
let compare = compare;;
let equal n m = compare n m = 0;;
let gt a b = a > b;;
let eq = equal;;
let ge a b = a >= b;;

(* Printers *)
let to_string = to_string;;
let fprintf ppf x = Format.fprintf ppf "%s" (Int64.to_string x);;

