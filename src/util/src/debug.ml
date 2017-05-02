(* Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
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

(*constants*)
let don = ref false;;
let t0 = ref (Unix.gettimeofday ());;

(*functions*)
let eprintf s = 
 Format.eprintf "--- %s (%f)@\n%!" s (Unix.gettimeofday () -. !t0);;

let debug s = if !don then eprintf s;;
let force s = eprintf s;;

let on () = 
 (* debug "debugging on"; *)
 don := true;
;;

let off () = 
 (* debug "debugging off"; *)
 don := false;
;;

