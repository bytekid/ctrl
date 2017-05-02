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

(*** OPENS *******************************************************************)
open Prelude;;
open Util;;

(*** MODULES *****************************************************************)
module PosSet = struct
  include Set.Make(Int)
  
  let fprintf fmt s =
    Format.fprintf fmt "{" ;
    iter (fun i -> Format.fprintf fmt "%d, " i) s ;
    Format.fprintf fmt "}"
  
  let copy s =
    let f i c = add i c in
    fold f s empty

  let hash = Hashtbl.hash
end;;

module FuncToPosses = Index.Make (Int) (PosSet);;

(*** TYPES *******************************************************************)
type func = Function.t;;
type t = int;;

(** STATE VARIABLES **********************************************************)
type internal = { mutable maps : FuncToPosses.t array };;
let state = { maps = [| |] };;

(*** FUNCTIONS ***************************************************************)

(* General Accessing Functions *)

let get c = state.maps.(c);;
let update c ftp = state.maps.(c) <- ftp;;

(* Constructors *)

let empty _ =
  let newmap = FuncToPosses.empty in
  let len = Array.length state.maps in
  state.maps <- Array.append state.maps [| newmap |] ;
  len
;;

let fill a c =
  let rec fillset n s =
    if n = 0 then s
    else fillset (n-1) (PosSet.add (n-1) s)
  in
  let rec fillmap m = function
    | [] -> m
    | head :: tail ->
      if not (Function.is_standard head) then fillmap m tail else
      if not (Alphabet.mem_ari head a) then fillmap m tail else
      let n = Alphabet.find_ari head a in
      let f = Function.std_to_int head in
      let fullset = fillset n PosSet.empty in
      fillmap (FuncToPosses.add f fullset m) tail
  in
  update c (fillmap (get c) (Alphabet.funs a))
;;

let copy c =
  let cp = FuncToPosses.copy (get c) in
  let len = Array.length state.maps in
  state.maps <- Array.append state.maps [| cp |] ;
  len
;;

(* Miscellaneous *)

let set_reducable_positions f lst c =
  let rec add_elements s = function
    | [] -> s
    | head :: t ->
      add_elements (PosSet.add head s) t
  in
  if not (Function.is_standard f) then () else
  let g = Function.std_to_int f in
  let newset = add_elements PosSet.empty lst in
  update c (FuncToPosses.add g newset (get c))
;;

let get_reducable_positions f c =
  if not (Function.is_standard f) then [] else
  let set = FuncToPosses.find (Function.std_to_int f) (get c) in
  let lst = PosSet.fold (fun i lst -> i :: lst) set [] in
  List.sort compare lst
;;

let is_reducable_at f pos c =
  if not (Function.is_standard f) then false else
  let set = FuncToPosses.find (Function.std_to_int f) (get c) in
  PosSet.mem pos set
;;

let hash = id;;

(* Printers *)

let fprintf fmt c = FuncToPosses.fprintf fmt (get c);;

let to_string = Format.flush_str_formatter <.> fprintf Format.str_formatter;;

