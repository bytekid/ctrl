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

(*** OPENS *******************************************************************)
open Prelude;;
open Util;;

(*** MODULES *****************************************************************)
module Names = Index.Isomorphic (Int) (String);;
module Sorts = Index.Make (Int) (Sort);;

(*** TYPES *******************************************************************)
type sort = Sort.t
type environment = {names : Names.t;
                    sorts : Sorts.t };; 
type t = int;;

(** STATE VARIABLES **********************************************************)
type internal = { mutable envs : environment array };;
let state = { envs = [| |] };;

(*** FUNCTIONS ***************************************************************)

(* General Accessing Functions *)

let get e = state.envs.(e);;
let names e = (get e).names;;
let sorts e = (get e).sorts;;
let update e env = state.envs.(e) <- env;;
let update_names upd x n e = update e {(get e) with names = upd x n (names e)};;
let update_sorts upd x d e = update e {(get e) with sorts = upd x d (sorts e)};;

(* Search Functions *)

let find_var x e = Variable.create (Names.find_key x (names e)) x;;
let find_sort x e = Sorts.find (Variable.to_int x) (sorts e);;
let var_names e = Names.elements (names e);;

let vars e =
  let lst = Names.to_list (names e) in
  let makevar (index, name) = Variable.create index name in
  List.map makevar lst
;;

(* Scan Functions *)

let is_defined x e = Names.mem_key (Variable.to_int x) (names e);;
let has_sort x e = Sorts.mem (Variable.to_int x) (sorts e);;
let mem_var_name x e = Names.mem_elt x (names e);;

let is_sort x d e =
  try
    let sort = find_sort x e in
    Sort.equal sort d
  with Not_found -> false
;;

(** {Constructors} *)

let empty n =
  let new_env = { names = Names.empty n; sorts = Sorts.empty } in
  let len = Array.length state.envs in
  state.envs <- Array.append state.envs [| new_env |] ;
  len
;;

let dummy () =
  if Array.length state.envs <> 0 then 0 else empty 0
;;

(* Updating Symbols *)

let add_sort = update_sorts Sorts.add <.> Variable.to_int;;
let replace_sort = update_sorts Sorts.replace <.> Variable.to_int;;

(* Fresh Symbols *)

let generate_var_name bound sortname funnames env =
  let isnew name = (not (List.mem name funnames)) &&
                   (not (mem_var_name name env)) in
  let letter =
    if sortname = "" then "x"
    else String.sub sortname 0 1
  in
  let start = if bound then "_" ^ letter else letter in
  let rec attempt i =
    let n = start ^ (string_of_int i) in
    if isnew n then n else attempt (i+1)
  in
  attempt 0
;;

let create_unsorted_var n e =
  try find_var n e
  with Not_found ->
    let (i, newnames) = Names.fresh (names e) in
    update e {(get e) with names = Names.add i n newnames} ;
    Variable.create i n
;;

let create_var n d e =
  let x = create_unsorted_var n e in
  if (has_sort x e && (not (is_sort x d e)))
  then failwith "incorrect sort"
  else ( add_sort x d e ; x )
;;

let create_sorted_var d l e =
  let name = generate_var_name false (Sort.to_string d) l e in
  create_var name d e
;;

let create_fresh_var l e =
  let name = generate_var_name false "" l e in
  create_unsorted_var name e
;;

let create_var_like x xenv l e =
  let origname = Variable.find_name x in
  let reusename = (not (List.mem origname l)) &&
                  (not (mem_var_name origname e)) in
  try
    let sort = find_sort x xenv in
    if reusename then create_var origname sort e
    else create_sorted_var sort l e
  with Not_found ->
    if reusename then create_unsorted_var origname e
    else create_fresh_var l e
;;

let add_unsorted_var = update_names Names.add <.> Variable.to_int;;
let add_var x n d e = add_unsorted_var x n e; add_sort x d e;;
let replace_unsorted_var = update_names Names.replace <.> Variable.to_int;;
let replace_var x n d e = replace_unsorted_var x n e; replace_sort x d e;;

let register to_int mem add p x e =
  let rec register i =
    let n = Format.sprintf "%s%i" p i in
    if mem n e then register (i + 1)
    else ( add x n e ; n )
  in
  register (to_int x)
;;

(* Miscellaneous *)

let copy e =
  let cp = { names = Names.copy (names e); sorts = Sorts.copy (sorts e) } in
  let len = Array.length state.envs in
  state.envs <- Array.append state.envs [| cp |] ;
  len
;;

let hash = id;;

let reset e =
  let n = Names.clear (names e) in
  let s = Sorts.clear (sorts e) in
  update e { names = n; sorts = s }
;;

let drop e =
  let len = Array.length state.envs in
  if e + 1 = len then state.envs <- Array.sub state.envs 0 e
  else reset e
;;

(* Printers *)

let fprintf fmt e =
  Format.fprintf fmt
    "@[Environment:@[<1>@\n%a@]@\nSorts:@[<1>@\n%a@]@]@\n"
    Names.fprintf (names e)
    Sorts.fprintf (sorts e)
;;

let to_string = Format.flush_str_formatter <.> fprintf Format.str_formatter;;

