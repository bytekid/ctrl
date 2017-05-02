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

(*** OPENS ********************************************************************)
open Prelude;;

(*** EXCEPTIONS **************************************************************)
exception Fail;;

(*** MODULES *****************************************************************)
module P = Pervasives;;

(*** TYPES ********************************************************************)
type ('a,'b) t = ('a,'b) Hashtbl.t;;

(*** FUNCTIONS ****************************************************************)
(* Iterators *)
let fold = Hashtbl.fold;;
let foldi f h d = snd (Hashtbl.fold (fun k e (i,x) -> (i + 1,f i k e x)) h (0,d));;
let iter = Hashtbl.iter;;
let iteri f = const () <.> flip (Hashtbl.fold (fun k e i -> f i k e; i + 1)) 0;;
let map f h = iter (fun k -> Hashtbl.replace h k <.> f) h; h;;
let mapi f h = iter (fun k -> Hashtbl.replace h k <.> f k) h; h;;

(* Search Functions *)
let find = Hashtbl.find;;
let find_all = Hashtbl.find_all;;
let find_ k h = Hashtbl.find h k;;
let find_all_ k h = Hashtbl.find_all h k;;
(*
exception Found of 'a * 'b;;
let search p m =
 try
  iter (fun k e -> if p k e then raise (Found (k,e)) else ()) m;
   raise Not_found
  with Found (k,e) -> (k,e)
;;
 *)

(* Scan Functions *)
let for_all p m =
 let p k e = if p k e then () else raise Fail in
 try iter p m; true with Fail -> false
;;

let exists p = not <.> for_all (fun k -> not <.> p k);;
let mem = Hashtbl.mem;;
let mem_ k h = Hashtbl.mem h k;;

(* Constructors *)
let add = Hashtbl.add;;
let add_ k e h = if mem_ k h then h else (Hashtbl.add h k e; h);;
let clear = Hashtbl.clear;;
let clear_ h = Hashtbl.clear h; h;;
let copy = Hashtbl.copy;;
let create : int -> ('a, 'b) t = Hashtbl.create;;
let empty () = create 0;;

let of_list xs =
 Listx.foldl (flip (Pair.uncurry add_)) (create (List.length xs)) xs
;;

let remove = Hashtbl.remove;;
let replace = Hashtbl.replace;;
let remove_ k h = Hashtbl.remove h k; h;;
let replace_ k e h = Hashtbl.replace h k e; h;;
let singleton k e = add_ k e (create 2);;
let to_list h = fold (curry Listx.cons) h [];;

(* Compare Functions *)
let compare ?(compare_d=P.compare) ?(compare_r=P.compare) h h' =
 let compare xs ys = match (xs,ys) with
   | [], [] -> 0
   | [], _ -> ~-1
   | _, [] -> 1
   | (k,e) :: xs, (k',e') :: ys ->
     let c = compare_d k k' in
     if c = 0 then let c = compare_r e e' in if c = 0 then compare xs ys else c else c
     in
  compare (to_list h) (to_list h')
;;

let equal ?(compare_d=P.compare) ?(compare_r=P.compare) h h' =
 compare ~compare_d:compare_d ~compare_r:compare_r h h' = 0;;

(* Miscallenous *)
let domain ?(compare_d=P.compare) h =
 Listx.unique ~c:compare_d (fold (drop Listx.cons) h []);;
let range ?(compare_r=P.compare) h =
 Listx.unique ~c:compare_r (fold (const Listx.cons) h []);;
let length = Hashtbl.length;;
let size = length;;

(* Properties *)
let is_empty h = size h = 0;;

(* Printers *)
let fprintf ?(delim = format_of_string "@ ->@ ") fprintf_k fprintf_d fmt =
 let fprintf fmt h =
  iteri (fun i k d ->
   Format.fprintf fmt (if i > 0 then format_of_string "@\n@[%a%a%a@]" else
    format_of_string "@[%a%a%a@]")
   fprintf_k k Format.fprintf delim fprintf_d d) h
 in Format.fprintf fmt "@[%a@]" fprintf
;;

let to_string ?(delim = format_of_string "@ ->@ ") fprintf_k fprintf_d =
 Format.flush_str_formatter <.>
   fprintf ~delim:delim fprintf_k fprintf_d Format.str_formatter;;

let hash = Hashtbl.hash;;
let hash_param = Hashtbl.hash_param;;
