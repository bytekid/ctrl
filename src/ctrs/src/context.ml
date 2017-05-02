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

(*** MODULES *****************************************************************)
module Fun = Function;;
module Pos = Position;;
module Var = Variable;;

(*** OPENS *******************************************************************)
open Prelude;;
open Util;;

(*** TYPES *******************************************************************)
type func = Function.t;;
type term = Term.t = Var of Var.t | Fun of Fun.t * term list |
            InstanceFun of Fun.t * term list * Sortdeclaration.t |
            Forall of Variable.t * term | Exists of Variable.t * term;;
type t = Hole | More of Fun.t * term list * t * term list;;
 
(*** FUNCTIONS ***************************************************************)
 
(* Miscellaneous *)

let hash = Hashtbl.hash;;
 
let rec hole_pos = function
  | Hole -> Pos.root
  | More (_,us,c,_) -> Pos.add_first (List.length us) (hole_pos c)
;;
 
let rec pos = function
  | Hole -> [Pos.root]
  | More (f,us,c,vs) ->
    let addi i = List.map (Pos.add_first i) in
    let f i ps ti = List.rev_append (addi i (Term.pos ti)) ps in
    let term_pos l = List.foldli (fun i -> f (i + l)) in
    let l = List.length us in
    term_pos 0 (term_pos (l + 1) (addi l (pos c)) vs) us
;;
 
(* Constructors and Destructors *)

let rec apply t = function
  | Hole -> t
  | More (f,us,c,vs) -> Fun (f,us @ apply t c :: vs)
;;
 
let rec compose c = function
  | Hole -> c
  | More (f,us,d,vs) -> More (f,us,compose c d,vs)
;;
 
let rec of_term p t = 
  if Pos.is_root p then Hole else (
    let (i,q) = Pos.split_first p in
    match t with
      | Var _ -> failwith "illegal position"
      | Forall _ | Exists _ ->
        failwith "Cannot make a context out of a quantified term."
      | Fun (f,ts) | InstanceFun (f,ts,_) ->
        try
          if List.length ts <= i then failwith "illegal position";
          let (us,vs) = List.split_at i ts in
          More (f,us,of_term q (List.hd vs),List.tl vs)
        with Failure "tl" -> failwith "illegal position")
;;
 
let rec subcontext p c =
  if Pos.is_root p then c else (
    let (i,q) = Pos.split_first p in
    match c with
      | Hole -> failwith "illegal position"; 
      | More (f,us,c,_) ->
        if i <> List.length us then failwith "illegal position"
        else subcontext q c)
;;
 
(* Properties *)

let is_empty = function Hole -> true | _ -> false;;

let rec is_mu_context c mu =
  match c with
    | Hole -> true
    | More (f,start,sub,_) ->
      let pos = List.length start in
      if Csmapping.is_reducable_at f pos mu
      then is_mu_context sub mu
      else false
;;
 
(* Compare Functions *)

let compare = compare;;
let equal c d = compare c d = 0;;
 
(* Printers *)

let rec to_string_help debug = function
  | Hole -> "[]"
  | More (f, us, c, vs) ->
    let doterm = if debug then Term.to_string else Term.to_stringm in
    let lus = List.length us and lvs = List.length vs in
    let sub = to_string_help debug c in
    let pus = if lus = 0 then "" else (List.to_string doterm "," us) ^ "," in
    let pvs = if lvs = 0 then "" else "," ^ (List.to_string doterm "," vs) in
    (Fun.to_string f) ^ "(" ^ pus ^ sub ^ pvs ^ ")"
;;

let to_string = to_string_help true;;
let to_stringm = to_string_help false;;
let fprintf fmt c = Format.fprintf fmt "%s" (to_string c)
let fprintfm fmt c = Format.fprintf fmt "%s" (to_stringm c)

(*let rec fprintf fmt = function
  | Hole -> F.fprintf fmt "@[[]@]"
  | More (f,us,c,vs) ->
    let lus = List.length us and lvs = List.length vs in
    let fs =
      if lus = 0 && lvs = 0 then format_of_string "@[%a(%a%a%a)@]"
      else if lus = 0 then format_of_string "@[%a(%a%a,%a)@]"
      else if lvs = 0 then format_of_string "@[%a(%a,%a%a)@]"
      else format_of_string "@[%a(%a,%a,%a)@]"
    in
    F.fprintf fmt fs Fun.fprintf f (List.fprintf Term.fprintf ",") us
      fprintf c (List.fprintf Term.fprintf ",") vs
;;

let fprintfm a e fmt t =
  let rec print fmt = function
    | Hole -> F.fprintf fmt "@[[]@]"
    | More (f,us,c,vs) ->
      let lus = List.length us and lvs = List.length vs in
      let fs =
        if lus = 0 && lvs = 0 then format_of_string "@[%a(%a%a%a)@]"
        else if lus = 0 then format_of_string "@[%a(%a%a,%a)@]"
        else if lvs = 0 then format_of_string "@[%a(%a,%a%a)@]"
        else format_of_string "@[%a(%a,%a,%a)@]"
      in
      let funprint fmt f =
        Alphabet.fprintf_fun fmt f (Environment.var_names e) a
      in
      F.fprintf fmt fs funprint f (List.fprintf (Term.fprintfm a e) ",") us
        fprintf c (List.fprintf (Term.fprintfm a e) ",") vs
  in
  print fmt t
;;

let to_string = Format.flush_str_formatter <.> fprintf Format.str_formatter;;
let to_stringm a e = Format.flush_str_formatter <.> (fprintfm a e Format.str_formatter);;*)

