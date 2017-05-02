(* Copyright 2014, 2015 Cynthia Kop
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

open Util;;
open Ctrs;;
open Io;;

(*** TYPES *******************************************************************)

type strategy = FULL | INNERMOST;;
type t = Alphabet.t * Environment.t * Dpgraph.t * Rule.t list * strategy;;
  (* (P,R,strategy) *)

(*** MODULES *****************************************************************)

(*** FUNCTIONS ***************************************************************)

let full_problem a e p r = (a, e, Dpgraph.create a e p r, r, FULL);;
let innermost_problem a e p r = (a, e, Dpgraph.create a e p r, r, INNERMOST);;

let update_graph (a,e,_,r,i) g = (a,e,g,r,i);;

let get_dps (_,_,g,_,_) = Dpgraph.get_dps g;;
let get_rules (_,_,_,r,_) = r;;
let get_innermost (_,_,_,_,s) = s = INNERMOST;;
let get_alphabet (a,_,_,_,_) = a;;
let get_environment (_,e,_,_,_) = e;;
let get_graph (_,_,g,_,_) = g;;

let set_dps p (a,e,g,r,s) = (a, e, Dpgraph.subgraph g p, r, s);;
let set_rules rr (a,e,p,r,s) = (a,e,p,rr,s);;

let graph_proc verbose (a,e,g,r,s) =
  let sccs = Dpgraph.get_sccs g in
  let makeprob scc = (a,e,scc,r,s) in
  let return_scc_list sccs =
    let verbosetext =
      "The dependency graph for this problem is:\n" ^
      (Dpgraph.tostringm g) ^ "\n" ^
      "We have the following SCCs.\n  " ^
      (List.implode Dpgraph.to_string_raw "\n  " sccs) ^ "\n"
    in
    if verbose then Printf.printf "%s" verbosetext ;
    (List.map makeprob sccs, verbosetext)
  in
  match sccs with
    | [scc] ->
      if Dpgraph.size_nodes g = Dpgraph.size_nodes scc then None
      else Some (return_scc_list sccs)
    | _ -> Some (return_scc_list sccs)
;;

let graph_followers (_,_,g,_,_) = Dpgraph.get_relations g;;

let tostring (a, e, g, r, s) =
  let rec print_list = function
    | [] -> ""
    | hd :: tl ->
      "  " ^ (Printer.to_string_rule hd) ^ "\n" ^ (print_list tl)
  in
  "\nDP problem for " ^
  (if s = FULL then "full" else "innermost") ^
  " termination.\nP =\n" ^
  (print_list (Dpgraph.get_dps g)) ^
  "R = \n" ^ (print_list r) ^ "\n"
;;

let fprintfm channel problem =
  Printf.fprintf channel "%s" (tostring problem)
;;

let printfm prob = fprintfm stdout prob;;

