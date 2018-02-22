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
open Ctrs;;
open Util;;
open Smt;;

(*** MODULES ******************************************************************)
module L = List
module P = Io.Printer
module Alph = Alphabet
module T = Term
module Rewriter = Rewriting.Rewriter

(*** TYPES ********************************************************************)
type t_unfold = Forward | Backward

(* context *)
type t = {
  alph: Alph.t;
  env: Environment.t
}

type prec = Function.t list

(*** GLOBALS ******************************************************************)
let check_time = ref 0.;;

(*** FUNCTIONS ****************************************************************)

(* Create a context record. *)
let mk_ctxt a e = {
  alph = a;
  env = e
}

let get_symbol getter name alphabet =
  try getter alphabet
  with Not_found -> failwith ("Cannot rewrite constrained terms " ^
    "when the " ^ name ^ " symbol is not set.")
;;

let and_symbol = get_symbol Alphabet.get_and_symbol "conjunction";;
let or_symbol = get_symbol Alphabet.get_or_symbol "disjunction";;
let eq_symbol = get_symbol Alphabet.get_equal_symbol "equality";;
let not_symbol = get_symbol Alphabet.get_not_symbol "negation";;
let top_symbol = get_symbol Alphabet.get_top_symbol "top (truth)";;
let bot_symbol = get_symbol Alphabet.get_bot_symbol "bottom (falsehood)";;
let imply_symbol = get_symbol Alphabet.get_imply_symbol "implication";;

let create fgetter args a e = T.make_function a e (fgetter a) args;;
let create_and = create and_symbol;;
let create_or = create or_symbol;;
let create_imply s t = create imply_symbol [s;t];;


(* Returns the SMT-solver we will use (just the default) *)
let solver () = Rewriter.smt_solver (Rewriter.get_current ());;

let create_gt s t alph env =
  let ss,ts = T.get_sort alph env s, T.get_sort alph env t in
  let bot = create bot_symbol [] alph env in
  if ss <> ts then bot
  else
    match Alphabet.get_wellfounded ss alph with
      [] -> bot
    | f :: _ -> T.make_function alph env f [s;t]
;;

let create_ge s t alph env =
  let gt = create_gt s t alph env in
  let eq = create eq_symbol [s;t] alph env in
  create_or [eq; gt] alph env
;;


(* preclist contains syms in decreasing order *)
let orient_rule (alph, env) preclist (rl, rl_env) =
  let logical t = T.check_logical_term alph t = None in
  let lsym f = Alphabet.find_symbol_kind f alph <> Alphabet.Terms in
  let l,r,phis = Rule.lhs rl, Rule.rhs rl, Rule.constraints rl in
  let phi = create_and phis alph env in
  let pmap = List.mapi (fun i f -> (f,i)) preclist in
  let prec f g =
    try List.assoc f pmap < List.assoc g pmap with _ -> 
      failwith ("precedence error " )
  in (* f > g *)
  let vars_in_phi s t =
    List.is_subset (T.vars s @ (T.vars t)) (T.vars phi)
  in
  let valid phi = Solver.valid [phi] (solver ()) env in

  let rec gt (s,t) =
    let imp _ = create_imply phi (create_gt s t alph env ) alph env in
    if logical s && logical t && vars_in_phi s t && valid (imp ()) then true
    else match (s,t) with
      | T.Var _, _ -> false
      | _, T.Var x -> List.mem x (T.vars s @ (T.vars phi))
      | T.Fun (f,ss), T.Fun (g,ts) ->
        if lsym f then false
        else if List.exists (fun si -> ge (si,t)) ss then true
        else if ((lsym g || prec f g) && List.for_all (fun tj -> gt (s,tj)) ts)
          then true
        else (f = g && lex (List.map2 Pair.make ss ts))
      (* (f = g && List.fold_left2 (fun b -> si tj -> ge (si,tj)) ss ts
                    && List.exists2 (fun si tj -> gt (si,tj)) ss ts)
      *)
      | _ -> false
         
  and ge (s,t) = 
    let imp _ = create_imply phi (create_ge s t alph env) alph env in
    if logical s && logical t && vars_in_phi s t && valid (imp ()) then true
    else if gt (s,t) then true
    else match (s,t) with
      | T.Var x, T.Var y -> x = y
      | T.Fun (f,ss), T.Fun (g,ts) when f = g && not (lsym f) ->
        List.for_all2 (fun si tj -> ge (si,tj)) ss ts
      | _ -> false
  and lex = function
     [] -> false
   | sti :: ssts -> gt sti || (ge sti && lex ssts)
  in gt (l,r)
;;

(* Main functionality *)
let orient prec trs =
  (*Format.printf "start CRPO\n%!";
  List.iter (fun f -> Format.printf "> %s " (Function.find_name f)) prec;
  Format.printf "\n%!";*)
  try
  let rules = Trs.get_rules trs in
  let alph = Trs.get_alphabet trs in
  let env = Trs.get_main_environment trs in
  let r = List.for_all (orient_rule (alph, env) prec) rules in
  r
  with Not_found ->
  let t = Printexc.get_callstack 20 |> Printexc.raw_backtrace_to_string in
  Format.printf "%s\n%!" t; failwith "Crpo.orient: Not_found"
;;

