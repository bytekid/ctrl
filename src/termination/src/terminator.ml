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

open Ctrs;;

(*** TYPES *******************************************************************)

type possible_results = TERMINATING | NONTERMINATING | UNKNOWN;;

(*** MODULES *****************************************************************)

(*** FUNCTIONS ***************************************************************)

let termination_procs = [Dpproblem.graph_proc;
                         (*Chainer.gcnf_process;*)
                         Valuecriterion.basic_process;
                         Valuecriterion.reverse_process;
                         Subtermcriterion.process;
                         Valuecriterion.extended_process];;

let nontermination_procs = [(Dpproblem.graph_proc, TERMINATING);
                            (Subtermcriterion.process, TERMINATING);
                            (Loop.process, NONTERMINATING)];;

let check_dps framework original_rules verbose =
  let rec try_p lst (problem : Dpproblem.t) =
    match lst with
      | [] -> None
      | processor :: rest -> (
        match processor verbose problem with
          | Some (x, y) -> Some (x, y)
          | None -> try_p rest problem
    )
  in
  let rec repeat f dpf txt =
    if Dpframework.solved dpf then (TERMINATING, txt)
    else
      let (problem, dp) = Dpframework.pop dpf in
      let probdesc = Dpproblem.tostring problem in
      if verbose then Printf.printf "%s" probdesc ;
      let txt = txt ^ probdesc in
      match f problem with
        | None ->
          if verbose then Printf.printf "We cannot handle this DP problem.\n" ;
          (UNKNOWN, txt)
        | Some (result, expl) ->
          repeat f (Dpframework.push_all dp result) (txt ^ expl)
  in
  let init_innermost framework =
    if Dpframework.solved framework then ("", framework) else
    let (problem, framework) = Dpframework.pop framework in
    match Chainer.innermost_fix verbose problem with
      | None -> ("", Dpframework.push framework problem)
      | Some (result, expl) ->
        (expl, Dpframework.push_all framework result)
  in
  let (txt, framework) = init_innermost framework in
  repeat (try_p termination_procs) framework txt
;;

let check_extended verbose trs rules =
  let rules_backup = Trs.get_rules trs in
  List.iter (fun (rule, env) -> Trs.add rule env trs) rules ;
  let framework = Dpframework.generate trs true in
  Trs.set_rules rules_backup trs ;
  fst (check_dps framework (List.append (Trs.get_rules trs) rules) verbose)
;;

let check verbose full trs =
  let framework = Dpframework.generate trs full in
  check_dps framework (Trs.get_rules trs) verbose
;;


let check_dps_nonterm framework original_rules verbose =
  let rec try_p lst (problem : Dpproblem.t) =
    match lst with
      | [] -> None
      | (processor, a) :: rest -> (
        match processor verbose problem with
          | Some (x, y) -> Some (x, y, a)
          | None -> try_p rest problem
    )
  in
  let rec repeat f dpf txt answer =
    if Dpframework.solved dpf then (answer, txt)
    else
      let (problem, dp) = Dpframework.pop dpf in
      let probdesc = Dpproblem.tostring problem in
      if verbose then Printf.printf "%s%!" probdesc ;
      match f problem with
        | None -> repeat f dp txt answer
        | Some (result, expl, a) ->
          let a = if result = [] && a = NONTERMINATING then a else answer in
          repeat f (Dpframework.push_all dp result) (txt ^ probdesc ^ expl) a
  in
  if Dpframework.solved framework then (TERMINATING, "")
  else repeat (try_p nontermination_procs) framework "" UNKNOWN
;;

let check_nontermination verbose trs =
  let framework = Dpframework.generate trs true in
  check_dps_nonterm framework (Trs.get_rules trs) verbose
;;

