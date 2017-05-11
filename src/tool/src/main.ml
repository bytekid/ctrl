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

open Ctrs;;
open Smt;;
open Rewriting;;
open Io;;
open Confluence;;
open Termination;;
open Inductive;;

let initialise _ =
  let trs = Trs.empty () in
  Trs.set_current trs ;
  let smt = Solver.create () in
  let rewriter = Rewriter.create smt in
  Rewriter.set_current rewriter
;;

let txt_answer = function
  | Terminator.TERMINATING -> "YES"
  | Terminator.NONTERMINATING -> "NO"
  | Terminator.UNKNOWN -> "MAYBE"
;;

let run _ =
  let filename = ref "" in
  let options = Arg.align 
    [("--debug", Arg.Unit (fun _ -> Util.set_debugging true),
      " Activate debugging output")] in
  Arg.parse options (fun x -> filename := x) "Usage: CTRL <options> filename\n";

  initialise () ;
  let (query, simp) = Reader.read_file !filename in
  ( match simp with
      | None -> ()
      | Some symbols ->
        let canchange f = not (List.mem f symbols) in
        Cleaner.simplify_trs (Trs.get_current ()) canchange
  ) ;
  match query with
    | Reader.NoQuery ->
      Printer.print_alphabet Alphabet.Terms ;
      Printer.print_newline () ;
      Printer.print_current_rules () ;
      Printer.flush ()
    | Reader.NormalForm t ->
      let reduction = Rewriter.reduce_to_normal t in
      Printer.print_term_reduction reduction ;
      Printer.flush ()
    | Reader.ConstrainedNormalForm (s, phi) ->
      let reduction = Constrainedrewriter.reduce_to_normal (s, phi) false true in
      Printer.print_constrained_reduction reduction ;
      Printer.flush ()
    | Reader.Termination full ->
      let verbose = Util.query_debugging () in
      let trs = Trs.get_current () in
      let (ans, comments) = Terminator.check verbose full trs in
      Printf.printf "%s\n%s" (txt_answer ans) (if verbose then "" else comments)
    | Reader.Nontermination ->
      let verbose = Util.query_debugging () in
      let trs = Trs.get_current () in
      let (ans, comments) = Terminator.check_nontermination verbose trs in
      Printf.printf "%s\n%s" (txt_answer ans) (if verbose then "" else comments)
    | Reader.Confluence ->
      if Confluencechecker.weak_orthogonal (Trs.get_current ()) then
        Printf.printf "YES\n"
      else Printf.printf "MAYBE\n"
    | Reader.Equivalence lst -> (
      try match Theoremprover.run (Trs.get_current ()) lst with
        | (Theoremprover.YES, explain) -> Printf.printf "YES\n" ; explain ()
        | (Theoremprover.NO, explain) -> Printf.printf "NO\n" ; explain ()
        | (Theoremprover.MAYBE, explain) -> Printf.printf "MAYBE\n" ; explain ()
      with Failure x ->
        Printf.printf "MAYBE\n%s\n" x
      )
    | Reader.AssistEquivalence lst -> (
      match Manualprover.run (Trs.get_current ()) lst with
        | Manualprover.YES -> Printf.printf "YES\n"
        | Manualprover.NO -> Printf.printf "NO\n"
        | Manualprover.MAYBE -> Printf.printf "MAYBE\n"
      )
    | Reader.SimplifiedLctrs (lst, filestart) ->
      let trs = Trs.get_current () in
      let canchange f = not (List.mem f lst) in
      let output = Cleaner.simplify trs canchange Printer.to_string_term in
      Printf.printf "%s%s\n" filestart output
    | Reader.Smt lst ->
      let trs = Trs.get_current () in
      let env = Trs.get_main_environment trs in
      let smt = Rewriter.smt_solver (Rewriter.get_current ()) in
      let psub var value sofar = sofar ^ (Variable.to_string var) ^ " -> " ^
                                  (Term.to_string value) ^ "\n" in
      let print_substitution gamma = Substitution.fold psub gamma "" in
      match Solver.satisfiable_formulas lst smt env with
        | (Smtresults.SAT, gamma) ->
          Printf.printf "SAT\n%s" (print_substitution gamma)
        | (Smtresults.UNSAT, _) -> Printf.printf "UNSAT\n"
        | (Smtresults.UNKNOWN, _) -> Printf.printf "UNKNOWN\n"
;;

