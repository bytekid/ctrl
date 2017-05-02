(* Copyright 2015 Cynthia Kop
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

(*** TYPES *******************************************************************)

type possible_results = Smtresults.t = SAT | UNSAT | UNKNOWN;;

(*** FUNCTIONS ***************************************************************)

let string_to_value a str = Term.read_value str a "inputted answer";;

let get_input question =
  Printf.printf "%s%!" question ;
  let answer = input_line stdin in
  if answer = "ABORT" then failwith "User requested abort."
  else answer
;;

let rec keep_asking question oneof =
  let answer = get_input question in
  if List.mem answer oneof then answer
  else keep_asking question oneof
;;

let split_conjunction a term =
  let rec recurse andsymb s =
    match s with
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
        if f = andsymb then List.flat_map (recurse andsymb) args
        else [s]
      | _ -> [s]
  in
  try recurse (Alphabet.get_and_symbol a) term
  with Not_found -> [term]
;;

let calculate term printer a =
  let txt = get_input ("Calculate " ^ (printer term) ^ ":  ") in
  string_to_value a txt
;;

let trivial_test printer term =
  let question = "Is " ^ (printer term) ^ " true? [y/n]  " in
  let answer = keep_asking question ["y";"n"] in
  answer = "y"
;;

let get_value sort a =
  let q = "Please supply a value of sort " ^ (Sort.to_string sort) ^ ":  " in
  string_to_value a (get_input q)
;;

let satisfiability formulas printer a =
  let vars = List.unique (List.flat_map Term.vars formulas) in
  let forms = List.flat_map (split_conjunction a) formulas in
  if vars = [] then (
    let gamma = Substitution.empty in
    if List.for_all (trivial_test printer) forms then (SAT, gamma)
    else (UNSAT, gamma)
  ) else (
    Printf.printf "Satisfiability for [%s] requested of the following formulas:\n  %s\n"
      (List.implode Variable.find_name ", " vars)
      (List.implode printer "\n  " forms) ;
    let question = "Are they satisfiable? [y/n/?]  " in
    let answer = keep_asking question ["y"; "n"; "?"] in
    let subst = Substitution.empty in
    if answer = "n" then (UNSAT, subst) else
    if answer = "?" then (UNKNOWN, subst) else
    let get_substitution sofar x =
      let name = Variable.find_name x in
      let answer = get_input ("Value for " ^ name ^ ":  ") in
      let value = string_to_value a answer in
      Substitution.add x value sofar
    in
    let gamma = List.fold_left get_substitution subst vars in
    (SAT, gamma)
  )
;;

let validity formulas printer a =
  let forms = List.flat_map (split_conjunction a) formulas in
  Printf.printf "Validity requested of the following formulas:\n  %s\n"
    (List.implode printer "\n  " forms) ;
  let question = "Are they all valid? [y/n/?]  " in
  let answer = keep_asking question ["y"; "n"; "?"] in
  if answer = "y" then SAT
  else if answer = "n" then UNSAT
  else UNKNOWN
;;

