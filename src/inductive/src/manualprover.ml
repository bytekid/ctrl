(* Copyright 2014, 2015, 2016 Cynthia Kop
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
open Io;;

(*** TYPES *******************************************************************)

type answer = YES | NO | MAYBE;;

(*** MODULES *****************************************************************)


(*** FUNCTIONS ***************************************************************)

(*******************************************************************)
(* the following functions handle conversions                      *)
(*******************************************************************)

(* parses the given string representation into a position *)
let from_string_position txt =
  let pos = (
    if txt = "" then txt
    else if String.get txt 0 <> '[' then txt
    else if String.get txt ((String.length txt) - 1) <> ']' then txt
    else String.sub txt 1 ((String.length txt) - 1)
  ) in
  try
    let parts = String.split ~d:"\\." pos in
    let iparts = List.map int_of_string parts in
    let lower = List.map (fun i -> i - 1) iparts in
    Position.of_list lower
  with _ -> failwith ("Illegal position: " ^ pos ^
    " (should be a list of positive integers, separated by periods)")
;;

(*******************************************************************)
(* the following functions print information to the user           *)
(*******************************************************************)

(** Prints the normal rules, and extra rules, with numbers *)
let print_all_rules extra_rules =
  let makeid pre i rule = (pre ^ (string_of_int (i+1)), rule) in
  let (_, _, rules) = Proverbase.get_data () in
  let arules = List.mapi (makeid "") rules in
  let brules = List.mapi (makeid "X") extra_rules in
  let allrules = List.append arules brules in
  let print_rule (index, rule) =
    [index ^ ") " ;
     Printer.to_string_term (Rule.lhs rule) ;
     " -> " ;
     Printer.to_string_term (Rule.rhs rule) ;
     Printer.to_string_constraints (Rule.constraints rule)
    ]
  in
  Printer.print_list print_rule
    [Printer.R;Printer.R;Printer.C;Printer.L;Printer.L] allrules ;
  Printer.flush ()
;;

(* prints the given goal (an equation) *)
let print_goal (l, r, phi) =
  let (alf, env, _) = Proverbase.get_data () in
  Printf.printf "GOAL: %s = %s [%s]\n"
    ( Printer.to_string_term l )
    ( Printer.to_string_term r )
    ( Printer.to_string_term phi )
;;

(*******************************************************************)
(* the following functions are helpers for the "auto" commands     *)
(*******************************************************************)

(**
 * This returns either None, if the given goal cannot be simplified
 * at all, or Some (newgoal, usedruleid, usedposition, swapped) if it
 * can be simplified ("swapped" is a boolean indicating that the goal
 * has been swapped before this simplification was done.
 *)
let best_simplification goal extra_rules =
  let positions = Proverbase.goal_positions goal in
  let allrules = Proverbase.get_all_rules extra_rules in
  let swappedgoal = Proverbase.try_swap goal in
  let rec try_rule rule = function
    | [] -> None
    | (swapped, (pos, _)) :: tail -> (
      let g = ( if swapped then swappedgoal else goal ) in
      match Proverbase.try_simplify g rule pos with
        | None -> try_rule rule tail
        | Some eq -> Some (eq, swapped, pos)
      )
  in
  let rec try_all_rules = function
    | [] -> None
    | (ruleid, rule) :: tail -> (
      match try_rule rule positions with
        | None -> try_all_rules tail
        | Some (eq, swapped, pos) -> Some (eq, swapped, pos, ruleid)
      )
  in
  try_all_rules allrules
;;

(**
 * This returns all different complete normalisations of the given
 * goal, using an innermost reduction strategy.
 *)
let simp_normalise goal extra_rules =
  (* get all the rules that we might be applying, in the order that
     we're going to try them *)
  let allrules = Proverbase.get_all_rules extra_rules in
  (* we will keep track of the positions where we do reductions,
  including the relevant rule, in an easy-to-handle format; these
  functions convert that back to normal *)
  let fix_position lst =
    match List.rev lst with
      | [] -> failwith "Unexpectedly empty position!"
      | side :: tail ->
        (side = 1, Position.of_list tail)
  in
  let fix_entry (rulename, pos) = (rulename, fix_position pos) in
  (* returns all the innermost normal forms of (term, phi), together
  with a history of how that term is reached from the original *)
  let rec all_simplifications currentpos ((term, phi), origin) =
    match term with
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
        let combinations = simplify_list phi currentpos 0 origin args in
        let maketerm (newargs, psi, o) =
          (Term.replace_args term newargs, psi, o)
        in
        let newterms = List.map maketerm combinations in
        List.flat_map (top_simplifications currentpos) newterms
      | Term.Forall _ | Term.Exists _ ->
        failwith ("Encountered quantifier inside term part of the " ^
                  "constraint.  This is not currently supported.")
      | _ -> [(term, phi, origin)]
  (* returns the normal forms of (term, phi) assuming children are
  normalised *)
  and top_simplifications pos (term, phi, origin) =
    let cterm = (term, phi) in
    let try_rule (rulename, rule) =
      match Proverbase.try_simplify_main cterm rule Position.root with
        | None -> []
        | Some (newterm, newphi) ->
          [((newterm, newphi), (rulename, pos) :: origin)]
    in
    let simplifications = List.flat_map try_rule allrules in
    if simplifications = [] then [(term, phi, origin)]
    else List.flat_map (all_simplifications pos) simplifications
  (* returns a list containing all ways to normalise the argument
  list (so a list of lists) *)
  and simplify_list phi pos i origin = function
    | [] -> [([], phi, origin)]
    | head :: tail ->
      let headpos = i :: pos in
      let headsimps = all_simplifications headpos ((head, phi), origin) in
      let finish (term, constr, org) =
        let remainderpossibilities =
          simplify_list constr pos (i+1) org tail
        in
        let handle_remainder (restargs, psi, o) =
          (term :: restargs, psi, o)
        in
        List.map handle_remainder remainderpossibilities
      in
      List.flat_map finish headsimps
  in
  (* main functionality *)
  let cterm = Proverbase.make_equation_cterm goal in
  let cterm = Rewriting.Constrainedrewriter.calc_normalise cterm None None in
  let simplifications = all_simplifications [] (cterm, []) in
  let makegoal (term, phi, origin) =
    let goal = Proverbase.unmake_constrained_term (term, phi) in
    let proper_origin = List.rev (List.map fix_entry origin) in
    (goal, proper_origin)
  in
  List.map makegoal simplifications
;;

(** gives all simplified forms, each together with a string
description of how to get there; duplicates are removed *)
let simp_normalise_describe goal extra_rules =
  let simplifications = simp_normalise goal extra_rules in
  let samegoal a (b, _) = a = b in
  let rec uniquify = function
    | [] -> []
    | (goal, origin) :: tail ->
      if List.exists (samegoal goal) tail then uniquify tail
      else (goal, origin) :: uniquify tail
  in
  let uniques = uniquify simplifications in
  let rec describe_origin swapped = function
    | [] -> []
    | (rulename, (sw, pos)) :: tail ->
      let strpos = Proverbase.to_string_position pos in
      let print = "simplify " ^ rulename ^ " " ^ strpos in
      if sw && (not swapped) then
        "swap" :: print :: describe_origin sw tail
      else print :: describe_origin sw tail
  in
  let update (simplification, origin) =
    let lstorigin = describe_origin false origin in
    let lstorigin = (
      if List.mem "swap" lstorigin then lstorigin @ ["swap"]
      else lstorigin
    ) in
    (simplification, List.implode id "; " lstorigin)
  in
  List.map update uniques
;;

(** returns either (left) a way to get rid of the given goal
completely, or (right) a list of normal forms of the given goal,
combined with information on how to get there; if trivial
should be applied instead (to get multiple new goals), Left ""
is returned *)
let good_riddance goal extra_rules =
  let equations = Proverbase.try_trivial goal in
  if equations = [] then Left "trivial"
  else if List.tl equations <> [] then Left ""
  else (
    let base = (if equations = [goal] then "" else "trivial; ") in
    let simps eq =
      let lst = simp_normalise_describe eq extra_rules in
      let updateorigin (x, o) = (x, base ^ o) in
      List.map updateorigin lst
    in
    let simplifications = List.flat_map simps equations in
    let rec collect sofar = function
      | [] -> Right sofar
      | (equation, origin) :: tail ->
        match Proverbase.try_trivial equation with
          | [] -> Left (origin ^ "; trivial")
          | eq :: [] ->
            let newor =
              if eq = equation then origin
              else origin ^ "; trivial"
            in
            collect ((eq, newor) :: sofar) tail
          | _ -> collect ((equation, origin) :: sofar) tail
    in
    collect [] simplifications
  )
;;

(*******************************************************************)
(* the following functions handle the various commands             *)
(*******************************************************************)

(* handles the "abort" command, which quits the user-assisted
derivation attempt
*)
let user_abort goal extra_rules continue nope = MAYBE;;

(* handles the user giving an illegal command *)
let user_illegal name goal extra_rules continue nope =
  Printf.printf "Illegal action: %s\n\n" name ;
  nope ()
;;

(* handles the "rules" command, which prints all the rules *)
let user_rules goal extra_rules continue nope =
  print_all_rules extra_rules ;
  Printf.printf "\n" ;
  nope ()
;;

(* handles queries for the available commands *)
let user_commands cmds goal extra_rules continue nope =
  let commands = List.map fst cmds in
  Printf.printf "Available commands:\n%s\n\n" (String.itemize 80 commands) ;
  nope ()
;;

(* handles the "swap" command *)
let user_swap goal extra_rules continue nope =
  continue [Proverbase.try_swap goal] []
;;

(* handles the "deletion" command *)
let user_deletion goal extra_rules continue nope =
  match Proverbase.try_deletion goal with
    | Some true -> continue [] []
    | _ ->
      Printf.printf "Deletion is not applicable.\n\n" ;
      nope ()
;;

(* handles the "eq-deletion" command *)
let user_eqdeletion goal extra_rules continue nope =
  match Proverbase.try_eqdelete goal with
    | None ->
      Printf.printf "Eq-deletion is not applicable.\n\n" ;
      nope ()
    | Some newgoal -> continue [newgoal] []
;;

(* handles the "constructor" command *)
let user_constructor goal extra_rules continue nope =
  match Proverbase.try_constructor goal with
    | None ->
      Printf.printf "%s\n\n" ("Both sides must be rooted by the " ^
        "same constructor symbol to apply this clause.") ;
      nope ()
    | Some lst -> continue (List.map fst lst) []
;;

(* handles the "calculate" command *)
let user_calculate arguments goal extra_rules continue nope =
  let parse_args = function
    | [] -> Position.root
    | pos :: _ -> from_string_position pos
  in
  try
    let pos = parse_args arguments in
    match Proverbase.try_calculate goal pos with
      | None ->
        Printf.printf "Calculation cannot be applied at this position.\n\n" ;
        nope ()
      | Some newgoal -> continue [newgoal] []
  with Failure msg ->
    let msg = ( if msg = "nth" then "no such subterm!" else msg ) in
    Printf.printf "%s\n\n" msg ;
    nope ()
;;

(* handles the "simplify" command *)
let user_simplify arguments goal extra_rules continue nope =
  let (_, _, rules) = Proverbase.get_data () in
  let get_rule num =
    let (n, group) = (
      try
        let start = String.get num 0 in
        let rest = String.sub num 1 ((String.length num) - 1) in
        if start = 'X' then (int_of_string rest, extra_rules)
        else (int_of_string num, rules)
      with _ -> failwith ("Illegal rule index " ^ num ^ ": should " ^
        "be a positive integer or X followed by a positive integer.")
    ) in
    try List.nth group (n-1)
    with _ -> failwith ("Unused rule index: " ^ num)
  in
  let parse_args = function
    | rule :: [] -> (get_rule rule, Position.root)
    | rule :: pos :: [] -> (get_rule rule, from_string_position pos)
    | _ -> failwith ("Simplify requires one or two arguments: " ^
      "the number of the rule to be used, and possibly a " ^
      "position (this defaults to the top position, and should be " ^
      "a list of integers (0-based!) separated by periods.)")
  in
  try
    let (rule, pos) = parse_args arguments in
    match Proverbase.try_simplify goal rule pos with
      | None ->
        Printf.printf "The rule cannot be applied at this position.\n\n" ;
        nope ()
      | Some newgoal -> continue [newgoal] []
  with Failure msg ->
    let msg = ( if msg = "nth" then "no such subterm!" else msg ) in
    Printf.printf "%s\n\n" msg ;
    nope ()
;;

(* handles the "case" command *)
let user_case arguments goal extra_rules continue nope =
  let parse_args = function
    | [] -> (Position.root, false)
    | ["weak"] -> (Position.root, true)
    | pos :: ["weak"] -> (from_string_position pos, true)
    | pos :: _ -> (from_string_position pos, false)
  in
  try
    let (pos, weak) = parse_args arguments in
    match Proverbase.try_case goal pos weak with
      | None ->
        Printf.printf "%s\n\n" ("Case cannot be applied at this " ^
          "position.") ;
        nope ()
      | Some lst -> continue lst []
  with Failure msg -> Printf.printf "%s\n\n" msg ; nope ()
;;

(* handles the "expand" command *)
let user_expansion force arguments goal extra_rules continue nope =
  let parse_args = function
    | [] -> Position.root
    | pos :: _ -> from_string_position pos
  in
  try
    let pos = parse_args arguments in
    match Proverbase.try_expand force goal pos extra_rules with
      | None ->
        Printf.printf "%s" ("Expansion cannot be be applied at " ^
          "this position (most likely, the position is not " ^
          "reduction complete or the resulting set of rules is " ^
          "non-terminating).\n\n") ;
        nope ()
      | Some (goals, rule) ->
        continue goals [rule]
  with
    | Failure "nth" -> Printf.printf "not a legal position\n\n" ; nope ()
    | Failure msg -> Printf.printf "%s\n\n" msg ; nope ()
;;

(* handles the "crewrite" command *)
let user_alterconstraint goal extra_rules continue nope =
  continue [Proverbase.try_alter_constraint goal] []
;;

(* handles the "abstract" command *)
let user_abstract goal extra_rules continue nope =
  match Proverbase.try_abstraction goal with
    | Some goal -> continue [goal] []
    | _ ->
      Printf.printf "Abstraction is not applicable.\n\n" ;
      nope ()
;;

(* handles the "generalise" command *)
let user_generalise arguments goal extra_rules continue nope =
  let spvars = Proverbase.get_special_vars () in
  let varname x = (Variable.find_name x, x) in
  let spvarnames = List.map varname spvars in
  let findvarname name =
    try Some (List.assoc name spvarnames)
    with Not_found ->
      Printf.printf "No such special variable: %s\n" name ;
      None
  in
  if arguments = [] then
    continue [Proverbase.try_generalise goal spvars] []
  else
    let somevars = List.map findvarname arguments in
    if List.mem None somevars then nope (Printf.printf "\n")
    else continue [Proverbase.try_generalise goal
                    (List.map Option.the somevars)] []
;;

(* handle the "rename" command *)
let user_rename merge arguments goal extra_rules continue nope =
  let (s, t, phi) = goal in
  let (_, e, _) = Proverbase.get_data () in
  let vars = List.flat_map Term.vars [s; t; phi] in
  let vnames = List.map Variable.find_name vars in
  let (orgname, newname) =
    match arguments with
      | [a;b] -> (a, b)
      | _ ->
        Printf.printf "Rename requires exactly two arguments!\n" ;
        ("", "")
  in
  if orgname = "" then continue [goal] [] else
  if not (List.mem orgname vnames) then (
    Printf.printf "No such variable: %s\n" orgname ;
    continue [goal] []
  ) else
  if (List.mem newname vnames != merge) then (
    if merge then Printf.printf "Variable %s not yet used!\n" newname
    else Printf.printf "Variable %s already used!\n" newname ;
    continue [goal] []
  ) else
  let orgvar = Environment.find_var orgname e in
  let newvar =
    try Environment.find_var newname e
    with Not_found ->
      let sort = Environment.find_sort orgvar e in
      Environment.create_var newname sort e
  in
  match Proverbase.try_merge goal orgvar newvar merge with
    | None ->
      Printf.printf "Cannot guarantee that variables are equal!\n" ;
      continue [goal] []
    | Some newgoal -> continue [newgoal] []
;;

(* handles the "trivial" command *)
let user_trivial goal extra_rules continue nope =
  let newgoals = Proverbase.try_trivial goal in
  ( if newgoals = [] then
    Printf.printf "Goal is removed using eq-deletion and deletion.\n\n"
  else if newgoals = [goal] then
    Printf.printf "No trivial steps suffice, try \"auto\" instead.\n\n"
  else
    Printf.printf "Replaced goal by %d new goals.\n\n" (List.length newgoals)
  ) ;
  continue newgoals []
;;

(* handles the "autocalc" command *)
let user_autocalculate goal extra_rules continue nope =
  continue [Proverbase.calc_normalise goal] []
;;

(* handles the "autosimp" command *)
let user_autosimplify goal extra_rules continue nope =
  match Proverbase.recommended_simplification goal extra_rules with
    | None ->
      Printf.printf "No simplification can be applied to this equation.\n\n" ;
      nope ()
    | Some (eq, swapped, pos, id) ->
      Printf.printf "We %sapply: simplify %s %s\n\n"
        (if swapped then "swap the sides and then " else "") id
        (Proverbase.to_string_position pos) ;
      continue [eq] []
;;

(* handles the "autoexp" command *)
let user_autoexpand goal extra_rules continue nope =
  match Proverbase.recommended_expansion goal extra_rules with
    | None ->
      Printf.printf "No simplification can be applied to this equation.\n\n" ;
      nope ()
    | Some (swapped, pos, cmd, eqs, rules) ->
      Printf.printf "We %sapply: %s\n\n"
        (if swapped then "swap the sides and then " else "") cmd ;
      continue eqs rules
;;

(* handles the "step" command *)
let user_step tryexpand goal extra_rules continue nope =
  match Proverbase.try_constructor goal with
    | Some newgoals ->
      Printf.printf "We apply: constructor.\n\n" ;
      continue (List.map fst newgoals) []
    | None -> match Proverbase.try_riddance goal with
        | Some (cmds, true) ->
          Printf.printf "Goal is removed using %s.\n\n"
            (List.implode id "; " cmds) ;
          continue [] []
        | Some (cmds, false) ->
          Printf.printf "%s\n" ("Goal can be DISPROVED.  If you " ^
            "have not yet used generalise or other dangerous " ^
            "steps, you may see this as a NO.\n\n") ;
          continue [] []
        | None ->
          let newnope _ =
            if tryexpand then
              user_autoexpand goal extra_rules continue nope
            else nope ()
          in
          user_autosimplify goal extra_rules continue newnope
;;

(* handles the "auto" command *)
let user_auto goal extra_rules continue nope =
  let rec trystep goals erules =
    let np _ = continue goals erules in
    match goals with
      | [] -> continue [] erules
      | hd :: tl ->
        let cont eqs rules = trystep (eqs @ tl) (erules @ rules) in
        user_step false hd (extra_rules @ erules) cont np
  in
  trystep [goal] []
  (*
  match good_riddance goal extra_rules with
    | Left "" -> user_trivial goal extra_rules continue nope
    | Left txt ->
      Printf.printf "Goal is removed using %s.\n\n" txt ;
      continue [] []
    | Right ((equation, "") :: []) ->
      Printf.printf "%s\n\n" ("Goal cannot be easily removed " ^
        "or simplified.") ;
      nope ()
    | Right ((equation, desc) :: []) ->
      Printf.printf "%s%s\n\n" ("Goal cannot be easily removed, " ^
        "but is simplified using ") desc ;
      continue [equation] []
    | Right _ ->
      Printf.printf "%s\n\n" ("Cannot automatically remove " ^
        "goal, and more than one simplification is possible.") ;
      nope ()
  *)
;;


(*******************************************************************)
(* the following functions handle the main loop and interaction    *)
(* with the outside world                                          *)
(*******************************************************************)

let rec user_assisted_derivation history state =
  let (eqs, erules) = state in
  (* retrieves user input and (mildly) parses it *)
  let get_action () =
    Printf.printf "> " ;
    let line = read_line () in
    Printf.printf "\n" ;
    let parts = String.split line in
    match parts with
      | [] -> ("empty", [])
      | command :: args -> (command, args)
  in
  (* continue with the current proof state like nothing happened *)
  let donothing _ = user_assisted_derivation history state in
  (* create a new proof state, with the given list of equations
  replacing the top equation, and the given list of rules appended
  to the rules *)
  let continue newgoals newrules =
    let newstate = (newgoals @ List.tl eqs, erules @ newrules) in
    user_assisted_derivation (state :: history) newstate
  in
  (* handles the case when the user wants to skip to the next goal *)
  let user_skip first remainder _ rules _ _ =
    match remainder with
      | [] ->
        Printf.printf "This is the only goal.\n\n" ;
        donothing ()
      | _ ->
        let newgoals = List.append remainder [first] in
        let childstate = (newgoals, rules) in
        user_assisted_derivation (state :: history) childstate
  in
  (* restores the current state to the parent *)
  let user_undo _ _ _ _ =
    match history with
      | [] ->
        Printf.printf "Nothing left to undo.\n\n" ;
        donothing ()
      | head :: tail ->
        user_assisted_derivation tail head
  in
  match eqs with
    | [] -> YES
    | goal :: rest ->
      print_goal goal ;
      let (action, arguments) = get_action () in
      let commands = [("abort",        user_abort)      ;
                      ("exit",         user_abort)      ;
                      ("skip",         user_skip goal rest) ;
                      ("rules",        user_rules)      ;
                      ("swap",         user_swap)       ;
                      ("delete",       user_deletion)   ;
                      ("eq-delete",    user_eqdeletion) ;
                      ("constructor",  user_constructor) ;
                      ("calculate",    user_calculate arguments) ;
                      ("simplify",     user_simplify arguments) ;
                      ("case",         user_case arguments) ;
                      ("expand",       user_expansion false arguments) ;
                      ("force-expand", user_expansion true arguments) ;
                      ("crewrite",     user_alterconstraint) ;
                      ("generalise",   user_generalise arguments) ;
                      ("abstract",     user_abstract) ;
                      ("rename",       user_rename false arguments) ;
                      ("merge",        user_rename true arguments) ;
                      ("trivial",      user_trivial) ;
                      ("autocalc",     user_autocalculate) ;
                      ("autosimp",     user_autosimplify) ;
                      ("autoexp",      user_autoexpand) ;
                      ("step",         user_step true) ;
                      (".",            user_step true) ;
                      ("auto",         user_auto) ;
                      ("undo",         user_undo)       ;
                     ] in
      let pre = List.map (fun name -> (name, user_commands commands))
                         ["list"; "empty"; "help"; "commands"] in
      let commands = List.append pre commands in
      let f = (
        try List.assoc action commands
        with Not_found -> user_illegal action
      ) in
      f goal erules continue donothing
;;

(* main functionality for assisted proving *)
let run trs eqs =
  Proverbase.precheck failwith (fun _ -> ()) trs eqs true ;
  let (backup, eqs) = Proverbase.initialise trs eqs in
  print_all_rules [] ;
  let state = (eqs, []) in
  let response = user_assisted_derivation [] state in
  match backup with
    | None -> response
    | Some t -> Trs.set_current t ; response
;;

