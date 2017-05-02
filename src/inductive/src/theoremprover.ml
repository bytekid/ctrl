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
open Smt;;
open Rewriting;;
open Confluence;;
open Termination;;

(*** TYPES *******************************************************************)

type answer = YES | NO | MAYBE;;
type equation = Term.t * Term.t * Term.t;;
  (* constraints have the form (s,t,phi), for s = t [phi] *)

type recursion = Proverbase.recursion =
                 NonRecursive | TailRecursive | GeneralRecursive;;

type progress = Beginning | Deletion |
                RestrictedBeginning of progress |
                RestrictedDeletion of progress |
                Simplifying of (bool * Position.t * Rule.t * string) list |
                Abstracting |
                Expanding of (bool * bool * bool * Position.t * string) list |
                Generalising of (Variable.t list * string) list |
                CaseAnalysing of (bool * bool * bool * Position.t * string) list

type state_status = SAT | UNSAT | ACTIVE of progress |
                    INACTIVE of int * string |
                    PROGRESS of int * int * string * progress;;
  (* SAT: proofstate has been proved acceptable; if any proofstate is
       acceptable, we can immediately propagate this up and finish
     UNSAT: proofstate cannot be handled with the current rules
     ACTIVE progress: we're working on it, and don't currently have
       any children
     INACTIVE child: we have worked on it, and reduced solvability to
       solvability of the given child
     PROGRESS (child, num, desc, progress): we're working on it, but
       we are currently focusing on a child; if that fails, we'll
       fall back to the given progress; "num" indicates the number of
       open goals generated from the current goal in the child state
  *)
type proofstate =
  { rules     : int list;
    equations : int list;
    parent    : int option;
    complete  : (int * int) list;
    status    : state_status
  };;

(*** MODULES *****************************************************************)

module VarSet = Set.Make(Variable);;

module ProofStateBase = struct
  type t = (int list) * (int list)
  let compare = compare
  let fprintf fmt (lst1, lst2) =
    Format.fprintf fmt "(%s; %s)\n" (List.implode string_of_int "," lst1)
                                    (List.implode string_of_int "," lst2)
end

module ProofStateIndex = struct
  type t = int
  let compare = compare
  let fprintf fmt i = Format.fprintf fmt "%d" i
end

module ProofStateLookup = Map.Make(ProofStateBase)(ProofStateIndex);;

module SymbolGraph = Graph.Make(Function);;

module SymbolIndex = Map.Make(Function)(Int);;

(*** VARIABLES ***************************************************************)

let internal_ps_lookup : ProofStateLookup.t ref = ref ProofStateLookup.empty;;
let all_extrarules : Rule.t option array ref = ref (Array.make 100 None);;
let all_numextrarules : int ref = ref 0;;
let all_goals : (equation * int) option array ref = ref (Array.make 100 None);;
let all_numgoals : int ref = ref 0;;
let all_states : proofstate option array ref = ref (Array.make 100 None);;
let all_numstates : int ref = ref 0;;

(*** FUNCTIONS ***************************************************************)

(********************************************************************)
(* the following functions give quick access to Proverbase functions*)
(********************************************************************)

let alphabet () = Proverbase.alphabet ();;
let environment () = Proverbase.environment ();;
let specialvars () = Proverbase.specialvars ();;
let logicsorts () = Proverbase.logicsorts ();;

let is_constructor f = Proverbase.is_constructor f;;

let equation_to_rule = Proverbase.equation_to_rule;;
let to_string_position = Proverbase.to_string_position;;

let term_positions = Proverbase.term_positions;;
let goal_positions = Proverbase.goal_positions;;

(*******************************************************************)
(* these functions deal with the globally maintained statuses      *)
(*******************************************************************)

let get_from internal_array index =
  match !internal_array.(index) with
    | None -> failwith "get_from_internal_array with wrong index"
    | Some status -> status
;;

let add_to internal_array internal_num status =
  let internal = !internal_array in
  let len = Array.length internal in
  let num = !internal_num in
  let internal = (
    if num < len then internal
    else Array.append internal (Array.make len None)
  ) in
  internal.(!internal_num) <- Some status ;
  internal_array := internal ;
  internal_num := num + 1 ;
  num
;;

let get_extra_rule = get_from all_extrarules;;
let get_state = get_from all_states;;
let add_extra_rule = add_to all_extrarules all_numextrarules;;

let get_goal id = fst (get_from all_goals id);;
let get_goal_depth id = snd (get_from all_goals id);;
let add_goal goal depth = add_to all_goals all_numgoals (goal, depth);;

let add_state state =
  let ret = add_to all_states all_numstates state in
  internal_ps_lookup := ProofStateLookup.add
    (state.equations, state.rules) ret !internal_ps_lookup ;
  ret
;;
let find_state goals rules = ProofStateLookup.find (goals, rules)
  !internal_ps_lookup;;

let update_state index newstate =
  !all_states.(index) <- Some newstate
;;

(*******************************************************************)
(* the following functions print information to the user           *)
(*******************************************************************)

(* prints the given equation to a string *)
let to_string_goal (l, r, phi) =
  ( Printer.to_string_term l ) ^ " = " ^
  ( Printer.to_string_term r ) ^ " [" ^
  ( Printer.to_string_term phi ) ^ "]"
;;

(*******************************************************************)
(* the following functions deal with proof statuses                *)
(*******************************************************************)

(* returns the initial proof status with the given equations
(which are rules representing the intended equations *)
let start_state equations =
  let base_goal equation = add_goal equation 0 in
  let eq_indexes = List.map base_goal equations in
  { rules     = [];
    equations = eq_indexes;
    parent    = None;
    complete  = [];
    status    = ACTIVE Beginning
  }
;;

(* returns a new active state with the given goals and rules, and the
given state as its parent *)
let make_state_child state goalindexes ruleindexes compl =
  let child =
    { rules     = ruleindexes ;
      equations = goalindexes ;
      parent    = Some state ;
      complete  = compl ;
      status    = ACTIVE Beginning
    }
  in
  add_state child
;;

(* returns a new active state as a child state from the given state,
with as goals all goals from the given state except the first, plus
the given replacement goals, and as rules both the given extra_rules
and the rules from the parent state; this returns Left newstate if a
new state was made, or Right oldstate if the given goals and rules
represent an existing state *)
let make_state_child_with state replacement_goals extra_rules inc
                          lose_completeness =
  let (depth, oldgoals) =
    match (get_state state).equations with
      | [] -> failwith ("Cannot replace the top goal in the empty " ^
                        "goal list!")
      | id :: tail -> (get_goal_depth id, tail)
  in
  let depth = if inc then depth + 1 else depth in
  let make_goal goal = add_goal goal depth in
  let newgoals = List.map make_goal replacement_goals in
  let goals = List.append newgoals oldgoals in
  let oldrules = (get_state state).rules in
  let newrules = List.map add_extra_rule extra_rules in
  let compl =
    if lose_completeness then
      (state, List.length (get_state state).equations) ::
      (get_state state).complete
    else (
      let c = (get_state state).complete in
      if replacement_goals <> [] then c else
      match c with
        | [] -> c
        | (_,n) :: tl ->
          if n > List.length goals then tl
          else c
    )
  in
  let rules =
    if newrules = [] then oldrules
    else List.append oldrules newrules
  in
  try Right (find_state goals rules)
  with Not_found -> Left (make_state_child state goals rules compl)
;;

(* sets the state, which must be in active mode, to have the given child *)
let set_state_child state child reason num_child_goals =
  let original = get_state state in
  let newstatus = (
    match original.status with
      | ACTIVE Beginning | ACTIVE (RestrictedBeginning _)
      | ACTIVE Deletion  | ACTIVE (RestrictedDeletion _) ->
        INACTIVE (child, reason)
      | ACTIVE x -> PROGRESS (child, num_child_goals, reason, x)
      | _ -> failwith "Asked to set a state child for an inactive state!"
  ) in
  let update = { original with status = newstatus } in
  update_state state update
;;

(*******************************************************************)
(* the following functions are used for automatic inductive        *)
(* theorem proving                                                 *)
(*******************************************************************)

(* returns all normal and extra rules, together with their name, in
the best order to try them *)
let get_all_rules extra_rules =
  Proverbase.get_all_rules (List.map get_extra_rule extra_rules)
;;

(* helping function for both simplifiable_positions functions *)
let relevant_positions (l,r,_) positions extra_rules =
  let goodpos (_, (_, f)) = List.mem f !Proverbase.internal_defs in
  let positions = List.filter goodpos positions in
  let rules = get_all_rules extra_rules in
  let product = List.product positions rules in
  let fixpair ((swap, (pos, _)), (name, rule)) =
    let desc = "simplify " ^ name ^ " " ^ (to_string_position pos) in
    let sub = Term.subterm pos (if swap then r else l) in
    if Term.root sub <> Term.root (Rule.lhs rule) then []
    else [(swap, pos, rule, desc)]
  in
  List.flat_map fixpair product
;;

(* returns all positions in the given goal where simplification may
be used (with false positives) *)
let simplifiable_positions goal extra_rules =
  let positions = goal_positions goal in
  let rightfirst posses =
    let (right, left) = List.partition (fun (x,_) -> x) posses in
    right @ left
  in
  let positions = (
    match goal with
      | (Term.Fun (f,_),_,_) | (Term.InstanceFun (f,_,_),_,_) ->
        if is_constructor f then rightfirst positions
        else positions
      | _ -> rightfirst positions
  ) in
  relevant_positions goal positions extra_rules
;;

let expandable_positions goal extra_rules =
  let erules = List.map get_extra_rule extra_rules in
  Proverbase.expandable_positions goal erules true false
;;

let case_positions goal extra_rules =
  let erules = List.map get_extra_rule extra_rules in
  Proverbase.expandable_positions goal erules false true
;;

(* given that we were simplifying a goal with the given set of
positions not yet tried, and reduced it at position (swapped,
reducedpos), returns the new set of positions on which we should
continue to try to simplify! *)
let update_simplifiable_positions posses goal swapped reducedpos
                                  extra_rules =
  let xor x y = if x then not y else y in
  let swappos (swap, p, r, d) = (xor swap swapped, p, r, d) in
  let posses = List.map swappos posses in
  let (lhs, rhs, phi) = goal in
  try
    let sub = Term.subterm reducedpos lhs in
    let makeposition (p, f) = (false, (Position.append reducedpos p, f)) in
    let newposses = List.map makeposition (term_positions sub) in
    (relevant_positions goal newposses extra_rules) @ posses
  with _ ->
    (* the position doesn't exist: it was a value, and it's been
    calculated upwards! *)
    let rec best_position pos term =
      if Term.is_var term then Position.root else
      let i = Position.head pos in
      let rest = Position.tail pos in
      let sub = List.nth (Term.args term) i in
      Position.add_first i (best_position rest sub)
    in
    let top = best_position reducedpos lhs in
    let goodpos (swap, p, r, d) = swap ||
                                  not (Position.is_prefix top p) in
    List.filter goodpos posses
;;

(* returns all variables in the given goal which can be generalised *)
let generalisable_variables (_, _, phi) =
  let vars = Term.vars phi in
  let special = specialvars () in
  let xs = List.filter (fun x -> VarSet.mem x special) vars in
  (*let getdesc x = ([x], "generalise " ^ (varname x)) in*)
  let combined = List.implode Variable.find_name " " xs in
  if xs = [] then []
  else (xs, "generalise " ^ combined) :: [] (* List.map getdesc xs *)
;;

(* finds the followup status if the current one failed *)
let next_status state =
  let original = get_state state in
  let next_active_status goal = function
    | Beginning -> ACTIVE Deletion
    | RestrictedBeginning nextstatus ->
      ACTIVE (RestrictedDeletion nextstatus)
    | Deletion ->
      ACTIVE (Simplifying (simplifiable_positions goal original.rules))
    | RestrictedDeletion nextstatus -> ACTIVE nextstatus
    | Simplifying [] -> ACTIVE Abstracting
    | Abstracting ->
      ACTIVE (Expanding (expandable_positions goal original.rules))
    | Expanding [] -> ACTIVE (Generalising (generalisable_variables goal))
    | Generalising [] ->
      ACTIVE (CaseAnalysing (case_positions goal original.rules))
    | CaseAnalysing [] -> UNSAT
    | Simplifying (_ :: tail) -> ACTIVE (Simplifying tail)
    | Expanding (_ :: tail) -> ACTIVE (Expanding tail)
    | Generalising (_ :: tail) -> ACTIVE (Generalising tail)
    | CaseAnalysing (_ :: tail) -> ACTIVE (CaseAnalysing tail)
  in
  let rec find_next_status goal = function
    | SAT | UNSAT -> failwith "Cannot progress finished status!"
    | INACTIVE _ -> UNSAT
    | ACTIVE p | PROGRESS (_, _, _, p) ->
      clean_status goal (next_active_status goal p)
  and clean_status goal status =
    match status with
      | ACTIVE Simplifying []
      | ACTIVE Expanding []
      | ACTIVE Generalising [] ->
        find_next_status goal status
      | _ -> status
  in
  match original.equations with
    | [] -> SAT
    | head :: tail ->
      find_next_status (get_goal head) original.status
;;

(* changes the status of the given state *)
let update_status_for state newstatus =
  update_state state { (get_state state) with status = newstatus }
;;

(* progresses the status of the given state, and returns the new status *)
let progress_status state =
  let newstatus = next_status state in
  update_status_for state newstatus ;
  newstatus
;;

(* showing some information about the current state to the user *)
let tostr_state state =
  let fullstate = get_state state in
  "state " ^ (string_of_int state) ^ " with " ^
  ( match fullstate.equations with
    | [] -> "no goals"
    | goal :: others ->
      let rec print_remainder = function
        | [] -> ""
        | x :: y ->
          "    * " ^ (to_string_goal (get_goal x)) ^ "\n" ^
          (print_remainder y)
      in
      "goals\n    > " ^ (to_string_goal (get_goal goal)) ^ "\n" ^
      (print_remainder others)
  )
;;

(* called when we have succesfully solved the given state *)
let success state docrewrite yesno =
  let print_state state fullstate =
    Printf.printf "%s\n" (tostr_state state) ;
    match fullstate.status with
      | SAT -> if yesno = NO then Printf.printf "  is disproved.\n"
      | UNSAT -> Printf.printf "... is unsatisfiable, hum\n"
      | ACTIVE _ -> Printf.printf "... is still active, how strange\n"
      | INACTIVE (_, desc) | PROGRESS (_, _, desc, _) ->
        Printf.printf "  is reduced using %s to\n" desc
  in
  let rec print_derivation state =
    let fullstate = get_state state in
    match fullstate.parent with
      | None -> print_state state fullstate
      | Some parent ->
        print_derivation parent ;
        print_state state fullstate
  in
  update_status_for state SAT ;
  let printit _ =
    Printf.printf "\n==========\nDERIVATION\n==========\n" ;
    if docrewrite then (
      Printf.printf "(%s)\n\n"
        ("All simplification, expansion and case steps are " ^
         "implicitly followed by a crewrite.")
    ) ;
    print_derivation state
  in
  (yesno, printit)
;;

let _DEBUG = 0;;

(* when we have solved a goal, but then fail on something else
later, we don't want to have to backtrack and retry all the
simplifications leading up to that goal being solved; thus, we
adapt the parent states to say this was the only decision we
could have made, seeing as it was the right one! *)
let rec solved_goal state =
  let fullstate = get_state state in
  let pass_to_parent = function
    | None -> ()
    | Some parent -> solved_goal parent
  in
  match fullstate.status with
    | ACTIVE _ -> pass_to_parent fullstate.parent      
    | PROGRESS (child, num, desc, p) ->
      if _DEBUG > 0 then
        Printf.printf "Cutting branches off from state %d\n" state ;
      if num > 1 then
        update_status_for state (PROGRESS (child, num - 1, desc, p))
      else (
        update_status_for state (INACTIVE (child, desc)) ;
        pass_to_parent fullstate.parent
      )
    | _ -> ()
;;

(* automatically proves solvability of the given state, or aborts
if we cannot prove that *)
let rec automatic_derivation bound state docrew =
  if _DEBUG = 2 then
    Printf.printf "Handling %s.\n%!" (tostr_state state) ;

  (* basic variables *)
  let fullstate = get_state state in
  match fullstate.equations with | [] -> success state docrew YES | eq :: tail ->
  let goal = get_goal eq in
  (* called if the current attempt at simplifying didn't work *)
  let try_next_status () =
    let _ = progress_status state in
    automatic_derivation bound state docrew
  in
  (* called if we have succesfully simplified the goal *)
  let continue_with mymethod newgoals extra_rules update_parent inc
                    lose_completeness =
    match make_state_child_with state newgoals extra_rules inc
                                lose_completeness with
      | Left newstate ->
        if _DEBUG > 0 then Printf.printf "Reduced using %s to %s.\n"
          mymethod  (tostr_state newstate) ;
        update_status_for state (update_parent newstate) ;
        automatic_derivation bound newstate docrew
      | Right _ -> try_next_status ()
  in
  (* used when there is only one reasonable way to make children *)
  let obvious desc child = INACTIVE (child, desc) in
  (* get the data *)
  let swapped_pair swap desc =
    if swap then (Proverbase.try_swap goal, "swap; " ^ desc)
    else (goal, desc)
  in
  (* main functionality, branch on the current status *)
  match fullstate.status with
    | SAT -> success state docrew YES
    | UNSAT -> failure state None bound docrew
    | INACTIVE (child, _) -> automatic_derivation bound child docrew
    | PROGRESS (child, _, _, _) -> automatic_derivation bound child docrew
    | ACTIVE Beginning | ACTIVE (RestrictedBeginning _) ->
      if _DEBUG = 2 then Printf.printf "Beginning\n%!" ;
      if Proverbase.try_anti_constructor goal then (
        match Proverbase.try_riddance goal with
          | None -> (
              match (get_state state).complete with
                | [] -> success state docrew NO
                | (o, _) :: _ -> failure state (Some o) bound docrew
            )
          | Some (descs, _) ->
            let desc = List.implode id "; " descs in
            solved_goal state ;
            continue_with desc [] [] (obvious desc) false false
      )
      else ( match Proverbase.try_constructor goal with
          | None -> try_next_status ()
          | Some lst -> 
            let f child =
              update_status_for child (ACTIVE Beginning) ;
              obvious "constructor" child
            in
            let newgoals = List.map fst lst in
            continue_with "constructor" newgoals [] f false false
      )
    | ACTIVE Deletion | ACTIVE (RestrictedDeletion _) ->
      if _DEBUG = 2 then Printf.printf "Deletion\n%!" ;
      ( match Proverbase.try_riddance goal with
          | None ->
            if Proverbase.try_all_logical goal then (
              match (get_state state).complete with
                | [] -> success state docrew NO
                | (o, _) :: _ -> failure state (Some o) bound docrew
            )
            else try_next_status ()
          | Some (descs, true) ->
            let desc = List.implode id "; " descs in
            solved_goal state ;
            continue_with desc [] [] (obvious desc) false false
          | Some (desc, false) -> (
              match (get_state state).complete with
                | [] -> success state docrew NO
                | (o, _) :: _ -> failure state (Some o) bound docrew
            )
      )
    | ACTIVE (Simplifying []) | ACTIVE (Expanding []) |
      ACTIVE (CaseAnalysing []) -> try_next_status ()
    | ACTIVE (Simplifying lst) ->
      let (swap, pos, rule, desc) = List.hd lst in
      if _DEBUG = 2 then Printf.printf "Simplifying (%s)\n%!" desc ;
      let (swappedgoal, swappeddesc) = swapped_pair swap desc in
      let x =
        try Proverbase.try_simplify swappedgoal rule pos
        with Failure _ -> failwith ((to_string_goal swappedgoal) ^ swappeddesc)
      in
      ( match x with
          | None -> try_next_status ()
          | Some newgoal ->
            let newgoal =
              if docrew then Proverbase.try_alter_constraint newgoal
              else newgoal
            in
            let newpositions = update_simplifiable_positions
              (List.tl lst) newgoal swap pos fullstate.rules in
            let simp = (RestrictedBeginning (Simplifying newpositions)) in
            let f child =
              update_status_for child (ACTIVE simp) ;
              INACTIVE (child, swappeddesc)
            in
            continue_with swappeddesc [newgoal] [] f false false
      )
    | ACTIVE (Expanding lst) | ACTIVE (CaseAnalysing lst) ->
      let expd = match fullstate.status with ACTIVE (Expanding _) -> true | _ -> false in
      if get_goal_depth eq > bound then failure state None bound docrew else
      let (swap, expand, inc, pos, desc) = List.hd lst in
      if _DEBUG = 2 then Printf.printf "Expanding (%s)\n%!" desc ;
      let (swappedgoal, swappeddesc) = swapped_pair swap desc in
      let extra_rules = fullstate.rules in
      let result =
        if expand then
          match Proverbase.try_expand true swappedgoal pos (List.map get_extra_rule extra_rules) with
            | None -> None
            | Some (newgoals, newrule) -> Some (newgoals, [newrule])
        else
          match Proverbase.try_case swappedgoal pos false with
            | None -> None
            | Some newgoals -> Some (newgoals, [])
      in
      ( match result with
        | None -> try_next_status ()
        | Some (newgoals, newrules) ->
          let newgoals =
            if docrew then List.map Proverbase.try_alter_constraint newgoals
            else newgoals
          in
          let n = List.length newgoals in
          let f child =
            if expd then PROGRESS (child, n, swappeddesc, (Expanding lst))
            else PROGRESS (child, n, swappeddesc, (CaseAnalysing lst))
          in
          continue_with swappeddesc newgoals newrules f inc false
      )
    | ACTIVE Abstracting ->
      ( match Proverbase.try_abstraction goal with
        | None -> try_next_status ()
        | Some goal ->
          let f child =
            update_status_for child (ACTIVE Abstracting) ;
            let _ = progress_status child in
            PROGRESS (child, 1, "abstract", Abstracting)
          in
          continue_with "abstraction" [goal] [] f false true
      )
    | ACTIVE (Generalising lst) ->
      let (vars, desc) = List.hd lst in
      if _DEBUG = 2 then Printf.printf "Generalising (%s)\n%!" desc ;
      let newgoal = Proverbase.try_generalise goal vars in
      let f child =
        update_status_for child (ACTIVE Abstracting) ;
        let _ = progress_status child in
        PROGRESS (child, 1, desc, Generalising lst)
      in
      continue_with desc [newgoal] [] f false true

(* called when we have decided we cannot solve the given state *)
and failure state backtrack_to bound docrew =
  if _DEBUG > 0 then Printf.printf "failing state %d\n" state ;
  let fullstate = get_state state in
  if backtrack_to <> None then update_status_for state UNSAT ;
  match fullstate.parent with
    | None -> (MAYBE, fun _ -> ())
    | Some parent ->
      let newstatus =
        if (backtrack_to = None) || (backtrack_to = Some parent) then
          progress_status parent
        else UNSAT
      in
      if newstatus = UNSAT then failure parent backtrack_to bound docrew
      else (
        if _DEBUG > 0 then
          Printf.printf "Backtracking to parent %s.\n" (tostr_state parent) ;
        automatic_derivation bound parent docrew
      )
;;

let reset_states eqs =
  all_states := Array.make 100 None;
  all_numstates := 0;
  add_state (start_state eqs)
;;

(* try automatic_derivation for a reasonable number of attempts *)
let rec automatic lowest highest eqs =
  let state = reset_states eqs in
  let a = alphabet () in
  let int_or_bool sort =
    ( sort = Alphabet.boolsort ) ||
    ( try sort = Alphabet.integer_sort a with Not_found -> false)
  in
  let docrewrite =
    (lowest >= 4) && not (List.for_all int_or_bool (logicsorts ()))
  in
  match automatic_derivation lowest state docrewrite with
    | (MAYBE, explanation) -> 
      if lowest + 2 <= highest then
        automatic (lowest + 2) highest eqs
      else if lowest + 1 <= highest then
        automatic (lowest + 1) highest eqs
      else (MAYBE, explanation)
    | response -> response
;;

(* here we initiate a fully automatic derivation *)
let run trs eqs =
  Proverbase.precheck failwith (fun _ -> ()) trs eqs false ;
  let (backup, eqs) = Proverbase.initialise trs eqs in
  let response = match automatic 2 5 eqs with
    | (NO, f) ->
      if Confluencechecker.weak_orthogonal trs then (NO, f)
      else (MAYBE, f)
    | pair -> pair
  in
  match backup with
    | None -> response
    | Some t -> Trs.set_current t ; response
;;

