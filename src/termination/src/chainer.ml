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
open Smt;;
open Rewriting;;
open Io;;

(*** MODULES *****************************************************************)

module List = Util.List;;

module Node = struct
  type t = int 

  let compare = compare
  let copy i = i 
  let hash i = i 
  let to_string = string_of_int
  let fprintf fmt = Format.fprintf fmt "%d"
end
module IntGraph = Util.Graph.Make(Node);;
module IntSet = Set.Make(Node);;

(*** FUNCTIONS ***************************************************************)

(* ========== detecting chainable DPs ========== *)

(* check whether this is a rule of the form f(l1,...,ln) -> r, where
all li are either variables or boolean values, and there is at least
one boolean! *)
let is_tester_rule a rule =
  if Rule.constraints rule <> [] then false else
  let args = Term.args (Rule.lhs rule) in
  let goodarg arg =
    match Term.root arg with
      | None -> true
      | Some f ->
        ( f = Alphabet.get_bot_symbol a ) ||
        ( f = Alphabet.get_top_symbol a ) 
  in  
  let notavar arg = not (Term.is_var arg) in
  (List.for_all goodarg args) && (List.exists notavar args) &&
  (Rule.is_left_linear rule)
;;

(* finds all ids of tester rules in the given graph *)
let find_all_tester_ids a graph =
  let ids = Dpgraph.get_node_ids graph in
  let get_dp i = (i, Dpgraph.get_node_dp i graph) in
  let data = List.map get_dp ids in
  let is_tester (i, dp) = is_tester_rule a dp in
  List.map fst (List.filter is_tester data)
;;

(* ========== fixing conditional recursion ========== *)

(* finds a recursive tester rule, e.g. f(true, x) -> f(x > 0, x - 1 *)
let find_recursive_tester testerids dpgraph =
  (* arrange the tester IDs in a graph, for easy lookups*)
  let neighbourdata i = (i, Dpgraph.get_node_neighbours i dpgraph) in
  let lookup = List.map neighbourdata testerids in
  let should_have_edge i j =
    let neighbours = List.assoc i lookup in
    if List.mem j neighbours then [(i,j)] else []
  in
  let g = IntGraph.generate should_have_edge testerids in
  (* find any that are part of a loop! *)
  let sccs = IntGraph.sccs g in
  let rec first_real = function
    | [] -> None
    | [] :: tl -> first_real tl
    | [a] :: tl ->
      if List.mem a (IntGraph.successors a g) then Some a
      else first_real tl
    | (a :: _) :: _ -> Some a
  in
  first_real sccs
;;

(* creates an unconditional rule over the same variables as dp,
using a new function symbol; returns the new pair and [dp] changed
to be non-recursive *)
let create_unconditional_variation a e dp =
  (* step 0: gather data *)
  let (lhs, rhs, cs) = (Rule.lhs dp, Rule.rhs dp, Rule.constraints dp) in
  let args = Term.args lhs in
  let varargs = List.filter Term.is_var args in
  (* step 1: select a new name *)
  let vn = Environment.var_names e in
  let fn = Alphabet.fun_names a in
  let basename = Function.find_name (Rule.left_root dp) in
  let base = String.sub basename 0 ((String.length basename) - 1) in
  let rec unused n k =
    let attempt = n ^ (string_of_int k) ^ "#" in
    if List.mem attempt vn then unused n (k + 1)
    else if List.mem attempt fn then unused n (k + 1)
    else attempt
  in
  let name = unused (base ^ "_") 1 in
  (* step 2: register the new function symbol *)
  let findsort term = Term.get_sort a e term in
  let isorts = List.map findsort varargs in
  let osort = findsort lhs in
  let sortdec = Sortdeclaration.create isorts osort in
  let f = Alphabet.create_fun sortdec name a in
  Alphabet.set_symbol_kind f Alphabet.Terms a ;
  (* step 3: create the two new rules *)
  let newside = Term.make_fun f varargs in
  let dp1 = Rule.create lhs newside [] in
  let dp2 = Rule.create newside rhs cs in
  (*let dp2 = Rule.fresh_renaming dp2 e e fn in*)
  (dp1, dp2)
;;

let rec fix_conditional_recursion didstuff a e graph =
  let tester_ids = find_all_tester_ids a graph in
  match find_recursive_tester tester_ids graph with
    | None -> (graph, didstuff)
    | Some id ->
      let dp = Dpgraph.get_node_dp id graph in
      let (dp1, dp2) = create_unconditional_variation a e dp in
      let (graph, newid) =
        Dpgraph.add_node a e dp2 None (Some id) None graph in
        (* now dp1 is unchanged, but dp2 is a loose node without
        incoming edges, and outgoing edges copied from dp1 *)
      let followers = Dpgraph.get_node_neighbours id graph in
      let subedge g next = Dpgraph.remove_edge (id,next) g in
      let graph = List.fold_left subedge graph followers in
      let graph = Dpgraph.add_edge (id,newid) graph in
      let graph = Dpgraph.replace_dp id dp1 graph in
        (* now the only outgoing edge from dp1 goes to dp2 *)
      fix_conditional_recursion true a e graph
;;

(* ========== applying the chaining ========== *)

(** chains the given DP [first] with the given DP [second], which has
only variables and boolean values; a failure is thrown if chaining is
impossible at this point *)
let simple_chain a e first second =
  let (alhs, arhs, acs) =
    (Rule.lhs first, Rule.rhs first, Rule.constraints first) in
  let (blhs, brhs, bcs) =
    (Rule.lhs second, Rule.rhs second, Rule.constraints second) in
  let bcvars = List.unique (List.flat_map Term.vars bcs) in
  let argzip = List.zip (Term.args arhs) (Term.args blhs) in
  let inst (subst, sofar) (term, varorvalue) =
    if Term.is_var varorvalue then
      let x = List.hd (Term.vars varorvalue) in
      try (Substitution.add x term subst, sofar)
      with Substitution.Inconsistent -> failwith "Non-linear concatenation!"
    else (
      try
        let f = List.hd (Term.funs varorvalue) in
        if f = Alphabet.get_top_symbol a then (subst, term :: sofar)
        else if f = Alphabet.get_bot_symbol a then
          let neg = Alphabet.get_not_symbol a in
          let notterm = Term.make_function a e neg [term] in
          (subst, notterm :: sofar)
        else failwith "Concatenation DP is not simple!"
      with Not_found -> failwith "Top, bottom or negation symbol unset!"
    )
  in
  let fn = Alphabet.fun_names a in
  let addfresh subst x =
    if Substitution.mem x subst then subst else
    let y = Environment.create_var_like x e fn e in
    Substitution.add x (Term.make_var y) subst
  in
  let (subst, newcs) = List.fold_left inst (Substitution.empty, []) argzip in
  let subst = List.fold_left addfresh subst (Rule.vars second) in
  let bcs_subst = List.map (Substitution.apply_term subst) bcs in
  let not_logical term = Term.check_logical_term a term <> None in
  if List.exists not_logical bcs_subst then
    failwith "DP cannot be concatenated due to old constraints!" ;
  if List.exists not_logical newcs then
    failwith "DP cannot be concatenated due to new constraints!" ;
  let updlhs = alhs in
  let updrhs = Substitution.apply_term subst brhs in
  let updcs = acs @ newcs @ bcs_subst in
  (Rule.create updlhs updrhs updcs)
;;

(* chains DPs to non-recursive tester rules *)
let find_simple_chaining testdps a e graph =
  let rec find_first_chaining = function
    | [] -> None
    | id :: tail ->
      let successors = Dpgraph.get_node_neighbours id graph in
      let successors = List.diff successors [id] in (* only SIMPLE chaining *)
      let get_dp i = (i, Dpgraph.get_node_dp i graph) in
      let followers = List.map get_dp successors in
      try
        let istester (i, dp) = List.mem i testdps in
        let (di, chainable) = List.find istester followers in
        let dp = snd (get_dp id) in
        Some (id, di, simple_chain a e dp chainable)
      with _ -> find_first_chaining tail
  in
  find_first_chaining (Dpgraph.get_node_ids graph)
;;

(* ========== finding, and adding information about, unconstrained variables *)

(* gets variables in the constranit for the given dependency pair *)
let constraint_vars dp =
  let cvars = List.flat_map Term.vars (Rule.constraints dp) in
  let justone = function [_] -> true | _ -> false in
  if justone (Rule.constraints dp) then cvars
  else List.unique cvars
;;

(* gets the arguments with the given (ordered!) indexes; call with k = 0 *)
let rec get_numbered_arguments k indexes arguments =
  match (indexes, arguments) with
    | ([], _) -> [] (* no further indexes *)
    | (_::_, []) ->
      failwith "get_numbered_arguments fails; DP graph problem?"
    | (num :: tl, arg :: rest) ->
      if k = num then arg :: get_numbered_arguments (k + 1) tl rest
      else get_numbered_arguments (k + 1) indexes rest
;;

(* returns the argument index and unconstrained variables for all
direct argument positions in the given side of [dp] where the
argument is a logical term, whose variables do not all occur in the
dependency pair's constraint *)
let logical_unconstrained_arguments getside a e logicsorts dp =
  let args = Term.args (getside dp) in
  let numbered_args = List.mapi (fun i arg -> (i, arg)) args in
  let cvars = constraint_vars dp in
  let check_logical (i, arg) =
    if Term.check_logical_term a arg <> None then [] else
    let vars = List.diff (Term.vars arg) cvars in
    if vars = [] then [] else
    [(i, vars)]
  in
  List.flat_map check_logical numbered_args
;;

(* returns all the variables that can safely be added to the
constraint of [dp] (which are not already there), assuming instances
of variables of logical sorts cannot reduce to two different values *)
let addable_output_variables_for (id, dp) graph a e logicsorts =
  let argdata = logical_unconstrained_arguments Rule.rhs a e logicsorts dp in
    (* a list of direct argument positions in the right-hand side of
    dp, and not-quite-logical variables occurring at those positions;
    these have the form (id, [x1;...;xn]) *)
  if argdata = [] then [] else
  let follower_ids = Dpgraph.get_node_neighbours id graph in
  let getdp j = Dpgraph.get_node_dp j graph in
  let follower_dps = List.map getdp follower_ids in
  let addnums = List.mapi (fun i x -> (i, x)) in
  let getdata p = ( addnums (Term.args (Rule.lhs p)), constraint_vars dp ) in
  let follower_data = List.map getdata follower_dps in
    (* a list containing, for all pairs following [dp] in the graph,
    all its arguments (numbered) and the variables in its constraint *)
  let limit_args (args, phi) =
    (get_numbered_arguments 0 (List.map fst argdata) args, phi) in
  let follower_data = List.map limit_args follower_data in
    (* now follower_data contains only relevant arguments whose
    indexes also occur in argdata *)
  let varin phivars (_, arg) =
    if not (Term.is_var arg) then false else
    let x = List.hd (Term.vars arg) in
    List.mem x phivars
  in
  let get_suitable_args (args, pv) =
    List.map fst (List.filter (varin pv) args) in
  let relevant_args = List.map get_suitable_args follower_data in
    (* relevant_args contains lists of argument indexes where a
    follower of dp has a constrained variable *)
  let suitable_everywhere = List.fold_left List.intersect
                              (List.map fst argdata) relevant_args in
    (* these are the indexes of arguments where *all* followers have
    only constrained variables *)
  let args = get_numbered_arguments 0 suitable_everywhere argdata in
  List.unique (List.flat_map snd args)
;;

let add_logical_variables a e vee neg eq dp vars =
  let (lhs, rhs, cs) = (Rule.lhs dp, Rule.rhs dp, Rule.constraints dp) in
  let makeboolvar v =
    [Term.make_function a e vee [v; Term.make_function a e neg [v]]] in
  let makeintvar v = [Term.make_function a e eq [v;v]] in
  let makeconstraint x =
    let sort = Environment.find_sort x e in
    if sort = Alphabet.boolsort then makeboolvar (Term.make_var x)
    else makeintvar (Term.make_var x)
  in
  let vcs = List.flat_map makeconstraint vars in
  Rule.create lhs rhs (cs @ vcs)
;;

(* ========== processors ========== *)

let innermost_fix verbose prob =
  (* basic data *)
  if not (Dpproblem.get_innermost prob) then None else
  let a = Dpproblem.get_alphabet prob in
  let e = Dpproblem.get_environment prob in
  let graph = Dpproblem.get_graph prob in
  (* fix conditional self-loops (which interfere with the next step) *)
  let (graph, didsomething) = fix_conditional_recursion false a e graph in
  (* merge steps with conditional followup steps *)
  let tester_dps = find_all_tester_ids a graph in
  let rec update_graph didsomething graph =
    match find_simple_chaining tester_dps a e graph with
      | Some (id1, id2, chaining) ->
        let successors = Dpgraph.get_node_neighbours id2 graph in
        let graph = Dpgraph.remove_edge (id1, id2) graph in
        let graph = fst (Dpgraph.add_node a e chaining (Some id1)
               (Some id2) (Some (Dpproblem.get_rules prob)) graph) in
        update_graph true graph
      | None -> (graph, didsomething)
  in
  (* update the DP graph with conditional chaining *)
  let (graph, didsomething) = update_graph didsomething graph in
  (* give the information! *)
  let text =
    if not didsomething then "" else
    let probdesc = Dpproblem.tostring prob in
    let probdesc = probdesc ^ "This problem is converted using " ^
      "chaining, where edges between chained DPs are removed.\n" in
    if verbose then (Printf.printf "%s" probdesc ; "")
    else probdesc
  in
  (* and return! *)
  if didsomething then Some ([Dpproblem.update_graph prob graph], text)
  else None
;;

let gcnf_process verbose prob =
  (* basic data *)
  if not (Dpproblem.get_innermost prob) then None else
  let a = Dpproblem.get_alphabet prob in
  let e = Dpproblem.get_environment prob in
  let graph = Dpproblem.get_graph prob in
  let ids = Dpgraph.get_node_ids graph in
  let dps = List.map (fun i -> (i, Dpgraph.get_node_dp i graph)) ids in
  let logicsorts = Alphabet.find_logical_sorts a in
  (* symbols we'll need *)
  try
    let neg = Alphabet.get_not_symbol a in
    let vee = Alphabet.get_or_symbol a in
    let eq = Alphabet.get_equal_symbol a in
    (* updating the dependency pairs *)
    let update (graph, didsomething) (i, dp) =
      let vs = addable_output_variables_for (i, dp) graph a e logicsorts in
      if vs = [] then (graph, didsomething) else
      let newdp = add_logical_variables a e vee neg eq dp vs in
      (Dpgraph.replace_dp i newdp graph, true)
    in
    let (graph, didsomething) = List.fold_left update (graph, false) dps in
    (* give the information! *)
    let text =
      if not didsomething then "" else
      let probdesc = "This problem is converted by adding " ^
        "normal-form information where applicable.\n" in
      if verbose then (Printf.printf "%s" probdesc ; "")
      else probdesc
    in
    (* and return! *)
    if didsomething then Some ([Dpproblem.update_graph prob graph], text)
    else None
  with Not_found -> None
;;

