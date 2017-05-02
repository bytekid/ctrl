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
module Graph = Util.Graph.Make(Node);;

module VarSet = Set.Make(Variable);;
module FunSet = Set.Make(Function);;

(*** TYPES *******************************************************************)

type t = (int * Rule.t) list * Graph.t;;

exception Not_reducible;;

(*** FUNCTIONS ***************************************************************)

(**
 * This returns the current smt solver
 *)
let smt _ = Rewriter.smt_solver (Rewriter.get_current ());;

(** Returns the term a = b *)
let equality alphabet environment a b =
  let message = "Cannot do termination analysis: standard " ^
    "techniques require a (boolean) equality symbol = to use in " ^
    "the SMT-solver." in
  try
    (*
    Printf.printf "creating equality [%s] = [%s]\n"
      (Term.to_stringm alphabet environment a)
      (Term.to_stringm alphabet environment b) ;
    *)
    let eq = Alphabet.get_equal_symbol alphabet in
    Term.make_function alphabet environment eq [a;b]
  with _ -> failwith message
;;

(** if [empty] is the empty set of some kind, and [add] is a function
to add elements to a list, this function creates the set of all
elements of [lst] *)
let set_of_list add empty lst =
  let foldfun set elem = add elem set in
  List.fold_left foldfun empty lst
;;

(**
 * This returns a list of constraints which must definitely be
 * satisfied if some instance sγ of s reduces to some instance
 * tδ of t.
 *
 * If there is no way sγ can be reduced to tδ regardless of γ and
 * δ, then an exception Not_reducible is thrown.
 *
 * The varset "bound" contains a list of variables which are
 * considered bound, so are *not* instantiated by γ or δ; these
 * occur in both s and t.
 *)
let rec reduction_constraints bound a e s t l1 l2 defs =
  (* purely_logical term l returns true if all function symbols in
     term are logical, and all variables occur in the set l *)
  let rec purely_logical term l =
    if Term.check_logical_term a term = None then
      let v = set_of_list VarSet.add VarSet.empty (Term.vars term) in
      VarSet.is_empty (VarSet.diff v l)
    else false
  in
  (* bound_variables term returns the bound variables occurring in
  term *)
  let bound_variables term =
    if (VarSet.is_empty bound) then [] else
    List.filter (fun x -> VarSet.mem x bound) (Term.vars term)
  in
  (* if s = x in l1, then sγ is logical, so tδ must also be logical,
     and [[sγ]] = [[tδ]] must hold; thus, [[s = t]] is satisfiable *)
  let handle_logical_variable x =
    if Term.check_logical_term a t = None then [equality a e s t]
    else raise Not_reducible
  in
  (* if x not in l1, then sγ could be anything; thus, there are no
  constraints (we already checked that t contains no bound variables
  *)
  let handle_arbitrary_variable x = [] in
  (* defined symbols can reduce to anything, unless they're logical
  (but that can only happen in a non-standard system); if they are,
  then their reduct is logical as well, and has the same value *)
  let handle_defined f args =
    if purely_logical s l1 then (
      if Term.check_logical_term a t = None then [equality a e s t]
      else raise Not_reducible
    )
    else []
  in
  (* s = f(...), t = y (a variable) *)
  let handle_constructor_variable f y =
    (* f(...)γ ->* yδ with f notin Sigma_theory cannot hold if y
    must be instantiated by a variable or logical term, but otherwise
    gives no constraints *)
    if Alphabet.find_symbol_kind f a = Alphabet.Terms then (
      if (VarSet.mem y l2) || (VarSet.mem y bound) then raise Not_reducible
      else []
    )
    (* f(...)γ ->* yδ with f in Sigma_theory but f(...)γ not
    necessarily a logical term might hold - hard to tell, let's not
    pose constraints *)
    else if not (purely_logical s l1) then []
    (* f(...)γ ->* yδ with f(...)γ a logical term => yδ must be
    equal to it! *)
    else if Term.check_logical_term a t = None then [equality a e s t]
    else raise Not_reducible
  in
  (* s = ALL x.s or EX x.s, t = y (a variable); similar to the
  previous function with a calculation symbol *)
  let handle_quantifier_variable y =
    if VarSet.mem y bound then raise Not_reducible
    else if not (purely_logical s l1) then []
    else [equality a e s t]
  in
  (* s = ALL x.s', t = ALL y.t' (or similar with EX); we must have
  that s' ->> t'[y:=x] *)
  let handle_quantifier_pair x y arg1 arg2 =
    let subst = Substitution.of_list [(y, Term.make_var x)] in
    let arg2mod = Substitution.apply_term subst arg2 in
    reduction_constraints (VarSet.add x bound) a e arg2 arg2mod l1 l2 defs
  in
  (* concatenates reduction_constraints for all pairs in lst1, lst2 *)
  let all_equal lst1 lst2 =
    let f (t1, t2) = reduction_constraints bound a e t1 t2 l1 l2 defs in
    try List.flat_map f (List.combine lst1 lst2)
    with Invalid_argument _ -> raise Not_reducible
  in
  (* handles the case where s is headed by a non-defined calculation,
  and t is not a variable, nor headed by the same calculation *)
  let handle_calculation_no_var f args g params =
    if (params <> []) ||
       (Alphabet.find_symbol_kind g a = Alphabet.Terms) then
      raise Not_reducible (* t must be a value *)
    else if not (purely_logical s l1) then []
    else [equality a e s t]
  in
  (* constructor symbols cannot be reduced, so only match the same
  constructor, or variables *)
  let handle_calculation_or_constructor f args =
    match t with
      | Term.Var y -> handle_constructor_variable f y
      | Term.Fun (g, params) | Term.InstanceFun (g, params, _) ->
        if f = g then all_equal args params
        (* <misc> + <misc> -> value ==> OK *)
        else if Alphabet.find_symbol_kind f a = Alphabet.Logical then
          handle_calculation_no_var f args g params
        else raise Not_reducible
      | Term.Forall _ | Term.Exists _ -> raise Not_reducible
  in
  (* a quantifer only reduces to a similar quantifier *)
  let handle_quantifier universal x arg =
    if true then
    failwith ("In handle_quantifier, termination/dpgraph.ml -- " ^
              "functionality for quantifiers in right-hand side " ^
              "is implemented, but not tested.  Please remove " ^
              "failure, and test the implementation.") else
    match t with
      | Term.Fun _ | Term.InstanceFun _ -> raise Not_reducible
      | Term.Var y -> handle_quantifier_variable y
      | Term.Forall (y, arg2) ->
        if not universal then raise Not_reducible
        else handle_quantifier_pair x y arg arg2
      | Term.Exists (y, arg2) ->
        if universal then raise Not_reducible
        else handle_quantifier_pair x y arg arg2
  in
  (* immediate check: it isn't going to work if t contains bound
  variables which do not occur in s *)
  if not (List.is_subset (bound_variables t) (bound_variables s)) then
    raise Not_reducible ;
  (* Main functionality: split in the basic cases. *)
  match s with
    | Term.Var x ->
      if VarSet.mem x bound then
        (if s = t then [] else raise Not_reducible )
      else if VarSet.mem x l1 then handle_logical_variable x
      else handle_arbitrary_variable x
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      if FunSet.mem f defs then handle_defined f args
      else handle_calculation_or_constructor f args
    | Term.Forall (x, arg) -> handle_quantifier true x arg
    | Term.Exists (x, arg) -> handle_quantifier false x arg
;;

let test_reducible alf env rules dp1 dp2 =
  let constraint_data rule =
    let c = Rule.constraints rule in
    let vars = List.flat_map Term.vars c in
    let setvars = set_of_list VarSet.add VarSet.empty vars in
    (c, setvars)
  in
  let rhs1 = Rule.rhs dp1 in
  let (c1, l1) = constraint_data dp1 in
  let lhs2 = Rule.lhs dp2 in
  let (c2, l2) = constraint_data dp2 in
  let defs = set_of_list FunSet.add FunSet.empty
                         (List.map Rule.left_root rules) in
  try
    let reqs = reduction_constraints VarSet.empty alf env rhs1 lhs2 l1 l2 defs in
    let reqs = List.concat [reqs ; c1 ; c2] in
    let (solvable, _) = Solver.satisfiable_formulas reqs (smt ()) env in
    solvable <> Smtresults.UNSAT
  with Not_reducible -> false
;;

(**
 * This determines whether the dependency graph should have an edge
 * between nodes a and b.  Here, a and b are integers, to wit,
 * indexes of the array dparray which maps numbers to dependency
 * pairs.
 * The argument "alf" is the alphabet used for the dependency pairs
 * and rules, "env" is the environment for the variables, and
 * "rules" is the set of rules with respect to which we shall
 * endeavour to create a dependency graph
 *)
let should_have_edge alf env rules dparray a b =
  let e = Environment.empty 10 in
  let fn = Alphabet.fun_names alf in
  let rule1 = Rule.fresh_renaming (Array.get dparray a) env e fn in
  let rule2 = Rule.fresh_renaming (Array.get dparray b) env e fn in
  let result = test_reducible alf e rules rule1 rule2 in
  Environment.drop e ;
  if result then [(a,b)]
  else []
;;

(**
 * returns a "graph" containing the given dependency pairs as nodes,
 * with edges set up with respect to the rules
 *)
let create a e dps rules =
  let dparray = Array.of_list dps in
  let numbers = List.mapi (fun i _ -> i) dps in
  let graph = Graph.generate (should_have_edge a e rules dparray) numbers in
  let ndps = List.mapi (fun i rule -> (i, rule)) dps in
  (ndps, graph)
;;

(**
 * returns a subgraph of (ps,graph) containing only the given
 * dependency pairs
 *)
let subgraph (ps,g) dp =
  let dpokay (num, d) = List.mem d dp in
  let goodnodes = List.filter dpokay ps in
  let oknum = List.map fst goodnodes in
  (goodnodes, Graph.restrict oknum g)
;;

(** removes nodes and edges not part of an SCC *)
let get_sccs (dps,graph) =
  let sccs = Graph.sccs ~trivial:false graph in
  let restriction scc = Graph.restrict scc graph in
  let graphs = List.map restriction sccs in
  let create_new subgraph =
    let nodeincluded (num, _) = Graph.mem_node num subgraph in
    let subdps = List.filter nodeincluded dps in
    (subdps, subgraph)
  in
  List.map create_new graphs
;;

(** returns the dependency pairs in the given graph *)
let get_dps (dps, graph) = List.map snd dps;;

(** returns ids for the nodes *)
let get_node_ids (dps, graph) = Graph.nodes graph;;

(** returns neighbouring ids for the nodes *)
let get_node_neighbours id (dps, graph) = Graph.successors id graph;;

(** returns the DP associated to a given node *)
let get_node_dp id (dps, graph) = List.assoc id dps;;

(** returns the number of nodes *)
let size_nodes (dps, _) = List.length dps;;

(** removes the given edge from the graph *)
let remove_edge edge (dps, graph) = (dps, Graph.remove_edge edge graph);;

(** adds the given edge to the graph *)
let add_edge edge (dps, graph) = (dps, Graph.add_edge edge graph);;

(** removes the given node from the graph *)
let remove_node node (dps, graph) =
  let dps = List.filter (fun (x,_) -> node <> x) dps in
  let graph = Graph.remove_node node graph in
  (dps, graph)
;;

let replace_dp id dp (dps, graph) =
  let update (i, p) =
    if i = id then (i, dp)
    else (i, p)
  in
  (List.map update dps, graph)
;;

(** returns nodes paired with their followers *)
let get_relations (dps, graph) =
  let nodes = Graph.nodes graph in
  let add_neighbours node = (node, Graph.successors node graph) in
  let data = List.map add_neighbours nodes in
  let nodetodp i = List.assoc i dps in
  let update (i, lst) = (nodetodp i, List.map nodetodp lst) in
  List.map update data
;;

(* adds a node, with edges to the given ids (if checkedges is true,
then each of these will be checked to make sure there *actually* is
an edge there first) *)
let add_node alf env dp pred succ checkedges (dps, graph) =
  (* step 0: prepare extra data *)
  let newenv = Environment.empty 10 in
  let fn = Alphabet.fun_names alf in
  let dprenamed = Rule.fresh_renaming dp env newenv fn in
  (* step 1: create an ID and add the DP into the graph *)
  let existing = get_node_ids (dps, graph) in
  let alter = List.range 0 ((List.length existing) + 1) in
  let newid = List.hd (List.diff alter existing) in
  let rec ordered_insert = function
    | [] -> [(newid, dp)]
    | (id, d) :: tl as lst ->
      if newid > id then (id, d) :: ordered_insert tl
      else (newid, dp) :: lst
  in
  let dps = ordered_insert dps in
  let graph = Graph.add_node newid graph in
  (* step 2: create outgoing edges *)
  let successors =
    match succ with
      | Some id -> Graph.successors id graph
      | None -> if checkedges = None then [] else existing
  in
  let add_edge_to g neighbour =
    match checkedges with
      | None -> Graph.add_edge (newid, neighbour) g
      | Some rules ->
        let otherdp = List.assoc neighbour dps in
        let otherdp = Rule.fresh_renaming otherdp env newenv fn in
        if test_reducible alf newenv rules dprenamed otherdp then
          Graph.add_edge (newid, neighbour) g
        else g
  in
  let graph = List.fold_left add_edge_to graph successors in
  (* step 3: create incoming edges *)
  let predecessors =
    match pred with
      | Some id ->
        let edges = Graph.edges graph in
        let relevant = List.filter (fun (_,x) -> x = id) edges in
        List.map fst relevant
      | None -> if checkedges = None then [] else existing
  in
  let add_edge_from g neighbour =
    match checkedges with
      | None -> Graph.add_edge (neighbour, newid) g
      | Some rules ->
        let otherdp = List.assoc neighbour dps in
        let otherdp = Rule.fresh_renaming otherdp env newenv fn in
        if test_reducible alf newenv rules otherdp dprenamed then
          Graph.add_edge (neighbour, newid) g
        else g
  in
  let graph = List.fold_left add_edge_from graph predecessors in
  (* step 4: finishing off *)
  Environment.drop newenv ;
  ((dps, graph), newid)
;;

let tostringm (dps, graph) =
  let printnode node =
    let successors = Graph.successors node graph in
    let succs = List.implode Node.to_string ", " successors in
    "  " ^ (Node.to_string node) ^ " -> " ^ succs
  in
  let printdp (num, rule) =
    let printedrule = Printer.to_string_rule rule in
    "  " ^ (string_of_int num) ^ ") " ^ printedrule
  in
  let sortednodes = List.sort compare (Graph.nodes graph) in
  let graphprint = List.implode printnode "\n" sortednodes in
  let dpprint = List.implode printdp "\n" dps in
  graphprint ^ "\nWhere:\n" ^ dpprint ^ "\n"
;;

(** prints the graph *)
let printfm (dps, graph) =
  Printf.printf "%s" (tostringm (dps, graph))
;;

(** prints just the numbers of the nodes of the given graph *)
let to_string_raw (dps, graph) =
  let print (num, _) = string_of_int num in
  let rec to_string_list = function
    | [] -> ""
    | [pair] -> print pair
    | head :: tail -> (print head) ^ ", " ^ (to_string_list tail)
  in
  "{ " ^ (to_string_list dps) ^ " }"
;;

