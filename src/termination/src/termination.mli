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

(** Modules to analyse termination of Constrained Rewriting
@author Cynthia Kop
@since  Feb  22 2012 *)

open Ctrs;;

(** Provides the main files for termination analysis. *)

(*** MODULES ******************************************************************)

(** {2 Module Dpproblem} *)

module Dpgraph : sig
  type t

  val create : Alphabet.t -> Environment.t -> Rule.t list -> Rule.t list -> t
  (** [create a e dps rules] returns a dependency graph containing the
  dependency pairs [dps], with connections given by [rules] *)
  val subgraph : t -> Rule.t list -> t
  (** [subgraph g p] returns the subgraph of [g] containing only the
  dependency pairs occurring in [p]; here [p] has to be a subset of
  the nodes of [g], with variables not renamed *)
  val get_dps : t -> Rule.t list
  (* [get_dps graph] returns the dependency pairs in the given graph *)
  val get_sccs : t -> t list
  (** [get_sccs graph] returns subgraphs of [graph] which correspond
  to strongly connected components *)
  val get_node_ids : t -> int list
  (** [get_node_ids graph] returns integer indexes for all nodes in
  the graph; the corresponding pair can be queried using get_node_dp *)
  val get_node_dp : int -> t -> Rule.t
  (** [get_node_dp id graph] returns the dependency pair corresponding
  to a node index *)
  val get_node_neighbours : int -> t -> int list
  (** [get_node_neighbours id graph] returns the IDs of the nodes to
  which an edge goes from [id] in the graph *)
  val remove_edge : (int * int) -> t -> t
  (** [remove_edge (i,j) graph] returns the DP graph with the given
  edge removed (indicating that we no longer consider DP chains where
  the pair with id [i] is followed by [j]) *)
  val remove_node : int -> t -> t
  (* [remove_node i graph] removes the node with id [i] *)
  val add_edge : (int * int) -> t -> t
  (* [add_edge edge] adds the given edge *)
  val add_node : Alphabet.t -> Environment.t -> Rule.t ->
                 int option -> int option -> Rule.t list option -> t ->
                 t * int
  (** [add_node a e dp pred succ rules graph] returns [graph] with
  node [dp] added; from [dp] there are edges to:
  - all nodes in [succ] if [succ] is not None and [check] is None
  - all nodes in [succ] such that a reduction to them from [dp] is
    possible if [succ] is not None and [rules] contains the rules to
    reduce with
  - all nodes for which a reduction from [dp] is possible if [succ]
    is None and [rules] contains the rules to reduce with
  - no nodes if [succ] is None and [check] is None
  The incoming nodes are defined by [pred] in the same way. The
  return value is the updated graph, with the id of the new node. *)
  val replace_dp : int -> Rule.t -> t -> t
  (* [replace_dp id dp] replaces the dependency pair associated to
  [id] by [dp], while preserving incoming and outgoing edges *)
  val size_nodes : t -> int
  (** [size_nodes graph] returns the number of nodes in [graph] *)
  val tostringm : t -> string
  (* [printfm graph] prints [graph] to a string *)
  val printfm : t -> unit
  (* [printfm graph] prints [graph] *)
  val to_string_raw : t -> string
  (* [to_string_raw graph] returns a string listing the nodes in the
  given graph (this is only useful if you have previously printed a
  supergraph fully) *)
end

module Dpproblem : sig
  type t

  val full_problem : Alphabet.t -> Environment.t -> Rule.t list -> Rule.t list -> t
  (* [full_problem a e P R] creates a dependency pair problem (P,R,full),
  which keeps track of alphabet [a] and environment [e] (over which these
  [P] and [R] must necessarily be built). *)
  val innermost_problem : Alphabet.t -> Environment.t -> Rule.t list -> Rule.t list -> t
  (* [innermost_problem a e P R] creates a dependency pair problem
  (P,R,in), with [a] and [e] as in full_problem.  Note that the
  innermost strategy is considered not with respect to [R], but with
  respect to the underlying set of rules in the DP framework *)

  val get_dps : t -> Rule.t list
  (* [get_dps (P, R)] returns P *)
  val get_rules : t -> Rule.t list
  (* [get_rules (P, R)] returns R *)
  val get_innermost : t -> bool
  (* [get_innermost prob] returns whether [prob] is an innermost problem *)
  val get_alphabet : t -> Alphabet.t
  (* [get_alphabet prob] returns the alphabet over which [prob] is defined *)
  val get_environment : t -> Environment.t
  (* [get_environment prob] returns the environment over which [prob] is defined *)

  val set_dps : Rule.t list -> t -> t
  (* [set_dps (P, R) P' returns (P', R) *)
  val set_rules : Rule.t list -> t -> t
  (* [set_dps (P, R) R' returns (P, R') *)

  val graph_proc : bool -> t -> (t list * string) option
  (* [graph_proc verbose prob] applies the dependency graph processor on the
  given problem *)

  val tostring : t -> string
  val fprintfm : out_channel -> t -> unit
  val printfm : t -> unit
end

(** {2 Module Dpframework} *)

module Dpframework : sig
  type t
    (* represents a collection of dependency pair problems, along with
    an alphabet and underlying TRS *)

  val generate : Trs.t -> bool -> t
  (* [generate trs full ] creates a dependency pair framework based on
  the alphabet of [trs] extended with marked function symbols, and with
  a single dependency pair problem (DP(R),R); if [full] is true, then
  this is a full dependency pair problem, otherwise it is an innermost
  one.
  Note that the set of rules R in the dependency pair problem is
  CALCULATION-FREE and, consequently, not necessarily regular.
  *)

  val values_assumed : t -> Dpproblem.t -> Sort.t -> bool
  (* [values_assumed w prob sort] returns whether we may assume that
  dependency pair arguments of sort [sort] are always values; we can
  do this in the innermost case, provided the only constructors of
  sort [sort] are values *)

  val get_alphabet : t -> Alphabet.t
  (* [get_alphabet w] returns the alphabet used in the dependency pair
  framework [w]; this alphabet may be extended without affecting
  anything, but no symbols may be removed *)
  val get_environment : t -> Environment.t
  (* [get_environment w] returns the environment used in framework
  [w] (all rules and dependency pairs necessarily use the same);
  this environment may be extended without affecting anything, but no
  variables may be removed *)
  val solved : t -> bool
  (* [solved w] returns true if there are no unsolved dependency pair
  problems associated with the framework [w] *)
  val pop : t -> (Dpproblem.t * t)
  (* [pop w] returns the first unsolved D problem associated with the
  DP framework [w], assuming there is one; the second return value is
  a modified copy of [w] which does not have this problem anymore
  @raise Failure "pop" if there are no dependency pair problems
  associated to [w]; if this is the case, [solved w] will return
  true *)
  val push : t -> Dpproblem.t -> t
  (* [push w problem] adds [problem] to the framework [w]; the
  variables and function symbols in [problem] must all appear in
  the environment and alphabet associated with the given
  framework *)
  val push_all : t -> (Dpproblem.t list) -> t
  (* [push_all w problems] pushes all problems in [problems] to [w] *)
end

(** {2 Module Chainer} *)

module Chainer : sig
  val innermost_fix : bool -> Dpproblem.t -> (Dpproblem.t list * string) option
  (* [innermost_process verbose prob] applies the chaining processor
  for innermost dependency pair problems to [prob]; this only needs
  to be done once *)
  val gcnf_process : bool -> Dpproblem.t -> (Dpproblem.t list * string) option
  (* [gcnf_process verbose prob] applies the ground constructor normal form
  processor to [prob]: this adds ground constructor normal form (and value)
  constraints to all dependency pairs where this can be safely done. For
  now, this is done only for the innermost case, although in confluent systems
  it would also be safe in the full termination case. *)
end

(** {2 Module Valuecriterion} *)

module Valuecriterion : sig
  val basic_process : bool -> Dpproblem.t -> (Dpproblem.t list * string) option
  (* [basic_process verbose prob] applies the basic value criterion
  processor on the given problem; this will attempt to orient values
  of those sorts where a well-founded relation is set, not especially
  the integers! *)
  val reverse_process : bool -> Dpproblem.t -> (Dpproblem.t list * string) option
  (* [reverse_process verbose prob] applies the reversed value
  criterion processor on the given problem: it tries to find a
  projection of the form x - y; this only applies to integer
  values *)
  val extended_process : bool -> Dpproblem.t -> (Dpproblem.t list * string) option
  (* [extended_process verbose prob] applies the extended value
  criterion processor on the given problem; this only applies to
  integer values*)
end

(** {2 Module Subtermcriterion} *)

module Subtermcriterion : sig
  val process : bool -> Dpproblem.t -> (Dpproblem.t list * string) option
  (* [process verbose prob] applies the subterm criterion
  processor on the given problem *)
end

(** {2 Module Terminator} *)

(** This module is used to interface with the SMT-solver. *)
module Terminator : sig
  type possible_results = TERMINATING | NONTERMINATING | UNKNOWN

  (** {3 Constructors} *)

  val check : bool -> bool -> Trs.t -> possible_results * string
  (* [check verbose full trs] analyses full or innermost termination
  of [trs] *)
  val check_extended : bool -> Trs.t ->
                       (Trs.rule * Environment.t) list ->
                       possible_results
  (* [check_extended verbose trs rules] analyses termination of the
  given trs appended with the additional rules *)
end

