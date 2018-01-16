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

(** Modules to do Constrained Rewriting
@author Cynthia Kop
@since  Oct  12 2012 *)

open Ctrs;;
open Smt;;

(** Provides the main files to do rewriting, such as the SMT-solver and
rewriter. *)

(*** MODULES ******************************************************************)

(** {2 Module Rewriter} *)

(** This module is used to rewrite terms in a constraint TRS *)
module Rewriter : sig
  type t

  (** {3 Constructors and Destructors} *)

  val create : Solver.t -> t
  (* [create smt] creates a new rewriter, using the SMT-solver [smt]. *)
  val smt_solver : t -> Solver.t
  (* [smt_solver t] returns the SMT-solver used by the rewriter [t]. *)

  (** {3 Reducing} *)

  val calc_reduce : Term.t -> Position.t -> Term.t option
  (** [calc_reduce t p] reduces term [t] at position [p] with a
  calculation step.  If the term cannot be calc-reduced at this
  position, then None is returned. The alphabet is taken from the
  current TRS. *)
  val calc_normalise : Term.t -> Term.t
  (** [calc_normalise t] reduces [t] with calculation steps until
  this is no longer possible *)
  val rule_reduce : Term.t -> Position.t -> (Rule.t * Environment.t)
    list option -> bool -> Term.t option
  (** [rule_reduce t p rules calc] reduces [t] at position [p] with
  a rule in in [rules] which is applicable (a random applicable rule
  is chosen).  If [calc] is true, then the result is moreover
  normalised for calculations that might have been created by the
  reduction, and also for errors if the rule used has the form l ->
  err [...].  If none of the given rules is applicable, then None
  is returned. If [rules] = None, then the rules in the current
  TRS are used.  Note that even if [calc] is true, no error
  reductions are done, because rules are not supposed to create errors
  below the top. *)

  val reduce_to_normal : Term.t -> Term.t list
  (** [reduce_to_normal t] reduces [t] to a normal form using an
  innermost strategy; for the moment, this only works if the system
  has no conditions or normal-form constraints. *)

  (** {3 Current Rewriter} *)
  
  val set_current : t -> unit
  val has_current : unit -> bool
  val get_current : unit -> t
end

(** {2 Module Constrainedrewriter} *)

(** This module is used to rewrite constrained terms in a constraint TRS.
For any rewriting steps, it always uses the current Rewriter. *)
module Constrainedrewriter : sig
  type cterm = Term.t * Term.t

  val assume_value_instantiations : bool ref
  (** if [assume_value_instantiations] is set to true, then we assume
  that constrained terms with a sort occurring in Sigma_logic can only
  be instantiated by values, even if they do not occur in the
  constraint of the constrained term; note that this should not be
  used in a system with errors for sorts which also admit values! *)
  val make_cterm : Term.t -> Term.t list -> Alphabet.t option -> cterm
  (* [make_cterm s c a] returns a constrained term s [cs], where [cs]
  is the conjunction of all elements of [c].  The given alphabet [a]
  must contain a conjunction operator; if not given, the alphabet for
  the current TRS is used (and this alphabet must contain conjunction)
  *)
  val restore_from_cterm : cterm -> Alphabet.t option ->
    (Term.t * Term.t list)
  (* [restore_from_cterm t a] is the reverse of [make_cterm]: given a
  constrained term, splits the constraint up in as many conjunctive
  parts as possible. *)
  val calc_reduce : cterm -> Position.t -> Alphabet.t option ->
    Environment.t option -> cterm option
  (* [calc_reduce s p a e] performs a calculation step at the given
  position and returns the result, or returns None if [t] cannot be
  calc-reduced at that position. *)
  val calc_normalise : cterm -> Alphabet.t option ->
    Environment.t option -> cterm
  (* [calc_normalise s a e] normalises [s] with constrained
  calculation steps until this is no longer possible, and returns the
  result; the given environment is used to choose fresh variables, and
  if None is given, the main environment of the current TRS is used *)

  val simplify_constrained_term : ?trs:Ctrs.Trs.t -> cterm -> bool -> cterm
  (* [simplify_constrained_term s strong] returns a simplified
  version of [s], where variables whose values are known are
  instantiated.  If [strong] is set to true, then we use the smt
  solver to determine whether a value is uniquely determined,
  otherwise we only check for equalities. *)

  val trivial_constraint_simplification : Alphabet.t -> Environment.t
    -> Term.t -> Term.t
  (** [trivial_constraint_simplification a e phi] replaces [phi] by
  an equivalent constraint [psi] which contains fewer obvious
  conjuncts like x = x *)

  val rule_reduce : cterm -> Environment.t -> Position.t ->
    (Rule.t * Environment.t) list -> bool ->
    ?forbidden_variables:Variable.t list list ->
    ?subst_allowed:((Variable.t -> Term.t -> bool) list) ->
    ?shuffle:bool ->
    ?extra_constraints:(Alphabet.t -> Environment.t -> Term.t list ->
    Term.t list -> Term.t list -> Term.t list) -> bool -> cterm option
  (** [rule_reduce t e p rules calc forbidden allowed shuffle extra general]
  reduces the constrained term [t] at position [p] with one of the
  rules in [rules]; here, [rules] contains tuples (rule, rule
  environment).  The result is calc- and error-reduced afterwards if
  [calc] is set to true (only reductions relevant to the redex are
  done).  If nothing is applicable, then None is returned.  [shuffle]
  indicates whether the rules should be shuffled before applying; if
  false, always the first applicable rule will be used (by default,
  this is set to [true]).
  If [general] = false, then this may not give the most general answer:
  a reduction which uses existing variables rather than fresh ones is
  preferred (e.g. a rule f(x) -> g(y,z) [y+z = x] will reduce a
  constrained term f(x) [x = 2+y] to g(2,y) [x=2+y], not to
  g(u,v) [x=2+y,u+v=x]).  This is a replacement with substitution
  gamma = [x->x, y->2, z->y].
  To exert some control over the chosen replacement, the
  [forbidden] and [allowed] variables affect gamma, but only where the
  variables not occurring in the left-hand side of the rule are
  concerned.  [forbidden] and [allowed], if supplied, must be the same
  length as [rules].  If the Nth element of [forbidden] contains
  variable X, then when rule N is applied, the variable X will not be
  in the domain of gamma (so it will be mapped to itself).  If the
  Nth element of [allowed] is a function f such that f(x,s) returns
  false, then gamma(x) will not be s (note: for fresh variables y,
  f(x,y) should return true!).
  If [extra] is supplied, then once a reduction has been found, this
  function is called with the current alphabet, [e], and three lists
  of constraints over [e]: first the constraints [phi] used in [t =
  c phi], second, if the rule l -> r [psi] was used with phi => EX
  vars [psi gamma[, then the constraints over fresh variables [vars]
  in psi gamma (these constraints will be added to the returned
  cterm), and third the remaining constraints in psi gamma (which
  are implied by phi).
  If [general] = true, then the most general answer is always
  preferred (but it may not be possible to find such an answer), and
  [forbidden] and [allowed] are both ignored.
  *)

  val trs_reduce : ?trs:Trs.t -> cterm -> Position.t -> bool ->
    bool -> cterm option
  (** [trs_reduce trs t p calc general] acts like [rule_reduce t e
  p rules calc general] where [e] is the main environment of [trs],
  [rules] are the rules of [trs], the rules are shuffled, and
  substitution choices are not restricted.  The default choice for
  [trs] is the current trs. *)

  val rule_reduce_single_env : cterm -> Environment.t ->
    Position.t -> Rule.t list -> bool ->
    ?forbidden_variables:Variable.t list list ->
    ?subst_allowed:((Variable.t -> Term.t -> bool) list) ->
    ?shuffle:bool ->
    ?extra_constraints:(Alphabet.t -> Environment.t -> Term.t list ->
    Term.t list -> Term.t list -> Term.t list) -> bool -> cterm option
  (** exactly like rule_reduce, except all rules are assumed to use
  variables in the given environment [e] *)

  val reduce_to_normal : cterm -> bool -> bool -> cterm list
  (** [reduce_to_normal t general simp] reduces the constrained term
  [t] until we can no longer figure out a step to do.  If [simp] is
  true, then the rule is put in strong simplified form before every
  rule step; if not, then no simplification is done (which is not a
  problem if the rules don't have values in the left-hand sides).
  If [general] is set to false, then the reducts may not be the most
  general, as in the rule_reduce function.
  *)

  val rewrite_bounded :
  bool -> bool -> bool -> Trs.t -> int -> cterm -> (cterm * bool) list

  val equivalent_cterms: Alphabet.t -> Environment.t -> Term.t -> Term.t ->
    Term.t list -> bool

  val equalities_into_rule: Alphabet.t -> Environment.t -> Rule.t -> Rule.t
end

