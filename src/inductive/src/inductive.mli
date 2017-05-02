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

(** Modules for inductive theorem proving in Constrained Rewriting
@author Cynthia Kop
@since  Feb  22 2012 *)

open Ctrs;;

(** Provides the main files for inductive theorem proving. *)

(*** MODULES ******************************************************************)

(** {2 Module Completenesschecker} *)

(**
 * This module checks whether a system is fully reduction-complete,
 * or reduction-complete for given terms.
 *)
module Completenesschecker : sig
  val check_value_safe : Trs.t -> bool
  (** [check_value_safe trs] returns whether the sorts in Sigmalogic
  of [trs] are not used for other constructors
  @raise Failure if not all function symbols in the trs have a symbol
  kind set. *)
  val check_value_sound : Trs.t -> bool
  (** [check_value_sound trs] returns whether the sorts in Sigmalogic
  of [trs] all admit values
  @raise Failure if not all function symbols in the trs have a symbol
  kind set. *)
  val check_constructor_sound : Trs.t -> bool
  (** [check_constructor_sound trs] returns whether all sorts in
  Sigmalogic of [trs] are inhabited by ground constrcutor terms *)
  val check_left_value_free : Trs.t -> bool
  (** [check_left_value_free trs] returns whether the rules in [trs]
  avoid values in the left-hand sides *)
  val make_left_value_free : Trs.t -> unit
  (** [make_left_value_free trs] makes [trs] updates [trs] to be
  left-value-free, without affecting the rewrite relation *)
  val precheck : Trs.t -> string option
  (** [precheck trs] checks whether [trs] is left-linear, value-sound
  and constructor-sound, and if so, makes it left-value-free and
  returns None.  If not, a string is returned describing at least one
  issue for sufficient completeness *)
  val quasi_reductive : Trs.t -> bool
  (** [quasi_reductive trs] aborts with Failure if one of the
  conditions for [precheck trs] fails, and otherwise returns whether
  every ground term in [trs] is either a constructor term or
  reducible *)
  val completely_reducible : Trs.t -> Term.t list -> string option
  (** [completely_reducible trs terms] returns None if [trs] is
  "completely reducible" with respect to [terms], and otherwise
  returns a message indicating which symbols are the problem.  Here,
  "completely reducible" means that any ground term built from
  constructors, symbols that occur in [terms] and symbols in the
  right-hand sides of rules, is either a constructor-normal form
  or reduces *)
end

(** {2 Module Proverbase} *)

(** This module is the basis for the manual and automatic provers.
It contains shared functionality to do all the steps. *)
module Proverbase : sig
  type equation
  type cterm

  val get_data : unit -> Alphabet.t * Environment.t * Rule.t list
  val get_special_vars : unit -> Variable.t list

  val precheck : (string -> unit) -> (unit -> unit) -> Trs.t ->
                 Rule.t list -> bool -> unit
  val initialise : Trs.t -> Rule.t list -> Trs.t option * equation list

  val try_deletion : equation -> bool option
  val try_eqdelete : equation -> equation option
  val try_constructor : equation -> (equation * Position.t) list option
  val try_anti_constructor : equation -> bool
  val try_all_logical : equation -> bool
  val try_swap : equation -> equation
  val try_riddance : equation -> (string list * bool) option
  val try_trivial : equation -> equation list
  val try_calculate : equation -> Position.t -> equation option
  val try_simplify_main : cterm -> Rule.t -> Position.t -> cterm option
  val try_simplify : equation -> Rule.t -> Position.t -> equation option
  val try_case : equation -> Position.t -> bool -> equation list option
  val try_expand : bool -> equation -> Position.t -> Rule.t list ->
                   (equation list * Rule.t) option
  val try_generalise : equation -> Variable.t list -> equation
  val try_alter_constraint : equation -> equation

  val goal_positions : equation -> (bool * (Position.t * Function.t)) list
  val to_string_position : Position.t -> string
end

(** {2 Module Manualprover} *)

(** This module handles automatic theorem proving. *)
module Manualprover : sig
  type answer = YES | NO | MAYBE

  val run : Trs.t -> Rule.t list -> answer
  (** [run trs eqs] attempts inductive theorem proving where the user
  has to indicate which rule to apply in every step *)
end

(** {2 Module Theoremprover} *)

(** This module is used to interface with the SMT-solver. *)
module Theoremprover : sig
  type answer = YES | NO | MAYBE

  (** {3 Constructors} *)

  val run : Trs.t -> Rule.t list -> answer * (unit -> unit)
  (** [run trs eqs] returns YES if for each (s,t,cs) in [eqs],
  s = t [cs] can be derived, and MAYBE if it cannot be derived for
  any element of [eqs]; the returned function will, when invoked,
  print an explanation of how the result is acquired *)
end

