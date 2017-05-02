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

(** Modules to analyse confluence of Constrained Rewriting
@author Cynthia Kop
@since  Feb  22 2012 *)

(** Provides the main files for confluence analysis. *)

open Ctrs;;

(*** MODULES ******************************************************************)

(** {2 Module Confluencechecker} *)

(** This module is used to interface with the SMT-solver. *)
module Confluencechecker : sig
  type criticalpair = Term.t * Term.t * Term.t list

  (** {3 Constructors} *)

  val constructor_trs : Trs.t -> bool
  (* [constructor_trs t] returns whether [t] is a constructor TRS, so defined
  symbols occur only at the root *)
  val critical_pair : Rule.t -> Rule.t -> Alphabet.t -> Environment.t ->
                      Position.t -> criticalpair list
  (* [critical_pair rule1 rule2 a e p] returns the empty list if
  there is no critical pair between rule1 and rule2 at position [p]
  of the left-hand side of [rule1], or [(u,v,psi)] if there is one
  critical pair (u,v,psi) at this position (it is impossible to have
  more than one).
  To call this function, it is required that both rules use entirely
  distinct variables, all of which are in [e]; all their function
  symbols should occur in [a], and they may only use logical
  constraints.
  *)
  val critical_pairs : (Rule.t * Environment.t) list ->
                       criticalpair list * Environment.t
  (* [critical_pairs rules] returns a list of all critical pairs
  between pairs of rules and critical pairs for calculations, and an
  environment for the variables in those critical pairs. *)
  val orthogonal : Trs.t -> bool
  val weak_orthogonal : Trs.t -> bool
end

