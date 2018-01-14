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

(** Modules for completion in Constrained Rewriting
@author Sarah Winkler
@since  Jan  02 2018 *)

open Ctrs;;

(** Provides the main files for completion. *)

(*** MODULES ******************************************************************)


(** {2 Module KB} *)

(** This module implements standard completion. *)
module KB : sig
  (** {3 Constructors} *)
  type result = (Ctrs.Rule.t * Ctrs.Environment.t) list

  val standard : bool -> Trs.t -> bool -> result option
  (** [run v trs] returns a completed TRS if possible *)

  val ordered : bool -> Trs.t -> bool -> (result * result) option
  (** [run v trs] returns a ground completed TRS if possible *)
end
