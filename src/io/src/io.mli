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

(** Main Constrained Rewriting Files
@author Cynthia Kop
@since  Aug  1 2012 *)

open Ctrs;;

(** Provides the main files for the tool: input, output and program flow. *)

(*** MODULES ******************************************************************)

(** {2 Module Cleaner} *)

(** This module is used to clean up ugly input, for instance adding
x = x constraints for variables of a logical sort for which no normal
forms of non-logical sorts exist *)
module Cleaner : sig
  val add_nf_constraints : bool -> Trs.t -> unit
  (** [add_nf_constraints innermost trs] adds constraints x = x to
  all the rules of [trs] where x is a variable of logical sort, and
  one of the following holds:
  - [innermost] is true and the only normal forms of this sort are
    values (this is not fully supported yet, but may be in the
    future)
  - [innermost] is false and the only terms of this sort are fully
    logical

  Note that in a non-innermost system, adding normal form constraints
  is only valid if we are allowed to impose a reduction strategy that
  logical terms are normalised immediately.  That is:
  * the system must be standard, so there are no non-value logical
    symbols in the left-hand sides of rules
  * we are interested only in the reduction of ground terms (or
    perhaps constrained terms)
  * we are not interested in complexity, or only in complexity where
    the calculation steps are not considered of interest.
  *)
  val simplify : Trs.t -> (Function.t -> bool) ->
                 (Term.t -> string) -> string
  (** [simplify canchange print trs] combines rules, and removes
  unnecessary arguments and function symbols in [trs]; if [canchange
  f] returns false, then that symbol (and its rules) will not be
  removed or changed. The return value is a string representing both
  the updated alphabet (in so far as symbols are actually used in the
  rules) and the updated rules, in the format as used for the input.
  The [print] argument is used to print both sides of rules. *)

  val simplify_trs : Trs.t -> (Function.t -> bool) -> unit
  (** [simplify_trs trs canchange] does the simplification steps from
  [simplify] directly on an LCTRS, changing the original; after that,
  add_nf_constraints is automatically called. *)
end

(** This module is used for pretty printing.  It outputs only when flushed
(error output is printed immediately, however).  The printer assumes that there
is a current TRS, and all actions use this TRS.  Moreover, before printing
anything using the printer, you should use set_style to indicate how the output
is to be printed. *)
module Printer : sig
  type style = Plain
  type aligns = L | R | C

  val set_style : style -> unit

  val debug_printf : ('a, out_channel, unit) format -> 'a

  val print_alphabet :  Alphabet.symbolkind -> unit
  (** [print_alphabet kind] prints elements of the alphabet with the symbol
  kind [kind]. If [kind] is Both, then all elements are printed. *)
  val print_current_rules : unit -> unit
  val print_term : Term.t -> unit
  val print_constrained_term : (Term.t * Term.t) -> unit
  val print_rule : Rule.t -> Environment.t -> string -> string -> unit
  (** print_rule rule env arrz constraints] prints the rule in the
  following form: lhs [arrz] rhs [constraints] constraintlist *)
  val print_rules : (Rule.t * Environment.t) list -> string -> string -> unit
  (** [print_rules lst arrz constraints] prints all rules in [lst] in
  the following form: lhs [arrz] rhs [constraints] constraintlist; the rules
  are formatted in table lay-out *)
  val print_term_reduction : Term.t list -> unit
  val print_constrained_reduction : (Term.t * Term.t) list -> unit
  val print_text : string -> unit
  val print_newline : unit -> unit

  val print_list : ('a -> string list) -> aligns list -> 'a list -> unit
  (** [print_list f al lst] prints the elements of [lst] in a table,
  using the printing function [f].  Here, [f] should always return a list
  of, say, n strings (with n fixed), which are placed in a table formatted
  with aligns [al]; [al] must also have length n. *)
  val to_string_term : Term.t -> string
  (** [to_string_term term] returns a string representation of [term] *)
  val to_string_constraints : Term.t list -> string
  (** [to_string_constraints term] returns a string representation of
  [constraints] *)
  val to_string_rule : Rule.t -> string
  (** [to_string_rule rule] returns a string representation of [rule] *)

  val flush : unit -> unit

  val add_infix_symbol : string -> int -> bool -> unit
  (** [add_infix_symbol f p b] stores [f] as an infix symbol for
  any future prints, which has priority [p].  If [b] is true,
  then [f] is left-associative (or not associative at all),
  otherwise right-associative.
  *)
end
(** {2 Module Reader} *)

(** This module is used to read (part of) a conditional CTRS from string or
from an input file. *)
module Reader : sig
  type query = NormalForm of Term.t |
               ConstrainedNormalForm of Term.t * Term.t |
               Termination of bool |
               Nontermination |
               Completion of (Function.t list * bool * bool) |
               Confluence |
               SimplifiedLctrs of Function.t list * String.t |
               Equivalence of Rule.t list |
               AssistEquivalence of Rule.t list |
               NoQuery |
               Smt of Term.t list

  val read_file : string -> query * Function.t list option
  (* [read_file fname] creates a TRS, sets it as current, and then
  reads the file with the given name into this TRS.  If anything goes
  wrong, an error describing the problem is thrown.  If all goes
  right, the query suggested by the file is returned, along with a
  requirement for advance simplification. *)
  val read_alphabet : string -> bool -> unit
  (* [read_alphabet txt b] reads a list of function symbols (possibly
  with sort declarations) into the current alphabet; if [b] is true
  the symbols are read into the logical alphabet, otherwise into the
  term alphabet *)
  val read_rules : string -> unit
  (* [read_rules txt] reads a list of rules into the current TRS.  No
  infix symbols may be used, since these are not stored anywhere. *)
  val read_term : string -> Term.t
  (* [read_term txt] reads a term from string, assuming all symbols
  in the term are declared, and returns the result.  Do not use infix
  symbols in [txt]. *)
end
(** {2 Module Printer} *)


