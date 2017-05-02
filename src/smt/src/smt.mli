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

(** Modules to handle SMT-solving, both directly and using an external
solver
@author Cynthia Kop
@since  Feb  22 2012 *)

open Ctrs;;

(*** MODULES ******************************************************************)

(** {2 Module Smtresults} *)

(** This module simply defines the possible results an SMT-check can give *)
module Smtresults : sig
  type t = SAT | UNSAT | UNKNOWN
end

(** {2 Module Smtquantifiers} *)

(** This module defines functionality to deal with bounded quantifiers *)
module Smtquantifiers : sig
  exception UnboundedQuantification of Term.t
  (** the failure thrown if a quantifier does not have an obvious range *)
  val universal_quantification : Variable.t -> Term.t -> bool -> Term.t ->
                                 bool -> Term.t -> Alphabet.t -> Term.t
  (** [universal_quantification x n false m false phi a] returns the
  formula FORALL x in {n,...,m}: phi.  To do this, the alphabet must
  contain suitable symbols.  If this is not the case, a failure is
  thrown. If the first boolean is true, we instead consider n+1.  If
  the second boolean is true, we instead consider m-1. *)
  val existential_quantification : Variable.t -> Term.t -> bool -> Term.t ->
                                   bool -> Term.t -> Alphabet.t -> Term.t
  (** [existential_quantification x n false m false a phi] returns the
  formula EXISTS x in {n,...,m}: phi.  To do this, the alphabet must
  contain suitable symbols.  If this is not the case, a failure is
  thrown. If the first boolean is true, we instead consider n+1. If
  the second boolean is true, we instead consider m-1. *)
  val universal_range : Variable.t -> Alphabet.t -> Term.t ->
                        (Term.t * bool) * (Term.t * bool) * Term.t
  (** [universal_range x a "n <= x <= m ==> phi" returns (n,m,phi).  If
  phi does not have this form (or a variant thereof), then a failure
  is thrown.  In addition to n and m, a boolean is included
  indicating whether the bound is strict (e.g. n > for an upper bound
  instead of >=). *)
  val existential_range : Variable.t -> Alphabet.t -> Term.t ->
                          (Term.t * bool) * (Term.t * bool) * Term.t
  (** [universal_range x a "n <= x <= m /\ phi" returns (n,m,phi).  If
  phi does not have this form (or a variant thereof), then a failure
  is thrown.  In addition to n and m, a boolean is included indicating
  whether the bound is strict. *)
end

(** {2 Module Externalsolver} *)

(** This module is used to interface with an external SMT-solver. *)
module Externalsolver : sig
  type possible_results = Smtresults.t
  type solverdata = string * string
    (* (name of the SMT-solver to use, name of the theory to use) *)
  type renaming = (string * string) list
    (* mapping from symbol names to smt-symbol names *)
  type translation = (string * (string,int) Util.either list) list;;
    (* mapping from symbol names to smt-expressions with argument indexes*)

  (** {3 Technical Interactions} *)

  val check_smt_file : string -> string ->
                       possible_results * (string * string) list
  (** [check_smt_file problem solver] runs the given SMT-solver on the
  given file in a standard input format.  The output is parsed and
  returned, where the list maps variable names to the name of the
  corresponding value *)
  val check_smt_file_and_parse : string -> string -> Environment.t ->
                       Alphabet.t -> possible_results * Substitution.t
  (** [check_smt_file_and_parse problem solver e a] acts like
  check_smt_file, but also parses the resulting list into a
  substitution using the given environment [e] and alphabet [a] *)
  val create_smt_file : Environment.t -> Variable.t list -> 'a list ->
                        ('a -> string) -> string -> string
  (** [create_smt_file e a vars expr tostring logic] returns the
  contents of a file in SMT-lib format (which can be fed into
  check_smt_file), provided the variables in the problem are [vars],
  which are all in the given environment [e], and [expr] is some
  kind of boolean expression which can be translated into SMT-lib
  format using [tostring]; [logic] should be a string like QF_NIA,
  indicating what logic the smt-solver should use *)

  (** {3 Working with Terms} *)

  val calculate : Term.t -> solverdata -> renaming -> translation ->
                  Alphabet.t -> Environment.t -> Term.t
  (** [calculate term solverdata renamings translations a e]
  calculates the value of the logical term [term], using the
  smt-solver and logic given by [solverdata]; the result is wrapped
  into a term and returned.  Here, [renamings] is a list mapping
  names of logical symbols in the given term to names used by the
  SMT-solver, and [translations] maps symbols with arguments
  directly to SMT-terms.  The alphabet is used to find a function
  symbol for the given value, and the environment merely to look up
  variables which may occur in the term; if this term is ground
  (which will usually be the case), just use a dummy environment *)
  val get_value : Sort.t -> solverdata -> Alphabet.t -> Term.t
  (** [get_value s t a] asks the SMT-solver with data [t] for a value
  of sort [s], using [a] to parse the result into a value. *)
  val check_formula : Term.t -> solverdata -> renaming -> translation ->
                      Alphabet.t -> Environment.t ->
                      possible_results * Substitution.t
  (** [check_formula form data ren tra a e] checks the formula [form]
  using the SMT-solverdata [data] and renamings [ren] and translations
  [tra]; for sorts and names of variables in [form] the environment
  [e] is consulted.  If the formula is satisfiable, then a pair (SAT,
  gamma) is returned, where gamma maps all variables in [form] to
  terms.  If the formula is not satisfiable, or the SMT-solver cannot
  figure it out, then a pair (UNSAT, gamma) or (UNKNOWN, gamma) is
  returned where gamma is the empty substitution *)
  val check_formulas : Term.t list -> solverdata -> renaming ->
                       translation -> Alphabet.t -> Environment.t ->
                       possible_results * Substitution.t
  (** [check_formulas [form1;...;formn] data ren tra a e] checks the
  formula [form1] AND ... AND [formn] using the SMT-solverdata [data];
  for sorts and names of variables in [forms] the environment [e] is
  consulted.  If the formulas are all satisfiable together, then a
  pair (SAT, gamma) is returned, where gamma maps all variables in
  [form] to terms.  If the formula is not satisfiable, or the
  SMT-solver cannot figure it out, then a pair (UNSAT, gamma) or
  (UNKNOWN, gamma) is returned where gamma is the empty
  substitution *)
end

(** {2 Module Internalthinker} *)

(** This module is used as the core of the internal solver.  Not
typically used directly (instead, call Internalsolver), this module
takes care of advanced formula simplification.  It uses its own
internal expression and formula types. *)

module Internalthinker : sig
  type intformula
  type possible_results = Smtresults.t
end

(** {2 Module Internalsolver} *)

(** This module is used for preparsing, handling basic things without
reference to the SMT-solver, and handling things which the SMT-solver
isn't able to do (such as existential quantification) *)
module Internalsolver : sig
  type possible_results = Smtresults.t
  type renaming = (string * string) list
    (* mapping from symbol names to smt-symbol names *)
  type translation = (string * (string,int) Util.either list) list
    (* mapping from symbol names to smt-expressions *)
  type intformula (*= Internalthinker.intformula*)
    (* internal formula representation *)

  val acceptable_logic : string -> bool
  (** [acceptable_logic str] returns whether the internal solver can
  handle queries in the given logic *)

  (** {3 Calculations (nothing technical happens)} *)

  val calculate : Term.t -> renaming -> translation ->
                  Alphabet.t -> Environment.t -> Term.t
  (** [calculate term renamings translations a e] calculates the
  value of thelogical term [term]; the result is wrapped into a term
  and returned.  Here, [renamings] is a list mapping names of logical
  symbols in the given term to names used by the SMT-solver, and
  [translations] a list mapping such names to SMT-terms with
  argument positions.  The alphabet is used to find a function symbol
  for the given value, and the environment merely to look up
  variables which may occur in the term; if this term is ground
  (which will usually be the case), just use a dummy environment;
  throws a NoIntegerProblem exception if illegal symbols occur,
  and a failwith if the system has any free variables which cannot
  be avoided (free variables in an ite(true,1,x) are okay) *)
  val trivial_test : Term.t -> renaming -> translation ->
                     Alphabet.t -> Environment.t -> bool
  (** [trivial_test term renamings translations a e] calculates the
  boolean value of the logical term [term] and returns it (as
  calculate, but the result is not wrapped into a term). *)
  val get_value : Sort.t -> Alphabet.t -> Term.t
  (** [get_value s a ] returns a value of sort [s]; here, [s] must be
  one of Int or Bool, otherwise a NoIntegerProblem is thrown *)

  (** {3 Advanced Techniques} *)

  val solve_satisfiability : Term.t list -> string -> renaming ->
                       translation -> Alphabet.t -> Environment.t ->
                       possible_results * Substitution.t
  (* [solve_satisfiability formulas solvername ren tra a e] solves
  satisfiability of [formula] using internal simplifications,
  followed up by a call to the SMT-solver if basic simplifications
  are not enough; if [solvername] is left empty, no smt-solver is
  called, and we just complete with UNKNOWN in this case
  @raise NoIntegerProblem <message> if the given formulas cannot be
  handled internally *)
  val solve_validity : Term.t list -> string -> renaming ->
                       translation -> Alphabet.t -> Environment.t ->
                       possible_results
  (* [solve_validity formulas solvername ren tra a e] determines
  whether [formula] is valid using internal simplifications, followed
  up by a call to the SMT-solver if basic simplifications are not
  enough; if [solvername] is left empty, no smt-solver is called, and
  we just complete with UNKNOWN if basic simplifying does not suffice.
  The result is SAT if the problem is valid, UNSAT if it is not, and
  UNKNOWN if we can't tell
  @raise NoIntegerProblem <message> if the given formulas cannot be
  handled internally *)
  val solve_existential_validity : Term.t list ->
    (Variable.t * ((int * int) option)) list -> string -> renaming ->
    translation -> Alphabet.t -> Environment.t ->
    possible_results * Substitution.t
  (* [solve_existential_validity formulas varswithrange solvername
  ren tra a e] determines whether there are instantiations of
  the variables in [varswithrange], where the instantiations must be
  in the given range if one is given, such that the formula is valid
  (so this proves an EXISTS FORALL statement). *)

  (* {3 Side work: altering constraints} *)

  val simplify_constraint : renaming -> translation -> Alphabet.t ->
                Environment.t -> Variable.t list -> Term.t -> Term.t
  (* [simplify_constraint ren tra a e vars phi] rewrites [phi] to an
  equivalent formula which may be easier to work with; this may cause
  the introduction of range quantifiers, and removal of variables not
  in [vars].  Here we assume variables in [vars] are universally
  quantified and other variables existentially; equivalence of phi
  and psi means that FORALL vars. (EXISTS xs [phi(xs,vars)]) <=>
  EXISTS ys [psi(ys,vars)] holds. *)
end

(** {2 Module Manualsolver} *)

(** This module is used so that ultimately, we can handle all logics
even when there is no SMT-solver available for them: the user is
prompted to determine validity or satisfiability herself!*)
module Manualsolver : sig
  type possible_results = Smtresults.t

  val calculate : Term.t -> (Term.t -> string) -> Alphabet.t -> Term.t
  (** [calculate term printer a] prompts the user to provide a value
  for the given logical term, and returns the result. *)
  val trivial_test : (Term.t -> string) -> Term.t -> bool
  (** [trivial_test printer term] prompts the user to determine
  whether the given logical term evaluates to true. *)
  val get_value : Sort.t -> Alphabet.t -> Term.t
  (** [get_value printer s a] prompts the user to supply a value of
  sort [s]. *)
  val satisfiability : Term.t list -> (Term.t -> string) ->
                       Alphabet.t ->  possible_results * Substitution.t
  (** [satisfiabiilty printer forms e a] returns whether all formulas
  are satisfiable, and if so, a substitution which satisfies them. *)
  val validity : Term.t list -> (Term.t -> string) -> Alphabet.t ->
                 possible_results
  (** [validity printer forms a] returns whether the given formulas
  are valid. *)
end

(** {2 Module Solver} *)

(** This module interfaces with both the internal and external
solver, to find an answer to the given problem. *)
module Solver : sig
  type t
  type possible_results = Smtresults.t

  (** {3 Constructors} *)

  val create : unit -> t
  (* [create ()] returns a new smt-solver. *)
  val intsolver : t 
  (* [intsolver] is a predefined smt-solver which can handle
  non-linear integer arithmetic *)
  val solvername : t -> string
  (* [solvername t] returns the name for the given smt-solver *)
  val use_solver : string -> t -> unit
  (* [use_solver solver t] alters the smt-solver [t] to use the external tool
  [solver] instead of the default smtsolver. *)
  val use_internal_solver : t -> unit
  (* [use_internal_solver t] alters the smt-solver [t] to use the "internal"
  solver instead of the default or given solver whenever possible.  For
  simple calculations, this means that the program will calculate those
  functions and formulas by itself; for more complex calculations, the
  default smt-solver, use the solver given by [use_solver], is still used. *)
  val use_manual_solver : t -> (Term.t -> string) -> unit
  (* [use_manual_solver printer t] alters the smt-solver [t] to use the
  "manual" solver instead of the default or given solver, and passes the
  given term printer to this solver.  This means that the user will be
  prompted for the answers to calculations and satisfiability queries
  (and can abort by typing ABORT at any time).  This cannot be combined
  with an automatic solver. *)
  val use_logic : string -> t -> unit
  (* [use_logic logic t] alters the smt-solver [t] to use the logic [logic]. *)
  val get_logic : t -> string
  (* [get_logic t] returns the logic [t] was set to use *)
  val add_symbol_renaming: string -> string -> t -> bool -> unit
  (* [add_symbol_renaming symb ren t addtoint] alters the smt-solver [t]
  by adding a symbol renaming: every occurrence of the symbol [symb] in 
  terms fed to the smt-solver will be printed as [ren]; if [addtoint] is
  true, the symbol is also added to the internal intsolver. *)
  val add_symbol_translation: string -> (string,int) Util.either list ->
                              t -> bool -> unit
  (* [add_symbol_translation symb trans t addtoint] alters the smt-solver [t]
  by adding a symbol translation: every occurrence of the symbol [symb] in 
  terms fed to the smt-solver will be printed as [trans], with each argument
  Right i replaced by the corresponding parameter of symb; if [addtoint] is
  true, the symbol translation is also added to the internal intsolver. *)

  (** {3 Using the SMT-solver} *)

  val calculate : Term.t -> t -> Term.t
  (** [calculate term t] calculates the value of the logical term [term],
  using the SMT-solver [t], wraps the result into a term, and returns it. *)
  val get_value : Sort.t -> t -> Term.t
  (** [get_value s t] asks the SMT-solver [t] for a value of sort [s]. *)
  val satisfiable_formulas : Term.t list -> t -> Environment.t ->
                             possible_results * Substitution.t
  (** [satisfiable_formulas forms t e] checks the formulas [forms]
  using the SMT-solver [t]; for sorts and names of variables in [t]
  the environment [e] is consulted. If the formula is satisfiable,
  then a pair (SAT, gamma) is returned, where gamma maps all
  variables in [form] to terms.  If the formula is not satisfiable,
  or the SMT-solver cannot figure it out, then a pair (UNSAT, gamma)
  or (UNKNOWN, gamma) is returned where gamma is the empty
  substitution *)
  val valid_formulas : Term.t list -> t -> Environment.t ->
                       possible_results
  (** [valid_formulas forms t e] returns SAT if the given formulas
  are all valid, UNSAT if they are not all valid, and UNKNOWN if we
  don't know.  For sorts and names of variables in[t], the environment
  [e] is consulted. *)
  val satisfiable : Term.t list -> t -> Environment.t -> bool
  (** [satisfiable forms t e] simply returns true if we can definitely
  satisfy all [forms], false if we cannot or we don't know *)
  val unsatisfiable : Term.t list -> t -> Environment.t -> bool
  (** [unsatisfiable forms t e] simply returns true if we can definitely
  not satisfy all [forms], false if we can or we don't know *)
  val valid : Term.t list -> t -> Environment.t -> bool
  (** [valid forms t e] simply returns true if all [forms] are
  definitely valid, false if they are not or we don't know *)
  val exists_valid : Variable.t list -> Term.t -> t -> Environment.t -> bool
  (** [exists_valid vars phi smt env] checks whether the formula
  "exists [vars].[phi]" is valid *)
  val forall_satisfiable : Variable.t list -> Term.t -> t -> Environment.t
                                           -> possible_results * Substitution.t
  (** [forall_satisfiable vars phi smt env] checks whether the formula
  forall [vars].[phi] is satisfiable, and returns SAT and a
  substitution which satisfies the formula if so *)
  val existential_implication : Variable.t list -> Term.t ->
    Term.t list -> Term.t list -> t -> Environment.t -> bool
  (** [existential_implication vars phi psi1 psi2 smt env checks
  whether the formula exists [vars].[phi] => [psi1] /\ [psi2] is
  valid.  Here, [psi1] is a list of formulas which may contain the
  variables in [vars], and [psi2] may not contain them.  This differs
  from exists_valid in that the checker will use the split and try
  some optimisations before sending the formula to the smt-solver,
  even when we are not using the internal solver*)
  val find_values : Term.t list -> (Variable.t * ((int * int) option))
    list -> Alphabet.t -> Environment.t ->
    (Variable.t * int) list option
  (* [find_values formulas varswithrange a e] uses the internal solver
  to determine whether there are instantiations of the variables in
  [varswithrange], where the instantiations must be in the given range
  if one is given.  The result may well have false negatives (None is
  returned if no definitely suitable instantiation can be found), but
  when a solution is found, Some <that solution> is returned *)

  (** {3 Misc} *)

  val simplify_constraint : t -> Alphabet.t -> Environment.t ->
                            Variable.t list -> Term.t -> Term.t
  (* [simplify_constraint tr a e vars phi] rewrites [phi] to an equivalent
  formula which may be easier to work with; this may cause the
  introduction of range quantifiers
  (see also Internalsolver.simplify_constraint) *)
  val setup_core_symbols : t -> Alphabet.t -> unit
  (** [setup_core_symbols t a] tells the alphabet [a] which symbols are used
  for and, or, not, implies, bottom and top *)
end

