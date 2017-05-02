(* Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
 * and 2014, 2015 Cynthia Kop
 * GNU Lesser General Public License
 *
 * This file is part of CTRL (and originates in TTT2).
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

(*** INCLUDES *****************************************************************)
include Ctrsx.Prelude;;

(*** OPEN *********************************************************************)
open Util;;

(*** MODULE TYPES *************************************************************)
module type FUNCTION = sig
  type t
  
  val standard_symbol : int -> string -> t
  val integer_symbol : int -> t
  val array_symbol : t array -> t
  val mixed_symbol : string -> string -> string -> t
  val is_standard : t -> bool
  val is_integer : t -> bool
  val is_array : t -> bool
  val is_mixed : t -> bool
  val std_to_int : t -> int
  val integer_to_int : t -> int
  val array_to_array : t -> t array
  val mixed_to_string : t -> string
  val mixed_brackets : t -> string * string
  val find_name : t -> string
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val copy : t -> t
  val hash : t -> int
  val fprintf : Format.formatter -> t -> unit
  val to_string : ?debug:(bool) -> t -> string
end

module type VARIABLE = sig
  type t
 
  val create : int -> string -> t
  val copy : t -> t
  val hash : t -> int
  val to_int : t -> int
  val find_name : t -> string
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
end

module type SORT = sig
  type t
 
  val copy : t -> t
  val hash : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
  val from_string : string -> t
  val from_indexed : string -> int -> t
end

module type SORTDECLARATION = sig
  type sort
  type t
 
  val create : sort list -> sort -> t
  val output_sort : t -> sort
  val input_sort : t -> int -> sort
  val input_sorts : t -> sort list
  val arity : t -> int
  val copy : t -> t
  val hash : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
end

module type SPECIALDECLARATION = sig
  type sort
  type t
  type polsort
  type sd

  val polymorphic_declaration : polsort list -> polsort -> t 
  val variable_declaration : polsort -> polsort -> t 
  val known_arity : t -> bool 
  val arity : t -> int
  val input_sort : int -> t -> polsort
  val input_sorts : t -> polsort list
  val output_sort : t -> polsort
  val is_normal_sortdec : t -> bool
  val make_normal_sortdec : t -> sd
  val make_polsort : string -> ?index:int option -> polsort
  val sort_to_pol : sort -> polsort
  val pol_to_sort : polsort -> sort
  val is_polymorphic : polsort -> bool 
  val copy : t -> t
  val hash : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val pol_to_string : polsort -> string
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
end

module type ENVIRONMENT = sig
  type sort
  type t

  val empty : int -> t
  val dummy : unit -> t
  val drop : t -> unit
  val create_var : string -> sort -> t -> Variable.t
  val create_unsorted_var : string -> t -> Variable.t
  val create_sorted_var : sort -> string list -> t -> Variable.t
  val create_fresh_var : string list -> t -> Variable.t
  val create_var_like : Variable.t -> t -> string list -> t -> Variable.t
  val generate_var_name : bool -> string -> string list -> t -> string
  val add_sort : Variable.t -> sort -> t -> unit
  val replace_sort : Variable.t -> sort -> t -> unit
  val find_var : string -> t -> Variable.t
  val find_sort : Variable.t -> t -> sort
  val vars : t -> Variable.t list
  val var_names : t -> string list
  val is_defined : Variable.t -> t -> bool
  val has_sort : Variable.t -> t -> bool
  val mem_var_name : string -> t -> bool
  val is_sort : Variable.t -> sort -> t -> bool
  val copy : t -> t
  val hash : t -> int
  val reset : t -> unit
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
end

module type ALPHABET = sig
  type t
  type sort
  type sd
  type spd
  type func
  type symbolkind = Terms | Logical | Both
 
  val empty : int -> t
  val value_alphabet : unit -> t
  val create_fun : sd -> string -> t -> func
  val create_instance_fun : spd -> string -> t -> func
  val create_unsorted_fun : int -> string -> t -> func
  val fresh_fun : string -> t -> func
  val include_integers : sort -> t -> unit
  val include_arrays : sort -> sort -> t -> unit
  val include_mixed : string -> string -> sort -> t -> unit
  val add_ari : func -> int -> t -> unit
  val add_sortdec : func -> (sd, spd) either -> t -> unit
  val add_normal_sortdec : func -> sd -> t -> unit
  val add_special_sortdec : func -> spd -> t -> unit
  val replace_ari : func -> int -> t -> unit
  val replace_sortdec : func -> (sd, spd) either -> t -> unit
  val replace_normal_sortdec : func -> sd -> t -> unit
  val replace_special_sortdec : func -> spd -> t -> unit
  val set_symbol_kind : func -> symbolkind -> t -> unit
  val add_symbol_kind : func -> symbolkind -> t -> unit
  val find_ari : func -> t -> int
  val find_sortdec : func -> t -> (sd, spd) either
  val find_fun : string -> t -> func
  val find_symbol_kind : func -> t -> symbolkind
  val funs : ?p:(func -> bool) -> t -> func list
  val fun_names : t -> string list
  val integer_sort : t -> sort
  val array_sort : sort -> t -> sort
  val mixed_sort : (string * string) -> t -> sort
  val default_intsort : sort
  val boolsort : sort
  val arraysorts : t -> sort list
  val arraysorts_of : t -> sort list
  val mixedsorts : t -> sort list
  val find_sorts : t -> sort list
  val find_logical_sorts : t -> sort list
  val find_symbols_with_sort : t -> sort -> func list
  val test_mixed : sort -> t -> (string * string) option
  val is_ari : int -> func -> t -> bool
  val is_sort : sort -> func -> t -> bool option
  val is_argument_sort : int -> sort -> func -> t -> bool option
  val is_defined_fun : func -> t -> bool
  val is_value : func -> t -> bool
  val mem_ari : func -> t -> bool
  val mem_fun_name : string -> t -> bool
  val mem_symbol_kind : func -> t -> bool
  val mem_sortdec : func -> t -> bool
  val has_integers : t -> bool
  val has_arrays : t -> bool
  val has_arrays_of : sort -> t -> bool
  val has_mixeds : t -> bool
  val logical_sorts_inhabited : t -> bool
  val set_and_symbol : func -> t -> unit
  val set_or_symbol : func -> t -> unit
  val set_imply_symbol : func -> t -> unit
  val set_not_symbol : func -> t -> unit
  val set_bot_symbol : func -> t -> unit
  val set_top_symbol : func -> t -> unit
  val set_equal_symbol : func -> t -> unit
  val set_geq_symbol : func -> t -> unit
  val set_leq_symbol : func -> t -> unit
  val set_greater_symbol : func -> t -> unit
  val set_smaller_symbol : func -> t -> unit
  val get_and_symbol : t -> func
  val get_or_symbol : t -> func
  val get_imply_symbol : t -> func
  val get_not_symbol : t -> func
  val get_bot_symbol : t -> func
  val get_top_symbol : t -> func
  val get_equal_symbol : t -> func
  val get_geq_symbol : t -> func
  val get_leq_symbol : t -> func
  val get_greater_symbol : t -> func
  val get_smaller_symbol : t -> func
  val add_wellfounded : sort -> func -> t -> unit
  val get_wellfounded : sort -> t -> func list
  val sorts_with_wellfounded_relations : t -> sort list
  val copy : t -> t
  val hash : t -> int
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
end

module type POSITION = sig
  type t
 
  val add_first : int -> t -> t
  val add_last : int -> t -> t
  val root : t
  val head : t -> int
  val init : t -> t
  val last : t -> int
  val make : int -> t
  val of_list : int list -> t
  val split_first : t -> int * t
  val split_last : t -> t * int
  val tail : t -> t
  val to_list : t -> int list
  val (||) : t -> t -> bool
  val (<=) : t -> t -> bool
  val (<) : t -> t -> bool
  val (>=) : t -> t -> bool
  val (>) : t -> t -> bool
  val is_root : t -> bool
  val are_parallel : t -> t -> bool
  val is_prefix : t -> t -> bool
  val is_proper_prefix : t -> t -> bool
  val is_proper_suffix : t -> t -> bool
  val is_suffix : t -> t -> bool
  val is_head : int -> t -> bool
  val append : t -> t -> t
  val copy : t -> t
  val hash : t -> int
  val length : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
end

module type CSMAPPING = sig
  type func
  type t

  val empty : unit -> t
  val fill : Alphabet.t -> t -> unit
  val set_reducable_positions : func -> int list -> t -> unit
  val get_reducable_positions : func -> t -> int list
  val is_reducable_at : func -> int -> t -> bool
  val fprintf : Format.formatter -> t -> unit
end

module type TERM = sig
  type func
  type sort
  type sd
  type t = Var of Variable.t | Fun of func * t list |
           InstanceFun of func * t list * sd |
           Forall of Variable.t * t |
           Exists of Variable.t * t

  val make_fun : func -> t list -> t
  val make_instance : func -> t list -> sd -> t
  val make_function : Alphabet.t -> Environment.t -> func -> t list -> t
  val make_var : Variable.t -> t
  val make_forall : Variable.t -> t -> t
  val make_exists : Variable.t -> t -> t
  val replace : Position.t -> t -> t -> t
  val reverse : t -> t
  val subterm : Position.t -> t -> t
  val subterm_with_binders : Position.t -> t -> Variable.t list * t
  val cons : t -> func list
  val funs : t -> func list
  val root : t -> func option
  val symbols : t -> (Variable.t,func) either list
  val vars : t -> Variable.t list
  val allvars : t -> Variable.t list
  val is_build : func list -> t -> bool
  val is_forall : t -> bool
  val is_exists : t -> bool
  val is_cons : t -> bool
  val is_dummy : t -> bool
  val is_flat : t -> bool
  val is_fun : t -> bool
  val is_instance : t -> bool
  val is_ground : t -> bool
  val is_linear : t -> bool
  val is_proper_subterm : t -> t -> bool
  val is_shallow : t -> bool
  val is_string : t -> bool
  val is_subterm : t -> t -> bool
  val is_var : t -> bool
  val is_value : Alphabet.t -> t -> bool
  val check_proper_term : Alphabet.t -> t -> Position.t option
  val check_logical_term : Alphabet.t -> t -> Position.t option
  val mem_fun : func -> t -> bool
  val mem_var : Variable.t -> t -> bool
  val fun_pos : func -> t -> Position.t list
  val funs_pos : t -> Position.t list
  val funs_pos_with_fun : t -> (Position.t * func) list
  val quantifier_pos : t -> Position.t list
  val pos : t -> Position.t list
  val req_pos : (t -> bool) -> t -> Position.t list
  val accessible_fun_pos : func -> Csmapping.t -> t -> Position.t list
  val accessible_funs_pos : Csmapping.t -> t -> Position.t list
  val accessible_pos : Csmapping.t -> t -> Position.t list
  val subterm_pos : t -> t -> Position.t list
  val var_pos : Variable.t -> t -> Position.t list
  val vars_pos : t -> Position.t list
  val has_pos : Position.t -> t -> bool
  val count_fun : func -> t -> int
  val fold_funs : (func -> 'a -> 'a) -> 'a -> t -> 'a
  val recurse : (Variable.t -> 'a) -> (func -> 'a list -> 'a) ->
    (func -> 'a list -> sd -> 'a) -> (Variable.t -> 'a -> 'a) ->
    (Variable.t -> 'a -> 'a) -> t -> 'a
  val map : (func -> func) -> t -> t
  val args : t -> t list
  val replace_args : t -> t list -> t
  val copy : t -> t
  val depth : t -> int
  val fun_size : t -> int
  val get_sort : Alphabet.t -> Environment.t -> t -> sort
  val hash : t -> int 
  val proper_subterms : ?p:(t -> bool) -> t -> t list
  val size : t -> int 
  val subterms : ?p:(t -> bool) -> t -> t list
  val var_size : t -> int 
  val quantifier_size : t -> int 
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val read_value : string -> Alphabet.t -> string -> t
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
  val to_stringm : t -> string
end

module type CONTEXT = sig 
  type func
  type term
  type t = Hole | More of func * term list * t * term list
 
  val apply : term -> t -> term
  val compose : t -> t -> t
  val of_term : Position.t -> term -> t
  val subcontext : Position.t -> t -> t
  val is_empty : t -> bool
  val is_mu_context : t -> Csmapping.t -> bool
  val hash : t -> int 
  val hole_pos : t -> Position.t
  val pos : t -> Position.t list
  val compare : t -> t -> int 
  val equal : t -> t -> bool
  val fprintf : Format.formatter -> t -> unit
  val fprintfm : Format.formatter -> t -> unit
  val to_string : t -> string
  val to_stringm : t -> string
end

module type SUBSTITUTION = sig 
  type func
  type term
  type context
 
  include Replacement.SIGNATURE with
    type domain = Variable.t and type range = term
 
  val apply_term : t -> term -> term
  val apply_context : t -> context -> context
  val is_bijective : t -> bool
  val is_renaming : t -> bool
  val fprintfm : Format.formatter -> t -> unit
  val to_stringm : t -> string
end

module type ELOGIC = sig
  type substitution
  type term

  exception Not_matchable
  exception Not_semi_unifiable
  exception Not_unifiable

  val are_unifiable : term -> term -> bool
  val is_variant : term -> term -> bool
  val unify : term -> term -> substitution
  val unify_problem : (term * term) list -> substitution
  val contains : term -> term -> bool
  (*val ground_matches : term -> term -> bool*)
  val matches : term -> term -> bool
  val match_problem : (term * term) list -> substitution
  val match_term : term -> term -> substitution
  val subsumes : term -> term -> bool
  val renaming : term list -> string list -> Environment.t -> substitution
  val environment_oblivious_renaming : term list -> term list
end

module type RULE = sig
  type substitution
  type func
  type term
  type t
  exception Not_an_lctrs
 
  val invert : t -> t
  val lhs : t -> term
  val rhs : t -> term
  val constraints : t -> term list
  val create : term -> term -> term list -> t
  val of_terms : term -> term -> t
  val apply : (term -> 'a) -> (term -> 'b) -> (term list -> 'c) -> t -> 'a * 'b * 'c
  val fold : (term -> 'a -> 'a) -> 'a -> t -> 'a
  val map : (term -> 'a) -> t -> 'a * 'a * 'a list
  val project : (term -> term) -> t -> t
  val uncurry : (term -> term -> term list -> 'a) -> t -> 'a
  val cons : t -> func list
  val funs : t -> func list
  val left_cons : t -> func list
  val left_funs : t -> func list
  val left_symbols : t -> (Variable.t,func) either list
  val left_vars : t -> Variable.t list
  val left_root : t -> func
  val right_cons : t -> func list
  val right_funs : t -> func list
  val right_symbols : t -> (Variable.t,func) either list
  val right_vars : t -> Variable.t list
  val right_root : t -> func
  val roots : t -> func list
  val symbols : t -> (Variable.t,func) either list
  val vars : t -> Variable.t list
  val allvars : t -> Variable.t list
  val is_build : func list -> t -> bool
  val is_collapsing : t -> bool
  val is_contained : t -> bool
  val is_dummy : t -> bool
  val is_duplicating : t -> bool
  val is_erasing : t -> bool
  val is_flat : t -> bool
  val is_ground : t -> bool
  val is_growing : t -> bool
  val is_left_build : func list -> t -> bool
  val is_left_dummy : t -> bool
  val is_left_erasing : t -> bool
  val is_left_flat : t -> bool
  val is_left_ground : t -> bool
  val is_left_linear : t -> bool
  val is_left_shallow : t -> bool
  val is_left_string : t -> bool
  val is_linear : t -> bool
  val is_normal_form : term -> t -> bool
  val is_redex : term -> t -> bool
  val is_rewrite_rule : t -> bool
  val is_right_build : func list -> t -> bool
  val is_right_dummy : t -> bool
  val is_right_flat : t -> bool
  val is_right_ground : t -> bool
  val is_right_linear : t -> bool
  val is_right_shallow : t -> bool
  val is_right_string : t -> bool
  val is_shallow : t -> bool
  val is_size_preserving : t -> bool
  val is_string : t -> bool
  val is_variant : t -> t -> bool
  val is_standard : t -> Alphabet.t -> bool
  val is_regular : t -> bool
  val matches : t -> t -> bool
  val subsumes : t -> t -> bool
  val are_overlapping : t -> t -> bool
  val is_overlap : t -> Position.t -> t -> bool
  val test_reasonable : t -> Alphabet.t -> Environment.t -> bool
  val reducts : term -> t -> term list
  val rewrite : term -> Position.t -> t -> term
  val rewrites : term -> Position.t -> t -> term -> bool
  val redex_pos : term -> t -> Position.t list
  val accessible_redex_pos : term -> Csmapping.t -> t -> Position.t list
  val apply_sub : substitution -> t -> t
  val count_fun : func -> t -> int 
  val reverse : t -> t
  val to_terms : t -> term * term
  val rename : t -> Environment.t -> t
  val rename_fully : t -> Environment.t -> Alphabet.t -> t
  val copy : t -> t
  val depth : t -> int
  val hash : t -> int
  val overlaps : t -> t -> (t * Position.t * t) list
  val var_overlaps : t -> t -> (t * Position.t * t) list
  val fresh_renaming : t -> Environment.t -> Environment.t -> string list -> t
  val environment_transfer : t -> Environment.t -> Environment.t -> string list -> t
  val left_value_free : Alphabet.t -> Environment.t -> t -> t
  val calculation_free : Alphabet.t -> Environment.t -> t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val fprintf : Format.formatter -> t -> unit
  val fprintfm : Format.formatter -> t -> unit
  val to_string : t -> string
  val to_stringm : t -> string
end

module type TRS = sig
  type rule
  type term
  type func
  type sort
  type t

  val empty : unit -> t
  val create : Alphabet.t -> Environment.t -> t
  val create_contextsensitive : Alphabet.t -> Environment.t -> Csmapping.t -> t
  val get_alphabet : t -> Alphabet.t
  val get_main_environment : t -> Environment.t
  val get_rules : t -> (rule * Environment.t) list
  val get_plain_rules : t -> rule list
  val get_context_sensitivity : t -> Csmapping.t
  val add : rule -> Environment.t -> t -> unit
  val set_rules : (rule * Environment.t) list -> t -> unit
  val set_alphabet : Alphabet.t -> t -> unit
  val lhs : t -> term list
  val rhs : t -> term list
  val count_fun : func -> t -> int
  val flat_map : (rule -> Environment.t -> 'a list) -> t -> 'a list
  val fold : (rule -> Environment.t -> 'a -> 'a) -> 'a -> t -> 'a
  val iter : (rule -> Environment.t -> unit) -> t -> unit
  val map : (rule -> Environment.t -> 'a) -> t -> 'a list
  val project : (rule -> Environment.t -> rule) -> t -> unit
  val choose : t -> rule * Environment.t
  val filter : (rule -> Environment.t -> bool) -> t -> unit
  val find : (rule -> Environment.t -> bool) -> t -> rule * Environment.t
  val find_option : (rule -> Environment.t -> bool) -> t -> (rule * Environment.t) option
  val find_all : (rule -> Environment.t -> bool) -> t -> (rule * Environment.t) list
  val exists : (rule -> Environment.t -> bool) -> t -> bool
  val exists_rule : (rule -> bool) -> t -> bool
  val for_all : (rule -> Environment.t -> bool) -> t -> bool
  val for_all_rule : (rule -> bool) -> t -> bool
  val cons : t -> func list 
  val con_symbols : t -> func list 
  val used_con_symbols : term list -> t -> func list 
  val def_symbols : t -> func list 
  val calc_symbols : t -> func list 
  val funs : t -> func list 
  val left_cons : t -> func list 
  val left_con_symbols : t -> func list 
  val left_funs : t -> func list 
  val left_roots : t -> func list 
  val left_symbols : t -> (Variable.t,func) Util.either list 
  val left_vars : t -> Variable.t list 
  val right_cons : t -> func list 
  val right_con_symbols : t -> func list 
  val right_funs : t -> func list 
  val right_roots : t -> func list 
  val right_symbols : t -> (Variable.t,func) Util.either list
  val right_vars : t -> Variable.t list
  val roots : t -> func list
  val symbols : t -> (Variable.t,func) Util.either list
  val vars : t -> Variable.t list
  val is_build : func list -> t -> bool
  val is_collapsing : t -> bool
  val is_constructor : t -> bool
  val is_constructor_term : term -> t -> bool
  val is_dummy : t -> bool
  val is_duplicating : t -> bool
  val is_erasing : t -> bool
  val is_empty : t -> bool
  val is_flat : t -> bool
  val is_ground : t -> bool
  val is_growing : t -> bool
  val is_left_build : func list -> t -> bool
  val is_left_constructor : t -> bool
  val is_left_dummy : t -> bool
  val is_left_flat : t -> bool
  val is_left_ground : t -> bool
  val is_left_linear : t -> bool
  val is_left_shallow : t -> bool
  val is_linear : t -> bool
  val is_normal_form : term -> t -> bool
  val is_redex : term -> t -> bool
  val is_right_build : func list -> t -> bool
  val is_right_constructor : t -> bool
  val is_right_dummy : t -> bool
  val is_right_flat : t -> bool
  val is_right_ground : t -> bool
  val is_right_linear : t -> bool
  val is_right_shallow : t -> bool
  val is_shallow : t -> bool
  val is_size_preserving : t -> bool
  val is_variant : t -> t -> bool
  val is_applicative : t -> bool
  val is_overlapping : t -> bool
  val is_overlay : t -> bool
  val is_trs : t -> bool
  val test_reasonable : t -> string
  val test_values : t -> string
  val test_variables : t -> bool -> string
  val test_regular : t -> string
  val test_standard : t -> string
  val test_safe_sort : t -> sort -> bool
  val rename : t -> unit
  val copy : t -> t
  val depth : t -> int
  val hash : t -> int
  val overlaps : t -> (rule * Position.t * rule) list
  val var_overlaps : t -> (rule * Position.t * rule) list
  val size : t -> int
  val replace_rules : (rule * Environment.t) list -> t -> unit
  val fprintf : Format.formatter -> t -> unit
  val to_string : t -> string
  val set_current : t -> unit
  val get_current : unit -> t
  val has_current : unit -> bool
end

module type TYPECHECKER = sig
  type func
  type sd
  type term
  type rule

  val type_check : (rule * Environment.t) list -> Alphabet.t -> unit
  val type_check_trs : Trs.t -> unit
  val type_derive : Trs.t -> unit
  val type_derive_term : term -> Trs.t -> term
  val type_derive_rules : (rule * Environment.t) list -> Alphabet.t ->
    (rule * Environment.t) list
end

(**
  ***** WHAT IS HAPPENING HERE? *****

  The packaging system of the term rewriting library is made in a
  somewhat complex way, which allows for a cnvenient nested module
  system.  Unfortunately, due to the fact that all modules get
  overridden by new versions of themselves, this also causes a few
  problems.

  The first problem we see when we try to use for instance the type
  Sortdeclaration.t in another module (within rewriting).  This is
  rejected with an error that (the original definition of)
  Sortdeclaration.t cannot be unified with (the overwritten version
  of) Sortdeclaration.t.  Interestingly enough, this only happens
  with somewhat advanced types: Variable.t for instance is just a
  type alias, so does not give problems.
  
  The trick to solve this problem is to take a type "sd" in the
  modules which use Sortdeclaration.t, and then to tell ocaml that
  sd = Sortdeclaration.t both in rewriting.mli and in the submodule's
  definition.

  Unfortunately, when types are even more advanced than records and
  inductive types, such as Substitution.t, even this workaround
  doesn't help anymore.  For these cases we use a Make functor.  By
  postponing the exact definition of the Substitution class we use,
  ocaml is able to derive the necessary type equalities.

  The Empty module itself is not used for anything.

  Note: none of the problems described above affect modules outside
  the rewriting top module; they can use Ctrs.Sortdeclaration.t
  and Ctrs.Substitution.t without problems.
*)
module Empty = struct end;;

module Sort = Ctrsx.Sort;;
module Function = Ctrsx.Function;;
module Variable = Ctrsx.Variable;;
module Sortdeclaration = Ctrsx.Sortdeclaration;;
module Specialdeclaration = Ctrsx.Specialdeclaration;;
module Environment = Ctrsx.Environment;;
module Alphabet = Ctrsx.Alphabet;;
module Position = Ctrsx.Position;;
module Term = Ctrsx.Term;;
module Context = Ctrsx.Context;;
module Substitution = Ctrsx.Substitution.Make(Empty);;
module Csmapping = Ctrsx.Csmapping;;
module Elogic = Ctrsx.Elogic;;
module Rule = Ctrsx.Rule;;
module Trs = Ctrsx.Trs;;
module Typechecker = Ctrsx.Typechecker;;

