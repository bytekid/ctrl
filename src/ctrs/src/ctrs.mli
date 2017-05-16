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

(** Ctrs Library
@author Martin Korp, Christian Sternagel, Harald Zankl, Cynthia Kop
@since  Mon Dec  1 12:58:07 CET 2008 *)

(**
Provides basic functionality to deal with the standard notions of
term rewriting, as well as term rewriting with constraints.
*)

(*** MODULES ******************************************************************)

(** {2 Module Function} *)

module type FUNCTION = sig
  (*** TYPES *******************************************************************)
  type t

  (*** VALUES ******************************************************************)
  (** {3 Miscellaneous} *)

  (** {3 Constructors} *)

  val standard_symbol : int -> string -> t
  (** [standard_symbol i name] returns the standard function symbol
  with index [i] and name [name]. Both are required to be unique
  within the context of for instance an alphabet.  The name is what
  we usually see when interacting with the symbol; the index is used
  for easy lookup in various tables. *)
  val integer_symbol : int -> t
  (** [integer_symbol i] returns the integer function symbol encoding
  the number [i] *)
  val array_symbol : t array -> t
  (** [array_symbol i] returns the array function symbol encoding the
  array [i] *)
  val mixed_symbol : string -> string -> string -> t
  (** [mixed_symbol name openbracket closebracket] returns the mixed
  symbol "name", which will always be presented with the given open-
  and close-bracket. *)

  (** {3 Destructors and applicability tests} *)

  val is_standard : t -> bool
  (** [is_standard f] returns true if [f] is a standard function
  symbol or false if it is not (for instance if it is an integer) *)
  val is_integer : t -> bool
  (** [is_integer f] returns true if [f] is an integer symbol *)
  val is_array : t -> bool
  (** [is_array f] returns true if [f] is an array symbol *)
  val is_mixed : t -> bool
  (** [is_mixed f] returns true if [f] is a mixed symbol *)

  val std_to_int : t -> int
  (** [std_to_int f] returns the integer that is uniquely associated
  with [f] if [f] is a standard function symbol (all integers map to
  a standard function symbol and vice versa).
  @fail if [f] is not a standard function symbol *)
  val integer_to_int : t -> int
  (** [integer_to_int f] returns the integer which [f] encodes. *)
  val array_to_array : t -> t array
  (** [array_to_array f] returns the array which [f] encodes. *)
  val mixed_to_string : t -> string
  (** [mixed_to_string f] returns the string underlying [f] (without
  brackets) *)
  val mixed_brackets : t -> string * string
  (** [mixed_brackets f] returns teh bracket pair for [f], assuming
  [f] is a mixed function symbol *)
  val find_name : t -> string
  (* [find_name t] returns a string that should (under normal
  circumstances) uniquely identify the symbol *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare f g] compares [f] and [g]. This function defines a total
  ordering on function symbols. *)
  val equal : t -> t -> bool
  (** [equal f g] checks if [f] and [g] are equal. This function is
  equivalent to [compare f g = 0]. *)

  (** {3 Miscellaneous} *)

  val copy : t -> t
  (** [copy f] returns a copy of [f]. *)
  val hash : t -> int
  (** [hash f] returns a hash value for [f]. It is guaranteed that
  [hash f = hash g] if and only if [compare f g = 0]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt f] prints [f] using the [OCaml] module [Format]. *)
  val to_string : ?debug:(bool) -> t -> string
  (** [to_string debug f] returns an unformatted string that
  represents [f]. Here, [debug] indicates whether non-standard
  symbols should be specifically marked. *)
end

(** This module provides basic functions that deal with function symbols. *)
module Function : FUNCTION

(** {2 Module Variable} *)

module type VARIABLE = sig
  (*** TYPES *******************************************************************)
  type t

  (*** VALUES ******************************************************************)
  (** {3 Miscellaneous} *)

  val create : int -> string -> t
  (** [create i name] creates a variable with index [i] and name [name].
  Both are required to be unique within the context of for instance an
  environment. The name is what we usually see when interacting with the
  variable; the index is used for easy lookup. *)
  val copy : t -> t
  (** [copy x] returns a copy of [x]. *)
  val hash : t -> int
  (** [hash x] returns a hash value for [x]. It is guaranteed that
  [hash x = hash y] if and only if [compare x y = 0]. *)
  val to_int : t -> int
  (** [to_int x] is equivalent to {!val: Ctrs.VARIABLE.hash}. *)
  val find_name : t -> string
  (** [find_name x] returns the name of [x] *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare x y] compares [x] and [y]. This function defines a total
  ordering on variables. *)
  val equal : t -> t -> bool
  (** [equal x y] checks if [x] and [y] are equal. This function is equivalent
  to [compare x y = 0]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt x] prints [x] using the [OCaml] module [Format]. *)
  val to_string : t -> string
  (** [to_string x] returns a string that represents [x]. *)
end

(** This module deals with variables. *)
module Variable : VARIABLE

(** {2 Module Sort} *)

module type SORT = sig
  (*** TYPES *******************************************************************)
  type t

  (*** VALUES ******************************************************************)
  (** {3 Miscellaneous} *)

  val copy : t -> t
  (** [copy x] returns a copy of [x]. *)
  val hash : t -> int
  (** [hash f] returns a hash value for [f]. It is not guaranteed that
  [hash f = hash g] if and only if [compare f g = 0]. *)
  val index : t -> int
  (** [index s] returns the index associated with [s], and fails if no index
  exists. *)


  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare x y] compares [x] and [y]. This function defines a total
  ordering on variables. *)
  val equal : t -> t -> bool
  (** [equal x y] checks if [x] and [y] are equal. This function is equivalent
  to [compare x y = 0]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt x] prints [x] using the [OCaml] module [Format]. *)
  val to_string : t -> string
  (** [to_string x] returns a string that represents [x]. *)
  val from_string : string -> t
  (** [from_string x] returns a sort that corresponds to [x]. *)
  val from_indexed : string -> int -> t
  (** [from_indexed x i] returns a sort that corresponds to [x]_[i]. *)
end

(** This module deals with sorts. *)
module Sort : SORT

(** {2 Module Sortdeclaration} *)

module type SORTDECLARATION = sig
  (*** TYPES *******************************************************************)
  type sort
  type t

  (*** VALUES ******************************************************************)
  (** {3 Creation and Recovery functions} *)

  val create : sort list -> sort -> t
  (** creates a sort declaration from a given sequence of input types
  and an output type *)
  val output_sort : t -> sort
  (** [output_sort [a1 * ... * an] ==> b] returns b *)
  val input_sort : t -> int -> sort
  (** [input_sort [a1 * ... * an] ==> b i] returns ai *)
  val input_sorts : t -> sort list
  (** [input_sorts [a1 * ... * an] ==> b] returns [a1 * ... * an] *)
  val arity : t -> int
  (** [arity [a1 * ... * an] ==> b] returns n *)

  (** {3 Miscellaneous} *)

  val copy : t -> t
  (** [copy x] returns a copy of [x]. *)
  val hash : t -> int
  (** [hash f] returns a hash value for [f]. It is not guaranteed that
  [hash f = hash g] if and only if [compare f g = 0]. *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare x y] compares [x] and [y]. This function defines a total
  ordering on sort declarations. *)
  val equal : t -> t -> bool
  (** [equal x y] checks if [x] and [y] are equal. This function is equivalent
  to [compare x y = 0]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt x] prints [x] using the [OCaml] module [Format]. *)
  val to_string : t -> string
  (** [to_string x] returns a string that represents [x]. *)
end

(** This module deals with sort declarations (combining input- and output sorts. *)
module Sortdeclaration : SORTDECLARATION with type sort = Sort.t

(** {2 Module Specialdeclaration} *)

module type SPECIALDECLARATION = sig
  (*** TYPES *******************************************************************)
  type sort
  type t
  type polsort
  type sd

  (*** VALUES ******************************************************************)
  (** {3 Creation and Recovery functions} *)
  
  val polymorphic_declaration : polsort list -> polsort -> t
  (** [polymorphic_declarations inps out] creates a polymorphic declaration
  with known arity, with input sorts [inps] and output sort [out] *)
  val variable_declaration : polsort -> polsort -> t
  (** [variable_declaration in out] creates a polymorphic declaration with
  unknown arity, with input sorts [inp] and output sort [out] *)
  val known_arity : t -> bool
  (** [known_arity d] returns true if [d] takes a fixed number of arguments *)
  val arity : t -> int
  (** [arity d] returns the number of arguments for [d] provided [d] has a
  known arity
  @raise Failure if the sort has variable arity *)
  val input_sort : int -> t -> polsort
  (** [input_sort i d] returns the [i]th input sort of declaration [d]; if
  [d] has variable arity, any [i] returns the same input sort
  @raise Not_found if [arity d] <= [i] *)
  val input_sorts : t -> polsort list
  (** input_sorts d] returns the list of all input arguments of [d]; if
  [d] has variable arity, this list contains exactly one element *)
  val output_sort : t -> polsort
  (** [output_sort d] returns the output sort of [d] *)

  (** {3 Transforming to normal sortdeclarations} *)

  val is_normal_sortdec : t -> bool
  (** [is_normal_sortdec d] returns true if [d] is a polymorphic sort
  declaration of fixed arity where all sorts in input and output are
  monomorphic *)
  val make_normal_sortdec : t -> sd
  (** [make_normal_sortdec d] transforms [d] into a Sortdeclaration.t
  @raise Failure if [d] has variable arity or polymorphic sorts *)

  (** {3 Dealing with polymorphic sorts} *)

  val make_polsort : string -> ?index:int option -> polsort
  (** [make_polsort str i] makes a possibly polymorphic sort from the
  given string; here, ?A maps to the sort variable A. The optional parameter
  i allows to index the sort. *)
  val sort_to_pol : sort -> polsort
  (** [sort_to_pol str] creates a "polsort" from the given sort *)
  val pol_to_sort : polsort -> sort
  (** [poltosrt s] converts [s] to a sort if [s] is not polymorphic
  @raise Failure if the sort is polymorphic. *)
  val is_polymorphic : polsort -> bool
  (** returns whether the given "polymorphic sort" is actually polymorphic *)

  (** {3 Miscellaneous} *)

  val copy : t -> t
  (** [copy x] returns a copy of [x]. *)
  val hash : t -> int
  (** [hash f] returns a hash value for [f]. It is not guaranteed that
  [hash f = hash g] if and only if [compare f g = 0]. *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare x y] compares [x] and [y]. This function defines a total
  ordering on special declarations. *)
  val equal : t -> t -> bool
  (** [equal x y] checks if [x] and [y] are equal. This function is equivalent
  to [compare x y = 0]. *)

  (** {3 Printers} *)

  val pol_to_string : polsort -> string
  (** [pol_to_string x] returns a string that represents [x];
  this is an inverse of make_polsort. *)
  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt x] prints [x] using the [OCaml] module [Format]. *)
  val to_string : t -> string
  (** [to_string x] returns a string that represents [x]. *)
end

(** This module deals with polymorphic declarations, and declaratios with
variable arity.  Symbols with such a declaration should always be used in
a combination with their currently active sort declaration. *)
module Specialdeclaration : SPECIALDECLARATION
  with type sd = Sortdeclaration.t and type sort = Sort.t

(** {2 Module Environment} *)

module type ENVIRONMENT = sig
  (*** TYPES *******************************************************************)
  type sort
  type t

  (*** VALUES ******************************************************************)
  (** {3 Constructors and Destructors} *)

  val empty : int -> t
  (** [empty i] creates an empty environment which will store approximately [n]
  variables *)
  val dummy : unit -> t
  (** [dummy i] returns an environment which may or may not be in use; it is
  useful for those calls where an environment must be supplied but is not
  actually needed *)
  val drop : t -> unit
  (** [drop e] indicates that environment [e] will no longer be used, and
  can be reset and changed at leisure. *)

  (** {3 Fresh Symbols} *)

  val create_var : string -> sort -> t -> Variable.t
  (** [create_var n d s] returns a fresh variable with name [n] and sort d.
  Note that this symbol is automatically added to the given environment. If [s]
  already contains a variable with name [n] and sort [d], this symbol is
  returned.
  @raise Failure "incorrect sort" if [s] contains already a function symbol
  with name [n] but different sort. *)
  val create_unsorted_var : string -> t -> Variable.t
  (** [create_unsorted_var n s] behaves like create_var, but you don't need to
  give a sort (this can be added afterwards). *)
  val create_sorted_var : sort -> string list -> t -> Variable.t
  (** [create_sorted_var s l e] returns a fresh variable, which has been added
  to the environment with a freshly chosen name, and the given sort. *)
  val create_fresh_var : string list -> t -> Variable.t
  (* [create_fresh_var l e] returns a fresh, unsorted variable which is
  registered in the environment with a newly generated name (not already
  in the environment or in [l]) *)
  val create_var_like : Variable.t -> t -> string list -> t -> Variable.t
  (* [create_var_like x xenv l e] creates a fresh variable in the environment
  [e] (which may, but does not need to, be equal to [xenv]), which has the
  same sort as [x] has in [xenv], if any, and if possible shares the same
  name as well (if not, which can be the case if the name already occurs in
  [e] or is in [l], a fresh name is chosen) *)
  val generate_var_name : bool -> string -> string list -> t -> string
  (** [generate_var_name bound sortname block env] suggests a name to be used
  for a variable which is bound if [bound] is true and has the given sort
  (omit if the sort is unknown); names in [block] and registered variables in
  the given environment are excluded *)

  (** {3 Updating Symbols} *)

  val add_sort : Variable.t -> sort -> t -> unit
  (** [add_sort x d s] sets the sort of the variable [x] to [d]. If the sort
  of [f] has already been set, the environment remains unchanged. *)
  val replace_sort : Variable.t -> sort -> t -> unit
  (** [replace_sort x d s] replaces the sort of the variable [x] by [d]. *)

  (** {3 Search Functions} *)
 
  val find_var : string -> t -> Variable.t
  (** [find_var n s] returns the variable that has name [n] with respect to
  the environment [s].
  @raise Not_found if [s] does not contain a binding for [n]. *)
  val find_sort : Variable.t -> t -> sort
  (** [find_sort x s] returns the sort of the variable [x] with respect to
  the environment [s].
  @raise Not_found if [s] does not contain a binding for [x], or it has no
  sort associated to it. *)
  val vars : t -> Variable.t list
  (** [vars s] returns all variables in the environment [s]. *)
  val var_names : t -> string list
  (** [var_names s] returns the names of all variables with respect
  to environment [s]. *)
 
  (** {3 Scan Functions} *)

  val is_defined : Variable.t -> t -> bool
  (** [is_defined_var x s] checks if the name of [x] is defined. *)
  val has_sort : Variable.t -> t -> bool
  (** [has_sort x s] checks if the sort of [x] is defined. *)
  val mem_var_name : string -> t -> bool
  (** [mem_var_name n s] checks if there exists a variable with name [n]. *)
  val is_sort : Variable.t -> sort -> t -> bool
  (** [is_sort x d s] checks if the sort of [x] is [d] (if x does not have
  a sort, false is returned). *)
 
  (** {3 Miscellaneous} *)
 
  val copy : t -> t
  (** [copy s] makes a copy of [s], stores it, and returns the poitner. *)
  val hash : t -> int
  (** [hash s] returns a hash code for [s]; equal enviroments may have
  different hash values if they have a different index! *)
  val reset : t -> unit
  (** [reset s] removes all variables, sorts and names from [s], to
  start over *)
 
  (** {3 Printers} *)
 
  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt s] prints [s] using the [OCaml] module [Format]. *)
  val to_string : t -> string
  (** [to_string s] returns a formatted string that represents [s]. *)
end

(** This module keeps track of an environment for variables, saving both a
name and a sort for each variable. Internally, the environment module saves
all environments ever declared; the Environment.t type merely gives a pointer
to refer to an existing environment. *)
module Environment : ENVIRONMENT with type sort = Sort.t

(** {2 Module Alphabet} *)

module type ALPHABET = sig
  (*** TYPES ******************************************************************)
  type t
  type sort
  type sd
  type spd
  type func
  type symbolkind = Terms | Logical | Both

  (*** VALUES *****************************************************************)
  (** {3 Constructors and Destructors} *)

  val empty : int -> t
  (** [empty i] creates an empty alphabet which will store approximately [n]
  variables and functions. *)
  val value_alphabet : unit -> t
  (** [value_alphabet ()] is an alphabet containing only the integers,
  booleans and integer arrays *)

  (** {3 Fresh Symbols} *)

  val create_fun : sd -> string -> t -> func
  (** [create_fun d n s] returns a fresh function with name [n] and sort
  declaration d. Note that this function symbol has been added to the
  alphabet. If [s] contains already a function symbol with name [n] and sort
  declaration [d], this function symbol is returned. 
  @raise Failure "incorrect arity" if [s] contains already a function symbol
  with name [n] but different arity or sort declaration. *)
  val create_instance_fun : spd -> string -> t -> func
  (** [create_instance_fun d n s] returns a fresh function with name [n] and
  special sort declaration [d]. Note that this function symbol is added to the
  alphabet. If [s] contains already a function symbol with name [n] and
  sort declaration [d], this function symbol is returned.
  @raise Failure "incorrect arity" if [s] contains already a function symbol
  with name [n] but different arity or sort declaration. *)
  val create_unsorted_fun : int -> string -> t -> func
  (** [create_unsorted_fun a s] behaves like create_fun, but does not require
  a sort declaration (the sort can be added afterwards by add_sortdec, or may
  be derived automatically given a set of rules). Note that if the given
  function already exists, with or without sort declaration, this function
  symbol is returned. *)
  val fresh_fun : string -> t -> func
  (** [fresh_fun n s] returns a fresh function symbol with name [n]. Note
  that this function symbol is immediately added to the alphabet, but
  without arity or sort declaration! *)
  val include_integers : sort -> t -> unit
  (** [include_integers s d] makes sure that occurrences of an integer
  (positive or negative) in [s] are treated in a special way: they are
  considered to be pre-declared, become "integer symbols" (see also Function.t)
  and are all included in the alphabet with sort [d] (although due to the
  infinite number of them, they will not be printed).  This should be done
  before including any function symbols which may be integers! *)
  val include_arrays : sort -> sort -> t -> unit
  (** [include_arrays isort osort a] makes sure that occurrences of an
  array with input elements of sort [isort] are treated in a special way:
  they are considered to be pre-declared, become "array symbols") (see also
  Function.t) and are all included in the alphabet with sort [sort] (although
  due to their infinite number, they will not be printed).
  This should be done before including any function symbols which may be
  arrays!
  Note: you may call include_arrays multiple times, but the input sorts must
  be unique. *)
  val include_mixed : string -> string -> sort -> t -> unit
  (** [include_mixed openbracket closebracket sort a] makes sure that "mixed"
  strings are included in the alphabet [a].  The strings are identified by
  starting with [openbracket] and ending with [closebracket]; typically, the
  brackets should be something like [ and ], or " and ", but it could also be
  multi-character combinations to allow for a variety of different sorts with
  mixed symbols.  The include_mixed call should be done before including any
  function symbols which may be mixed symbols!
  Note: you may call include_mixed multiple times, but the bracketing must
  uniquely identify a symbol. Do not also include a function symbol which
  starts and ends with these same strings! There is no guarantee what will
  happen if a given function name could correspond to different kinds of
  symbols (including mixed symbols with different sorts). *)

  (** {3 Adding information to function symbols} *)

  val add_ari : func -> int -> t -> unit
  (** [add_ari f a s] sets the arity of the function symbol [f] to [a]. If
  the arity of [f] has already been set, the alphabet remains unchanged. *)
  val add_sortdec : func -> (sd, spd) Util.either -> t -> unit
  (** [add_sortdec f a s] sets the sort declaration of the function symbol [f]
  to [a]. If the sort declaration of [f] has already been set, the alphabet
  remains unchanged. *)
  val add_normal_sortdec : func -> sd -> t -> unit
  (** [add_normal_sortdec f d s] is just [add_sortdec f (Left d) s] *)
  val add_special_sortdec : func -> spd -> t -> unit
  (** [add_special_sortdec f d s] is just [add_sortdec f (Right d) s] *)
  val replace_ari : func -> int -> t -> unit
  (** [replace_ari f a s] replaces the arity of the function symbol [f] by
  [a]. *)
  val replace_sortdec : func -> (sd, spd) Util.either -> t -> unit
  (** [replace_ari f a s] replaces the sort of the function symbol [f] by
  [a]. *)
  val replace_normal_sortdec : func -> sd -> t -> unit
  (** [replace_normal_sortdec f d s] is just [replace_sortdec f (Left d) s] *)
  val replace_special_sortdec : func -> spd -> t -> unit
  (** [replace_special_sortdec f d s] is just [replace_sortdec f (Right d) s] *)
  val set_symbol_kind : func -> symbolkind -> t -> unit
  (** [set_symbol_kind f k s] determines that [f] is in the sub-alphabet [k]
  of [s].  If [s] contains already contains a sub-alphabet for [f], then this
  is overridden.  Note that integers are automatically marked as "Both" and
  only values may be marked as Both. *)
  val add_symbol_kind : func -> symbolkind -> t -> unit
  (** [add_symbol_kind f k s] adds the symbol kind ]k] to [f] in [s].  Here,
  "adding" means that if Terms is added and its symbol kind is already Logical,
  then the kind because Both; also the other way around.  If the existing kind
  is already Both, nothing is done. *)

  (** {3 Search Functions} *)
 
  val find_ari : func -> t -> int
  (** [find_ari f s] returns the arity of the function symbol [f] with respect
  to the alphabet [s].
  @raise Not_found if [s] does not contain a binding for [f]. *)
  val find_sortdec : func -> t -> (sd, spd) Util.either
  (** [find_sortdec f s] returns the sort declaration of the function symbol
  [f] with respect to the alphabet [s]; this may be either a normal or a
  special sort declaration
  @raise Not_found if [s] does not contain a binding for [f]. *)
  val find_fun : string -> t -> func
  (** [find_fun n s] returns the function that has name [n] with respect to
  the alphabet [s].
  @raise Not_found if [s] does not contain a binding for [n]. *)
  val find_symbol_kind : func -> t -> symbolkind
  (** [find_symbol_kind f s] returns the symbol kind of the function symbol
  [f] with respect to the alphabet [s].
  @raise Not_found if [s] does not contain a symbol kind for [f]. *)
  val funs : ?p:(func -> bool) -> t -> func list
  (** [funs p s] returns all functions occurring in the alphabet [s],
  which for which [p] returns true.  If [p] is not given, it simply
  returns all functions. *)
  val fun_names : t -> string list
  (** [fun_names s] returns the names of all functions with respect
  to alphabet [s]. *)
  val integer_sort : t -> sort
  (** [integer_sort s] returns the sort for all integers in the given
  alphabet [s]
  @raise Not_found if [s] does not support integers. *)
  val array_sort : sort -> t -> sort
  (** [array_sort sort a] returns the sort for arrays with input sort
  [sort] in the given alphabet [a]
  @raise Not_found if [a] does not support arrays of the given sort *)
  val mixed_sort : (string * string) -> t -> sort
  (** [mixed_sort (ob, cb) a] returns the sort for mixed symbols with
  brackets ([ob], [cb]) in the given alphabet [a]
  @raise Not_found if [a] does not support mixed symbols with the
  given brackets *)
  val default_intsort : sort
  (* [default_intsort] is the recommended sort to use for integers *)
  val boolsort : sort
  (* [boolsort a] is the (immutable) sort to be used for booleans *)
  val arraysorts : t -> sort list
  (* [arraysorts a] contains all the array sorts registered to [a] *)
  val arraysorts_of : t -> sort list
  (* [arraysorts a] contains all the sorts t such that an array of
  values of type [t] is registered as arraysort *)
  val mixedsorts : t -> sort list
  (* [mixedsorts a] contains all the sorts of mixed symbols registered
  to [a] *)
  val find_sorts : t -> sort list
  (* [sorts s] returns all sorts used in the given alphabet [s] *)
  val find_logical_sorts : t -> sort list
  (* [find_logical_sorts s] returns all sorts used as input or output
  sorts for logical symbols occurring in the given alphabet [s] *)
  val find_symbols_with_sort : t -> sort -> func list
  (* [find_symbols_with_sort s sort] returns all symbols which have
  either a variable output sort, or the given output sort.  Note that
  no integers are returned, even if the intsort is supported, and
  that polymorphic symbols with variable output sort are always
  included. *)
  val test_mixed : sort -> t -> (string * string) option
  (* [test_mixed sort a] returns None if [sort] is not a MIXED sort,
  otherwise Some (openbracket, closebracket) *)
 
  (** {3 Scan Functions} *)
 
  val is_ari : int -> func -> t -> bool
  (** [is_ari n f s] checks if the arity of [f] is [n]. *)
  val is_sort : sort -> func -> t -> bool option
  (** [is_sort n f s] checks if the output sort of [f] is [n]; if
  the output sort is unknown (or polymorphic), this returns None,
  otherwise Some <true|false>. *)
  val is_argument_sort : int -> sort -> func -> t -> bool option
  (** [is_argument_sort n a f s] checks if the [n]th argument of [f]
  should have sort [a]; if the input sorts are unknown (or polymorphic)
  this returns None, otherwise Some <true|false>.
  @raise Failure if the sort declaration is known, but the arity is
  lower than [n]. *)
  val is_defined_fun : func -> t -> bool
  (** [is_defined_fun f s] checks if the arity and name of [f] is defined. *)
  val is_value : func -> t -> bool
  (** [is_value f s] checks if [f] is a value in [s]; this simplify returns
  false if the arity is not set!
  @raise failure if symbol kind of f is not set *)
  val mem_ari : func -> t -> bool
  (** [mem_ari f s] checks if the arity of [f] is defined. *)
  val mem_fun_name : string -> t -> bool
  (** [mem_var_name n s] checks if there exists a function with name [n]. *)
  val mem_symbol_kind : func -> t -> bool
  (** [mem_symbol_kind f s] checks if the symbol kind of [f] is defined. *)
  val mem_sortdec : func -> t -> bool
  (** [mem_sortdec f s] returns true if the function symbol [f] has been
  given a sort declaration in the alphabet [s] (which may be a normal or
  a special declaration). *)
  val has_integers : t -> bool
  (** [has_integers s] checks whether [s] includes the integers. *)
  val has_arrays : t -> bool
  (** [has_arrays s] checks whether [s] includes any arrays. *)
  val has_arrays_of : sort -> t -> bool
  (** [has_arrays_of sort s] checks whether [s] includes arrays of sort
  [sort] *)
  val has_mixeds : t -> bool
  (** [has_mixeds s] checks whether [s] includes any mixed symbols. *)
  val logical_sorts_inhabited : t -> bool
  (** [logical_sorts_inhabited s] checks whether [s] contains values
  for all sorts occurring in a logical or shared symbol *)

  (** {3 Logical Functions with a Special meaning} *)

  val set_and_symbol : func -> t -> unit
  (** [set_and_symbol f a] stores [f] as the symbol AND
  raises Failure if func does not have at least arity 2, or a
  polymorphic output sort *)
  val set_or_symbol : func -> t -> unit
  (** [set_or_symbol f a] stores [f] as the symbol OR
  raises Failure if func does not have at least arity 2, or a
  polymorphic output sort *)
  val set_imply_symbol : func -> t -> unit
  (** [set_imply_symbol f a] stores [f] as the symbol =>
  raises Failure if func does not have fixed arity 2, or a polymorphic
  output sort *)
  val set_not_symbol : func -> t -> unit
  (** [set_not_symbol f a] stores [f] as the symbol NOT
  raises Failure if func does not have fixed arity 1, or a polymorphic
  output sort *)
  val set_bot_symbol : func -> t -> unit
  (** [set_bot_symbol f a] stores [f] as the symbol FALSE
  raises Failure if func does not have fixed arity 0, or a polymorphic
  output sort *)
  val set_top_symbol : func -> t -> unit
  (** [set_top_symbol f a] stores [f] as the symbol TRUE
  raises Failure if func does not have fixed arity 0, or a polymorphic
  output sort *)
  val set_equal_symbol : func -> t -> unit
  (** [set_equal_symbol f a] stores [f] as the symbol =
  raises Failure if func does not have at least arity 2, or a
  polymorphic output sort *)
  val set_geq_symbol : func -> t -> unit
  (** [set_geq_symbol f a] stores [f] as the symbol >=
  raises Failure if func does not have arity 2, or a polymorphic
  output sort *)
  val set_leq_symbol : func -> t -> unit
  (** [set_leq_symbol f a] stores [f] as the symbol <=
  raises Failure if func does not have arity 2, or a polymorphic
  output sort *)
  val set_greater_symbol : func -> t -> unit
  (** [set_geq_symbol f a] stores [f] as the symbol >
  raises Failure if func does not have arity 2, or a polymorphic
  output sort *)
  val set_smaller_symbol : func -> t -> unit
  (** [set_smaller_symbol f a] stores [f] as the symbol >=
  raises Failure if func does not have arity 2, or a polymorphic
  output sort *)
  val get_and_symbol : t -> func
  (** [get_and_symbol a] returns the symbol for AND stored in [a], or
  throws a Not_found error if no such symbol has been set *)
  val get_or_symbol : t -> func
  (** [get_or_symbol a] returns the symbol for OR stored in [a], or
  throws a Not_found error if no such symbol has been set *)
  val get_imply_symbol : t -> func
  (** [get_imply_symbol a] returns the symbol for => stored in [a],
  or throws a Not_found error if no such symbol has been set *)
  val get_not_symbol : t -> func
  (** [get_not_symbol a] returns the symbol for NOT stored in [a], or
  throws a Not_found error if no such symbol has been set *)
  val get_bot_symbol : t -> func
  (** [get_bot_symbol a] returns the symbol for FALSE stored in [a],
  or throws a Not_found error if no such symbol has been set *)
  val get_top_symbol : t -> func
  (** [get_top_symbol a] returns the symbol for TRUE stored in [a],
  or throws a Not_found error if no such symbol has been set *)
  val get_equal_symbol : t -> func
  (** [get_equal_symbol a] returns the symbol for = stored in [a],
  or throws a Not_found error if no such symbol has been set *)
  val get_geq_symbol : t -> func
  (** [get_geq_symbol a] returns the symbol for >= stored in [a],
  or throws a Not_found error if no such symbol has been set *)
  val get_leq_symbol : t -> func
  (** [get_leq_symbol a] returns the symbol for <= stored in [a],
  or throws a Not_found error if no such symbol has been set *)
  val get_greater_symbol : t -> func
  (** [get_greater_symbol a] returns the symbol for > stored in [a],
  or throws a Not_found error if no such symbol has been set *)
  val get_smaller_symbol : t -> func
  (** [get_smaller_symbol a] returns the symbol for < stored in [a],
  or throws a Not_found error if no such symbol has been set *)

  val add_wellfounded : sort -> func -> t -> unit
  (** [add_wellfounded sort f] marks a relation symbol for the given
  sort (i.e. f : sort * sort => Bool) as well-founded, for use in
  termination checks *)
  val get_wellfounded : sort -> t -> func list
  (** [get_wellfounded sort] returns all the symbols marked as
  wellfounded for the given sort *)
  val sorts_with_wellfounded_relations : t -> sort list
  (** [sorts_with_wellfounded_relations] returns all the sorts for
  which a well-founded relation is set *)
 
  (** {3 Miscellaneous} *)
 
  val copy : t -> t
  (** [copy s] returns a copy of [s]. *)
  val hash : t -> int
  (** [hash s] returns a hash code for [s]; equal alphabets may have
  different hash values if they have a different index! *)
 
  (** {3 Printers} *)
 
  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt s] prints [s] using the [OCaml] module [Format]. *)
  val to_string : t -> string
  (** [to_string s] returns a formatted string that represents [s]. *)
end

(** This module keeps track of an alphabet for function symbols, saving both
name, arity and a sort declaration for each symbol. Internally, the alphabet
module saves all alphabets ever declared; the Alphabet.t type merely gives a
pointer to refer to an existing environment. *)
module Alphabet : ALPHABET with type sort = Sort.t
       and type sd = Sortdeclaration.t and type spd = Specialdeclaration.t
       and type func = Function.t

(** {2 Module Position} *)

module type POSITION = sig
  (*** TYPES *******************************************************************)
  type t
 
  (*** VALUES ******************************************************************)
  (** {3 Constructors and Destructors} *)
  
  val add_first : int -> t -> t
  (** [add_first i p] creates the position [ip]. *)
  val add_last : int -> t -> t
  (** [add_last i p] creates the position [pi]. Not tail-recursive. *)
  val root : t
  (** [root] represents the root position. *)
  val head : t -> int
  (** [head p] returns the first number of the position [p], i.e., if [p = iq]
  then [i] is returned.
  @raise Failure "root position" if [p] is the root position. *)
  val init : t -> t
  (** [init p] returns the position [p] without the last number, i.e., if
  [p = qi] then the position [q] is returned.
  @raise Failure "root position" if [p] is the root position. *)
  val last : t -> int
  (** [last p] returns the last number of the position [p], i.e., if [p = qi]
  then [i] is returned.
  @raise Failure "root position" if [p] is the root position. *)
  val make : int -> t
  (** [make i] creates the position [i]. *)
  val of_list : int list -> t
  (** [of_list l] constructs the position [i_1...i_n] where the list
  [l = \[i_1;...;i_n\]]. *)
  val split_first : t -> int * t
  (** [split_first p] returns the pair [(i,q)] where [p = iq].
  @raise Failure "root position" if [p] is the root position. *)
  val split_last : t -> t * int
  (** [split_last p] returns the pair [(q,i)] where [p = qi].
  @raise Failure "root position" if [p] is the root position. *)
  val tail : t -> t
  (** [tail p] returns the position [p] without the first number, i.e., if
  [p = iq] then the position [q] is returned.
  @raise Failure "root position" if [p] is the root position. *)
  val to_list : t -> int list
  (** [to_list p] returns [p] as a list. *)
 
  (** {3 Properties} *)
  
  val (||) : t -> t -> bool
  (** [p || q] checks if [p] and [q] are parallel positions. *)
  val (<=) : t -> t -> bool
  (** [p <= q] checks if [p] is a prefix of [q]. *)
  val (<) : t -> t -> bool
  (** [p < q] checks if [p] is a proper prefix of [q]. *)
  val (>=) : t -> t -> bool
  (** [p >= q] is equivalent to [q <= p]. *)
  val (>) : t -> t -> bool
  (** [p > q] is equivalent to [q < p]. *)
  val is_root : t -> bool
  (** [is_root p] checks if [p] is the root position. *)
  val are_parallel : t -> t -> bool
  (** [are_parallel p q] is equivalent to {!val: Ctrs.POSITION.(||)}. *)
  val is_prefix : t -> t -> bool
  (** [is_prefix p q] is equivalent to {!val: Ctrs.POSITION.(<=)}. *)
  val is_proper_prefix : t -> t -> bool
  (** [is_proper_prefix p q] is equivalent to {!val: Ctrs.POSITION.(<)}. *)
  val is_proper_suffix : t -> t -> bool
  (** [is_proper_suffix p q] checks if [p] is a proper suffix of [q]. *)
  val is_suffix : t -> t -> bool
  (** [is_suffix p q] checks if [p] is a suffix of [q]. *)
  val is_head : int -> t -> bool
  (** [is_head i p] checks if [p] has the form [iq]. *)
 
  (** {3 Miscellaneous} *)
 
  val append : t -> t -> t
  (** [append p q] concatenates the positions [p] and [q]. The returned position
  is [pq]. This function is not tail-recursive. *)
  val copy : t -> t
  (** [copy p] returns a copy of [p]. *)
  val hash : t -> int
  (** [hash p] returns the hash value of [p]. It is guaranteed that
  [hash p = hash q] if [compare p q = 0]. *)
  val length : t -> int
  (** [length p] returns the length of the position [p]. *)
 
  (** {3 Compare Functions} *)
  
  val compare : t -> t -> int
  (** [compare p q] compares [p] and [q]. This function defines a total
  ordering on positions. *)
  val equal : t -> t -> bool
  (** [equal p q] checks if [p] and [q] are equal. This function is equivalent
  to [compare p q = 0]. *)
  
  (** {3 Printers} *)
  
  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt p] prints [p] using the [OCaml] module [Format]. *)
  val to_string : t -> string
  (** [to_string p] returns a formatted string that represents [p]. *)
end

(** This module provides basic functions that deal with term positions. Note
that the first argument of a term has position [0] and not [1]. *)
module Position : POSITION

(** {2 Module Csmapping} *)

module type CSMAPPING = sig
  (*** TYPES ******************************************************************)
  type func
  type t

  (*** VALUES *****************************************************************)
  (** {3 Constructors} *)

  val empty : unit -> t
  (** [empty ()] creates a new context-sensitivity mapping and returns it *)
  val fill : Alphabet.t -> t -> unit
  (** [fill a m] fills the given context-sensitivity mapping [m] for the given
  alphabet; as the name suggests, the mapping contains all symbols and maps
  them to all their positions.  Only function symbols which have an arity in
  [a] are included in the result. *)

  (** {3 Usage Functions} *)

  val set_reducable_positions : func -> int list -> t -> unit
  (** [set_reducable_positions f lst mu] sets the arguments which can be
  reduced below [f] to [lst] in the context-sensitivity mapping [mu] *)
  val get_reducable_positions : func -> t -> int list
  (** [get_reducable_positions f mu] returns a list of positions of [f] below
  which may be reduced according to the mapping [mu].  This list is ordered.
  However, it is more efficient to use [is_reducable_at] to check whether a
  given position is reducable. *)
  val is_reducable_at : func -> int -> t -> bool
  (** [is_reducable_at f i mu] returns true if [i] is a reduable position for
  [f] in the context-sensitivity mapping [mu] and false otherwise *)

  (** {3 Printers} *)
  
  val fprintf : Format.formatter -> t -> unit
end

(** This module provides functionality for context-sensitivity mappings (and
keeps track of all context-sensitivity mappings currently in use *)
module Csmapping : CSMAPPING with type func = Function.t;;

(** {2 Module Term} *)

module type TERM = sig
  (*** TYPES *******************************************************************)
  type func
  type sort
  type sd
  type t = Var of Variable.t | Fun of func * t list |
           InstanceFun of func * t list * sd |
           Forall of Variable.t * t |
           Exists of Variable.t * t
 
  (*** VALUES ******************************************************************)
  (** {3 Constructors} *)

  val make_fun : func -> t list -> t 
  (** [make_fun f ts] returns the term [Fun (f,ts)]. *)
  val make_instance : func -> t list -> sd -> t
  (** [make_instance f ts d] returns the term InstanceFun (f,ts,d). *)
  val make_function : Alphabet.t -> Environment.t -> func -> t list -> t
  (** [make_function a e f ts] returns either the term [Fun (f,ts)] or
  the term [InstanceFun (f,ts,d)] where [d] is a suitable sort
  declaration.  This function may only be used if [f] has a sort
  declaration in [a], and the output sort of this sort declaration is
  not polymorphic.  There is no check whether the sorts in [ts]
  actually match the expected input sorts (as there is also no check
  in the other make_ functions). *)
  val make_var : Variable.t -> t 
  (** [make_var x] returns the term [Var x]. *)
  (* val reflect : t -> t *)
  (** [reflect t] reverses the arguments of all functions in [t]. This function
  is not tail-recursive. *)
  val make_forall : Variable.t -> t -> t
  (** [make_forall x s] returns the term Forall (x,s). *)
  val make_exists : Variable.t -> t -> t
  (** [make_exists x s] returns the term Exists (x,s). *)
  val replace : Position.t -> t -> t -> t 
  (** [replace p s t] replaces the subterm of [t] at position [p] by [s].
  This function is not tail-recursive.
  @raise Failure "illegal position" if [p] is not a valid position for [t]. *)
  val reverse : t -> t
  (** [reverse t] reverses the string [t]. Note that a string is a term build
  of unary function symbols. This function is not tail-recursive.
  @raise Failure "not a string" if [t] is not a string.
  @raise Failure "Cannot reverse an instance function" if [t] uses any instance
  functions *)
  val subterm : Position.t -> t -> t
  (** [subterm p t] returns the subterm of [t] at position [p].
  @raise Failure "illegal position" if [p] is not a valid position for [t]. *)
  val subterm_with_binders : Position.t -> t -> Variable.t list * t
  (** [subterm_with_binders p t] returns the subterm of [t] at position [p],
  together with a list of variables which are free in the subterm but bound
  in the original *)
  val logical_cap : Alphabet.t -> Environment.t -> t -> t
  (** [logical_cap alph env t] replaces all non-variable subterms of nonlogical
  sort by a fresh variable. *)

  (** {3 Term Symbols} *)

  val cons : t -> func list
  (** [cons t] returns all constants of the term [t]. This function is not
  tail-recursive. *)
  val funs : t -> func list
  (** [funs t] returns all function symbols of the term [t]. This function is
  not tail-recursive. *)
  val root : t -> func option
  (** [root t] returns the root symbol of [t]; for variables and Forall /
  Exists, None is returned. *)
  val symbols : t -> (Variable.t,func) Util.either list
  (** [symbols t] returns all symbols of the term [t]. This function is not
  tail-recursive. *)
  val vars : t -> Variable.t list
  (** [vars t] returns all variables of the term [t]. This function is not
  tail-recursive, and does not return bound variables. *)
  val allvars : t -> Variable.t list
  (** [allvars t] returns all variables of the term [t], including bound
  ones.  This function is not tail-recursive. *)

  (** {3 Properties} *)

  val is_build : func list -> t -> bool
  (** [is_build fs t] checks if all function symbols of [t] occur in [fs]. *)
  val is_forall : t -> bool
  (** [is_forall t] checks if [t] is a Forall formula *)
  val is_exists : t -> bool
  (** [is_exists t] checks if [t] is an Exists formula *)
  val is_cons : t -> bool
  (** [is_cons t] checks if [t] is a constant. *)
  val is_dummy : t -> bool
  (** [is_dummy t] checks if [t] is term consisting only of unary function
  symbols and constants. *)
  val is_flat : t -> bool
  (** [is_flat t] checks if [t] is a flat term, i.e., a term with depth smaller
  or equal to [1]. *)
  val is_fun : t -> bool
  (** [is_fun t] checks if [t] is a function. This also returns true if
  [t] is an instance function! *)
  val is_instance : t -> bool
  (** [is_instance t] checks if [t] is an instance function. *)
  val is_ground : t -> bool
  (** [is_ground t] checks if [t] is a ground term, i.e., a term that does not
  contain any variables. *)
  val is_linear : t -> bool
  (** [is_linear t] checks if [t] is linear. A term [t] is said to be linear
  if all variables occur at most once. This function is not tail-recursive. *)
  val is_proper_subterm : t -> t -> bool
  (** [is_proper_subterm s t] check if [s] is a proper subterm of [t]. *)
  val is_shallow : t -> bool
  (** [is_shallow t] checks if the term [t] is shallow. Note that a term [t] is
  shallow if each variable occurs at most at depth [1]. *)
  val is_string : t -> bool
  (** [is_string t] checks if all function symbols of [t] have arity [1]. *)
  val is_subterm : t -> t -> bool
  (** [is_subterm s t] check if [s] is a subterm of [t]. *)
  val is_var : t -> bool
  (** [is_var t] checks if [t] is a variable. *)
  val is_value : Alphabet.t -> t -> bool
  (** [is_value t a] checks if [t] is a value in alphabet [a]
  @raise Not_found if [t] = f() and the symbol kind for f is not set *)
  val check_proper_term : Alphabet.t -> t -> Position.t option
  (** [is_proper_term a t] checks whether all symbols in [t] have symbol kind
  term (if this is not the case, [t] is just a typable expression) or Both.
  The result is either None, if [t] is a proper term, or a position of a
  logical subterm.
  @raise Failure if [t] contains a symbol whose kind is unknown. *)
  val check_logical_term : Alphabet.t -> t -> Position.t option
  (** [is_logical_term a t] checks whether all symbols in [t] have symbol
  kind Logical.  The result is either None, if [t] is a logical term, or a
  position of a non-logical subterm
  @raise Failure if [t] contains a symbol whose kind is unknown. *)

  (** {3 Search Functions} *)

  val mem_fun : func -> t -> bool
  (** [mem_fun f t] checks if [f] occurs in [t]. *)
  val mem_var : Variable.t -> t -> bool
  (** [mem_var x t] checks if [x] occurs in [t]. *)

  (** {3 Positions} *)

  val fun_pos : func -> t -> Position.t list
  (** [fun_pos f t] returns the positions of the function [f] with respect to
  the term [t]. This function is not tail-recursive. *)
  val funs_pos : t -> Position.t list
  (** [funs_pos t] returns the positions of all functions of the term [t]. This
  function is not tail-recursive. *)
  val funs_pos_with_fun : t -> (Position.t * func) list
  (** [funs_pos t] returns the positions of all functions of the term [t],
  together with the function symbol at that position. This function is not
  tail-recursive. *)
  val quantifier_pos : t -> Position.t list
  (** [quantifier_pos t] returns the positions of all quantifiers of the term
  [t].  This function is not tail-recursive. *)
  val pos : t -> Position.t list
  (** [pos t] returns all positions of the term [t]. This function is not
  tail-recursive. Note: positions ending in -1 denote the positions of
  binder variables of Forall or Exist occurrences. *)
  val req_pos : (t -> bool) -> t -> Position.t list
  (** [req_pos f t] returns all positions of the term [t] such that [f s] is
  true, where s is the subterm at that position *)
  val accessible_fun_pos : func -> Csmapping.t -> t -> Position.t list
  (** [accessible_fun_pos f t] returns all [mu]-accessible positions of the
  function [f] with respect to the term [t].
  This function is not tail-recursive. *)
  val accessible_funs_pos : Csmapping.t -> t -> Position.t list
  (** [accessible_funs_pos t] returns all [mu]-accessible positions of all
  functions of the term [t]. This function is not tail-recursive. *)
  val accessible_pos : Csmapping.t -> t -> Position.t list
  (** [accessible_pos t mu] returns all positions of the term [t] which are
  [mu]-accessible *)
  val subterm_pos : t -> t -> Position.t list
  (** [subterm_pos s t] returns the positions of the term [s] with respect to
  the term [t]. This function is not tail-recursive. *)
  val var_pos : Variable.t -> t -> Position.t list
  (** [var_pos x t] returns the positions of the variable [x] with respect to
  the term [t]. This function is not tail-recursive. *)
  val vars_pos : t -> Position.t list
  (** [vars_pos t] returns the positions of all variables of the term [t].
  This function is not tail-recursive. *)
  val has_pos : Position.t -> t -> bool
  (** [has_pos p t] returns whether [p] is a position of [t] *)

  (** {3 Folds} *)
  val count_fun : func -> t -> int
  (** [count_fun f t] returns the number of occurrences of [f] in [t]. *)
  val fold_funs : (func -> 'a -> 'a) -> 'a -> t -> 'a
  (** [fold_funs f d t] combines all function symbols of [t] with the
  default value [d], using the function [f]. *)

  (** {3 Iterators} *)

  val recurse : (Variable.t -> 'a) -> (func -> 'a list -> 'a) ->
                (func -> 'a list -> sd -> 'a) ->
                (Variable.t -> 'a -> 'a) -> (Variable.t -> 'a -> 'a) ->
                t -> 'a
  (** [recurse fv ff fi fa fe term] applies the function fv on a variable,
  and for terms f(t1,...,tn), it recursively calculates the values of
  arguments, and then applies ft on f and the list of values, or fi on f,
  the list of values and the sortdeclaration if f is an instance function.
  Forall and Exists terms are handled with fa and fe respectively.
  This function is not tail-recursive. *)
  val map : (func -> func) -> t -> t
  (** [map f t] applies the function [f] to all function symbols of the term
  [t]. This function is not tail-recursive. *)

  (** {3 Miscellaneous} *)

  val args : t -> t list
  (** [args t] returns the immediate arguments of the term [t]. If [t] is a
  variable, the empty list is returned. *)
  val replace_args : t -> t list -> t
  (** [replace_args f(a1,...,an) (b1,...,bm)] returns f(b1,...,bm); typability
  of the new term is not checked, but n and m should be the same, and also the
  ai and bi should have the same types (even if, in theory, the term would
  still be typable if this were not the case). If the given term is a variable,
  it is returned unmodified. For a quantifier, the single argument is replaced.
  *)
  val copy : t -> t
  (** [copy t] copies the term [t]. *)
  val depth : t -> int
  (** [depth t] returns the depth of the term [t]. This function is not
  tail-recursive. *)
  val fun_size : t -> int
  (** [fun_size t] returns the total number of function symbols of the term
  [t]. Note that double occurrences of a function symbol are counted twice.
  This function is not tail-recursive. *)
  val get_sort : Alphabet.t -> Environment.t -> t -> sort
  (** [get_sort alph env t] returns the sort of the given term, for the
  given alphabet and environment.
  @fail if the sort of the given term is not known. *)
  val hash : t -> int
  (** [hash t] returns a hash value for [t]. It is guaranteed that
  [hash s = hash t] whenever [compare s t = 0]. *)
  val proper_subterms : ?p:(t -> bool) -> t -> t list
  (** [proper_subterms ~p:p t] returns all proper subterms of [t] that satisfy
  the predicate [p]. This function is not tail-recursive. *)
  val size : t -> int
  (** [size t] returns the size of the term [t]. This function is not
  tail-recursive. *)
  val subterms : ?p:(t -> bool) -> t -> t list
  (** [subterms ~p:p t] returns all subterms of [t] that satisfy the predicate
  [p]. This function is not tail-recursive. *)
  val var_size : t -> int
  (** [var_size t] returns the total number of variables of the term [t].
  Note that double occurrences of a variable are counted twice, and that
  bound variables are also counted. This function is not tail-recursive. *)
  val quantifier_size : t -> int
  (** [quantifier_size t] returns the total number of quantifiers of the term
  [t]. This function is not tail-recursive. *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare s t] compares [s] and [t]. This function defines a total
  ordering on terms. *)
  val equal : t -> t -> bool
  (** [equal s t] checks if [s] and [t] are equal. This function is equivalent
  to [compare s t = 0]. *)

  (** {3 Parsers} *)

  val read_value : string -> Alphabet.t -> string -> t
  (* [read_value t a src] reads [t] into a term provided [t] represents a
  value for alphabet [a].  The text src is used in error messages if the
  given string does not represent a value.
  In [t], infix notation is not permitted, applicative notation is.
  This must be a value which is both in the logical alphabet and in the
  term alphabet. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt t] prints [t] using the [OCaml] module [Format]. This
  function is not tail-recursive. *)
  val to_string : t -> string
  (** [to_string t] returns a string that represents [t]. This function is
  not tail-recursive.*)
  val to_stringm : t -> string
  (** [to_stringm t a e] returns a string that represents [t], but with less
  debug information than to_string. This function is not tail-recursive. *)
end

(** This module provides basic functions that deal with terms. *)
module Term : TERM with type func = Function.t and type sort = Sort.t
                    and type sd = Sortdeclaration.t;;

(** {2 Module Context} *)

module type CONTEXT = sig
  (*** TYPES *******************************************************************)
  type func
  type term
  type t = Hole | More of func * term list * t * term list

  (*** VALUES ******************************************************************)
  (** {3 Constructors and Destructors} *)

  val apply : term -> t -> term
  (** [apply t c] plugs the term [t] into the hole of [c]. This function is
  not tail-recursive. *)
  val compose : t -> t -> t
  (** [compose c d] plugs the context [c] into the hole of [d]. This function
  is not tail-recursive.*)
  val of_term : Position.t -> term -> t
  (** [of_term p t] constructs a context from the term [t], by replacing
  the subterm of [t] at position [p] by a hole. This function is not
  tail-recursive.
  @raise Failure "illegal position" if [p] does not exist in [t]. *)
  val subcontext : Position.t -> t -> t
  (** [subcontext p c] returns the subcontext of [c] at position [p].
  @raise Failure "Context.subcontext: illegal position" if the subterm
  of [c] at position [p] is not a subcontext of [c]. *)

  (** {3 Properties} *)

  val is_empty : t -> bool
  (** [is_empty c] checks if [c] is the empty context. *)
  val is_mu_context : t -> Csmapping.t -> bool
  (** [is_mu_context c mu] checks if the whole in [c] is [mu]-accessible *)

  (** {3 Miscellaneous} *)

  val hash : t -> int
  (** [hash c] returns the hash value of [c]. It is guaranteed that
  [hash c = hash d] if [compare c d = 0]. *)
  val hole_pos : t -> Position.t
  (** [hole_pos] returns the position of the hole in [c]. This function is
  not tail-recursive. *)
  val pos : t -> Position.t list
  (** [pos] returns all positions in [c]. This function is not
  tail-recursive. *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare c d] compares [c] and [d]. This function defines a total
  ordering on contexts. *)
  val equal : t -> t -> bool
  (** [equal c d] checks if [c] and [d] are equal. This function is equivalent
  to [compare c d = 0]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt c] prints [c] using the [OCaml] module [Format]. This
  function is not tail-recursive.*)
  val fprintfm : Format.formatter -> t -> unit
  (** [fprintfm a e fmt c] prints [c] using the [OCaml] module [Format],
  giving less debug information but a prettier output than fprintf. *)
  val to_string : t -> string
  (** [to_string c] returns a string that represents [c]. This function is not
  tail-recursive.*)
  val to_stringm : t -> string
  (** [to_stringm c] returns a string that represents [c], giving more
  debug information in the representation of function symbols. *)
end

(** This module provides basic functions that deal with contexts. *)
module Context : CONTEXT with type func = Function.t and type term = Term.t

(** {2 Module Substitution} *)

module type SUBSTITUTION = sig
  (*** TYPES ******************************************************************)
  type func
  type term 
  type context
 
  (*** INCLUDES ***************************************************************)
  include Util.Replacement.SIGNATURE with 
    type domain = Variable.t and type range = term 
 
  (*** VALUES *****************************************************************)
  (** {3 Apply Substitutions} *)
 
  val apply_term : t -> term -> term 
  (** [apply_term s u] applies the substitution [s] to the term [u]. This
  function is not tail-recursive. *)
  val apply_context : t -> context -> context
  (** [apply_context s c] applies the substitution [s] to the context [c].
  This function is not tail-recursive. *)
 
  (** {3 Predicates} *)
 
  val is_bijective : t -> bool 
  (** [is_bijective s] checks if [s] is bijective. *)
  val is_renaming : t -> bool 
  (** [is_renaming s] checks whether [s] is a variable renaming. This function
  is a synonym for [is_bijective]. *)
 
 
  (** {3 Printers} *)
 
  val fprintfm : Format.formatter -> t -> unit
  (** [fprintfm fmt a e s] prints [s] using the [OCaml] module [Format], giving
  less debug information but a prettier output than fprintf. *)
  val to_stringm : t -> string
  (** [to_stringm a e s] returns a string that represents [s], giving less
  debug information but a prettier output than to_string. *)
end

(** This module provides basic functions that deal with substitutions. *)
module Substitution : SUBSTITUTION with
  type func = Function.t and type term = Term.t and type context = Context.t

(** {2 Module Elogic} *)

module type ELOGIC = sig
  (*** TYPES ******************************************************************)
  type substitution
  type term

  (*** EXCEPTION **************************************************************)
  exception Not_matchable
  exception Not_semi_unifiable
  exception Not_unifiable

  (*** VALUES *****************************************************************)
  (** {3 Unification} *)

  val are_unifiable : term -> term -> bool
  (** [are_unifiable u v] checks if [u] and [v] are unifiable, i.e., if there is
  a most general unifier [s] such that [us = vs]. *)
  val is_variant : term -> term -> bool
  (** [is_variant u v] checks if [u] is a variant of [v], i.e., if there is
  a renaming [s] such that [us = vs]. *)
  val unify : term -> term -> substitution
  (** [unify u v] computes a most general unifier for [u] and [v].
  @raise Not_unifiable if [u] and [v] are not unifiable. *)
  val unify_problem : (term * term) list -> substitution
  (** [unify_problem p] computes a most general unifier for the unification
  problem [p].
  @raise Not_unifiable if [p] does not admit a most general unifier. *)

  (** {3 Matching} *)

  val contains : term -> term -> bool
  (** [contains u v] checks if a subterm of [u] matches [v]. This function
  is not tail-recursive. *)
  (*val ground_matches : term -> term -> bool*)
  (** [ground_matches u v] checks if [u] ground matches [v], i.e., if
  there is a substitution [s] such that [u = vs] where variables of [u]
  are instantiated by arbitrary ground terms. *)
  val matches : term -> term -> bool
  (** [matches u v] checks if [u] matches [v], i.e., if there is a substitution
  [s] such that [u = vs]. *)
  val match_problem : (term * term) list -> substitution
  (** [match_problem p] computes a substitution [s] such that [u = vs] for all
  pairs [(u,v)] in [p].
  @raise Not_matchable if [p] does not admit such a substitution. *)
  val match_term : term -> term -> substitution
  (** [match_term u v] computes a substitution [s] such that [u = vs].
  @raise Not_matchable if [u] does not match [v]. *)
  val subsumes : term -> term -> bool
  (** [subsumes u v] is equivalent to [matches v u]. *)

  (** {3 Renaming} *)

  val renaming : term list -> string list -> Environment.t -> substitution
  (** [renaming u a e] computes a renaming [s] with respect to the terms [u].
  Note that a renaming is a bijective mapping from variables to variables;
  the variables in the range will be fresh, and will be given an actual
  name in the environment [e], which does not clash with the names in [a] (but
  may clash with a function symbol in [u]!). This function is not
  tail-recursive. Note that as a side effect [e] changes all over. Variables
  in quantifications are also renamed. *)

  val environment_oblivious_renaming : term list -> term list
  (** [environment_oblivious_renaming lst] replaces the variables in each
  of the terms in lst by different variables.  However, these new variables
  are not stored in any environment.  This is primarily done for the sake
  of unifying terms which may have the same variables but in different
  environments. *)
end

(** This module provides some special functions that deal with terms,
contexts and substitutions. *)
module Elogic : ELOGIC with
  type substitution = Substitution.t and type term = Term.t

(** {2 Module Rule} *)

module type RULE = sig
  (*** TYPES ******************************************************************)
  type substitution
  type func
  type term 
  type t

  exception Not_an_lctrs
 
  (*** VALUES *****************************************************************)
  (** {3 Constructors and Destructors} *)
 
  val invert : t -> t 
  (** [invert r] flips the left- and right hand side of [r], i.e., if
  [r = (s,t,c)] then the rule [(t,s,c)] is returned. Note that the returned
  rule is not longer a rewrite rule if [s] contains variables which do
  not occur in [t]. *)
  val lhs : t -> term 
  (** [lhs r] returns the left-hand side of the rule [r]. *)
  val rhs : t -> term 
  (** [rhs r] returns the right-hand side of the rule [r]. *)
  val constraints : t -> term list
  (** [constr r] returns the constraints of the rule [r]. *)
  val create : term -> term -> term list -> t
  (** [create l r c] creates a rewrite rule with left-hand side [l],
  right-hand side [r] and constraint list [c] *)
  val of_terms : term -> term -> t 
  (** [of_terms s t] creates a rewrite rule consisting of the left-hand
  side [s] and the right-hand side [t]. *)

  (** {3 Iterators} *)

  val apply : (term -> 'a) -> (term -> 'b) -> (term list -> 'c) -> t -> 'a * 'b * 'c
  (** [apply f g h r] applies the function [f] to the left-, [g] to the
  right-hand side and [h] to the constraints of [r], i.e., if [r = (l,r,c)]
  then the result [(f l,g r,h c)] is returned. *)
  val fold : (term -> 'a -> 'a) -> 'a -> t -> 'a
  (** [fold f d r] combines the left- and right-hand side of [r] using the
  function [f]. *)
  val map : (term -> 'a) -> t -> 'a * 'a * 'a list
  (** [map f r] is equivalent to [apply f f (List.map f) r]. *)
  val project : (term -> term) -> t -> t
  (** [project f r] applies the function [f] to the left- and right-hand
  side of rule [r] as well as to the constraints. *)
  val uncurry : (term -> term -> term list -> 'a) -> t -> 'a
  (** [uncurry f r] applies [f] to the parts of [r]. I.e. if [r = (s,t,c)]
  then the result [f s t c] is returned. *)

  (** {3 Rule Symbols} *)

  val cons : t -> func list
  (** [cons r] returns all constants of the whole rule (including
  constraints.  This function is not tail-recursive. *)
  val funs : t -> func list
  (** [funs r] returns all function symbols of the whole rule (including
  constraints).  This function is not tail-recursive. *)
  val left_cons : t -> func list
  (** [left_cons r] returns all constants of the left-hand side of [r]. This
  function is not tail-recursive. *)
  val left_funs : t -> func list
  (** [left_funs r] returns all function symbols of the left-hand side of [r].
  This function is not tail-recursive. *)
  val left_symbols : t -> (Variable.t,func) Util.either list
  (** [left_symbols r] returns all symbols of the left-hand side of the rule
  [r]. This function is not tail-recursive. *)
  val left_vars : t -> Variable.t list
  (** [left_vars r] returns all variables of the left-hand side of the rule [r].
  This function is not tail-recursive. *)
  val left_root : t -> func
  (** [left_root r] returns the root symbol of the left-hand side of [r].
  @raise Failure "left-hand side is a variable" if the left-hand side of
  [r] is a variable. *)
  val right_cons : t -> func list
  (** [right_cons r] returns all constants of the right-hand side of [r]. This
  function is not tail-recursive. *)
  val right_funs : t -> func list
  (** [right_funs r] returns all function symbols of the right-hand side of [r].
  This function is not tail-recursive. *)
  val right_symbols : t -> (Variable.t,func) Util.either list
  (** [right_symbols r] returns all symbols of the right-hand side of [r]. This
  function is not tail-recursive. *)
  val right_vars : t -> Variable.t list
  (** [right_vars r] returns all variables of the right-hand side of the rule
  [r]. This function is not tail-recursive. *)
  val right_root : t -> func
  (** [right_root r] returns the root symbol of the right-hand side of [r].
  @raise Failure "right-hand side is a variable" if the right-hand side of
  [r] is a variable. *)
  val roots : t -> func list
  (** [roots r] returns the root symbol of the left- and right-hand side of
  [r]. Note that the returned list is unique. *)
  val symbols : t -> (Variable.t,func) Util.either list
  (** [symbols r] returns all symbols of the rule [r]. This function
  is not tail-recursive. *)
  val vars : t -> Variable.t list
  (** [vars r] returns all variables of the rule (including constraints,
  but not including bound variables).
  This function is not tail-recursive. *)
  val allvars : t -> Variable.t list
  (** [allvars r] returns all variables of the rule including both
  constraints and bound variables.  This function is not tail-recursive. *)

  (** {3 Properties} *)

  val is_build : func list -> t -> bool
  (** [is_build fs r] checks if all function symbols in the left- and
  right-hand side of [t] occur in [fs] (function symbols in constraints are
  ignored). *)
  val is_collapsing : t -> bool
  (** [is_collapsing r] checks if the right-hand side of [r] is a variable. *)
  val is_contained : t -> bool
  (** [is_contained r] checks if the left-hand side of [r] is contained in the
  right-hand side. This function is not tail-recursive. *)
  val is_dummy : t -> bool
  (** [is_dummy r] checks if the left- and right-hand side of [r] consists only
  of unary function symbols and constants. *)
  val is_duplicating : t -> bool
  (** [is_duplicating r] checks if there is a variable which occurs more often
  on the right-hand side than on the left-hand side. Not tail-recursive. *)
  val is_erasing : t -> bool
  (** [is_erasing r] checks if [r] is erasing, i.e., if there is a variable
  of the left-hand side which does not occur on the right-hand side. This
  function is not tail-recursive. *)
  val is_flat : t -> bool
  (** [is_flat r] checks if the left- and right-hand side of [r] are flat
  terms. See {!val: Ctrs.TERM.is_flat}. *)
  val is_ground : t -> bool
  (** [is_ground r] checks if the left- and right-hand side of [r] are ground
  terms. *)
  val is_growing : t -> bool
  (** [is_growing r] checks if the rewrite rule [r] is growing. Note that a
  rewrite rule is called growing if all variables that occur in the left- and
  right-hand side of [r] occur at most at depth [1] in the left-hand side of
  [r]. Constraints are ignored. Not tail-recursive. *)
  val is_left_build : func list -> t -> bool
  (** [is_left_build fs r] checks if all function symbols of the left-hand
  side of [r] occur in [fs]. *)
  val is_left_dummy : t -> bool
  (** [is_left_dummy r] checks if the left-hand side of [r] consists only of
  unary function symbols and constants. *)
  val is_left_erasing : t -> bool
  (** [is_left_erasing r] returns whether the right-hand side of [r] contains
  variables which do not occur in the left-hand side. *)
  val is_left_flat : t -> bool
  (** [is_left_flat r] checks if the left-hand side of [r] is a flat term.
  See {!val: Ctrs.TERM.is_flat}. *)
  val is_left_ground : t -> bool
  (** [is_left_ground r] checks if the left-hand side of [r] is a ground
  term. *)
  val is_left_linear : t -> bool
  (** [is_left_linear r] checks if the left-hand side of [r] is a linear term.
  Not tail-recursive. *)
  val is_left_shallow : t -> bool
  (** [is_left_shallow r] checks if the left-hand side of [r] is a shallow
  term. See {!val: Ctrs.TERM.is_shallow}. *)
  val is_left_string : t -> bool
  (** [is_left_string r] checks if the left-hand side of [r] is a string. *)
  val is_linear : t -> bool
  (** [is_linear r] checks if the left- and right-hand side of [r] are linear
  terms. Not tail-recursive. *)
  val is_normal_form : term -> t -> bool
  (** [is_normal_form t r] checks if [t] is in normal form with respect to
  [r] *ignoring constraints of r*. This function is not tail-recursive. *)
  val is_redex : term -> t -> bool
  (** [is_redex t r] checks if [t] matches the left-hand side of [r] (note
  that constraints are ignored). *)
  val is_rewrite_rule : t -> bool
  (** [is_rewrite_rule r] checks if [r] is a rewrite rule, i.e., if the
  left-hand side of [r] is not a variable and all variables of the right-hand
  side occur also in the left-hand side and the constraint list is empty. *)
  val is_right_build : func list -> t -> bool
  (** [is_right_build fs r] checks if all function symbols of the right-hand
  side of [r] occur in [fs]. *)
  val is_right_dummy : t -> bool
  (** [is_right_dummy r] checks if the right-hand side of [r] consists only of
  unary function symbols and constants. *)
  val is_right_flat : t -> bool
  (** [is_right_flat r] checks if the right-hand side of [r] is a flat term.
  See {!val: Ctrs.TERM.is_flat}. *)
  val is_right_ground : t -> bool
  (** [is_right_ground r] checks if the right-hand side of [r] is a ground
  term. *)
  val is_right_linear : t -> bool
  (** [is_right_linear r] checks if the right-hand side of [r] is a linear
  term. Not tail-recursive. *)
  val is_right_shallow : t -> bool
  (** [is_right_shallow r] checks if the right-hand side of [r] is a shallow
  term. See {!val: Ctrs.TERM.is_shallow}. *)
  val is_right_string : t -> bool
  (** [is_right_string r] checks if the right-hand side of [r] is a string. *)
  val is_shallow : t -> bool
  (** [is_shallow r] checks if both the left- and right-hand side of [r] are
  shallow terms. See {!val: Ctrs.TERM.is_shallow}. *)
  val is_size_preserving : t -> bool
  (** [is_size_preserving r] checks if the size of the left-hand side of [r] is
  greater or equal than the size of the right-hand side of [r]; if r contains
  variables which do not occur in l, or contains them more often, then false is
  returned regardless of any conditions which may impose bounds on these
  variables. *)
  val is_string : t -> bool
  (** [is_string r] checks if the left- and right-hand side of [r] are
  strings. *)
  val is_variant : t -> t -> bool
  (** [is_variant r r'] checks if there is a renaming [s] such that [us = u's]
  and [vs = v's] where [r = (u,v)] and [r' = (u',v')]. The renaming is NOT
  applied to the constraints, so being a variant does not mean that they are
  in principle the same rule! *)
  val is_standard : t -> Alphabet.t -> bool
  (** [is_standard r a] checks if the left-hand side of r is proper *)
  val is_regular : t -> bool
  (** [is_regular r a] checks if the variables occurring in the constraints all
  occur in the left-hand side as well *)
  val matches : t -> t -> bool
  (** [matches r r'] checks if [r] matches [r'], i.e., if there is a
  substitution [s] such that [u = u's] and [v = v's] where [r = (u,v)] and
  [r' = (u',v')]. Constraints are ignored. *)
  val subsumes : t -> t -> bool
  (** [subsumed r r'] is equivalent to [matches r' r]. *)
  val are_overlapping : t -> t -> bool
  (** [are_overlapping r r'] checks if [r] and [r'] overlap. Rewrite rules [r]
  and [r'] overlap if there is a position [p] such that the subterm of the 
  left-hand side of [r'] at position [p] unifies with the left-hand side of [r].
  Furthermore if [p] is the root position, [r] and [r'] may not be variants.
  Not tail-recursive. *)
  val is_overlap : t -> Position.t -> t -> bool
  (** [is_overlap r1 p r2] checks if [r1] and [r2] are overlapping at
  position [p] of r2 (and the root position of r1). Not tail-recursive. *)
  val test_reasonable : t -> Alphabet.t -> Environment.t -> bool
  (** [test_termstatus r] checks whether all symbols in [r] have a sort and
  symbol kind, whether the left-hand side is not a value, and the constraints
  have symbols in the right alphabets.  If any of these constraints is
  violated, a Failure is thrown.
  It returns false if these requirements are satisfied but the left-hand side
  is a logical term (variables count!), and true if they are satisfied and
  the left-hand side is not a logical term (typically, it should be, to avoid
  logical terms reducing to something with a different value).
  @raise Failure if a well-definedness rule is broken. *)

  (** {3 Rewrite Terms} *)

  val reducts : term -> t -> term list
  (** [reducts t r] computes all reducts of the term [t] with respect to the
  rewrite rule [r] *ignoring constraints*. The order of the reducts is
  arbitrary. Not tail-recursive.
  @raise Failure "left-hand side is a variable" if the left-hand side of [r]
  is a variable. *)
  val rewrite : term -> Position.t -> t -> term
  (** [rewrite t p r] rewrites the term [t] at position [p] using the rewrite
  rule [r]; constraints of [r] are ignored. Not tail-recursive.
  @raise Elogic.Not_matchable if the subterm of [t] at position [p] does not
  match the left-hand side of [r]. *)
  val rewrites : term -> Position.t -> t -> term -> bool
  (** [rewrites s p r t] checks if [s] rewrites to [t] using rule [r] at
  position [p], ignoring constraints. Does not work for extra-variable TRSs. *)
  val redex_pos : term -> t -> Position.t list
  (** [redex_pos t r] computes all redex positions of the term [t] with
  respect to the rewrite rule [r], ignoring constraints. Not tail-recursive.
  @raise Failure "left-hand side is a variable" if the left-hand side of
  [r] is a variable. *)
  val accessible_redex_pos : term -> Csmapping.t -> t -> Position.t list
  (** [redex_pos t m r] computes all redex positions of the term [t] with
  respect to the context-sensitivity mapping [m] and the rewrite rule [r],
  ignoring constraints. Not tail-recursive.
  @raise Failure "left-hand side is a variable" if the left-hand side of
  [r] is a variable. *)

  (** {3 Equational Logic} *)

  val apply_sub : substitution -> t -> t
  (** [apply_sub s r] applies the substitution [s] to the left- and
  right-hand side of [r], as well as to the constraints. *)

  (** {3 Miscellaneous} *)

  val count_fun : func -> t -> int
  (** [count_fun f r] counts the number of occurrences of [f] in the rule
  [r], ignoring constraints. *)
  (*val reflect : t -> t  *)
  (** [reflect r] reflects the left- and right-hand side of [r]. See
  {!val: Ctrs.TERM.reflect}. This function is not tail-recursive. *)
  val reverse : t -> t 
  (** [reverse r] reverses the left- and right-hand side of [r]. See
  {!val: Ctrs.TERM.reverse}. This function leaves constraints alone,
  and is not tail-recursive.
  @raise Failure "term is not a string" if either the left- or
  right-hand side of [r] is not a string. *)
  val to_terms : t -> term * term 
  (** [to_terms r] return the left- and right-hand side of [r]. *)
  val rename : t -> Environment.t -> t
  (** [rename r e] renames all variables in [r] via a renaming (also those in
  constraints).  The new variables are added to [e], although their names may
  clash with existing function names.  The old variables do not need to be in
  [e]. This function is not tail-recursive. *)
  val rename_fully : t -> Environment.t -> Alphabet.t -> t
  (** [rename_fully r a e] renames the variables of the left- and right-hand
  side of [r] via a renaming, and stores them in [e]; the new variables are
  moreover given new names, which do not clash with any function names in
  [a]. This function is not tail-recursive, and the new variables will not
  have sorts.*)
  val copy : t -> t
  (** [copy r] returns a copy of [r]. *)
  val depth : t -> int
  (** [depth r] returns the maximal depth of the left- and right-hand side of
  [r]. This function is not tail-recursive. *)
  val hash : t -> int
  (** [hash r] returns the hash value of [r]. *)
  val overlaps : t -> t -> (t * Position.t * t) list
  (** [overlaps r r'] computes all positions of [r'] that cause an overlap with
  [r]. Rewrite rules [r] and [r'] overlap if there is a position [p] such that
  the subterm of the left-hand side of [r'] at position [p] unifies with the
  left-hand side of [r]. Furthermore if [p] is the root position, [r] and [r']
  may not be variants. Not tail-recursive. *)
  val var_overlaps : t -> t -> (t * Position.t * t) list
  (** [var_overlaps r r'] computes overlaps at variable positions. 
  see overlaps for details. *)
  val fresh_renaming : t -> Environment.t -> Environment.t -> string list -> t
  (** [fresh_renaming r e1 e2 l] creates a renamed version of [r] with
  all variables fresh.  Originally, [r] should use variables from
  [e1], and the fresh new variables are registered into [e2]. The last
  parameter, [l], is a list of names which may not be used for
  variables in the renaming. *)
  val environment_transfer : t -> Environment.t -> Environment.t -> string list -> t
  (** [environment_transfer r e1 e2 l] creates a renamed copy of
  [r] with variables in the new environment [e2] (where originally,
  all variables of [r] must be in [e1]).  Where possible, the name of
  variables is preserved: a variable named x in [e1] is mapped to a
  variable named x in [e2] if, at least, this variable doesn't already
  exist with a different sort.  Existing variables in the environment
  _may_ be reused, but all variables in [r] are mapped to distinct
  variables in [e2].
  *)
  val left_value_free : Alphabet.t -> Environment.t -> t -> t
  (** [left_value_free a e rule] returns a copy of [rule] where the
  left-hand side does not contain values; these are moved into the
  constraints.  This requires the "equal" symbol to be set in the
  alphabet [a], and uses [e] to register fresh variables. *)
  val calculation_free : Alphabet.t -> Environment.t -> t -> t
  (** [calculation_free a e rule] returns a copy of [rule] where
  calculations such as x + y are moved from the right-hand side of
  the rule into the constraints *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare r r'] compares [r] and [r']. This function defines a total
  ordering on rules. *)
  val equal : t -> t -> bool
  (** [equal r r'] checks if [r] and [r'] are equal. This function is
  equivalent to [compare r r' = 0]. *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf fmt r] prints [r] using the [OCaml] module [Format]. This
  function is not tail-recursive. *)
  val fprintfm : Format.formatter -> t -> unit
  (** [fprintfm a e fmt r] prints [r] using the [OCaml] module [Format],
  giving less debug information but a prettier output than fprintf. *)
  val to_string : t -> string
  (** [to_string r] returns a string that represents [r]. This function is not
  tail-recursive. *)
  val to_stringm : t -> string
  (** [to_stringm a e r] returns a string that represents [r], giving less
  debug information but a prettier output than fprintf. *)
end

(** This module deals with rewrite rules. *)
module Rule : RULE with
  type substitution = Substitution.t and
  type term = Term.t and type func = Function.t

(** {2 Module Trs} *)

module type TRS = sig
  (*** TYPES ******************************************************************)
  type rule 
  type term 
  type func
  type sort
  type t
 
  (*** VALUES *****************************************************************)
  (** {3 Constructors and Destructors} *)

  val empty : unit -> t
  (** [empty ()] returns an empty TRS *)
  val create : Alphabet.t -> Environment.t -> t
  (** [create a e m] returns an empty TRS built on alphabet [a] and
  main environment [e] *)
  val create_contextsensitive : Alphabet.t -> Environment.t -> Csmapping.t -> t
  (** [create a e m] returns an empty TRS built on alphabet [a], main
  environment [e] and context-sensitivity mapping [m].
  WARNING: context-sensitivity is implemented in *principle*, in the
  code for the TRS, the reader and the rewriter, but is otherwise
  completely ignored in all analyses. It is there only to enable
  future extensions. *)
  val get_alphabet : t -> Alphabet.t
  (** [get_alphabet t] returns the alphabet used in the given TRS *)
  val get_main_environment : t -> Environment.t
  (** [get_main_environment t] returns the environment used for terms
  in the given TRS; this environment is NOT used for the rules, they
  each have their own environment (essentially representing that rules
  may be renamed) which may or may not be equal to the main
  environment *)
  val get_rules : t -> (rule * Environment.t) list
  (** [get_rules t] returns the list of rules used in the TRS [t],
  along with their environments (which are used for naming and typing) *)
  val get_plain_rules : t -> rule list
  (** [get_plain_rules t] returns the list of rules used in the TRS
  [t] without environment information *)
  val get_context_sensitivity : t -> Csmapping.t
  (** [get_context_sensitivity t] returns the context-sensitivity
  mapping associated with the conditional trs [t] *)
  val add : rule -> Environment.t -> t -> unit
  (** [add u e r] adds the rule [u] to [r] with environment [e]. In case
  that [u] is already contained in [r], it is added again. *)
  val set_rules : (rule * Environment.t) list -> t -> unit
  (** [set_rules rules trs] removes all rules in [trs] and replaces
  them by [rules] *)
  val set_alphabet : Alphabet.t -> t -> unit
  (** [set_alphabet alf trs] replaces the alphabet in [trs] by [alf] *)
  val lhs : t -> term list
  (** [lhs r] returns the left-hand sides of [r]. Note that the returned list
  is unique. Furthermore the order of the terms is arbitrary. *)
  val rhs : t -> term list
  (** [rhs r] returns the right-hand sides of [r]. Note that the returned list
  is unique. Furthermore the order of the terms is arbitrary. *)

  (** {3 Iterators} *)

  val count_fun : func -> t -> int
  (** [count_fun f trs] counts the number of occurrences of the function
  symbol [f] in the TRS [trs]; constraints and infinite rule sets are
  ignored. *)
  val flat_map : (rule -> Environment.t -> 'a list) -> t -> 'a list
  (** [flat_map f r] is similar to {!val: Util.List.flat_map}. *)
  val fold : (rule -> Environment.t -> 'a -> 'a) -> 'a -> t -> 'a
  (** [fold f d r] is similar to {!val: Util.List.foldr}. *)
  val iter : (rule -> Environment.t -> unit) -> t -> unit
  (** [iter f r] is similar to {!val: Util.List.LIST.iter}. *)
  val map : (rule -> Environment.t -> 'a) -> t -> 'a list
  (** [map f r] is similar to {!val: Util.List.LIST.map}. Not
  tail-recursive. *)
  val project : (rule -> Environment.t -> rule) -> t -> unit
  (** [project f r] applies the function [f] to all rules in [r]. Not
  tail-recursive. *)

  (** {3 Search Functions} *)

  val choose : t -> rule * Environment.t
  (** [choose r] chooses a rule from the given TRS
  @raise Failure "empty TRS" if [r] is the empty TRS *)
  val filter : (rule -> Environment.t -> bool) -> t -> unit
  (** [filter p r] removes rules from [r] which do not satisfy [p]. *)
  val find : (rule -> Environment.t -> bool) -> t -> rule * Environment.t
  (** [find p r] returns a rule/environment combination which satisfies [p]
  @raise Not_found if no rewrite rule in [r] satisfies the predicate [p]. *)
  val find_option : (rule -> Environment.t -> bool) -> t -> (rule * Environment.t) option
  (** [find_option p r] is like find, but returns None in case no satisfying
  rewrite rule is found. *)
  val find_all : (rule -> Environment.t -> bool) -> t -> (rule * Environment.t) list
  (** [find_all p r] is like find, but returns all rules which satisfy [p]. *)

  (** {3 Scan Functions} *)

  val exists : (rule -> Environment.t -> bool) -> t -> bool
  (** [exists p r] is similar to {!val: Util.List.LIST.exists}. *)
  val exists_rule : (rule -> bool) -> t -> bool
  (** [exists_rule p r] is similar to {!val: Util.List.LIST.exists}. *)
  val for_all : (rule -> Environment.t -> bool) -> t -> bool
  (** [for_all p r] is similar to {!val: Util.List.LIST.for_all}. *)
  val for_all_rule : (rule -> bool) -> t -> bool
  (** [for_all p r] is similar to {!val: Util.List.LIST.for_all}. *)

  (** {3 TRS Symbols} *)

  val cons : t -> func list
  (** [cons r] returns the constants of the TRS [r]. This function is not
  tail-recursive. *)
  val con_symbols : t -> func list
  (** [con_symbols r] returns the constructor symbols of the TRS [r]. This
  includes all symbols in the terms alphabet which are not defined symbols,
  and which are not calculations.  Note that values which are only in the
  theory alphabet (so with symbolkind Logical instead of Both) are not
  included. Infinite valuesets like the integers are also not included. *)
  val used_con_symbols : term list -> t -> func list
  (** like con_symbols, but only returns symbols occurring in [rules] or
  the given terms *)
  val def_symbols : t -> func list
  (** [def_symbols r] returns the root symbols of the left-hand sides (defined
  symbols) of [r]. *)
  val calc_symbols : t -> func list
  (** [calc_symbols r] returns the calculation symbols in the alphabet
  of [r] *)
  val funs : t -> func list
  (** [funs r] returns the function symbols of the TRS [r]. This function is
  not tail-recursive. *)
  val left_cons : t -> func list
  (** [left_cons r] returns the constants of the left-hand sides of [r]. This
  function is not tail-recursive. *)
  val left_con_symbols : t -> func list
  (** [left_con_symbols r] returns the constructor symbols of the left-hand
  sides of [r]. This function is not tail-recursive. *)
  val left_funs : t -> func list
  (** [left_funs r] returns the function symbols of the left-hand sides of
  [r]. This function is not tail-recursive. *)
  val left_roots : t -> func list
  (** [left_roots r] is equivalent to {!val: Ctrs.TRS.def_symbols}. *)
  val left_symbols : t -> (Variable.t,func) Util.either list
  (** [left_symbols r] returns the function symbols and variables of the
  left-hand sides of [r]. This function is not tail-recursive. *)
  val left_vars : t -> Variable.t list
  (** [left_vars r] returns the variables of the left-hand sides of [r]. This
  function is not tail-recursive. *)
  val right_cons : t -> func list
  (** [right_cons r] returns the constants of the right-hand sides of [r].
  This function is not tail-recursive. *)
  val right_con_symbols : t -> func list
  (** [right_con_symbols r] returns the constructor symbols of the right-hand
  sides of [r]. This function is not tail-recursive. *)
  val right_funs : t -> func list
  (** [right_funs r] returns the function symbols of the right-hand sides of
  [r]. This function is not tail-recursive. *)
  val right_roots : t -> func list
  (** [right_roots r] returns the root symbols of the right-hand sides of
  [r]. *)
  val right_symbols : t -> (Variable.t,func) Util.either list
  (** [right_symbols r] returns the function symbols and variables of the
  right-hand sides of [r]. This function is not tail-recursive. *)
  val right_vars : t -> Variable.t list
  (** [right_vars r] returns the variables of the right-hand sides of [r].
  This function is not tail-recursive. *)
  val roots : t -> func list
  (** [roots r] returns all root symbols of the TRS [r]. *)
  val symbols : t -> (Variable.t,func) Util.either list
  (** [symbols r] returns the function symbols and variables of the TRS [r]
  (not constraints). This function is not tail-recursive. *)
  val vars : t -> Variable.t list
  (** [vars r] returns the variables of the TRS [r]. This function is not
  tail-recursive. Note that for the answer to be useful, all rules should
  have the same environment, which can be established using the renaming
  function below. *)

  (** {3 Properties} *)

  val is_build : func list -> t -> bool
  (** [is_build fs r] checks if all function symbols of [r] occur in [fs]. *)
  val is_collapsing : t -> bool
  (** [is_collapsing r] checks if [r] contains a collapsing rewrite rule. 
  See {!val: Ctrs.RULE.is_collapsing}. *)
  val is_constructor : t -> bool
  (** [is_constructor r] checks if all left-hand sides of [r] are
  constructor terms. Note that a term is a constructor term if all function
  symbols below the root are constructor symbols. Not tail-recursive. *)
  val is_constructor_term : term -> t -> bool
  (** [is_constructor_term t r] checks if [t] is a constructor term with
  respect to [r].  This is the case if none of the symbols in [t] is a
  defined symbol.  This differs from Term.is_build <.> Trs.con_symbols by
  also allowing constructor symbols which do not occurin the alphabet to
  occur in [t]. *)
  val is_dummy : t -> bool
  (** [is_dummy r] checks if all rewrite rules of [r] are dummy. See
  {!val: Ctrs.RULE.is_dummy}. *)
  val is_duplicating : t -> bool
  (** [is_duplicating r] checks if [r] admits a duplicating rewrite rule. This
  function is not tail-recursive. *)
  val is_erasing : t -> bool
  (** [is_erasing r] checks if [r] contains an erasing rewrite rule. See
  {!val: Ctrs.RULE.is_erasing}. This function is not tail-recursive. *)
  val is_empty : t -> bool
  (** [is_empty r] checks if [r] is empty. *)
  val is_flat : t -> bool
  (** [is_flat r] checks if all rules in [r] are flat. See
  {!val: Ctrs.RULE.is_flat}. *)
  val is_ground : t -> bool
  (** [is_ground r] checks if [r] consists only of ground rewrite rules. *)
  val is_growing : t -> bool
  (** [is_growing r] checks if [r] consists only of growing rewrite rules.
  Not tail-recursive. *)
  val is_left_build : func list -> t -> bool
  (** [is_left_build fs r] checks if all function symbols of the left-hand
  sides of [r] occur in [fs]. *)
  val is_left_constructor : t -> bool
  (** [is_left_constructor r] is equivalent to
  {!val: Ctrs.TRS.is_constructor}. This function is not tail-recursive. *)
  val is_left_dummy : t -> bool
  (** [is_left_dummy r] checks if all left-hand sides of [r] are dummy. *)
  val is_left_flat : t -> bool
  (** [is_left_flat r] checks if all left-hand sides of [r] are flat. *)
  val is_left_ground : t -> bool
  (** [is_left_ground r] checks if all left-hand sides of [r] are ground. *)
  val is_left_linear : t -> bool
  (** [is_left_linear r] checks if all rules in [r] are left-linear. This
  function is not tail-recursive. *)
  val is_left_shallow : t -> bool
  (** [is_left_shallow r] checks if all left-hand sides of [r] are shallow. *)
  val is_linear : t -> bool
  (** [is_linear r] checks if all rules in [r] are linear. This function is
  not tail-recursive. *)
  val is_normal_form : term -> t -> bool
  (** [is_normal_form t r] checks if [t] is a normal form with respect to [r].
  This function is not tail-recursive. *)
  val is_redex : term -> t -> bool
  (** [is_redex u r] checks if [u] is a redex with respect to [r]. *)
  val is_right_build : func list -> t -> bool
  (** [is_right_build fs r] checks if all function symbols of the right-hand
  sides of [r] occur in [fs]. *)
  val is_right_constructor : t -> bool
  (** [is_right_constructor r] checks if all right-hand sides of [r] are
  constructor terms. Note that a term is a constructor term if all function
  symbols below the root are constructor symbols. Not tail-recursive. *)
  val is_right_dummy : t -> bool
  (** [is_right_dummy r] checks if all right-hand sides of [r] are dummy. *)
  val is_right_flat : t -> bool
  (** [is_right_flat r] checks if all right-hand sides of [r] are flat. *)
  val is_right_ground : t -> bool
  (** [is_right_ground r] checks if all right-hand sides of [r] are ground. *)
  val is_right_linear : t -> bool
  (** [is_right_linear r] checks if all rules in [r] are right-linear. This
  function is not tail-recursive. *)
  val is_right_shallow : t -> bool
  (** [is_right_shallow r] checks if all right-hand sides of [r] are shallow. *)
  val is_shallow : t -> bool
  (** [is_shallow r] checks if all rewrite rules in [r] are shallow. *)
  val is_size_preserving : t -> bool
  (** [is_size_preserving r] checks if all rewrite rules in [r] are size
  preserving (i.e. if the size of each left-hand side is greater or equal
  than the size of the corresponding right-hand side). *)
  val is_variant : t -> t -> bool
  (** [is_variant r s] checks if [r] is a variant of [s], i.e., if for all
  rules in [r] there is a variant in [s] and vice versa. *)
  val is_applicative : t -> bool
  (** [is_applicative r] checks if [r] is an applicative system. If [r]
  contains a function symbol with undefined arity, an error is thrown.
  Note that a TRS is applicative if its signature consists of one
  binary symbol and arbitrary many constants, and there are no constraints.
  Not tail-recursive. *)
  val is_overlapping : t -> bool
  (** [is_overlapping r] checks if some rules in [r] cause an overlap.
  This function ignores constraints and is not tail-recursive. *)
  val is_overlay : t -> bool
  (** [is_overlay r] checks if [r] is an overlay system. An overlay system is
  a TRS where overlaps take place only at root positions. This function
  ignores constraints and is not tail-recursive. *)
  val is_trs : t -> bool
  (** [is_trs r] checks if [r] is a TRS, so no rules carry any constraints. *)

  (** [3 Validity Checking} *)

  val test_reasonable : t -> string
  (** [test_termstatus r] checks whether all rules in [r] satisfy term
  constraints, following Rule.test_reasonable; if Rule.test_reasonable ever
  returns false, or fails, then a string describing the problem is returned *)
  val test_values : t -> string
  (** [test_values r] checks whether the alphabet of [r] satisfies value
  constraints for a standard CTRS: the only overlap between the term and
  logical alphabet may be constants.  *)
  val test_variables : t -> bool -> string
  (** [test_rule_variables r regular] checks whether all rules in [r] satisfy
  variable requirements.  For example, fresh variables in the right-hand side
  must have a specific naming, and if [regular] is set, variables in logical
  constraints must occur in the left-hand side.  If there are no problems, the
  empty string is returned, otherwise a string describing the problem. *)
  val test_regular : t -> string
  (** [test_regular r] checks whether all rules in [r] are regular.
  If everything is okay, the empty string is returned, otherwise an explanation
  of what is wrong. *)
  val test_standard : t -> string
  (** [test_standard r] checks whether all rules in [r] are standard.
  If everythingis okay, the empty string is returned, otherwise an explanation
  of what is wrong. *)
  val test_safe_sort : t -> sort -> bool
  (** [test_safe_sort r sort] returns true if the only constructors with
  output sort [sort] are values *)

  (** {3 Miscellaneous} *)

  val rename : t -> unit
  (** [rename r] renames the variables of the left- and right-hand sides of
  [r].  For each rule, a fresh renaming is used.  The new variables are all
  in the TRS's main environment, and are given a name which does not clash
  with the TRS's alphabet. This function is not tail-recursive. *)
  val copy : t -> t
  (** [copy r] copies the TRS [r]. *)
  val depth : t -> int
  (** [depth r] returns the maximal depth of the TRS [r], ignoring
  constraints. This function is not tail-recursive. *)
  val hash : t -> int
  (** [hash r] returns a hash value for [r]. It is guaranteed that
  [hash r = hash s] whenever [compare s t = 0]. *)
  val overlaps : t -> (rule * Position.t * rule) list
  (** [overlaps r] computes all overlaps between rewrite rules in [r]. 
  Rewrite rules [u] and [v] cause an overlap if there is a position
  [p] such that the subterm of the left-hand side of [v] at position [p]
  unifies with the left-hand side of [u]. Furthermore if [p] is the root
  position, [u] and [v] may not be variants. Not tail-recursive. Note that as
  a side effect the underlying signature changes all over. *)
  val var_overlaps : t -> (rule * Position.t * rule) list
  (** [var_overlaps r] computes overlaps at variable positions.
  see [overlaps] for details. *)
  val size : t -> int
  (** [size r] returns the number of rewrite rules contained in [r]. *)
  val replace_rules : (rule * Environment.t) list -> t -> unit
  (** [replace_rules rules trs] replaces the rules in [trs] by [rules] *)

  (** {3 Printers} *)

  val fprintf : Format.formatter -> t -> unit
  (** [fprintf out r] prints [r] using the [OCaml] module [Format]. This
  function is not tail-recursive. *)
  val to_string : t -> string
  (** [to_string r] returns a string that represents [r]. This function is
  not tail-recursive. *)

  (** {3 Keep Track of a Current TRS} *)

  val set_current : t -> unit
  val get_current : unit -> t
  val has_current : unit -> bool
 
(*
  val mem : rule -> Environment.t -> t -> bool
  (** [mem u r] is similar to {!val: Util.List.mem}. *)
  val diff : t -> t -> t 
  (** [diff r s] is equivalent to {!val: Util.List.diff}. *)
  val intersect : t -> t -> t 
  (** [intersect r s] computes the intersection of [r] and [s]. *)
  val invert : t -> t
  (** [invert r] switches the left- and right-hand sides of [r]. This function
  is not tail-recursive. *)
  val of_list : rule list -> t
  (** [of_list rs] returns a TRS consisting of the rewrite rules contained in
  [rs]. Note that multiple copies are preserved. *)
  val partition : (rule -> bool) -> t -> t * t
  (** [partition p r] splits the TRS [r] into those rules that satisfy [p]
  and those that do not. *)
  val reflect : t -> t
  (** [reflect r] reflects the left- and right-hand sides of [r]. This
  function is not tail-recursive. See {!val: Ctrs.RULE.reflect}. *)
  val remove : rule -> t -> t
  (** [remove u r] is equivalent to {!val: Util.List.remove_all}. *)
  val reverse : t -> t
  (** [reverse r] reverses the left- and right-hand sides of [r]. This function
  is not tail-recursive.
  @raise Failure "not a srs" if [r] is not a SRS. *)
  val rhs : t -> term list
  (** [rhs r] returns the right-hand sides of [r]. Note that the returned list
  is unique. Furthermore the order of the terms is arbitrary. *)
  val singleton : rule -> t
  (** [singleton u] is equivalent to {!val: Util.List.singleton}. *)
  val to_list : t -> rule list
  (** [to_list r] returns the rules of [r] as a list. *)
  val union : t -> t -> t
  (** [union] is equivalent to {!val: Util.List.union}. *)
  val unique : t -> t
  (** [unique r] drops rules from [r] that are syntactically equivalent. *)
  val terms : t -> term list
  (** [terms r] returns the left- and right-hand sides of [r]. Note that the
  returned list is unique. Furthermore the order of the terms is arbitrary. *)
  val variant_free : t -> t
  (** [variant_free r] returns variant free version of [r]. *)

  (** {3 Rewrite Terms} *)

  val reducts : term -> t -> term list
  (** [reducts u r] computes all reducts of the term [u] with respect to the
  TRS [r]. The order of the reducts is arbitrary. Not tail-recursive.
  @raise Failure "left-hand side is a variable" if some left-hand side of [r]
  is a variable. *)
  val rewrite : term -> Position.t -> t -> term list
  (** [rewrite u p r] rewrites the term [u] at position [p] using the rewrite
  rules in [r]. Not tail-recursive.
  @raise Failure "illegal position" if [p] is not a function position.
  @raise Elogic.Not_matchable if the left-hand side of [r] does not match the
  subterm of [u] at position [p]. *)
  val rewrites : term -> Position.t -> t -> term -> bool
  (** [rewrites s p trs t] checks if [s] rewrites to [t] using a rule in
  [trs] at position [p]. *)

  (** {3 Compare Functions} *)

  val compare : t -> t -> int
  (** [compare r s] compares if [r] and [s] contain the same rules
  (duplicate rules are not ignored). This function defines a total
  ordering on TRSs. *)
  val equal : t -> t -> bool
  (** [equal r s] checks if [r] and [s] are equal (duplicates of rules are
  not ignored). This function is equivalent to [compare r s = 0]. *)
  val equivalent : t -> t -> bool
  (** [equivalent r s] checks if [r] and [s] contain the same rules using
  set comparison. I.e., duplicates of rules are ignored. *)

  (** {3 Parsers} *)

  val of_string : string list -> string -> t m
  (** [of_string vs s] applies [parse vs] to the input string [s] and lifts
  the result into the signature monad. *)
  val of_xml_string : string -> t m
  (** [of_xml_string s] applies [xml] to the input string [s] and lifts
  the result into a monad. *)
  val parse : string list -> t p
  (** [parse vs] takes a list of strings (the identifiers that should be
  parsed as variables) and returns a TRS-parser (having a signature as
  internal state). *)
  val xml : t x
  (** [xml] returns a TRS-parser (having a signature as internal state). *)

*)
end

(** Term Rewrite Systems
@author Martin Korp, Christian Sternagel, Harald Zankl
@since  Mon Sep  1 12:21:37 CEST 2008 *)

(** This module deals with term rewrite systems. *)
module Trs : TRS with type rule = Rule.t and type term = Term.t
                 and type sort = Sort.t and type func = Function.t

(** {2 Module Typechecker} *)

module type TYPECHECKER = sig
  type func
  type sd
  type term
  type rule

  val type_check : (rule * Environment.t) list -> Alphabet.t -> unit
  (** [type_check lst a] checks whether all rules in [lst] are
  well-typed, or can become well-typed by assigning sort declarations
  to function symbols whose sort is currently unknown.  If the system
  does not type-check correctly, an error is throw which explains the
  cause of type-checking problems (in so far as possible).  If the
  system does type-check, then the return value is the empty string,
  and all function symbols which occur in any rule are assigned a
  sort in [a]; also variables are declared in their respective
  environments.  If sorts for any symbol are ambiguous, the sort
  becomes "unit".
  @raise Not_found if any function symbol occurring in [lst] is not
  declared with arity in [a].
  @raise Failure str if the system does not typecheck correctly *)
  val type_check_trs : Trs.t -> unit
  (** [type_check t] is just [type_check r a], where r are the rules
  of [t] and [a] its alphabet. *)
  val type_derive : Trs.t -> unit
  (** [type_derive lst t] is like type_check_trs, but also allows
  special function symbols; the rules of the TRS are replaced by
  completely well-typed and declared counterparts. *)
  val type_derive_term : term -> Trs.t -> term
  (** [type_derive t s] returns a term with normal function symbol
  occurrences replaced by special symbols where necessary; it is
  assumed that all symbols in the TRS are already properly
  declared! This also declares all variables in the environment. *)
  val type_derive_rules : (rule * Environment.t) list -> Alphabet.t ->
    (rule * Environment.t) list
  (** [type_derive_rules rules a] is like [type_check rules a], but
  also allows special function symbols; the completely well-typed
  and declared copies of [rules] are returned; these rules may not
  be polymorphic *)
end

(** Type Checker
@author Cynthia Kop
@cince Tue Sep 18 13:17 CEST 2012 *)

(** This module deals with automatic type derivation and other validity
checks on conditional term rewriting systems *)
module Typechecker : TYPECHECKER with type func = Function.t and type
  sd = Sortdeclaration.t and type term = Term.t and type rule = Rule.t 

