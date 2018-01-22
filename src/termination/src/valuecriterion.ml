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

exception NoIntegerSymbols;;

(*** FUNCTIONS ***************************************************************)

(*****************************************************************************)
(*                            basic functionality                            *)
(*****************************************************************************)

(* returns the SMT-solver we will use (just the default) *)
let smt () = Rewriter.smt_solver (Rewriter.get_current ());;

(* returns true if premises => formula is definitely valid *)
let valid_implication a env neg premises formula =
  (* premises => formula is valid if and only if
     NOT (premises => formula) is unsatisfiable, so if
     premises /\ NOT formula is not satisfiable *)
  let forms = Term.make_function a env neg [formula] :: premises in
  Solver.unsatisfiable forms (smt ()) env
;;

(*****************************************************************************)
(*                 basic functionality dealing with integers                 *)
(*****************************************************************************)

let intsort = Sort.from_string "Int";;

(* returns a term representing the given number *)
let make_num num = Term.make_fun (Function.integer_symbol num) [];;

(* returns that at least num of the given terms must be positive,
where all the termss are either 0 or 1 *)
let atleastnum num a e geq plus terms =
  let rec termsum = function
    | [] -> make_num 0
    | [single] -> single
    | head :: tail ->
      Term.make_function a e plus [termsum tail; head]
  in
  Term.make_function a e geq [termsum terms; make_num num]
;;

(* creates an integer variable *)
let freshvar env _ = Environment.create_sorted_var intsort [] env;;
(* creates a boolean variable *)
let boolvar env _ = Environment.create_sorted_var (Alphabet.boolsort) [] env;;

let arithmetic_symbols a =
  try
    (Alphabet.find_fun ">=" a, Alphabet.find_fun "+" a,
     Alphabet.find_fun "*" a, Alphabet.get_or_symbol a,
     Alphabet.get_equal_symbol a, Alphabet.get_not_symbol a
    )
  with
    | Not_found -> raise NoIntegerSymbols
      (*failwith ("When proving termination with " ^
        "integer values, please include >=, + and * symbols in " ^
        "the theory.")
      *)
    | _ -> failwith ("When proving termination, disjunction, " ^
        "equality and negation symbols must be included in the " ^
        "theory and explicitly marked.")
;;

(*****************************************************************************)
(*                          handling the processors                          *)
(*****************************************************************************)

(* returns a list of suitable argument indexes, where an argument is
   suitable for f if it's always mapped to a logical term in [terms]
*)
let get_value_arguments a terms f =
  (* find terms with f as root symbol *)
  let isrelevant term = Term.root term = Some f in
  let relevant = List.filter isrelevant terms in
  (* for all argument positions, make lists of the used arguments *)
  let allargs = List.map Term.args relevant in
  let arglist = List.transpose allargs in
  let numberedlist = List.mapi (fun i arg -> (i, arg)) arglist in
  (* check whether all arguments at a position are okay *)
  let islogical arg = Term.check_logical_term a arg = None in
  let alllogical (i, args) = List.for_all islogical args in
  let goodpositions = List.filter alllogical numberedlist in
  (* return the positions where all arguments are okay! *)
  List.map fst goodpositions
;;

(* returns a list of tuples (f, sd, [...]) where [...] is the list of
   suitable argument indexes as in get_value_arguments, but combined
   with a boolean indicating whether the position has one of the given
   sorts; if verbose is true, then a warning is given about all
   arguments which might be candidates for the value criterion, but
   which have an unsuitable sort*)
let get_suitable_arguments kind verbose a terms sorts =
  let getroot term = match Term.root term with
    | None -> failwith "Dependency pair with a variable or quantifier!"
    | Some f -> f
  in
  let get_symbol_data f =
    let sortdec = match Alphabet.find_sortdec f a with
      | Left sd -> sd
      | Right _ -> failwith ("Defined symbols should have a fixed " ^
          "sort declaration!")
    in
    let arglist = get_value_arguments a terms f in
    (f, sortdec, arglist)
  in
  let rec update_for_sorts datasofar badsortssofar = function
    | [] -> (datasofar, badsortssofar)
    | (f, sd, lst) :: tail ->
      let getsort num = Sortdeclaration.input_sort sd (num + 1) in
      let goodarg num = List.mem (getsort num) sorts in
      let addinfo num = (num, goodarg num) in
      let infolst = List.map addinfo lst in
      let bads = List.filter (not <.> snd) infolst in
      let badsorts = List.unique (List.map (getsort <.> fst) bads) in
      let allbadsorts = List.union badsorts badsortssofar in
      update_for_sorts ((f,sd,infolst)::datasofar) allbadsorts tail
  in
  let symbs = List.unique (List.map getroot terms) in
  let data = List.map get_symbol_data symbs in
  let (data, badsorts) = update_for_sorts [] [] data in
  if verbose && (badsorts <> []) then (
    let str = List.implode Sort.to_string ", " badsorts in
    Printf.printf ("Warning: %s %s %s %s: %s.\n")
      "cannot use the" kind "value criterion for sort" str
      (if kind = "basic" then "no well-founded relation given"
       else "this is not yet implemented")
  ) ;
  data
;;

let get_dp_data prob =
  (* get basic data *)
  let a = Dpproblem.get_alphabet prob in
  let dps = Dpproblem.get_dps prob in
  (* create an environment for the interpretation variables *)
  let env = Environment.copy (Dpproblem.get_environment prob) in
  (* decide what terms occur *)
  let getterms rule = [Rule.lhs rule; Rule.rhs rule] in
  let terms = List.flat_map getterms dps in
  (a, env, dps, terms)
;;

(* creates a variable with a recognisable name, for later replacing *)
let make_internal_var i sort f a e =
  let name = "::INTERNAL::" ^ (Function.find_name f) ^ "::" ^
             (string_of_int (i+1)) in
  if Environment.mem_var_name name e then
    Environment.create_sorted_var sort [] e
  else Environment.create_var name sort e
;;

(* returns a list of triples (f, [x1,...,xn], nu), where nu is a list
of all arguments (as terms) which f(x1,...,xn) might be mapped onto *)
let standard_candidates a e _ functioninfo =
  (* returns all elements of vars, as terms, whose index appears in
  [usable] *)
  let rec get_usable vars usable k =
    match (vars, usable) with
      | (_, []) -> []
      | ([], _) -> []
      | (x :: tail, i :: rest) ->
        if i = k then (Term.make_var x) :: get_usable tail rest (k + 1)
        else get_usable tail (i :: rest) (k + 1)
  in
  (* returns all [xi] with i in [options] *)
  let get_candidates (f, sd, options) =
    let positions = List.map fst (List.filter snd options) in
    let makevar i sort = make_internal_var i sort f a e in
    let input = List.mapi makevar (Sortdeclaration.input_sorts sd) in
    (f, input, get_usable input positions 0)
  in
  List.map get_candidates functioninfo
;;

(*****************************************************************************)
(*                            printing the result                            *)
(*****************************************************************************)

(* print a known interpretation -- a mapping from a function symbol
to a pair (x1,...,xn) -> term -- to the user *)
let tostr_known_projection (f, (vars, projection)) =
  let funname = Function.find_name f in
  let varname x = Variable.find_name x in
  let varsstring =
    if vars = [] then ""
    else "(" ^ (List.implode varname "," vars) ^ ")"
  in
  let interpstring = Printer.to_string_term projection in
  let iname = "::INTERNAL::" ^ (Function.find_name f) ^ "::" in
  let replace i o = Str.global_replace (Str.regexp_string i) o in
  let varsstring = replace iname "z" varsstring in
  let interpstring = replace iname "z" interpstring in
  "  NU[" ^ funname ^ varsstring ^ "] = " ^ interpstring
;;

(* print a filtered term using a known filtering / projection *)
let tostr_projected_term nu term =
  match term with
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      let (vars, projection) = List.assoc f nu in
      let gamma = Substitution.of_list (List.zip vars args) in
      let result = Substitution.apply_term gamma projection in
      Printer.to_string_term result
    | _ -> failwith ("Encountered variable or quantifier as " ^
              "left- or right-hand side of a dependency pair!")
;;

let oriented_text allstrict =
  if allstrict then
    "All dependency pairs are strictly oriented, so the " ^
    "entire dependency pair problem may be removed.\n"
  else "We remove all the strictly oriented dependency pairs.\n"
;;

(* after having determined a suitable projection function and
strictness settings, determine the remaining dependency pairs and
report on what we did! *)
let finish a e kind verbose dps dpprob strictinfo projection
           explanation =
  let combined = List.zip strictinfo dps in
  let expl = explanation a e kind combined projection in
  if verbose then Printf.printf "%s" expl ;
  Environment.drop e ;
  let goodcombined = List.filter (fun (x,_) -> not x) combined in
  let remainingdp = List.map snd goodcombined in
  if remainingdp = [] then Some ([], expl)
  else Some ([Dpproblem.set_dps remainingdp dpprob], expl)
;;

(*****************************************************************************)
(*   basic value criterion for values where a well-founded relation is set   *)
(*****************************************************************************)

(* returns the requirements that always:
   - if strict then phi => left > right
   - if not strict then phi => left > right \/ left = right
*)
let basic_dp_requirements projection alf env vee neg eq rel compsort str dps =
  (* At least one of the DPs has to be oriented strictly, otherwise
  the whole thing is pointless! Thus, given that str = [strict1;strict2;
  ...;strictn], we create strict1 \/ ... \/ strictn *)
  let rec make_disjunction = function
    | [] -> Term.make_function alf env (Alphabet.get_bot_symbol alf) []
    | [x] -> x
    | hd :: tl -> Term.make_function alf env vee [hd;make_disjunction tl]
  in
  let somethingstrict = Term.make_function alf env vee str in
  (* used to make sure we only do legal things in check_pair *)
  let logical_sorts = Alphabet.find_logical_sorts alf in
  let is_logical term =
    match Term.check_logical_term alf term with
      | Some _ -> false
      | None -> List.mem (Term.get_sort alf env term) logical_sorts
  in
  (* xs are the variables specifying the projection function for the
  left-hand side, ys the projection function for the right-hand side;
  check_pair returns, for a DP f x1 ... xn => g y1 ... yn [phi],
  formulas whose conjunction indicates the following (roughly):
    if filter(left) = arg1 and filter(right) = arg2, then:
    - arg1 >= arg2
    - if strictvar, then even arg1 > arg2
  *)
  let rec check_pair xs ys strictvar constraints ((i,arg1),(j,arg2)) =
    let xnoti = Term.make_function alf env neg [List.nth xs i] in
    let ynotj = Term.make_function alf env neg [List.nth ys j] in
    let notthesetwo = Term.make_function alf env vee [xnoti;ynotj] in
    (* if they don't have the same type, then we can't have this
       combination! *)
    let sort1 = Term.get_sort alf env arg1 in
    let sort2 = Term.get_sort alf env arg2 in
    if sort1 <> sort2 then notthesetwo else
    (* if the terms are physically equal, then the >= comparison is
    valid, but the > is not *)
    let notstrictreq = Term.make_function alf env vee
          [notthesetwo; Term.make_function alf env neg [strictvar]] in
    if arg1 = arg2 then notstrictreq else
    (* if the terms cannot be handled in the logic, and they are not
    physically equal, then this is not a valid pair *)
    if not (is_logical arg1) then notthesetwo else
    if not (is_logical arg2) then notthesetwo else
    (* if they cannot strictly be compared, we must check only for
    equality, and they cannot be oriented strictly *)
    let equal = Term.make_function alf env eq [arg1;arg2] in
    if Term.get_sort alf env arg1 <> compsort then (
      if valid_implication alf env neg constraints equal then notstrictreq
      else notthesetwo
    ) else
    (* if they CAN be strictly compared, do the check! *)
    let greater = Term.make_function alf env rel [arg1;arg2] in
    if valid_implication alf env neg constraints greater then (
      (* constraints => arg1 > arg2 -- filter(left) = arg1 and
      filter(right) = arg2, then strict might be assumed to be *)
      let strictreq = Term.make_function alf env vee
        [notthesetwo ; strictvar] in
      strictreq
    ) else
    (* if not, they can still be compared using >=, which is better
    than individual checks for validity and equality *)
    let geq = Term.make_function alf env vee [greater;equal] in
    if valid_implication alf env neg constraints geq then notstrictreq
    else notthesetwo
  in
  (* Find the requirements for the given dp, given that var indicates
  whether this dp is strictly oriented. *)
  let requirements_for (dp, var) =
    let f1 = Rule.left_root dp in
    let f2 = Rule.right_root dp in
    let args1 = Term.args (Rule.lhs dp) in
    let args2 = Term.args (Rule.rhs dp) in
    let phis = Rule.constraints dp in
    let zipsubst vars args = Substitution.of_list (List.zip vars args) in
    let subpossibilities gamma possible =
      let substandpair i x = (i, Substitution.apply_term gamma x) in
      List.mapi substandpair possible
    in
    let (vars1, vars2, combinations) = (
      if f1 = f2 then
        let (xs, vars, possible) = List.assoc f1 projection in
        let gamma1 = zipsubst vars args1 in
        let gamma2 = zipsubst vars args2 in
        let combi1 = subpossibilities gamma1 possible in
        let combi2 = subpossibilities gamma2 possible in
        (xs, xs, List.zip combi1 combi2)
      else
        let (xs, vars1, possible1) = List.assoc f1 projection in
        let (ys, vars2, possible2) = List.assoc f2 projection in
        let gamma1 = zipsubst vars1 args1 in
        let gamma2 = zipsubst vars2 args2 in
        let combi1 = subpossibilities gamma1 possible1 in
        let combi2 = subpossibilities gamma2 possible2 in
        (xs, ys, List.product combi1 combi2)
    ) in
    List.map (check_pair vars1 vars2 var phis) combinations
  in
  somethingstrict :: List.flat_map requirements_for (List.zip dps str)
;;

(* poses the requirements on a projection: the boolean variables xs
must indicate a unique value for the projection *)
let rec projection_requirements env alf vee neg (_,(xs,_,_)) =
  let rec atleastone = function
    | [] -> Term.make_function alf env (Alphabet.get_bot_symbol alf) []
    | [x] -> x
    | hd :: tl -> Term.make_function alf env vee [hd; atleastone tl]
  in
  let nopair x y =
    let anti z = Term.make_function alf env neg [z] in
    Term.make_function alf env vee [anti x; anti y]
  in
  let rec nopairs = function
    | [] | [_] -> []
    | x :: tl -> (List.map (nopair x) tl) @ nopairs tl
  in
  (atleastone xs) :: nopairs xs
;;

(* given a variable-dependent projection function proj, which maps
function symbols f to triples (ys [indicating the index of the
argument filtering in possibilities], xs (arguments to f),
possibilities [variables xi]), returns a projection function,
mapping f to pairs (xs, chosen xi) *)
let determine_projection proj gamma top =
  let rec first_true i = function
    | [] -> failwith ("determine_projection called when " ^
                      "projection constraints are not satisfied!")
    | hd :: tl ->
      if Term.root (Substitution.find hd gamma) = Some top then i
      else first_true (i + 1) tl
  in
  let determine_projection (f, (ys, xs, possibilities)) =
    let i = first_true 0 (List.flat_map Term.vars ys) in
    ( f, ( xs, List.nth possibilities i ) )
  in
  List.map determine_projection proj
;;

(* prints an explanation of how the basic value criterion is applied;
here, nu maps function symbols to tuples (vars, projection) *)
let basic_explanation relation a e kind dps nu =
  (* print an interpreted dependency pair *)
  let tostr_interpreted_dp (strict, dp) =
    let lhs = tostr_projected_term nu (Rule.lhs dp) in
    let rhs = tostr_projected_term nu (Rule.rhs dp) in
    let phis = Rule.constraints dp in
    let constr = List.implode Printer.to_string_term "/\\" phis in
    let rel =
      if strict then Function.find_name relation
      else "(" ^ (Function.find_name relation) ^ " \\union =)"
    in
    "  " ^ constr ^ "  ==>  " ^ lhs ^ " " ^ rel ^ " " ^ rhs
  in
  (* actually do all the printing! *)
  let text = "We use the basic value criterion with the projection " ^
    "function NU:\n" ^
    (List.implode tostr_known_projection "\n" nu) ^ "\n\n" ^
    "This gives the following inequalities:\n" ^
    (List.implode tostr_interpreted_dp "\n" dps) ^ "\n\n"
  in
  text ^ (oriented_text (List.for_all fst dps))
;;

let basic_process verbose prob =
  (* get basic data *)
  let (alf, env, dps, terms) = get_dp_data prob in
  let (vee, neg, eq, top)  =
    ( Alphabet.get_or_symbol alf, Alphabet.get_not_symbol alf,
      Alphabet.get_equal_symbol alf, Alphabet.get_top_symbol alf )
  in
  let sorts = Alphabet.sorts_with_wellfounded_relations alf in
  (* for every sort, try finding a good projection function *)
  let rec try_each_sort = function
    | [] ->
      (* we tried all sorts, and found nothing *)
      if verbose then
        Printf.printf "Cannot use basic value criterion: %s%s.\n"
          "There is no well-founded relation which is suitable "
          "for all symbols.\n" ;
      None
    | sort :: tail ->
      (* trying sort [sort]; figure out the list [candidates] of
      triples (f, [x1,...,xn], nu), where [nu] is a list of all
      arguments (as terms) which f(x1,...,xn) might be mapped onto;
      that is, arguments which are values of sort [sort] *)
      let suitable = get_suitable_arguments "basic" verbose alf terms [sort] in
      let candidates = standard_candidates alf env dps suitable in
      (* from this, create the possible projection list; [projection]
      lists items (f, (xs, [x1,...,xn], nu)) where [nu] lists
      arguments which f(x1,...,xn) might be mapped onto, and xs
      indicates the inde of the filtering in [nu] *)
      let choose_projection (f, argvars, possibilities) =
        let len = List.length possibilities in
        let fvars = List.map_range (boolvar env) 0 len in
        (f, (List.map Term.make_var fvars, argvars, possibilities))
      in
      let projection = List.map choose_projection candidates in
      let projreq = projection_requirements env alf vee neg in
      let basereqs = List.flat_map projreq projection in
      (* make a list of boolean variables, indicating for each DP
      whether it should be oriented strictly *)
      let strictness = List.map (boolvar env) dps in
      let tstrict = List.map Term.make_var strictness in
      (* and for each of the relations well-ordering values of this
      sort, check whether we can use it! *)
      let rec try_each_relation vee neg eq = function
        | [] -> try_each_sort tail
        | rel :: tl ->
          let dpreqs = basic_dp_requirements projection alf env vee
                                       neg eq rel sort tstrict dps in
          let fullreqs = List.append basereqs dpreqs in
          match Solver.satisfiable_formulas fullreqs (smt ()) env with
            | (Smtresults.SAT, gamma) ->
              let strictinfo =
                let isset x =
                  Term.root (Substitution.find x gamma) = Some top in
                List.map isset strictness
              in
              let projection = determine_projection projection gamma top in
              finish alf env "basic" verbose dps prob strictinfo
                projection (basic_explanation rel)
            | _ ->
              if verbose then
                Printf.printf "%s.\n" ("Failure using the basic " ^
                  "value criterion for sort " ^ (Sort.to_string sort)
                  ^ " and relation " ^ (Function.to_string rel)) ;
              (*Environment.drop env ;*)
              try_each_relation vee neg eq tl
      in
      try_each_relation vee neg eq (Alphabet.get_wellfounded sort alf)
  in
  try_each_sort sorts
;;

(* runs the main basic_processor, but aborts if '\/, not or = are unset *)
let basic_process verbose prob =
  try basic_process verbose prob
  with Not_found -> None
;;

(*****************************************************************************)
(*              basic and reversed value criterion for integers              *)
(*****************************************************************************)

(* returns the range requirements on the newly introduced variables *)
let range_requirements a e geq eq neg strictness projection =
  (* check whether each pi(f) is in the arity range for f *)
  let projectwithrange (_, (x, num, _, _)) = (Term.make_var x, 0, num-1) in
  let strictwithrange x = (x, 0, 1) in
  let checkbetween (x, below, above) =
    [(Term.make_function a e geq [make_num above; x]);
     (Term.make_function a e geq [x; make_num below])
    ]
  in
  let str = List.map strictwithrange strictness in
  let proj = List.map projectwithrange projection in
  List.flat_map checkbetween (List.append str proj)
;;

(* returns the requirements that always phi => left >= right + strict
   and if strict is 1 also phi => left >= 0 *)
let dp_requirements projection a e geq eq neg vee plus strictness dps =
  let unequal var num =
    Term.make_function a e neg [
      Term.make_function a e eq [
        Term.make_var var;
        make_num num
      ]
    ]
  in
  let goodsort term = Term.get_sort a e term = Alphabet.integer_sort a in
  let rec check_each x y strictvar constraints = function
    | [] -> []
    | ((i, arg1), (j, arg2)) :: tail ->
      (* don't add constraints if they are not both integers; we have
      already excluded that possibility in range_requirements *)
      if not (goodsort arg1) then
        unequal x i :: check_each x y strictvar constraints tail
      else if not (goodsort arg2) then
        unequal y j :: check_each x y strictvar constraints tail
      else
      let base = Term.make_function a e geq [arg1;arg2] in
      if valid_implication a e neg constraints base then (
        let atleast0 = Term.make_function a e geq [arg1; make_num 0] in
        let arg2plusone = Term.make_function a e plus [arg2; make_num 1] in
        let strict = Term.make_function a e geq [arg1; arg2plusone] in
        if (valid_implication a e neg constraints atleast0) &&
           (valid_implication a e neg constraints strict) then
          check_each x y strictvar constraints tail
        else (
          let xnoti = unequal x i in
          let ynotj = unequal y j in
          let nonstrict = Term.make_function a e eq [strictvar; make_num 0] in
          let either = Term.make_function a e vee [xnoti; ynotj] in
          let eitheror = Term.make_function a e vee [either; nonstrict] in
          eitheror :: check_each x y strictvar constraints tail
        )
      )
      else (
        let xnoti = unequal x i in
        let ynotj = unequal y j in
        let either = Term.make_function a e vee [xnoti; ynotj] in
        either :: check_each x y strictvar constraints tail
      )
  in
  let requirements_for (dp, var) =
    let f1 = Rule.left_root dp in
    let f2 = Rule.right_root dp in
    let args1 = Term.args (Rule.lhs dp) in
    let args2 = Term.args (Rule.rhs dp) in
    let phis = Rule.constraints dp in
    let zipsubst vars args = Substitution.of_list (List.zip vars args) in
    let subpossibilities gamma possible =
      let substandpair i x = (i, Substitution.apply_term gamma x) in
      List.mapi substandpair possible
    in
    let (var1, var2, combinations) = (
      if f1 = f2 then
        let (x, _, vars, possible) = List.assoc f1 projection in
        let gamma1 = zipsubst vars args1 in
        let gamma2 = zipsubst vars args2 in
        let combi1 = subpossibilities gamma1 possible in
        let combi2 = subpossibilities gamma2 possible in
        (x, x, List.zip combi1 combi2)
      else
        let (x, _, vars1, possible1) = List.assoc f1 projection in
        let (y, _, vars2, possible2) = List.assoc f2 projection in
        let gamma1 = zipsubst vars1 args1 in
        let gamma2 = zipsubst vars2 args2 in
        let combi1 = subpossibilities gamma1 possible1 in
        let combi2 = subpossibilities gamma2 possible2 in
        (x, y, List.product combi1 combi2)
    ) in
    check_each var1 var2 var phis combinations
  in
  List.flat_map requirements_for (List.zip dps strictness)
;;

let get_projection projection gamma a e =
  let get_projection_value (f, (x,_,vars,possible)) =
    let value = Substitution.find x gamma in
    match value with
      | (Term.Fun (g, [])) ->
        if Function.is_integer g then
          let k = Function.integer_to_int g in
          (f, (vars, List.nth possible k))
        else failwith ("Error in value criterion: projection " ^
          "function with strange value, NU maps to " ^
          (Function.find_name g) ^ ".")
      | _ -> failwith ("Error in value criterion: projection " ^
          "function maps to unexpected value " ^
          (Printer.to_string_term value) ^ ".")
  in
  List.map get_projection_value projection
;;

(* helping function for basic_process: runs the smt-solver in such a
way (possibly more than once) to get as many formulas strict as
possible *)
let try_many atleast env reqs num =
  let rec check_better gamma num =
    if num <= 1 then (Smtresults.SAT, gamma)
    else (
      let fullreqs = (atleast num) :: reqs in
      match Solver.satisfiable_formulas fullreqs (smt ()) env with
        | (Smtresults.SAT, delta) -> (Smtresults.SAT, delta)
        | _ -> check_better gamma (num - 1)
    )
  in
  let fullreqs = (atleast 1) :: reqs in
  match Solver.satisfiable_formulas fullreqs (smt ()) env with
    | (Smtresults.SAT, gamma) -> check_better gamma num
    | pair -> pair
;;

(* prints an explanation of how the basic value criterion is applied;
here, nu maps function symbols to tuples (vars, projection) *)
let explanation a e kind dps nu =
  (* print an interpreted dependency pair *)
  let tostr_interpreted_dp (strict, dp) =
    let lhs = tostr_projected_term nu (Rule.lhs dp) in
    let rhs = tostr_projected_term nu (Rule.rhs dp) in
    let phis = Rule.constraints dp in
    let constr = List.implode Printer.to_string_term "/\\" phis in
    if strict then "  " ^ constr ^ "  ==>  " ^ lhs ^ " > " ^ rhs ^
                   "  with  " ^ lhs ^ " >= 0"
    else "  " ^ constr ^ "  ==>  " ^ lhs ^ " >= " ^ rhs
  in
  (* actually do all the printing! *)
  let text = "We use the " ^ kind ^
    " value criterion with the projection function NU:\n" ^
    (List.implode tostr_known_projection "\n" nu) ^ "\n\n" ^
    "This gives the following inequalities:\n" ^
    (List.implode tostr_interpreted_dp "\n" dps) ^ "\n\n"
  in
  text ^ (oriented_text (List.for_all fst dps))
;;

let simple_process candidatemaker kind verbose prob =
  let (a, env, dps, ts) = get_dp_data prob in
  let suitable_arguments =
    get_suitable_arguments kind verbose a ts [intsort] in
  (* make sure we can select an argument for each function symbol *)
  let nocandidates (f, _, lst) =
    if (lst = []) && verbose then
      Printf.printf "Cannot use basic value criterion: symbol %s %s.\n"
        (Function.find_name f) "has no value arguments of Int sort." ;
    lst = []
  in
  if List.exists nocandidates suitable_arguments then None else
  (* create projection and bits to indicate strict ordering *)
  let candidates = candidatemaker a env dps suitable_arguments in
  let (geq, plus, _, vee, eq, neg) = arithmetic_symbols a in
  let choose_projection (f, argvars, possibilities) =
    (f, (freshvar env (), List.length possibilities, argvars, possibilities))
  in
  let projection = List.map choose_projection candidates in
  let strictness = List.map (freshvar env) dps in
  let tstrict = List.map Term.make_var strictness in
  let basereqs = range_requirements a env geq eq neg tstrict projection in
  (* create requirements for each of the dependency pairs *)
  let dpreqs = dp_requirements projection a env geq eq neg vee plus
                               tstrict dps in
  (* get as many requirements strict as possible! *)
  let atleast n = atleastnum n a env geq plus tstrict in
  let fullreqs = List.append dpreqs basereqs in
  match try_many atleast env fullreqs (List.length tstrict) with
    | (Smtresults.SAT, gamma) ->
      let strictinfo =
        let isset x = Substitution.find x gamma = make_num 1 in
        List.map isset strictness
      in
      let projection = get_projection projection gamma a env in
      finish a env kind verbose dps prob strictinfo projection
             explanation
    | _ ->
      if verbose then
        Printf.printf "The %s value criterion is not applicable.\n" kind ;
      Environment.drop env ;
      None

let basic_integer_process v p =
  try simple_process standard_candidates "basic-integer" v p
  with NoIntegerSymbols -> None
;;

(*****************************************************************************)
(*                         reversed value criterion                          *)
(*****************************************************************************)

(* returns a list of equations s >= x or s > x, where x is a variable;
here, s >= x is presented as (s,x,false) and s > x as (s,x,true). *)
let rec get_comparisons a undernot = function
  | [] -> []
  | Term.Fun (f, args) :: tail | Term.InstanceFun (f, args, _) :: tail ->
    let isand = (try f = Alphabet.get_and_symbol a with Not_found -> false) in
    let isor = (try f = Alphabet.get_or_symbol a with Not_found -> false) in
    let isnot = (try f = Alphabet.get_not_symbol a with Not_found -> false) in
    let recurse newargs = get_comparisons a undernot newargs in
    if isand || isor then recurse (args @ tail) else
    if isnot then get_comparisons a (not undernot) (args @ tail) else
    let checkargs combine = match args with
      | [x;y] ->
        let (u,v,k) = combine x y in
        (*if not (Term.is_var v) then recurse tail else
        else if List.is_subset (Term.vars v) (Term.vars u) then recurse tail
        else*) (u,v,k) :: recurse tail
      | _ -> recurse tail
    in
    let name = Function.find_name f in
    if name = ">" || name = "greater" then checkargs (fun x y -> (x,y,true))
    else if name = "<" || name = "smaller" then checkargs (fun x y -> (y,x,true))
    else if name = ">=" || name = "geq" then checkargs (fun x y -> (x,y,false))
    else if name = "<=" || name = "leq" then checkargs (fun x y -> (y,x,false))
    else recurse tail
  | _ :: tail -> get_comparisons a undernot tail
;;

(* Given a dependency pair and a set of other pairs, returns both the
pairs and, if pair is not recursive, all its chainings with followup
pairs *)
let try_chaining e dps pair =
  let (left, right, cs) = (Rule.lhs pair, Rule.rhs pair,
                           Rule.constraints pair) in
  let chain dp =
    let (lhs, rhs, dcs) = (Rule.lhs dp, Rule.rhs dp,
                           Rule.constraints dp) in
    let gamma =
      try Elogic.match_term right lhs
      with Elogic.Not_matchable ->
        failwith "Error in try_chaining: somehow matching fails."
    in
    let vars = List.diff (Rule.vars dp) (Term.vars lhs) in
    let extend_with_fresh gamma x =
      let y = Environment.create_var_like x e [] e in
      Substitution.add x (Term.make_var y) gamma
    in
    let gamma = List.fold_left extend_with_fresh gamma vars in
    let newrhs = Substitution.apply_term gamma rhs in
    let newcs = List.map (Substitution.apply_term gamma) dcs in
    Rule.create left newrhs (cs @ newcs)
  in
  match (Term.root left, Term.root right) with
    | (None, _) | (_, None) -> [pair]
    | (Some f, Some g) ->
      if f = g then [pair] else
      let chainable dp =
        if g <> Rule.left_root dp then false else
        let args = Term.args (Rule.lhs dp) in
        if not (List.for_all Term.is_var args) then false
        else args = List.unique args
      in
      let chaindps = List.filter chainable dps in
      pair :: List.map chain chaindps
;;

(* given that vars lists variables for each argument position,
together with an integer indicating whether it can be used in a
projection function for f (0: it cannot be used; 1: it can be used,
but is not one of the sorts we can handle; 2: it can be used however
we like),  finds a number of (reasonable) functions over these
variables of the form <something> - variable *)
let reverse_candidates_for f a e dps vars =
  let relevant dp = f = Rule.left_root dp in
  let reldps = List.filter relevant dps in
  let reldps = List.flat_map (try_chaining e dps) reldps in
  let dpinfo dp = (Term.args (Rule.lhs dp), 
                   get_comparisons a false (Rule.constraints dp)
                  ) in
  let info = List.map dpinfo reldps in
  let makereplacement args =
    let make (arg, (x, b)) =
      if b = 0 then []
      else match arg with
        | Term.Var y -> [(y, Term.make_var x)]
        | _ -> []
    in
    let rec uniquify = function
      | [] -> []
      | head :: tail ->
        let x = fst head in
        let rest = List.filter (fun (y, _) -> x <> y) tail in
        head :: uniquify rest
    in
    let base = List.flat_map make (List.zip args vars) in
    Substitution.of_list (uniquify base)
  in
  let dpsubst = List.map (fun (a,c) -> (makereplacement a, c)) info in
  (* substitute the given comparison, provided ALL its variables are
  in the domain of gamma (otherwise return []) *)
  let substitute_comparison gamma (s, t, b) =
    let vars = (Term.vars t) @ (Term.vars s) in
    if List.exists (fun x -> not (Substitution.mem x gamma)) vars
    then []
    else [(Substitution.apply_term gamma s,
           Substitution.apply_term gamma t,
           b)]
  in
  (* apply the given substitution on all given comparisons which
  contain only variables in subst's domain *)
  let substitute_comparisons (subst, comparisons) =
    List.flat_map (substitute_comparison subst) comparisons
  in
  (* get expressions representing terms s > x or s >= x, using only
  the legal variables in vars *)
  let comparisons = List.flat_map substitute_comparisons dpsubst in
  let comparisons = List.unique comparisons in
  (* given a constraint "term >= x", proposes a reversal "term+1-x" *)
  let (_, plus, times, _, _, _) = arithmetic_symbols a in
  let propose_reversal (term, x, b) =
    let minone = Term.make_fun (Function.integer_symbol (-1)) [] in
    let xneg = Term.make_function a e times [minone; x] in
    let together = Term.make_function a e plus [term; xneg] in
    (*
    if b then together else
    let one = Term.make_fun (Function.integer_symbol 1) [] in
    Term.make_function a e plus [together; one]
    *)
    together
  in
  List.map propose_reversal comparisons
;;

(* returns all projection functions f(x1,...,xn) = xi AND all
reversed projection functions f(x1,...,xn) = <something> - xi *)
let reverse_candidates a e dps functioninfo =
  (* combines the list of variables with integers depending on
  whether the index of the variable is in usable, and has a good
  sort; 2 means usable and the right sort, 1 just usable *)
  let rec get_usable_info vars usable k =
    match (vars, usable) with
      | ([], _) -> []
      | (lst, []) -> List.map (fun x -> (x, 0)) vars
      | (x :: tail, (i, goodsort) :: rest) ->
        if i = k then (
          if goodsort then (x, 2) :: get_usable_info tail rest (k + 1)
          else (x, 1) :: get_usable_info tail rest (k + 1)
        )
        else (x, 0) :: get_usable_info tail usable (k + 1)
  in
  (* returns all projection functions of the form f(x1,...,xn) = xi
  (assuming that "f(x1,...,xn) =" is added by the calling function) *)
  let get_standard_candidates vars =
    let get_good_vars (x, b) =
      if b = 2 then [Term.make_var x]
      else []
    in
    List.flat_map get_good_vars vars
  in
  (* returns all projection functions of the form f(x1,...,xn) =
  <term> - xi (assuming that "f(x1,...,xn) =" is added by the
  calling function) *)
  let get_reversed_candidates f vars =
    reverse_candidates_for f a e dps vars
  in
  (* returns all projection functions f(x1,...,xn) = <term> *)
  let get_candidates (f, sd, options) =
    let makevar i sort = make_internal_var i sort f a e in
    let input = List.mapi makevar (Sortdeclaration.input_sorts sd) in
    let vars = get_usable_info input options 0 in
    (f, input, (get_standard_candidates vars) @
               (get_reversed_candidates f vars))
  in
  List.map get_candidates functioninfo
;;

let reverse_process v p =
  try simple_process reverse_candidates "reverse" v p
  with NoIntegerSymbols | Not_found -> None
;;

(*****************************************************************************)
(*                         extended value criterion                          *)
(*****************************************************************************)

(* returns an interpretation of the form [x1,...,xn], y, and returns:
   (f, ([list of good argument positions tupled with the variable
   assigned to that position], extra variable))
*)
let choose_interpretation env (f, sd, args) =
  let intvar = freshvar env in
  let extra = intvar 37 in
    (* note: 37 is just a random number to avoid typing issues *)
  let args = List.map fst (List.filter snd args) in
  let argvars = List.map intvar args in
  (f, ((List.zip args argvars), extra))
;;

(* returns the requirements that always left >= right + strict, and
   if strict is 1 also left >= 0 *)
let dp_requirements interpretations a e plus times geq vee strictvars dps =
  let add x y = Term.make_function a e plus [x;y] in
  let mul x y = Term.make_function a e times [x;y] in
  let greater x y phi strictvar =
    let xgeqy = Term.make_function a e geq [x;y] in
    let nul = Term.make_fun (Function.integer_symbol 0) [] in
    let xgeq0 = Term.make_function a e geq [x;nul] in
    let maybexgeq0 = Term.make_function a e vee
      [Term.make_function a e geq [nul;strictvar]; xgeq0] in
    [(phi,xgeqy);(phi,maybexgeq0)]
  in
  let rec make_sum extra args n = function
    | [] -> Term.make_var extra
    | (num,var) :: tail ->
      let m = n + 1 in
      let (arghd, argtl) = (List.hd args, List.tl args) in
      if num = n then (
        let part = mul (Term.make_var var) arghd in
        add part (make_sum extra argtl m tail)
      )
      else make_sum extra argtl m ((num,var) :: tail)
  in
  let interpret = function
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      let (argmul, extra) = List.assoc f interpretations in
      make_sum extra args 0 argmul
    | _ -> failwith "Unexpected function shape"
  in
  let make_req strictvar dp =
    let left = interpret (Rule.lhs dp) in
    let right = interpret (Rule.rhs dp) in
    let fullright = add right strictvar in
    greater left fullright (Rule.constraints dp) strictvar
  in
  List.flat_map id (List.map2 make_req strictvars dps)
;;

(* returns the range requirements on the newly introduced variables *)
let range_requirements a e geq vars =
  let is_between x above below =
    [(Term.make_function a e geq [make_num above; x]);
     (Term.make_function a e geq [x; make_num below])
    ]
  in
  let handle (x, (bottom, top)) = is_between (Term.make_var x) top bottom in
  List.flat_map handle vars
;;

(* given the chosen parameter assignments, returns the actual
projection function represented by interpretations *)
let get_projection interpretations choices =
  let parse_interpretation (f, (lst, extra)) =
    let getvalue (k, arg) = (k, List.assoc arg choices) in
    let chosenlst = List.map getvalue lst in
    let relevant (_, value) = value <> 0 in
    let chosenlst = List.filter relevant chosenlst in
    let chosenextra = List.assoc extra choices in
    (f, (chosenlst, chosenextra))
  in
  List.map parse_interpretation interpretations
;;

(* makes the formula premises => conclusion, where premises is
considered as a conjunction *)
let rec make_implication vee neg a e premises conclusion =
  match premises with
    | [] -> conclusion
    | head :: tail ->
      Term.make_function a e vee [Term.make_function a e neg [head];
                       make_implication vee neg a e tail conclusion]
;;

(* prints an explanation of how the extended value criterion is
applied; here, nu maps function symbols to pairs ((list of argument
index, count for that argument), added number) *)
let explanation a e kind dps nu =
  (* print the combination of a string (for instance a variable) and
  the number of times this string must occur; we are quite liberal
  with brackets, because it is nicer to have (x+1) + (x+1) than
  x + 1 + x + 1 *)
  let print_combination args (varnum, count) =
    let (arg, brackets) = List.nth args varnum in
    let bracketedarg = if brackets then "(" ^ arg ^ ")" else arg in
    if count = 0 then "0"
    else if count = 1 then bracketedarg
    else if count = -1 then "-" ^ bracketedarg
    else (string_of_int count) ^ bracketedarg
  in
  (* print an interpretation, applied on arguments which are
  already translated to strings, which may need brackets adding
  depending on their parameters *)
  let rec print_interpretation args extra = function
    | [] -> string_of_int extra
    | [single] ->
      let main = print_combination args single in
      if extra = 0 then main
      else if extra > 0 then main ^ " + " ^ (string_of_int extra)
      else main ^ " - " ^ (string_of_int (-extra))
    | head :: (num, count) :: tail ->
      let main = print_combination args head in
      let (symbol, poscount) =
        if count >= 0 then (" + ", count)
        else (" - ", -count)
      in
      let newlist = (num, poscount) :: tail in
      main ^ symbol ^ (print_interpretation args extra newlist)
  in
  (* print an interpretation to the user *)
  let tostr_interpretation (f, (lst, extra)) =
    let arity = Alphabet.find_ari f a in
    let xs = List.gen (fun i -> "x" ^ (string_of_int i)) arity in
    let xscombi = List.map (fun x -> (x, false)) xs in
    let xsstring =
      if xs = [] then ""
      else "(" ^ (List.implode id "," xs) ^ ")"
    in
    "  NU[" ^ (Function.find_name f) ^ xsstring ^ "] = " ^
              (print_interpretation xscombi extra lst)
  in
  (* convert an interpretation applied on a term to a string *)
  let topairterm term =
    match term with
      | Term.InstanceFun (_, [], _) | Term.Fun (_, [])
      | Term.Forall _ | Term.Exists _ | Term.Var _ ->
        (Printer.to_string_term term, false)
      | _ -> (Printer.to_string_term term, true)
  in
  let print_interpreted_term term =
    match term with
      | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
        let (lst, extra) = List.assoc f nu in
        let arguments = List.map topairterm args in
        print_interpretation arguments extra lst
      | _ -> failwith ("Encountered variable or quantifier as " ^
                "left- or right-hand side of a dependency pair!")
  in
  (* print an interpreted dependency pair *)
  let tostr_interpreted_dp (strict, dp) =
    let lhs = print_interpreted_term (Rule.lhs dp) in
    let rhs = print_interpreted_term (Rule.rhs dp) in
    let phis = Rule.constraints dp in
    let constr = List.implode Printer.to_string_term "/\\" phis in
    if strict then "  " ^ constr ^ "  ==>  " ^ lhs ^ " > " ^ rhs ^
                   "  with  " ^ lhs ^ " >= 0"
    else "  " ^ constr ^ "  ==>  " ^ lhs ^ " >= " ^ rhs
  in
  (* actually do all the printing! *)
  let text = "We use the " ^ kind ^
    " value criterion with the projection function NU:\n" ^
    (List.implode tostr_interpretation "\n" nu) ^ "\n\n" ^
    "This gives the following inequalities:\n" ^
    (List.implode tostr_interpreted_dp "\n" dps) ^ "\n\n"
  in
  let text =
    if List.for_all fst dps then
      text ^ "All dependency pairs are strictly oriented, so the " ^
        "entire dependency pair problem may be removed.\n"
    else text ^ "We remove all the strictly oriented dependency pairs.\n"
  in
  text
;;

let extended_process_main verbose prob =
  (* get data from DP problem *)
  let (a, env, dps, ts) = get_dp_data prob in
  let suitable = get_suitable_arguments "extended" verbose a ts [intsort] in
  (* create interpretations and bits to indicate strict ordering *)
  let interpretations = List.map (choose_interpretation env) suitable in
  let strictness = List.map (freshvar env) dps in
  (* store newly created variables in all_unknowns *)
  let varwithrange (_,y) = (y, Some (-1,1)) in
  let get_unknowns (_, (lst, x)) = (x,None) :: (List.map varwithrange lst) in
  let inter_unknowns = List.flat_map get_unknowns interpretations in
  let bitrange = List.map (fun x -> (x,Some (0,1))) in
  let all_unknowns = List.append (bitrange strictness) inter_unknowns in
  (* create the requirements *)
  let (geq, plus, times, vee, _, neg) = arithmetic_symbols a in
  (*let tinter = List.map (Term.make_var <.> fst) inter_unknowns in*)
  let tstrict = List.map Term.make_var strictness in
  let reqs = dp_requirements interpretations a env plus times geq vee
                 tstrict dps in
  let reqs = ([], atleastnum 1 a env geq plus tstrict) :: reqs in
  let makereq (phis, psi) = make_implication vee neg a env phis psi in
  let reqs = List.map makereq reqs in
  (* determine satisfiability *)
  (*let reqs = List.append (range_requirements a env geq all_unknowns) reqs in*)
  match Solver.find_values reqs all_unknowns a env with
    | Some vars ->
      let strictinfo =
        let isset x = try List.assoc x vars = 1 with Not_found -> true in
        List.map isset strictness
      in
      let projection = get_projection interpretations vars in
      finish a env "extended" verbose dps prob strictinfo projection
             explanation
    | None ->
      if verbose then
        Printf.printf "The extended value criterion is not applicable.\n" ;
      Environment.drop env ;
      None
;;

let extended_process verbose prob =
  try extended_process_main verbose prob
  with NoIntegerSymbols | Not_found -> None
;;
