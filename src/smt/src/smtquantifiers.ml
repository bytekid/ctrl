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

(*** OPENS *******************************************************************)

open Util;;
open Ctrs;;

(*** TYPES *******************************************************************)

exception UnboundedQuantification of Term.t;;

(*** FUNCTIONS ***************************************************************)

let special_symbols alf =
  let gsymb   = try Some (Alphabet.get_greater_symbol alf) with _ -> None in
  let ssymb   = try Some (Alphabet.get_smaller_symbol alf) with _ -> None in
  let geqsymb = try Some (Alphabet.get_geq_symbol alf)     with _ -> None in
  let leqsymb = try Some (Alphabet.get_leq_symbol alf)     with _ -> None in
  let eqsymb  = try Some (Alphabet.get_equal_symbol alf)   with _ -> None in
  let impsymb = try Some (Alphabet.get_imply_symbol alf)   with _ -> None in
  let andsymb = try Some (Alphabet.get_and_symbol alf)     with _ -> None in
  let notsymb = try Some (Alphabet.get_not_symbol alf)     with _ -> None in
  let orsymb  = try Some (Alphabet.get_or_symbol alf)      with _ -> None in
  (gsymb, ssymb, geqsymb, leqsymb, eqsymb, impsymb, andsymb, notsymb, orsymb)
;;

(* constructors *)

let make_quantification universal x n nstrict m mstrict phi alf =
  (* get all the symbols *)
  let (gsymb, ssymb, geqsymb, leqsymb, eqsymb, impsymb, andsymb,
       notsymb, orsymb) =
    special_symbols alf in
  (* we'll need x as a term as well as as a variable *)
  let xvar = Term.make_var x in
  (* builders for a <= b and a < b terms *)
  let env = Environment.dummy () in
  let make symb a b = Term.make_function alf env (Option.the symb) [a;b] in
  let negate a = Term.make_function alf env (Option.the notsymb) [a] in
  let fail () = failwith
    ( "Cannot make ranged " ^
      (if universal then "universal" else "existential") ^
      " quantification: the required core symbols have not been set!"
    ) in
  let leq a b =
    if leqsymb <> None then make leqsymb a b
    else if geqsymb <> None then make geqsymb b a
    else if (notsymb <> None) && (gsymb <> None) then negate (make gsymb a b)
    else if (notsymb <> None) && (ssymb <> None) then negate (make ssymb b a)
    else fail ()
  in
  let smaller a b =
    if ssymb <> None then make ssymb a b
    else if gsymb <> None then make gsymb b a
    else if (notsymb <> None) && (geqsymb <> None) then negate (make geqsymb a b)
    else if (notsymb <> None) && (leqsymb <> None) then negate (make leqsymb b a)
    else fail ()
  in
  let c1, a1 = if nstrict then (smaller, leq) else (leq, smaller) in
  let c2, a2 = if mstrict then (smaller, leq) else (leq, smaller) in
  (* build a universal quantification; this can be done in two ways *)
  if universal then (
    try Term.make_forall x (
      try make impsymb (make andsymb (c1 n xvar) (c2 xvar m)) phi
      with _ -> make orsymb (make orsymb (a1 xvar n) (a2 m xvar)) phi
    )
    with _ -> fail ()
  )
  (* build an existential quantification; there is only one way to do this *)
  else (
    try Term.make_exists x (
      make andsymb (make andsymb (c1 n xvar) (c1 xvar m)) phi
    )
    with _ -> fail ()
  )
;;

let universal_quantification = make_quantification true;;
let existential_quantification = make_quantification false;;

(* destructors *)

let rec check_boundary x term negate alf =
  (* get all symbols *)
  let (gsymb, ssymb, geqsymb, leqsymb, eqsymb, _, _, notsymb, _) =
    special_symbols alf in
  (* deal with negation *)
  let rev (below, above) =
    if not negate then (below, above)
    else match (below, above) with
      | (None, Some (a, b)) -> (Some (a, not b), None)
      | (Some (a, b), None) -> (None, Some (a, not b))
      | _ -> failwith "strange call to rev!"
  in
  (* handle the situations a R x and x R a together *)
  let maybeswap swap (a, b) =
    if swap then (b, a)
    else (a, b)
  in
  let handle_fun f a swap =
    let sf = Some f in
    let finish pair = rev (maybeswap swap pair) in
    if sf = gsymb then finish (None, Some (a, true))
    else if sf = geqsymb then finish (None, Some (a, false))
    else if sf = ssymb then finish (Some (a, true), None)
    else if sf = leqsymb then finish (Some (a, false), None)
    else if sf = eqsymb then (
      if negate then (None, None)
      else (Some (a, false), Some (a, false))
    )
    else (None, None)
  in
  (* check all possible forms of boundaries! *)
  match term with
    | Term.Fun (f, [a;Term.Var y])
    | Term.InstanceFun (f, [a; Term.Var y], _) ->
      if y = x then handle_fun f a false
      else if a = Term.Var x then handle_fun f (Term.Var y) true
      else (None, None)
    | Term.Fun (f, [Term.Var y; a])
    | Term.InstanceFun (f, [Term.Var y; a], _) ->
      if y = x then handle_fun f a true
      else (None, None)
    | Term.Fun (f, [a]) | Term.InstanceFun (f, [a], _) ->
      if Some f = notsymb then check_boundary x a (not negate) alf
      else (None, None)
    | _ -> (None, None)
;;

(* returns a lower boundary, an upper boundary, and the remaining term *)
let rec split_boundaries symb x below above term alf negate =
  (* if we already have an upper and lower boundary, we won't do anything *)
  if (below <> None) && (above <> None) then (below, above, Some term) else
  (* see whether the term is a basic term that gives us boundaries! *)
  let (lower, higher) = check_boundary x term negate alf in
  (* upper AND lower boundaries, oh dear *)
  if (lower <> None) && (higher <> None) then (
    if (below = None) && (above = None) then (lower, higher, None)
    else if below = None then (lower, above, Some term)
    else (below, higher, Some term)
      (* we have to return the term as well, because it cannot
      replace the previous boundaries: we don't have those terms
      anymore! *)
  )
  (* we have improved a single boundary *)
  else if (below = None) && (lower <> None) then (lower, above, None)
  else if (above = None) && (higher <> None) then (below, higher, None)
  (* we haven't improved on a boundary, but maybe we have children that can? *)
  else match term with
    | Term.Fun (f, args) | Term.InstanceFun (f, args, _) ->
      if Some f <> symb then (below, above, Some term) else
      let rec handle_children below above badargs = function
        | [] ->
          if badargs = [] then (below, above, None)
          else if List.tl badargs = [] then
            (below, above, Some (List.hd badargs))
          else (below, above, Some (Term.replace_args term (List.rev badargs)))
        | head :: tail ->
          match split_boundaries symb x below above head alf negate with
            | (b, a, None) -> handle_children b a badargs tail
            | (b, a, Some t) -> handle_children b a (t :: badargs) tail
      in
      handle_children below above [] args
    | _ -> (below, above, Some term)
;;

let universal_range x alf phi =
  (* get all the symbols *)
  let (gsymb, ssymb, geqsymb, leqsymb, eqsymb, impsymb, andsymb,
       notsymb, orsymb) = special_symbols alf in
  let fail _ = raise (UnboundedQuantification phi) in
  let handle_implication premise result =
    match split_boundaries andsymb x None None premise alf false with
      | (Some b, Some a, Some rest) ->
        (b, a, Term.replace_args phi [rest;result])
      | (Some b, Some a, None) -> (b, a, result)
      | _ -> fail ()
  in
  let handle_disjunction phi =
    match split_boundaries orsymb x None None phi alf true with
      | (Some b, Some a, Some rest) -> (b, a, rest)
      | (Some b, Some a, None) ->
        ( try (b, a, Term.make_fun (Alphabet.get_bot_symbol alf) [])
          with Not_found -> (b, a, phi)
        )
      | _ -> fail ()
  in
  match phi with
    | Term.Fun (f, [a;b]) | Term.InstanceFun (f, [a;b], _) ->
      if Some f = impsymb then handle_implication a b
      else handle_disjunction phi
    | _ -> handle_disjunction phi
;;

let existential_range x alf phi =
  (* get all the symbols *)
  let (_,_,_,_,_,_,andsymb,_,_) = special_symbols alf in
  (* split off the boundary conditions as required! *)
  match split_boundaries andsymb x None None phi alf false with
    | (Some b, Some a, Some rest) -> (b, a, rest)
    | (Some b, Some a, None) ->
      ( try (b, a, Term.make_fun (Alphabet.get_top_symbol alf) [])
        with Not_found -> (b, a, phi)
      )
    | _ -> raise (UnboundedQuantification phi)
;;

