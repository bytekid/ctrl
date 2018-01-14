(* Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
 * and 2014 Cynthia Kop
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

(*** MODULES ******************************************************************)
module Fun = Function;;
module Var = Variable;;

(*** EXCEPTIONS ***************************************************************)
exception Not_semi_unifiable;;
exception Not_unifiable;;
exception Not_matchable;;

(*** OPENS ********************************************************************)
open Prelude;;
open Util;;

(* the use of a label module is explained in rewriting.ml *)
module L = struct end;;
module S = Substitution.Make(L);;

(*** TYPES *******************************************************************)
type substitution = S.t;;
type term = Term.t = Var of Var.t | Fun of Fun.t * term list |
            InstanceFun of Fun.t * term list * Sortdeclaration.t |
            Forall of Var.t * term | Exists of Var.t * term;;
 
(*** EXCEPTIONS **************************************************************)
exception Not_semi_unifiable = Not_semi_unifiable;;
exception Not_unifiable = Not_unifiable;;
exception Not_matchable = Not_matchable;;
 
(*** FUNCTIONS ***************************************************************)
 
(* Renaming *)

let renaming terms forbidden_names e =
  let rename_var x s =
    let y = Environment.create_var_like x e forbidden_names e in
    S.add x (Var y) s
  in
  let rec renaming s = function
    | Var x -> if S.mem x s then s else rename_var x s
    | Fun (_,ts) | InstanceFun (_,ts,_) -> List.foldl renaming s ts
    | Forall (x, t) | Exists (x, t) ->
      renaming (rename_var x s) t
  in
  List.foldl renaming S.empty terms
;;

let environment_oblivious_renaming lst =
  let rec rename_list sub i = function
    | [] -> (sub, i)
    | head :: tail -> rename_term sub i tail head
  and rename_term sub i lst = function
    | Var x -> (
      if S.mem x sub then rename_list sub i lst
      else
        let next = i + 1 in
        let y = Variable.create i ("x" ^ (string_of_int i)) in
        rename_list (S.add x (Var y) sub) next lst
      )
    | Fun (_,ts) | InstanceFun (_,ts,_) ->
      rename_list sub i (List.append ts lst)
    | Forall (x, t) | Exists (x, t) ->
      rename_term sub i (t :: lst) (Var x)
  in
  let rec rename_all i = function
    | [] -> []
    | head :: tail ->
      let (gamma, j) = rename_term S.empty i [] head in
      let changed = S.apply_term gamma head in
      changed :: rename_all j tail
  in
  rename_all 0 lst
;;
 
(* Unification *)

let unify_problem =
  let rec unify s = function
    | [] -> s
    | (u,v) :: p when u = v -> unify s p
    | (Var x as u,(Var y as v)) :: p ->
      if S.apply x v s = v then
        let t =
          if String.sub (Variable.find_name x) 0 1 = "C" then S.singleton x v 
          else S.singleton y u
        in
        let apply = S.apply_term in
        unify (S.compose apply s t) (List.rev_map (Pair.map (apply t)) p)
      else raise Not_unifiable
    | (Var x as u,v) :: p | (v,(Var x as u)) :: p ->
      if not (Term.is_subterm u v) && S.apply x v s = v then
        let t = S.singleton x v and apply = S.apply_term in
        unify (S.compose apply s t) (List.rev_map (Pair.map (apply t)) p)
      else raise Not_unifiable
    | (Fun (f,us),Fun (g,vs)) :: p ->
      if f = g then unify s (List.rev_append (List.rev_zip us vs) p)
      else raise Not_unifiable
    | (InstanceFun (f,us,fd),InstanceFun (g,vs,gd)) :: p ->
      if f = g && fd = gd then unify s (List.rev_append (List.rev_zip us vs) p)
      else raise Not_unifiable
    | (Forall (x, u), Forall (y, v)) :: p
    | (Exists (x, u), Exists (y, v)) :: p ->
      if (S.mem x s) || (S.mem y s) then
        failwith ("Substituting buggers up if binder variables " ^
          "are not uniquely binders!")
      else unify (S.add x (Term.make_var y) s) ((u,v) :: p)
    | _ -> raise Not_unifiable
  in
  unify S.empty
;;
 
let unify u v = unify_problem [(u,v)];;
let are_unifiable u = catch Not_unifiable (const true <.> unify u) false;;
 
(* Matching *)

(* general matching *)

let match_problem =
  let rec solve s = function
    | [] -> s
    | (u,Var x) :: p ->
      (try solve (S.add x u s) p with S.Inconsistent -> raise Not_matchable)
    | (Fun (f,us),Fun (g,vs)) :: p ->
      if f = g then solve s (List.rev_append (List.rev_zip us vs) p)
      else raise Not_matchable
    | (InstanceFun (f,us,df), InstanceFun (g,vs,dg)) :: p ->
      if (f = g) && (df = dg) then solve s (List.rev_append (List.rev_zip us vs) p)
      else raise Not_matchable
    | (Forall (x,u),Forall (y,v)) :: p | (Exists (x,u),Exists (y,v)) :: p ->
      ( try solve (S.add y (Term.make_var x) s) ((u,v) :: p)
        with S.Inconsistent -> failwith ("Substituting buggers up if binder " ^
          "variables are not uniquely binders!")
      )
    | _ -> raise Not_matchable
  in
  solve S.empty
;;
 
let match_term u v = match_problem [(u,v)];;
let matches u = catch Not_matchable (const true <.> match_term u) false;;
let is_variant u v = matches u v && matches v u
let subsumes = flip matches;;
let contains u v = List.exists (subsumes v) (Term.subterms u);;
 
(* ground matching *)

(* not used, and the functions were undocumented so it was unclear how
they should be modified for quantifiers, so outcommented until they are
used for something! *)

(*
let rec simplify = function
  | [] -> Some []
  | (Var _,_) :: ps -> simplify ps
  | (Fun (f,us),Fun (g,vs)) :: ps ->
    if f = g then simplify (List.combine us vs @ ps) else None
  | (InstanceFun (f,us,fd),InstanceFun (g,vs,gd)) :: ps ->
    if f = g && fd = gd then simplify (List.combine us vs @ ps) else None
  | (t,Var x) :: ps -> Option.map (List.cons (t,x)) (simplify ps)
  | _ -> None
;;
 
let rec merge term =
  let merge_funs f us fd g vs gd =
    if f = g && fd = gd then
      let ws =
        List.foldr2 (fun u v ws -> Option.fold (fun ws ->
        Option.map (flip List.cons ws) (merge (u,v))) None ws) (Some []) us vs
      in
      Option.map (fun ws -> Fun (f,ws)) ws
    else None
  in
  match term with
    | Var _,u | u,Var _ -> Some u
    | Fun (f,us),Fun (g,vs) -> merge_funs f us None g vs None
    | InstanceFun (f,us,fd), InstanceFun (g,vs,gd) ->
      merge_funs f us fd g vs gd
    | _ -> None
;;
 
let rec extend x u = function
  | [] -> Some []
  | (v,y) :: ps ->
    if x = y then Option.fold (flip (extend x) ps) None (merge (u,v))
    else Option.map (List.cons (v,y)) (extend x u ps)
;;
 
let rec solve = function
  | [] -> true
  | (u,x) :: ps -> Option.fold solve false (extend x u ps)
;;
 
let ground_matches u v = Option.fold solve false (simplify [(u,v)]);;
*)

