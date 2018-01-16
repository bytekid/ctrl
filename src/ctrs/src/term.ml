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

(*** MODULES *****************************************************************)
module Pos = Position;;
module E = Util.Either;;
module Parser = Parsec.MakeCharParser(Parsec.StringInput);;

(*** OPENS *******************************************************************)
open Util;;
open Prelude;;

(*** TYPES *******************************************************************)
type func = Function.t;;
type sort = Sort.t;;
type sd = Sortdeclaration.t;;
type t = Var of Variable.t | Fun of func * t list |
         InstanceFun of func * t list * sd |
         Forall of Variable.t * t |
         Exists of Variable.t * t;;

(*** EXCEPTIONS **************************************************************)
exception Fail;;

(*** FUNCTIONS ***************************************************************)

(* Compare Functions *)

let compare s t =
  (* l1 contains mappings (x -> y) to replace bound variables in the
  left-hand side by the right-hand side, l2 contains (y -> x) for the
  replacement in the other direction (only one is necessary for
  finding replacements, but we also care whether we aren't comparing
  a bound with a free variable) *)
  let rec compare_main l1 l2 = function
    | (Var x, Var y) ->
      if List.mem_assoc x l1 then (
        try let z = List.assoc y l2 in compare x z
        with Not_found -> -1
      )
      else if List.mem_assoc y l2 then 1
      else compare x y
    | (Fun (f1, args1), Fun (f2, args2)) ->
      let cmp = compare f1 f2 in
      if cmp = 0 then compare_args l1 l2 (args1, args2) else cmp
    | (InstanceFun (f1, args1, _), InstanceFun (f2, args2, _)) ->
      let cmp = compare f1 f2 in
      if cmp = 0 then compare_args l1 l2 (args1, args2) else cmp
    | (Forall (x, s), Forall (y, t)) ->
      compare_main ((x,y) :: l1) ((y,x) :: l2) (s, t)
    | (Exists (x, s), Exists (y, t)) ->
      compare_main ((x,y) :: l1) ((y,x) :: l2) (s, t)
    | (Var _, _) -> -1 | (_, Var _) -> 1
    | (Fun _, _) -> -1 | (_, Fun _) -> 1
    | (InstanceFun _, _) -> -1 | (_, InstanceFun _) -> 1
    | (Forall _, Exists _) -> -1 | (Exists _, Forall _) -> 1
  and compare_args l1 l2 = function
    | ([], []) -> 0
    | ([], _) -> -1
    | (_, []) -> 1
    | (h1 :: t1, h2 :: t2) ->
      let cmp = compare_main l1 l2 (h1, h2) in
      if cmp = 0 then compare_args l1 l2 (t1, t2) else cmp
  in
  compare_main [] [] (s,t)
;;

let equal s t = compare s t = 0;;

(* Constructors *)

let make_fun f ts = Fun (f, ts);;
let make_instance f ts d = InstanceFun (f, ts, d);;
let make_var x = Var x;;
let make_forall x s = Forall (x, s);;
let make_exists x s = Exists (x, s);;


(* Printers *)

let rec to_string = function
| Var x -> Variable.to_string x
| Fun (f,ts) | InstanceFun (f,ts,_) ->
  (Function.to_string ~debug:true f) ^ "(" ^ (List.implode to_string "," ts) ^ ")"
| Forall (x, s) -> "?A" ^ (Variable.to_string x) ^ "." ^ (to_string s)
| Exists (x, s) -> "?E" ^ (Variable.to_string x) ^ "." ^ (to_string s)
;;

let rec to_stringm = function
| Var x -> Variable.to_string x
| Fun (f,ts) | InstanceFun (f,ts,_) ->
  (Function.to_string ~debug:false f) ^ "(" ^ (List.implode to_stringm "," ts) ^ ")"
| Forall (x, s) -> "?A" ^ (Variable.to_string x) ^ "." ^ (to_stringm s)
| Exists (x, s) -> "?E" ^ (Variable.to_string x) ^ "." ^ (to_stringm s)
;;

let rec fprintf fmt = function
| Var x -> Variable.fprintf fmt x
| Fun (f,ts) | InstanceFun (f,ts,_) ->
  Format.fprintf fmt "@[%a@[(%a)@]@]" Function.fprintf f (List.fprintf fprintf ",") ts
| Forall (x, s) -> Format.fprintf fmt "@[?A%a.@[%a@]@]" Variable.fprintf x fprintf s
| Exists (x, s) -> Format.fprintf fmt "@[?E%a.@[%a@]@]" Variable.fprintf x fprintf s
;;

(*
let rec reflect = function
  | Var _ as x -> x
  | Fun (f,ts) -> Fun (f,List.rev_map reflect ts)
;;
*)

let is_forall = function | Forall _ -> true | _ -> false;;
let is_exists = function | Exists _ -> true | _ -> false;;

let rec replace p s t = 
  if Pos.is_root p then s
  else (
    let (i,q) = Pos.split_first p in
    match t with
      | Var _ -> failwith "illegal position"; 
      | Fun (f, ts) ->
        let l = List.length ts in
        if i < 0 || i >= l then failwith "illegal position"
        else Fun (f, List.mapi (fun j -> if i = j then replace q s else id) ts)
      | InstanceFun (f, ts, d) ->
        let l = List.length ts in
        if i < 0 || i >= l then failwith "illegal position"
        else InstanceFun (f, List.mapi (fun j -> if i = j then replace q s else id) ts, d)
      | Forall (x, u) ->
        if i <> 0 then failwith "illegal position"
        else Forall (x, replace q s u)
      | Exists (x, u) ->
        if i <> 0 then failwith "illegal position"
        else Exists (x, replace q s u)
  )
;;

let reverse t = 
  let rec reverse fs = function
    | Var _ as x -> List.foldr (fun f t -> Fun (f,[t])) x fs
    | Fun (f,ts) ->
      if List.is_singleton ts then reverse (f :: fs) (List.hd ts) 
      else failwith "not a string"
    | _ -> failwith "Can only replace terms representing strings."
  in  
  reverse [] t
;;

let subterm_with_binders p t =
  let rec subterm p t binders =
    if Pos.is_root p then (binders, t) else
    let (i,q) = Pos.split_first p in
    match t with
      | Var _ -> failwith "illegal position";
      | Fun (_,ts) | InstanceFun (_, ts, _) ->
        ( try subterm q (List.nth ts i) binders
          with Invalid_argument _ -> failwith "illegal position"
        )
      | Forall (x,s) | Exists (x,s) ->
        if i <> 0 then failwith "illegal position (in Exists/Forall)"
        else subterm q s (x :: binders)
  in
  subterm p t []
;;

let subterm p t = snd (subterm_with_binders p t);;

(* Term Symbols *)

let fsymbols p f =
  let add s ss = if p s then f s :: ss else ss in
  let rec fsymbols bound = function
    | Var x -> if List.mem x bound then [] else add (Left x) []
    | Fun (f,ts) | InstanceFun (f,ts,_) ->
      add (Right f) (List.flat_map (fsymbols bound) ts)
    | Forall (x,s) | Exists (x,s) -> fsymbols (x :: bound) s
  in
  List.unique_hash <.> (fsymbols [])
;;

let cons =
  let rec cons = function
    | Var _ -> []
    | Fun (f,ts) | InstanceFun (f,ts,_) ->
      let cs = List.flat_map cons ts in if ts = [] then f::cs else cs
    | Forall (_,s) | Exists (_,s) -> cons s
  in
  List.unique_hash <.> cons
;;

let funs = fsymbols (E.either (const false) (const true)) E.right;;
let vars = fsymbols (E.either (const true) (const false)) E.left;;
let symbols = fsymbols (const true) id;;
let root = function Fun(f,_) | InstanceFun(f,_,_) -> Some f | _ -> None;;

(* Properties *)
(*
let rec is_embedded s t = match (s,t) with
  | Var x, Var y -> x = y
  | Fun (f,ss), Fun (g,ts) ->
    (f = g && List.for_all2 is_embedded ss ts) || List.exists (is_embedded s) ts
  | InstanceFun (f,ss,sd), InstanceFun (g,ts,td) ->
    (f = g && sd = td && List.for_all2 is_embedded ss ts) ||
    List.exists (is_embedded s) ts
  | _, Fun (f,ts) | _, InstanceFun (f,ts,_) -> List.exists (is_embedded s) ts
  | _, _ -> false
;;
*)

let rec is_subterm s t =
  equal s t || is_proper_subterm s t

and is_proper_subterm s = function
    | Var _ -> false
    | Fun (_,ts) | InstanceFun (_,ts,_) ->
      List.exists (is_subterm s) ts
    | Forall (_,q) | Exists (_,q) -> is_subterm s q
;;

let is_cons = function | Fun (_,[]) | InstanceFun (_,[],_) -> true | _ -> false;;
let is_fun = function | Fun _ | InstanceFun _ -> true | _ -> false;;
let is_instance = function InstanceFun _ -> true | _ -> false;;
let is_var = function | Var _ -> true | _ -> false;;
let is_value a t = match t with
  | Fun (f,[]) | InstanceFun (f,[],_) ->
    Alphabet.find_symbol_kind f a <> Alphabet.Terms
  | _ -> false
;;
let is_flat = function
  | Var _ -> true
  | Fun (_,ts) | InstanceFun (_,ts,_) -> List.for_all is_var ts
  | Forall _ | Exists _ -> false
;;

let rec is_build fs = function
  | Var _ -> true
  | Fun (f,ts) | InstanceFun (f,ts,_) ->
    List.mem f fs && List.for_all (is_build fs) ts
  | Forall (_,s) | Exists (_,s) -> is_build fs s
;;

let rec is_dummy = function
  | Var _ -> true
  | Fun (_,ts) | InstanceFun (_,ts,_) ->
    ts = [] || (List.is_singleton ts && is_dummy (List.hd ts))
  | Forall _ | Exists _ -> false
;;

let is_ground s =
  let rec ground bound = function
    | Var x -> List.mem x bound
    | Fun (_,ts) | InstanceFun (_,ts,_) ->
      List.for_all (ground bound) ts
    | Forall (x,t) | Exists (x,t) -> ground (x :: bound) t
  in
  ground [] s
;;

let is_linear =
  let rec is_linear bound xs = function
    | Var x ->
      if List.mem x xs then raise Fail
      else if List.mem x bound then xs
      else x :: xs
    | Fun (_,ts) | InstanceFun (_,ts,_) ->
      List.foldl (is_linear bound) xs ts
    | Forall (x, s) | Exists (x, s) ->
      is_linear (x :: bound) xs s
  in
  catch Fail (const true <.> is_linear [] []) false
;;

let is_shallow =
  let rec is_shallow d = function
    | Var _ -> d <= 1
    | Fun (_,ts) | InstanceFun (_,ts,_) ->
      let d = d + 1 in List.for_all (is_shallow d) ts
    | Forall (_, q) | Exists (_, q) ->
      is_shallow (d+1) q
  in
  is_shallow 0
;;

let rec is_string = function
  | Var _ -> true
  | Fun (_, ts) | InstanceFun (_,ts,_) ->
    List.is_singleton ts && is_string (List.hd ts)
  | Forall _ | Exists _ -> false
;;

let rec check_term kind a runfun = function
  | Var _ -> None
  | Forall (_,s) | Exists (_,s) as term ->
    if kind = Alphabet.Logical then runfun term
    else ( match check_term kind a runfun s with
      | None -> None
      | Some p -> Some (Pos.add_first 0 p)
    )
  | Fun (f,ts) | InstanceFun (f,ts,_) as term ->
    try
      let k = Alphabet.find_symbol_kind f a in
      if k = kind then runfun term
      else
        let addi i t = match check_term kind a runfun t with
          | None -> None
          | Some p -> Some (Pos.add_first i p)
        in
        let badposses = List.filter (fun o -> o <> None) (List.mapi addi ts) in
        if badposses = [] then None
        else List.hd badposses
    with Not_found -> failwith ("Symbol " ^ (Function.find_name f) ^
      " in term is not declared as either a logical or term symbol.")
;;

let check_proper_term a = check_term Alphabet.Logical a (const (Some Pos.root));;
let check_logical_term a = check_term Alphabet.Terms a (const (Some Pos.root));;
let check_semi_term a = check_term Alphabet.Logical a (check_logical_term a);;
  (* note: this was used in an older definition of LCTRSs, where right-hand
     sides had to be "semi-terms" as logical symbols were only used for
     calculatioons
  *)

(* Search Functions *)
let rec mem_fun f = function
  | Var _ -> false
  | Fun (g,ts) | InstanceFun (g,ts,_) ->
    f = g || List.exists (mem_fun f) ts
  | Forall (_,s) | Exists (_,s) -> mem_fun f s
;;

let rec mem_var x = function
  | Var y -> x = y
  | Fun (_,ts) | InstanceFun (_,ts,_) ->
    List.exists (mem_var x) ts
  | Forall (_,s) | Exists (_,s) -> mem_var x s
;;

(* Positions *)
let rec pos p = function
  | Var _ as x -> if p x then [Pos.root] else []
  | Fun (_,ts) | InstanceFun (_,ts,_) as t ->
    let addi i = List.map (fun j -> Pos.add_first i j) <.> pos p in
    let ps = List.flat_mapi addi ts in if p t then Pos.root::ps else ps
  | Forall (_,s) | Exists (_,s) ->
    List.map (Pos.add_first 0) (pos p s)
;;

let rec funs_pos_with_fun term =
  let addi i (pos, f) = (Pos.add_first i pos, f) in
  let addirecurse i sub = List.map (addi i) (funs_pos_with_fun sub) in
  match term with
    | Var _ -> []
    | Fun (f, ts) | InstanceFun (f, ts, _) ->
      (Pos.root, f) :: List.flat_mapi addirecurse ts
    | Forall (_,s) | Exists (_,s) -> addirecurse 0 s
;;

let rec pos_acc mu p = function
  | Var _ as x -> if p x then [Pos.root] else []
  | Fun (f,ts) as t ->
    let pos_acc_sub i term =
      if Csmapping.is_reducable_at f i mu
      then pos_acc mu p term else []
    in
    let addi i = List.map (fun p -> Pos.add_first i p) <.> pos_acc_sub i in
    let ps = List.flat_mapi addi ts in
    if p t then Pos.root::ps else ps
  | InstanceFun (f,ts,_) as t ->
    let addi i = List.map (fun p -> Pos.add_first i p) <.> pos_acc mu p in
    let ps = List.flat_mapi addi ts in
    if p t then Pos.root::ps else ps
  | Forall (_,s) | Exists (_,s) as t ->
    let ps = List.map (Pos.add_first 0) (pos_acc mu p s) in
    if p t then Pos.root::ps else ps
;;

let fun_pos f = pos (function Fun (g,_) | InstanceFun (g,_,_) -> g = f | _ -> false);;
let var_pos x = pos (function Var y -> y = x | _ -> false);;
let funs_pos = pos is_fun;;
let quantifier_pos = pos (function | Exists _ | Forall _ -> true | _ -> false);;
let vars_pos = pos is_var;;
let has_pos p t = try let _ = subterm p t in true with _ -> false;;
let subterm_pos s = pos (equal s);;
let req_pos = pos;;
let pos = pos (const true);;
let accessible_fun_pos f mu =
  pos_acc mu (function Fun (g,_) | InstanceFun (g,_,_) -> g = f | _ -> false)
;;
let accessible_funs_pos mu = pos_acc mu is_fun;;
let accessible_pos mu = pos_acc mu (const true);;

(* Iterators *)

let rec recurse fv ft fi fa fe term =
  let children = recurse fv ft fi fa fe in
  match term with
    | Var x -> fv x
    | Fun (f, ts) -> ft f (List.map children ts)
    | InstanceFun (f, ts, d) -> fi f (List.map children ts) d
    | Forall (x, s) -> fa x (children s)
    | Exists (x, s) -> fe x (children s)
;;

let rec map f = function
  | Var _ as x -> x
  | Fun (g,ts) -> Fun (f g, List.map (map f) ts)
  | InstanceFun (g,ts,d) -> InstanceFun (f g, List.map (map f) ts, d)
  | Forall (x, s) -> Forall (x, map f s)
  | Exists (x, s) -> Exists (x, map f s)
;;

let allvars term =
  let fv x = [x] in
  let ft _ args = List.flat_map id args in
  let fi f args _ = ft f args in
  let fq _ xs = xs in
  List.unique (recurse fv ft fi fq fq term)
;;

(* Folds *)
let rec fold_funs op d = function
  | Var _ -> d
  | Fun (f, ts) | InstanceFun (f, ts, _) ->
    op f (List.foldl (fold_funs op) d ts)
  | Forall (_, s) | Exists (_, s) -> fold_funs op d s
;;

let count_fun f = fold_funs (fun g s ->
  if Function.equal f g then s + 1 else s
) 0;;

(* Miscellaneous *)

let args = function
  | Var _ -> []
  | Fun (_,ts) | InstanceFun (_,ts,_) -> ts
  | Forall (_,s) | Exists (_,s) -> [s]
;;

let copy = id;;
let hash = Hashtbl.hash;;

let replace_args t args = match t with
  | Var _ -> t
  | Fun (f, _) -> Fun (f, args)
  | InstanceFun (f, _, sd) -> InstanceFun (f, args, sd)
  | Forall (x, s) ->
    ( match args with
        | [q] -> Forall (x, q)
        | [Var y; q] -> Forall (y, q)
        | _ -> failwith "borky replacement for forall"
    )
  | Exists (x, s) ->
    ( match args with
        | [q] -> Exists (x, q)
        | [Var y; q] -> Exists (y, q)
        | _ -> failwith "borky replacement for exists"
    )
;;

let rec size = function
  | Var _ -> 1
  | Fun (_,ts) | InstanceFun (_,ts,_) ->
    List.foldl (fun s -> (+) s <.> size) 1 ts
  | Forall (_, s) | Exists (_, s) -> 1 + size s
;;

let rec fun_size = function
  | Var _ -> 0
  | Fun (_,ts) | InstanceFun (_,ts,_) ->
    List.foldl (fun s -> (+) s <.> fun_size) 1 ts
  | Forall (_, s) | Exists (_, s) -> size s
;;

let rec var_size = function
  | Var _ -> 1
  | Fun (_,ts) | InstanceFun (_,ts,_) ->
    List.foldl (fun s -> (+) s <.> var_size) 0 ts
  | Forall (_, s) | Exists (_, s) -> size s
;;

let rec quantifier_size = function
  | Var _ -> 0
  | Fun (_,ts) | InstanceFun (_,ts,_) ->
    List.foldl (fun s -> (+) s <.> var_size) 0 ts
  | Forall (_, s) | Exists (_, s) -> 1 + size s
;;

let rec depth = function
  | Var _ -> 0
  | Fun (_,ts) | InstanceFun (_,ts,_) ->
    if ts = [] then 0 else 1 + List.foldl (fun d -> max d <.> depth) 0 ts
  | Forall (_, s) | Exists (_, s) -> 1 + depth s
;;

let proper_subterms ?(p = const true) =
  let rec subterms = function
    | Var _ as x -> if p x then [x] else []
    | Fun (_,ts) | InstanceFun (_,ts,_) as t ->
      let ss = List.flat_map subterms ts in if p t then t::ss else ss
    | Forall (_,s) | Exists (_,s) as t ->
      let ss = subterms s in if p t then t :: ss else ss
  in
  List.unique_hash <.> List.flat_map subterms <.> args
;;

let subterms ?(p = const true) t =
  let acc = proper_subterms ~p:p t in if p t then t::acc else acc
;;

let get_sort alph env = function
  | Var x -> Environment.find_sort x env
  | Fun (f, ts) -> (
    match Alphabet.find_sortdec f alph with
      | Left d -> Sortdeclaration.output_sort d
      | Right d -> Specialdeclaration.pol_to_sort (Specialdeclaration.output_sort d)
    )
  | InstanceFun (f, ts, d) -> Sortdeclaration.output_sort d
  | Forall _ | Exists _ -> Sort.from_string "Bool"
;;

(* Last constructor (postponed because it needs get_sort) *)

let make_function a e f ts =
  match Alphabet.find_sortdec f a with
    | Left sd -> make_fun f ts
    | Right spd ->
      let inputs = (
        List.map (fun ti -> try get_sort a e ti
        with Not_found -> failwith ("Attempting to dynamically " ^
          "make a function with unsorted subterms." ^ (to_string ti))) ts
      ) in
      let osort = Specialdeclaration.output_sort spd in
      let outsort =
        if Specialdeclaration.is_polymorphic osort then (
          let get_inp i s = (Specialdeclaration.input_sort (i + 1) spd, s) in
          let combined_inps = List.mapi get_inp inputs in
          let isgood (polsort, _) = polsort = osort in
          match List.filter isgood combined_inps with
            | [] -> failwith ("special declaration with output " ^
                "sort that does not occur in the input; cannot  "^
                "determine sort of term!")
            | (_, realsort) :: _ -> realsort
        )
        else Specialdeclaration.pol_to_sort osort
      in
      let sd = Sortdeclaration.create inputs outsort in
      make_instance f ts sd
;;

let rec logical_cap alph env t =
  let s = get_sort alph env t in
  let var () = make_var (Environment.create_sorted_var s [] env) in
  if not (List.mem s (Alphabet.find_logical_sorts alph)) then var ()
  else match t with
    | Var _ -> t
    | Fun (f, ts) ->
      if (Alphabet.find_symbol_kind f alph) = Alphabet.Terms then var ()
      else Fun (f, List.map (logical_cap alph env) ts)
    | InstanceFun (f, ts, d) ->
      if (Alphabet.find_symbol_kind f alph) = Alphabet.Terms then var ()
      else InstanceFun (f, List.map (logical_cap alph env) ts, d)
    | Forall (x,t) -> Forall (x, logical_cap alph env t)
    | Exists (x,t) -> Exists (x, logical_cap alph env t)
;;

(* Parsers *)

let (>>=) = Parser.(>>=);;
let (<|>) = Parser.(<|>);;

let ident = Parser.many1 (Parser.noneof " \t\n\r(),") >>= Parser.return;;

let build_fun f args a =
  let e = Environment.dummy () in
  match Alphabet.find_sortdec f a with
    | Left _ -> Parser.return (make_fun f args)
    | Right sd ->
      let inputsorts = List.map (get_sort a e) args in
      let outsort = Specialdeclaration.output_sort sd in
      let actualout = (
        if not (Specialdeclaration.is_polymorphic outsort) then
          Specialdeclaration.pol_to_sort outsort
        else if not (Specialdeclaration.known_arity sd) then
          List.hd inputsorts
        else (
          let inps = Specialdeclaration.input_sorts sd in
          let rec iterate lst1 lst2 =
            let hd = List.hd lst1 in
            if hd = outsort then List.hd lst2
            else iterate (List.tl lst1) (List.tl lst2)
          in
          iterate inps inputsorts
        )
      ) in
      let realsd = Sortdeclaration.create inputsorts actualout in
      Parser.return (make_instance f args realsd)
;;

let check_symbol name alphabet source =
  if not (Alphabet.mem_fun_name name alphabet) then
    failwith ("Cannot parse value from " ^ source ^ ": symbol " ^
      name ^ " does not occur in alphabet.") ;
  let f = Alphabet.find_fun name alphabet in
  (*
  let kind = Alphabet.find_symbol_kind f alphabet in
  if kind = Alphabet.Terms then
    failwith ("Cannot parse value from " ^ source ^ ": symbol " ^
      name ^ " is not a logical symbol.") ;
  if kind = Alphabet.Logical then
    failwith ("Cannot parse value from " ^ source ^ ": symbol " ^
      name ^ " is not a term symbol.") ;
  *)
  f
;;

let parse_symbol alphabet source =
  Parser.lex ident >>= fun i ->
  let name = String.of_char_list i in
  Parser.return (check_symbol name alphabet source)
;;

(*
let rec parse_value a e source phase =
  (
    Parser.lex (Parser.char '(') >>= fun _ ->
    parse_value a e source (if phase = 0 then 1 else phase) >>= fun ret ->
    Parser.lex (Parser.char ')') >>= fun _ ->
    Parser.return ret
  ) <|>
  (
    Parser.lex ident >>= fun i ->
    let name = String.of_char_list i in
      else parse_args a e source f [] phase
    )
  )

and parse_args a e source f args phase =
  ( Parser.eoi >>= fun _ -> build_fun f args a ) <|>
  ( Parser.lex (Parser.char ',') >>= fun _ ->
    if phase = 2 then build_fun f args a
    else failwith ("Cannot parse value from " ^ source ^ ": unexpected ,")
  ) <|>
  ( Parser.lookahead (Parser.char ')') >>= fun _ ->
    build_fun f args a
  ) <|>
;;

and parse_args a e source f args =
  (
    parse_value a source >>= fun arg ->
    parse_args a source f (arg :: args)
  )
;;
*)

let rec parse_functional a source =
  parse_symbol a source >>= fun f ->
  ( Parser.lex (Parser.char '(') >>= fun _ ->
    Parser.sep_by (parse_functional a source)
      (Parser.lex (Parser.char ',')) >>= fun args ->
    Parser.lex (Parser.char ')') >>= fun _ ->
    build_fun f args a
  ) <|>
  ( Parser.get_state >>= fun _ ->  (* avoid evaluating too soon *)
    build_fun f [] a
  )
;;

let rec parse_applicative a source =
  ( Parser.lex (Parser.char '(') >>= fun _ ->
    parse_applicative a source >>= fun ret ->
    Parser.lex (Parser.char ')') >>= fun _ ->
    Parser.return ret
  ) <|>
  ( parse_symbol a source >>= fun f ->
    parse_args f a source []
  )

and parse_args f a source args =
  ( Parser.lookahead (Parser.char ')') >>= fun _ ->
    build_fun f (List.rev args) a
  ) <|>
  ( Parser.eoi >>= fun _ ->
    build_fun f (List.rev args) a
  ) <|>
  ( Parser.lookahead (Parser.char '(') >>= fun _ ->
    parse_applicative a source >>= fun arg ->
    parse_args f a source (arg :: args)
  ) <|>
  ( parse_symbol a source >>= fun g ->
    build_fun g [] a >>= fun arg ->
    parse_args f a source (arg :: args)
  )
;;

let parse_completely f a source =
  f a source >>= fun term ->
  Parser.eoi >>= fun _ ->
  Parser.return term
;;

let rec read_value txt a source =
  let f =
    if String.contains txt ','
    then parse_completely parse_functional
    else parse_completely parse_applicative
  in
  let m = f a source >>= Parser.return in
  match Parser.run m () (Parsec.StringInput.of_string txt) with
    | Left e -> failwith (Parsec.Error.to_string e)
    | Right answer -> answer
;;


