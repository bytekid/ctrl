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
open Ctrs;;
open Util;;

(*** MODULES *****************************************************************)

module NamePriorityMap = Map.Make(String)(Int);;

(*** TYPES *******************************************************************)

type style = Plain;;
type aligns = L | R | C;;

(*** MUTABLES ****************************************************************)

let currentstyle = ref Plain;;
let storage = ref "";;
let infix_left = ref NamePriorityMap.empty;;
let infix_right = ref NamePriorityMap.empty;;

(*** FUNCTIONS ***************************************************************)

(* Accessing the current TRS *)

let alphabet () = Trs.get_alphabet (Trs.get_current ());;
let environment () = Trs.get_main_environment (Trs.get_current ());;

(* Styles *)

let set_style s = currentstyle := s;;

(* Storage *)

let store txt = storage := !storage ^ txt;;
let flush () = Printf.printf "%s" !storage ; storage := "";;

(* Handling Codes *)

let print str = store str;;
  (* TODO: figure out how to use unicode libraries for the unicode /
  utf8 / latex styles, and make a number of fixed conversions for the
  plain style (this can probably be done in the input parser) *)

let get_length style = String.length;;
  (* TODO: this will print the length of the replacement in the given
  style, which must be either plain or unicode *)

let add_infix_symbol n p b =
  if b then infix_left := NamePriorityMap.add n p !infix_left
  else infix_right := NamePriorityMap.add n p !infix_right
;;

(* help for printing calls *)

let print_aligned txt style align size =
  let n = get_length style txt in
  if n >= size then txt else (
    match align with
      | L -> txt ^ (String.make (size-n) ' ')
      | R -> (String.make (size-n) ' ') ^ txt
      | C ->
        let a = size-n in
        (String.make (a/2) ' ') ^ txt ^ (String.make (a-a/2) ' ')
  )
;;

let plain_table lst align =
  let rec nullist = function
    | [] -> []
    | head :: tail -> 0 :: nullist tail
  in
  let rec update strings = function
    | [] -> []
    | x :: xs -> ( max (get_length Plain (List.hd strings)) x ) ::
                 ( update (List.tl strings) xs )
  in
  let rec column_widths sofar = function
    | [] -> sofar
    | head :: tail -> column_widths (update head sofar) tail
  in
  let rec print_row widths align = function
    | [] -> "\n"
    | entry :: tail ->
      (print_aligned entry Plain (List.hd align) (List.hd widths)) ^ " " ^
      (print_row (List.tl widths) (List.tl align) tail)
  in
  let rec print_table widths = function
    | [] -> ""
    | row :: tail -> (print_row widths align row) ^ (print_table widths tail)
  in
  let widths = column_widths (nullist align) lst in
  print_table widths lst
;;

let table lst align =
  match !currentstyle with
    | Plain -> plain_table lst align
;;

(* Turn Structures Into Strings *)

let to_string_term term =
  let print_var x = (Variable.find_name x, None) in
  let print_fun_functional fname args =
    match args with
      | [] -> (fname, None)
      | _ -> (fname ^ "(" ^ (List.to_string id ", " args) ^ ")", None)
  in
  let add_brackets left prio term e = function
    | None -> term
    | Some (p, l) ->
      if prio > p then "(" ^ term ^ ")"
      else if p > prio then term
      else if left = e then term
      else "(" ^ term ^ ")"
  in
  let really_print_infix fname left prio (a, ainfo) (b, binfo) =
    let a = add_brackets left prio a true ainfo in
    let b = add_brackets left prio b false binfo in
    (a ^ " " ^ fname ^ " " ^ b, Some (prio, left))
  in
  let print_fun_infix fname left prio args =
    match args with
      | a :: b :: [] -> really_print_infix fname left prio a b
      | _ as args -> print_fun_functional fname (List.map fst args)
  in
  let print_fun f args =
    let fname = Function.find_name f in
    if NamePriorityMap.mem fname !infix_left then
      print_fun_infix fname true (NamePriorityMap.find fname !infix_left) args
    else if NamePriorityMap.mem fname !infix_right then
      print_fun_infix fname false (NamePriorityMap.find fname !infix_right) args
    else print_fun_functional fname (List.map fst args)
  in
  let print_sorted_fun f args _ = print_fun f args in
  let print_quantifier kind x (arg, _) =
    let (xname, _) = print_var x in
    ("?" ^ kind ^ " " ^ xname ^ " [" ^ arg ^ "]", None)
  in
  fst (Term.recurse print_var print_fun print_sorted_fun
            (print_quantifier "A") (print_quantifier "E") term)
;;

let to_string_constraints lst =
  let p s = to_string_term s in
  if lst = [] then ""
  else "[" ^ (List.implode p ", " lst) ^ "]"
;;

let to_string_rule rule =
  (to_string_term (Rule.lhs rule)) ^ " -> " ^
  (to_string_term (Rule.rhs rule)) ^ " " ^
  (to_string_constraints (Rule.constraints rule))
;;

(* Defined Printing Functions *)

let debug_printf = Printf.eprintf;;

let print_text = print;;
let print_newline () = print "\n";;

let print_alphabet kind =
  let a = alphabet () in
  let funs = Alphabet.funs a in
  let including f =
    if kind = Alphabet.Both then true
    else if kind = Alphabet.Logical &&
           Alphabet.find_symbol_kind f a = Alphabet.Terms then false
    else if kind = Alphabet.Terms &&
            Alphabet.find_symbol_kind f a = Alphabet.Logical then false
    else true
  in
  let create_entry f =
    [Function.find_name f; ":";
     if Alphabet.mem_sortdec f a
     then (match Alphabet.find_sortdec f a with
      | Left d -> Sortdeclaration.to_string d
      | Right d -> Specialdeclaration.to_string d)
     else "";
     if Alphabet.mem_ari f a
     then "(arity " ^ (Int.to_string (Alphabet.find_ari f a)) ^ ")"
     else ""
    ]
  in
  let rec create_table_list = function
    | [] -> []
    | f :: tail ->
      if including f then create_entry f :: create_table_list tail
      else create_table_list tail
  in
  print (table (create_table_list funs) [R;C;L;L])
;;

let print_list f aligns lst =
  let rec create_table_list = function
    | [] -> []
    | entry :: tail -> (f entry) :: create_table_list tail
  in
  print (table (create_table_list lst) aligns)
;;

let print_rules rules arrz constraints =
  let create_entry (rule, _) =
    let cs = Rule.constraints rule in
    [to_string_term (Rule.lhs rule);
     arrz;
     to_string_term (Rule.rhs rule);
     if (List.is_empty cs) then "" else constraints;
     to_string_constraints cs
    ]
  in
  print_list create_entry [R;C;L;C;L] rules
;;

let print_current_rules () =
  print_rules (Trs.get_rules (Trs.get_current ())) " -> " "  <--"
;;

let print_term term = print (to_string_term term);;

let print_constrained_term (term, constr) =
  print_term term ;
  print_text " [[";
  print_term constr ;
  print_text "]] "
;;

let print_rule rule env arrz constraints =
  let cs = Rule.constraints rule in
  let txt = (to_string_term (Rule.lhs rule)) ^ arrz ^
            (to_string_term (Rule.rhs rule)) ^
            (if (List.is_empty cs) then "" else constraints ) ^
            to_string_constraints cs
  in
  print txt
;;

let print_reduction red printfun =
  let rec print_recursive = function
    | [] -> ()
    | head :: tail ->
      print "  -> " ;
      printfun head ;
      print_newline () ;
      print_recursive tail
  in
  match red with
    | [] -> failwith "Asked to print an empty reduction!\n"
    | head :: tail ->
      printfun head ;
      print_newline () ;
      print_recursive tail
;;

let print_term_reduction red = print_reduction red print_term;;
let print_constrained_reduction red = print_reduction red print_constrained_term;;

