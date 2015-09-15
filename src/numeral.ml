(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)


(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* Arbitrary precision numerals are big integers *)
type t = | NaN | Int of Big_int.big_int

(* The numeral zero *)
let zero = Int Big_int.zero_big_int

(* The numeral one *)
let one = Int Big_int.unit_big_int


(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


(* Return a string representation of a numeral *)
let string_of_numeral = function
| NaN -> "NaN"
| Int n -> Big_int.string_of_big_int n

(* Pretty-print a numeral *)
let pp_print_numeral ppf n =
  Format.fprintf ppf "%s" (string_of_numeral n)

let pp_print_numeral_sexpr = pp_print_numeral


(* ********************************************************************** *)
(* Conversions                                                            *)
(* ********************************************************************** *)


(* Convert an big integer to a numeral *)
let of_big_int n = Int n


(* Convert an integer to a numeral *)
let of_int i = Big_int.big_int_of_int i |> of_big_int


(* Convert a string to a numeral *)
let of_string s = 

  try 

    Big_int.big_int_of_string s |> of_big_int

  with Failure _ -> raise (Invalid_argument "of_string")


(* Convert a numeral to an integer *)
let to_int = function
| NaN -> invalid_arg "to_int NaN"
| Int n ->
  try 

    (* Convert with library function *)
    Big_int.int_of_big_int n

  (* Conversion failed because of limited precision *)
  with Failure "int_of_big_int" -> raise (Failure "to_int")


(* Convert an big integer to a numeral *)
let to_big_int = function
| NaN -> invalid_arg "to_big_int NaN"
| Int n -> n


(* ********************************************************************** *)
(* Arithmetic operators                                                   *)
(* ********************************************************************** *)

(* Applies [f] to the input if it's not [NaN] and wraps the result in [Int].
   Returns [NaN] otherwise. *)
let handle_nan_unary f = function
| NaN -> NaN | Int n -> f n |> of_big_int

(* Applies [f] to the inputs if neither is [NaN] and wraps the result in
   [Int]. Returns [NaN] otherwise. *)
let handle_nan_binary f l r = match l,r with
| NaN, _ | _, NaN -> NaN
| Int l, Int r -> f l r |> of_big_int

(* Increment a numeral by one *)
let succ = handle_nan_unary Big_int.succ_big_int

(* Decrement a numeral by one *)
let pred = handle_nan_unary Big_int.pred_big_int

(* Increment a numeral in a reference by one *)
let incr n =
  match !n with
  | NaN -> ()
  | Int v -> n := Big_int.succ_big_int v |> of_big_int

(* Decrement a numeral in a reference by one *)
let decr n =
  match !n with
  | NaN -> ()
  | Int v -> n := Big_int.pred_big_int v |> of_big_int

(* Absolute value *)
let abs = handle_nan_unary Big_int.abs_big_int

(* Unary negation *)
let neg = handle_nan_unary Big_int.minus_big_int

(* Sum *)
let add = handle_nan_binary Big_int.add_big_int

(* Difference *)
let sub = handle_nan_binary Big_int.sub_big_int

(* Product *)
let mult = handle_nan_binary Big_int.mult_big_int

(* Quotient *)
let div n d =
  if d = zero then NaN else
    handle_nan_binary Big_int.div_big_int n d

(* Remainder *)
let rem = handle_nan_binary Big_int.mod_big_int


(* ********************************************************************** *)
(* Comparison operators                                                   *)
(* ********************************************************************** *)

(* Applies [f] to the inputs if neither is [NaN]. Returns [default]
   otherwise. *)
let handle_nan_rel f default l r = match l,r with
| Int l, Int r -> f l r
| _ -> default

(* Equality *)
let equal = handle_nan_rel Big_int.eq_big_int false

(* Comparison *)
let compare l r = match l,r with
| Int l, Int r -> Big_int.compare_big_int l r
| NaN, NaN -> 0
| NaN, _ -> -100
| _, NaN -> 100

(* Less than or equal predicate *)
let leq = handle_nan_rel Big_int.le_big_int false

(* Less than predicate *)
let lt = handle_nan_rel Big_int.lt_big_int false

(* Greater than or equal predicate *)
let geq = handle_nan_rel Big_int.ge_big_int false

(* Greater than predicate *)
let gt = handle_nan_rel Big_int.gt_big_int false


(* ********************************************************************** *)
(* Infix operators                                                        *)
(* ********************************************************************** *)


let ( ~- ) = neg

let ( + ) = add

let ( - ) = sub

let ( * ) = mult

let ( / ) = div

let ( mod ) = rem

let ( <= ) = leq

let ( < ) = lt

let ( >= ) = geq

let ( > ) = gt

let ( = ) = equal

let ( <> ) a b = not (equal a b)


(* ********************************************************************** *)
(* Utilities                                                              *)
(* ********************************************************************** *)


(* Return smaller of two numerals *)
let min = handle_nan_binary (fun x y ->
  if Big_int.le_big_int x y then x else y
)

(* Return greater of two numerals *)
let max = handle_nan_binary (fun x y ->
  if Big_int.ge_big_int x y then x else y
)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
