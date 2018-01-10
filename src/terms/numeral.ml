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
type t = Big_int.big_int


(* The numeral zero *)
let zero = Big_int.zero_big_int 

(* The numeral one *)
let one = Big_int.unit_big_int 


(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


(* Pretty-print a numeral *)
let pp_print_numeral_sexpr ppf n =
  Format.fprintf ppf "%s" (Big_int.string_of_big_int n)


let pp_print_numeral ppf n =
  Format.fprintf ppf "%s" (Big_int.string_of_big_int n)


(* Return a string representation of a numeral *)
let string_of_numeral = Big_int.string_of_big_int 


(* ********************************************************************** *)
(* Conversions                                                            *)
(* ********************************************************************** *)


(* Convert an integer to a numeral *)
let of_int i = Big_int.big_int_of_int i


(* Convert an big integer to a numeral *)
let of_big_int i = i

(* Convert a string to a numeral *)
let of_string s = 

  try

    match Hexadecimal.to_numeral s with
    | Some res -> res
    | None -> Big_int.big_int_of_string s 

  with Failure _ -> raise (Invalid_argument "of_string")


(* Convert a numeral to an integer *)
let to_int n = 

  try 

    (* Convert with library function *)
    Big_int.int_of_big_int n 

  (* Conversion failed because of limited precision *)
  with Failure _ -> raise (Failure "to_int")


(* Convert an big integer to a numeral *)
let to_big_int n = n


(* ********************************************************************** *)
(* Arithmetic operators                                                   *)
(* ********************************************************************** *)


(* Increment a numeral by one *)
let succ n = Big_int.succ_big_int n

(* Decrement a numeral by one *)
let pred n = Big_int.pred_big_int n

(* Increment a numeral in a reference by one *)
let incr n = n := Big_int.succ_big_int !n

(* Decrement a numeral in a reference by one *)
let decr n = n := Big_int.pred_big_int !n

(* Absolute value *)
let abs = Big_int.abs_big_int

(* Unary negation *)
let neg = Big_int.minus_big_int

(* Sum *)
let add = Big_int.add_big_int

(* Difference *)
let sub = Big_int.sub_big_int

(* Product *)
let mult = Big_int.mult_big_int

(* Quotient *)
let div = Big_int.div_big_int

(* Remainder *)
let rem = Big_int.mod_big_int


(* ********************************************************************** *)
(* Comparison operators                                                   *)
(* ********************************************************************** *)


(* Equality *)
let equal = Big_int.eq_big_int

(* Comparison *)
let compare = Big_int.compare_big_int

(* Less than or equal predicate *)
let leq = Big_int.le_big_int

(* Less than predicate *)
let lt = Big_int.lt_big_int

(* Greater than or equal predicate *)
let geq = Big_int.ge_big_int

(* Greater than predicate *)
let gt = Big_int.gt_big_int


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
let min x y = if x <= y then x else y

(* Return greater of two numerals *)
let max x y = if x >= y then x else y



(* |===| Version handling division by zero.

(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* Arbitrary precision numerals are big integers *)
type t = | InfPos | InfNeg | Undef | I of Big_int.big_int

(* The numeral zero *)
let zero = I Big_int.zero_big_int

(* The numeral one *)
let one = I Big_int.unit_big_int


(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


(* Return a string representation of a numeral *)
let string_of_numeral = function
| InfPos -> "InfPos"
| InfNeg -> "InfNeg"
| Undef -> "Undef"
| I n -> Big_int.string_of_big_int n

(* Pretty-print a numeral *)
let pp_print_numeral ppf n =
  Format.fprintf ppf "%s" (string_of_numeral n)

let pp_print_numeral_sexpr = pp_print_numeral


(* ********************************************************************** *)
(* Conversions                                                            *)
(* ********************************************************************** *)


(* Convert an big integer to a numeral *)
let of_big_int n = I n


(* Convert an integer to a numeral *)
let of_int i = Big_int.big_int_of_int i |> of_big_int


(* Convert a string to a numeral *)
let of_string s = 

  try 

    Big_int.big_int_of_string s |> of_big_int

  with Failure _ -> raise (Invalid_argument "of_string")

let raise_invalid_arg name naN =
  Format.sprintf "%s %s" name (string_of_numeral naN) |> invalid_arg

(* Convert a numeral to an integer *)
let to_int = function
| I n -> (
  (* Convert with library function *)
  try Big_int.int_of_big_int n
  (* Conversion failed because of limited precision *)
  with Failure "int_of_big_int" -> raise (Failure "to_int")
)
| naN -> raise_invalid_arg "to_int" naN


(* Convert an big integer to a numeral *)
let to_big_int = function
| I n -> n
| naN -> raise_invalid_arg "to_big_int" naN


(* ********************************************************************** *)
(* Comparison operators                                                   *)
(* ********************************************************************** *)

(* Equality *)
let equal l r = match l, r with
| I l, I r -> Big_int.eq_big_int l r
| _ -> l = r

(* Comparison *)
let compare l r = match l,r with
| I l, I r -> Big_int.compare_big_int l r
| Undef, Undef -> 0
| Undef, _ -> 100
| _, Undef -> -100
| InfPos, InfPos -> 0
| InfPos, _ -> 100
| _, InfPos -> -100
| InfNeg, InfNeg -> 0
| InfNeg, _ -> -100
| _, InfNeg -> 100

(* Less than or equal predicate *)
let leq l r = match l, r with
| I l, I r -> Big_int.le_big_int l r
| Undef, _ | _, Undef -> false
| InfPos, _ | _, InfNeg-> true
| _, InfPos | InfNeg, _ -> false

(* Less than predicate *)
let lt l r = match l, r with
| I l, I r -> Big_int.lt_big_int l r
| _ -> leq l r && not (equal l r)

(* Greater than or equal predicate *)
let geq l r = match l, r with
| I l, I r -> Big_int.ge_big_int l r
| _ -> not (lt l r)

(* Greater than predicate *)
let gt l r = match l, r with
| I l, I r -> Big_int.gt_big_int l r
| _ -> not (leq l r)


(* ********************************************************************** *)
(* Arithmetic operators                                                   *)
(* ********************************************************************** *)

(* Increment a numeral by one *)
let succ = function
| I i -> Big_int.succ_big_int i |> of_big_int
| naN -> naN

(* Decrement a numeral by one *)
let pred = function
| I i -> Big_int.pred_big_int i |> of_big_int
| naN -> naN

(* Increment a numeral in a reference by one *)
let incr n = match !n with
| I v -> n := Big_int.succ_big_int v |> of_big_int
| _ -> ()

(* Decrement a numeral in a reference by one *)
let decr n = match !n with
| I v -> n := Big_int.pred_big_int v |> of_big_int
| _ -> ()

(* Absolute value *)
let abs = function
| I i -> Big_int.abs_big_int i |> of_big_int
| Undef -> Undef
| _ -> InfPos

(* Unary negation *)
let neg = function
| I i -> Big_int.minus_big_int i |> of_big_int
| Undef -> Undef
| InfPos -> InfNeg
| InfNeg -> InfPos

(* Sum *)
let add l r = match l, r with
| I l, I r -> Big_int.add_big_int l r |> of_big_int
| Undef, _
| _, Undef
| InfPos, InfNeg
| InfNeg, InfPos -> Undef
| InfPos, _ | _, InfPos -> InfPos
| InfNeg, _ | _, InfNeg -> InfNeg

(* Difference *)
let sub l r = match l, r with
| I l, I r -> Big_int.sub_big_int l r |> of_big_int
| Undef, _
| _, Undef
| InfPos, InfNeg
| InfNeg, InfPos -> Undef
| InfPos, _ | _, InfNeg -> InfPos
| InfNeg, _ | _, InfPos -> InfNeg

(* Product *)
let mult l r = match l, r with
| I l, I r -> Big_int.mult_big_int l r |> of_big_int
| Undef, _ | _, Undef -> Undef
| InfPos, n | n, InfPos ->
  if n = zero then Undef else
  if lt n zero then InfNeg else InfPos
| InfNeg, n | n, InfNeg ->
  if n = zero then Undef else
  if lt n zero then InfPos else InfNeg

(* Quotient *)
let div l r = match l, r with
| I l', I r' ->
  if r = zero then (
    if l = zero then Undef else
    if lt l zero then InfNeg else InfPos
  ) else Big_int.div_big_int l' r' |> of_big_int
| I _, InfNeg | I _, InfPos -> zero
| InfPos, I _ ->
  if lt r zero then InfNeg else InfPos
| InfNeg, I _ ->
  if lt r zero then InfPos else InfNeg
| _ -> Undef

(* Remainder *)
let rem l r = match l, r with
| I l, I r ->Big_int.mod_big_int l r |> of_big_int
| _ -> Undef


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
let min = if le x y then x else y

(* Return greater of two numerals *)
let max = if ge x y then x else y


*)




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
