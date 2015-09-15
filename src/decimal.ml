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

open Lib

(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* Arbitrary precision rational numbers are numerals *)
type t = | NaN | N of Num.num


(* The rational number zero *)
let zero = N (Num.num_of_int 0)


(* The rational number one *)
let one = N (Num.num_of_int 1)


(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


(* Pretty-print a numeral as an S-expression *)
let pp_print_positive_decimal_sexpr ppf = function

  | Num.Int i -> Format.fprintf ppf "%d.0" i

  | Num.Big_int n -> Format.fprintf ppf "%s.0" (Big_int.string_of_big_int n)

  | Num.Ratio r -> 

    (* Normalize rational number *)
    let r' = Ratio.normalize_ratio r in

    (* Get numerator and denominator *)
    let rn = Ratio.numerator_ratio r' in
    let rd = Ratio.denominator_ratio r' in
    
    (* Print with division as prefix operator *)
    Format.fprintf ppf 
      "@[<hv 1>(/@ %s@ %s)@]" 
      (Big_int.string_of_big_int rn)
      (Big_int.string_of_big_int rd)


let pp_print_decimal_sexpr ppf = function
| NaN -> Format.fprintf ppf "NaN"
| N d ->
  (* assert (Num.ge_num d zero); *)
  pp_print_positive_decimal_sexpr ppf d


(* Pretty-print a numeral as an S-expression *)
let pp_print_positive_decimal ppf = function

  | Num.Int i -> Format.fprintf ppf "%d" i

  | Num.Big_int n -> Format.fprintf ppf "%s" (Big_int.string_of_big_int n)

  | Num.Ratio r -> 

    (* Normalize rational number *)
    let r' = Ratio.normalize_ratio r in

    (* Get numerator and denominator *)
    let rn = Ratio.numerator_ratio r' in
    let rd = Ratio.denominator_ratio r' in
    
    (* Print with division as prefix operator *)
    Format.fprintf ppf 
      "%s/%s" 
      (Big_int.string_of_big_int rn)
      (Big_int.string_of_big_int rd)


let pp_print_decimal ppf = function
| NaN -> Format.fprintf ppf "NaN"
| N d ->
  (* assert (Num.ge_num d zero); *)
  pp_print_positive_decimal ppf d


(* Return a string representation of a decimal *)
let string_of_decimal_sexpr = string_of_t pp_print_decimal_sexpr

(* Return a string representation of a decimal *)
let string_of_decimal = string_of_t pp_print_decimal


(* ********************************************************************** *)
(* Conversions                                                            *)
(* ********************************************************************** *)


(* Convert an integer to a rational number *)
let of_int n = N (Num.num_of_int n)

(* Convert a string to a rational number *)
let of_string s = if s = "NaN" then NaN else (

  (* Buffer for integer part, initialize to length of whole string *)
  let int_buf = Buffer.create (String.length s) in

  (* Buffer for fractional part, initialize to length of whole string *)
  let frac_buf = Buffer.create (String.length s) in
 
  (* Buffer for exponent part, initialize to length of whole string *)
  let exp_buf = Buffer.create (String.length s) in

  (* Scan exponent part and add to buffer *)
  let rec scan_exp start_pos pos = 

    (* Terminate at end of string *)
    if (start_pos + pos) >= String.length s then () else

      (* Get character at current position *)
      match String.get s (start_pos + pos) with 

        (* Allow digits, append to buffer *)
        | '0'..'9' as c -> 
          Buffer.add_char exp_buf c; 
          scan_exp start_pos (succ pos) 

        (* Allow sign as the first character, append to buffer *)
        | '-' | '+' as c when pos = 0 -> 
          Buffer.add_char exp_buf c; 
          scan_exp start_pos (succ pos) 

        (* Fail on other characters *)
        | c -> 
          raise 
            (Invalid_argument 
               (Format.sprintf
                  "of_string: invalid character %c at position %d" 
                  c
                  (start_pos + pos)))

  in

  (* Scan fractional part and add to buffer *)
  let rec scan_frac start_pos pos = 

    (* Terminate at end of string *)
    if (start_pos + pos) >= String.length s then () else

      (* Get character at current position *)
      match String.get s (start_pos + pos) with

        (* Continue parsing exponent part *)
        | 'E' when pos > 0 -> scan_exp (start_pos + (succ pos)) 0

        (* Allow digits, append to buffer *)
        | '0'..'9' as c -> 
          Buffer.add_char frac_buf c; 
          scan_frac start_pos (succ pos) 

        (* Fail on other characters *)
        | c -> 
          raise 
            (Invalid_argument 
               (Format.sprintf
                  "of_string: invalid character %c at position %d" 
                  c
                  (start_pos + pos)))

  in

  (* Scan integer part and add to buffer *)
  let rec scan_int pos = 

    (* Terminate at end of string *)
    if pos >= String.length s then () else

      (* Get character at current position *)
      match String.get s pos with

        (* Continue parsing fractional part *)
        | '.' -> scan_frac (succ pos) 0

        (* Continue parsing exponent part *)
        | 'E'  when pos > 0 -> scan_exp (succ pos) 0

        (* Allow digits, append to buffer *)
        | '0'..'9' as c -> 
          Buffer.add_char int_buf c; 
          scan_int (succ pos) 

        (* Allow sign as the first character, append to buffer *)
        | '-' | '+' as c when pos = 0 -> 
          Buffer.add_char int_buf c; 
          scan_int (succ pos) 

        (* Fail on other characters *)
        | c -> 
          raise 
            (Invalid_argument 
               (Format.sprintf
                  "of_string: invalid character %c at position %d" 
                  c
                  pos))

  in

  (* Scan string into buffers starting at the first character *)
  scan_int 0;

  (* Convert integer buffer to numeral, default to zero if empty *)
  let int_num = 
    if Buffer.length int_buf = 0 then Num.num_of_int 0 else 
      Num.num_of_string (Buffer.contents int_buf) 
  in

  (* Convert fractional buffer to numeral, default to zero if empty *)
  let frac_num = 
    if Buffer.length frac_buf = 0 then Num.num_of_int 0 else 
      Num.num_of_string (Buffer.contents frac_buf) 
  in

  (* Convert exponent buffer to numeral, default to one if empty *)
  let exp_num = 
    if Buffer.length exp_buf = 0 then Num.num_of_int 0 else 
      Num.num_of_string (Buffer.contents exp_buf) 
  in

  (* Exponent *)
  let exp = 
    Num.power_num (Num.num_of_int 10) exp_num
  in

  (* Fractional part *)
  let frac = 
    Num.div_num 
      
      (* Numerator of fractional part *)
      frac_num
      
      (* Denominator of fractional part *)
      (Num.power_num 
         (Num.num_of_int 10)
         (Num.num_of_int (Buffer.length frac_buf)))
  in

  (* Combine integer part, fractional part and mantissa *)
  let res = 

    Num.mult_num
    
      (* Mantissa 
         
         Fractional part has sign of integer part *)
      ((if Num.sign_num int_num < 0 then Num.sub_num else Num.add_num)
      
         (* Integer part *)
         int_num
         
         frac)

      exp

  in

  N res
)



(* Division symbol *)
let s_div = HString.mk_hstring "/"

let s_unimus = HString.mk_hstring "-"


(* Convert an arbitrary large integer to a rational number *)
let of_big_int n = N (Num.num_of_big_int n)

(* Convert an ocaml Num to a rational *)
let of_num n = N n


(* Convert a rational number to an integer *)
let to_int = function
| NaN -> invalid_arg "to_int NaN"
| N d ->

  try 

    (* Convert with library function *)
    Num.int_of_num d

  (* Conversion failed because of limited precision *)
  with Failure _ -> raise (Failure "to_int")


(* Convert a rational number to an arbitrary large integer *)
let to_big_int = function
| NaN -> invalid_arg "to_int NaN"
| N d -> Num.big_int_of_num (Num.floor_num d)


(* Return true if decimal coincides with an integer *)
let is_int = function 
  | N (Num.Int _)
  | N (Num.Big_int _) -> true
  | _ -> false

(* ********************************************************************** *)
(* Arithmetic operators                                                   *)
(* ********************************************************************** *)



(* Applies [f] to the input if it's not [NaN] and wraps the result in [N].
   Returns [NaN] otherwise. *)
let handle_nan_unary f = function
| NaN -> NaN | N n -> f n |> of_num

(* Applies [f] to the inputs if neither is [NaN] and wraps the result in
   [N]. Returns [NaN] otherwise. *)
let handle_nan_binary f l r = match l,r with
| NaN, _ | _, NaN -> NaN
| N l, N r -> f l r |> of_num

(* Increment a decimal by one *)
let succ = handle_nan_unary Num.succ_num

(* Decrement a decimal by one *)
let pred = handle_nan_unary Num.pred_num

(* Absolute value *)
let abs = handle_nan_unary Num.abs_num

(* Unary negation *)
let neg = handle_nan_unary Num.minus_num

(* Sum *)
let add = handle_nan_binary Num.add_num

(* Difference *)
let sub = handle_nan_binary Num.sub_num

(* Product *)
let mult = handle_nan_binary Num.mult_num

(* Quotient *)
let div n d =
  if d = zero then NaN else
    handle_nan_binary Num.div_num n d

(* Remainder *)
let rem = handle_nan_binary Num.mod_num


(* ********************************************************************** *)
(* Comparison operators                                                   *)
(* ********************************************************************** *)

(* Applies [f] to the inputs if neither is [NaN]. Returns [default]
   otherwise. *)
let handle_nan_rel f default l r = match l,r with
| N l, N r -> f l r
| _ -> default

(* Equality *)
let equal = handle_nan_rel Num.eq_num false

(* Comparison *)
let compare l r = match l,r with
| N l, N r -> Num.compare_num l r
| NaN, NaN -> 0
| NaN, _ -> -100
| _, NaN -> 100

(* Less than or equal predicate *)
let leq = handle_nan_rel Num.le_num false

(* Less than predicate *)
let lt = handle_nan_rel Num.lt_num false

(* Greater than or equal predicate *)
let geq = handle_nan_rel Num.ge_num false

(* Greater than predicate *)
let gt = handle_nan_rel Num.gt_num false


(* ********************************************************************** *)
(* Infix operators                                                        *)
(* ********************************************************************** *)


(* Unary negation *)
let ( ~- ) = neg

(* Sum *)
let ( + ) = add

(* Difference *)
let ( - ) = sub

(* Product *)
let ( * ) = mult

(* Quotient *)
let ( / ) = div

(* Remainder *)
let ( mod ) = rem

(* Equality *)
let ( = ) = equal

(* Disequality *)
let ( <> ) a b = not (equal a b)

(* Less than or equal predicate *)
let ( <= ) = leq

(* Less than predicate *)
let ( < ) = lt

(* Greater than or equal predicate *)
let ( >= ) = geq

(* Greater than predicate *)
let ( > ) = gt


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
