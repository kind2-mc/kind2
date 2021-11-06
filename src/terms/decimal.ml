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
type t = | InfPos | InfNeg | Undef | N of Num.num


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
| InfPos -> Format.fprintf ppf "1/0"
| InfNeg -> Format.fprintf ppf "-1/0"
| Undef -> Format.fprintf ppf "0/0"
| N d ->
  (* assert (Num.ge_num d zero); *)
  pp_print_positive_decimal_sexpr ppf d


let pp_print_positive_decimal_as_json ppf = function

  | Num.Int i -> Format.fprintf ppf "{\"num\": %d, \"den\": 1}" i

  | Num.Big_int n -> Format.fprintf ppf "{\"num\": %s, \"den\": 1}" (Big_int.string_of_big_int n)

  | Num.Ratio r ->

    (* Normalize rational number *)
    let r' = Ratio.normalize_ratio r in

    (* Get numerator and denominator *)
    let rn = Ratio.numerator_ratio r' in
    let rd = Ratio.denominator_ratio r' in

    (* Print with division as prefix operator *)
    Format.fprintf ppf
      "@[<hv 1>{\"num\": %s, \"den\": %s}@]"
      (Big_int.string_of_big_int rn)
      (Big_int.string_of_big_int rd)

let pp_print_decimal_as_json ppf = function
| InfPos -> Format.fprintf ppf "{\"num\": 1, \"den\": 0}"
| InfNeg -> Format.fprintf ppf "{\"num\": -1, \"den\": 0}"
| Undef -> Format.fprintf ppf "{\"num\": 0, \"den\": 0}"
| N d ->
  (* assert (Num.ge_num d zero); *)
  pp_print_positive_decimal_as_json ppf d


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
| InfPos -> Format.fprintf ppf "1/0"
| InfNeg -> Format.fprintf ppf "-1/0"
| Undef -> Format.fprintf ppf "0/0"
| N d ->
  (* assert (Num.ge_num d zero); *)
  pp_print_positive_decimal ppf d

let pp_print_decimal_as_float fmt = function
| InfPos -> failwith "can't print decimal <infpos> as float"
| InfNeg -> failwith "can't print decimal <infneg> as float"
| Undef -> failwith "can't print decimal <undef> as float"
| N d -> (
  match d with
  | Num.Int i -> Format.fprintf fmt "%df64" i
  | Num.Big_int n -> Format.fprintf fmt "%sf64" (Big_int.string_of_big_int n)
  | Num.Ratio r -> 

    (* Normalize rational number *)
    let r' = Ratio.normalize_ratio r in

    (* Get numerator and denominator *)
    let rn = Ratio.numerator_ratio r' in
    let rd = Ratio.denominator_ratio r' in
    
    (* Print with division as prefix operator *)
    Format.fprintf fmt 
      "%sf64 / %sf64"
      (Big_int.string_of_big_int rn)
      (Big_int.string_of_big_int rd)
)

let pp_print_decimal_as_lus_real fmt = function
| InfPos -> failwith "can't print decimal <infpos> as lus real"
| InfNeg -> failwith "can't print decimal <infneg> as lus real"
| Undef -> failwith "can't print decimal <undef> as lus real"
| N d -> (
  match d with
  | Num.Int i -> Format.fprintf fmt "%d.0" i
  | Num.Big_int n -> Format.fprintf fmt "%s.0" (Big_int.string_of_big_int n)
  | Num.Ratio r -> 

    (* Normalize rational number *)
    let r' = Ratio.normalize_ratio r in

    (* Get numerator and denominator *)
    let rn = Ratio.numerator_ratio r' in
    let rd = Ratio.denominator_ratio r' in
    
    (* Print with division as prefix operator *)
    Format.fprintf fmt 
      "%s.0 / %s.0"
      (Big_int.string_of_big_int rn)
      (Big_int.string_of_big_int rd)
)

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
let of_decimal_string s =
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
        | 'E' | 'e' when pos > 0 -> scan_exp (start_pos + (succ pos)) 0

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
        | 'E' | 'e'  when pos > 0 -> scan_exp (succ pos) 0

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

let of_string s =
  match Hexadecimal.to_decimal s with
  | Some res -> N res
  | None -> of_decimal_string s

(*
(* Division symbol *)
let s_div = HString.mk_hstring "/"

let s_unimus = HString.mk_hstring "-"
*)


(* Convert an arbitrary large integer to a rational number *)
let of_big_int n = N (Num.num_of_big_int n)

(* Convert an ocaml Num to a rational *)
let of_num n = N n

(* Raises [Invalid_argument] exception. *)
let raise_invalid_arg name naN: 'a =
  Format.sprintf "%s %s" name (string_of_decimal naN) |> invalid_arg

(* Convert a rational number to an integer *)
let to_int = function
| N d -> (
  try 
    (* Convert with library function *)
    Num.int_of_num d
  (* Conversion failed because of limited precision *)
  with Failure _ -> raise (Failure "to_int")
)
| naN -> raise_invalid_arg "to_int" naN


(* Convert a rational number to an arbitrary large integer *)
let to_big_int = function
| N d -> Num.big_int_of_num (Num.floor_num d)
| naN -> raise_invalid_arg "to_int" naN


(* Return true if decimal coincides with an integer *)
let is_int = function 
  | N (Num.Int _)
  | N (Num.Big_int _) -> true
  | _ -> false

(* Converts to a float *)
let to_float = function
  | N (Num.Int n) -> float n
  | N (Num.Big_int n) -> Big_int.float_of_big_int n
  | N (Num.Ratio r) -> Ratio.float_of_ratio r
  | naN -> raise_invalid_arg "to_float" naN

(* ********************************************************************** *)
(* Comparison operators                                                   *)
(* ********************************************************************** *)

(* Equality *)
let equal l r = match l, r with
| N l, N r -> Num.eq_num l r
| _ -> l = r

(* Comparison *)
let compare l r = match l,r with
| N l, N r -> Num.compare_num l r
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
| N l, N r -> Num.le_num l r
| Undef, _ | _, Undef -> false
| InfPos, _ | _, InfNeg-> true
| _, InfPos | InfNeg, _ -> false

(* Less than predicate *)
let lt l r = match l, r with
| N l, N r -> Num.lt_num l r
| _ -> leq l r && not (equal l r)

(* Greater than or equal predicate *)
let geq l r = match l, r with
| N l, N r -> Num.ge_num l r
| _ -> not (lt l r)

(* Greater than predicate *)
let gt l r = match l, r with
| N l, N r -> Num.gt_num l r
| _ -> not (leq l r)

(* ********************************************************************** *)
(* Arithmetic operators                                                   *)
(* ********************************************************************** *)

(* Increment a decimal by one *)
let succ = function
| N n -> Num.succ_num n |> of_num
| nan -> nan

(* Decrement a decimal by one *)
let pred = function
| N n -> Num.pred_num n |> of_num
| nan -> nan

(* Absolute value *)
let abs = function
| N n -> Num.abs_num n |> of_num
| Undef -> Undef
| _ -> InfPos

(* Unary negation *)
let neg = function
| N n -> Num.minus_num n |> of_num
| Undef -> Undef
| InfPos -> InfNeg
| InfNeg -> InfPos

(* Sum *)
let add l r =
match l, r with
| N l, N r -> Num.add_num l r |> of_num
| Undef, _ | _, Undef -> Undef
| InfPos, InfNeg | InfNeg, InfPos -> Undef
| InfPos, _ | _, InfPos -> InfPos
| InfNeg, _ | _, InfNeg -> InfNeg

(* Difference *)
let sub l r = match l, r with
| N l, N r -> Num.sub_num l r |> of_num
| Undef, _ | _, Undef -> Undef
| InfPos, InfNeg -> InfPos
| InfNeg, InfPos -> InfNeg
| InfPos, _ | _, InfNeg -> InfPos
| InfNeg, _ | _, InfPos -> InfNeg

(* Product *)
let mult l r = match l, r with
| N l, N r -> Num.mult_num l r |> of_num
| Undef, _ | _, Undef -> Undef
| InfPos, InfNeg | InfNeg, InfPos -> InfNeg
| InfPos, InfPos | InfNeg, InfNeg -> InfPos
| InfPos, n | n, InfPos ->
  if n = zero then Undef else
  if lt n zero then InfNeg else InfPos
| InfNeg, n | n, InfNeg ->
  if n = zero then Undef else
  if lt n zero then InfPos else InfNeg

(* Quotient *)
let div l r = match l, r with
| N l', N r' -> if r = zero then (
  if l = zero then Undef else
  if lt l zero then InfNeg else InfPos
) else Num.div_num l' r' |> of_num
| N _, InfNeg | N _, InfPos -> zero
| InfPos, N _ ->
  if lt r zero then InfNeg else InfPos
| InfNeg, N _ ->
  if lt r zero then InfPos else InfNeg
| _ -> Undef

(* Remainder *)
let rem l r = match l, r with
| N l, N r -> Num.mod_num l r |> of_num
| _ -> Undef

(* Computes the rational 2^p with signed p *)
let epsilon_ratio p =
  if p > 0 then
    Ratio.ratio_of_big_int (Big_int.power_int_positive_int 2 p)
  else
  if p < 0 then
    Ratio.ratio_of_big_int (Big_int.power_int_positive_int 2 (-p)) |>
    Ratio.div_int_ratio 1
  else
    Ratio.ratio_of_int 1

let epsilon p = N (Num.Ratio (epsilon_ratio p))

(* Computes n such that 2^n <= | dec | < 2^n ; returns 0 is dec is null *)
let magnitude = function
  | InfPos | InfNeg | Undef -> failwith "magnitude of infinite"
  | N (Num.Int n) -> Big_int.num_bits_big_int (Big_int.big_int_of_int n)
  | N (Num.Big_int n) -> Big_int.num_bits_big_int n
  | N (Num.Ratio r) ->
      (* let r = a/b *)
      let n = Big_int.num_bits_big_int (Ratio.numerator_ratio r) in
      if n = 0 then 0 else
        let d = Big_int.num_bits_big_int (Ratio.denominator_ratio r) in
        if d = 0 then failwith "magnitude of infinite ratio" ;
        (* have  2^(n-1)  <= |a| < 2^n *)
        (* have  2^(d-1)  <= |b| < 2^d *)
        (* hence 2^(n-d-1) < |r| < 2^(n-d+1) *)
        let p = epsilon_ratio (n-d) in
        if Ratio.lt_ratio r p then n-d else n-d+1

let sign = function
  | InfPos -> 1
  | InfNeg -> -1
  | Undef -> failwith "sign of undef"
  | N (Num.Int n) -> Int.compare n 0
  | N (Num.Big_int n) -> Big_int.sign_big_int n
  | N (Num.Ratio r) -> Ratio.sign_ratio r

(* ********************************************************************** *)
(* Approximation Printing (need others operations)                        *)
(* ********************************************************************** *)

let pp_print_decimal_approximation fmt dec =
  match dec with
  | InfPos | InfNeg | Undef | N (Num.Int _ | Num.Big_int _) ->
      pp_print_decimal fmt dec
  | N (Num.Ratio _ as r) ->
      try
        let s = Num.sign_num r in
        if s = 0 then Format.pp_print_string fmt "0.0" else
          let value = abs dec in
          let approx = Printf.sprintf "%g" (to_float value) in
          let appro = of_string approx in
          let delta = sub value appro in
          let alpha = div delta appro in
          let p = magnitude alpha in
          let sr = if s >= 0 then "" else "-" in
          if p = 0 then
            Format.fprintf fmt "%s%s" sr approx
          else
            let se = if (sign delta >= 0) = (s >= 0) then '+' else '-' in
            Format.fprintf fmt "%s%s@{<black_b>%cf%d@}" sr approx se (-p)
      with _ -> (* Fallback *) pp_print_decimal fmt dec
                                 
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
