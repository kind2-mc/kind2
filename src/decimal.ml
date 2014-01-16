(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

type t = Num.num

(* The numeral zero *)
let zero = Num.num_of_int 0


(* The numeral one *)
let one = Num.num_of_int 1



(* Pretty-print a numeral *)
let pp_print_decimal ppf = function

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
      "@[<hv 1>(/@ %s@ %s)@]" 
      (Big_int.string_of_big_int rn)
      (Big_int.string_of_big_int rd)


(* Return a string representation of a decimal *)
let string_of_decimal = string_of_t pp_print_decimal 


(* Convert an integer to a numeral *)
let of_int = Num.num_of_int

(* Integer exponentiation *)
let pow x n = 
  let rec pow' accum x = 
    function 
      | 0 -> accum 
      | n when n < 0 -> invalid_arg "pow" 
      | n -> pow' (accum * x) x (pred n)
  in
  pow' 1 x n

(* Convert a floating-point number to a decimal *)
let of_float f = 

  match classify_float f with 

    (* Zero *)
    | FP_zero -> zero

    (* Do not convert infinity, NaN and subnormal numbers (too close
       to 1.0 for full precision) *)
    | FP_infinite
    | FP_nan
    | FP_subnormal -> raise (Invalid_argument "of_float")

    (* A normal floating-point number *)
    | FP_normal -> 

      (* Number of digits of a double float *)
      let precision = 16 in

      (* Get mantissa and exponent *)
      let m, e = frexp f in

      (* Numerator is m * (10 ^ precision) *)
      let n = int_of_float (m *. (10. ** float_of_int precision)) in

      (* Denominator is (10 ^ precision) *)
      let d = pow 10 precision in

      (* Construct decimal by dividing numerator by denominator and
         multiplying by the exponent *)
      Num.mult_num 
        (Num.div_num (Num.num_of_int n) (Num.num_of_int d)) 
        (Num.power_num (Num.num_of_int 2) (Num.num_of_int e))
      


let s_div = HString.mk_hstring "/"

let of_string s = 

  match SExprParser.sexp SExprLexer.main (Lexing.from_string s) with 

    | HStringSExpr.List
        [HStringSExpr.Atom o; HStringSExpr.Atom n; HStringSExpr.Atom d] 
      when o = s_div -> 

      let n' = 
        try 

          Num.num_of_string (HString.string_of_hstring n) 

        with Failure _ -> raise (Invalid_argument "of_string")

      in

      let d' = 

        try 

          Num.num_of_string (HString.string_of_hstring d) 

        with Failure _ -> raise (Invalid_argument "of_string")

      in

      Num.div_num n' d'

    | HStringSExpr.Atom n -> 

      (try 
         
         Num.num_of_string (HString.string_of_hstring n)
           
       with Failure _ -> 

         try 

           of_float (float_of_string (HString.string_of_hstring n))

         with Invalid_argument _ | Failure _ -> 
           
           raise (Invalid_argument "of_string"))


    | _ -> raise (Invalid_argument "of_string")


(* Convert a numeral to an integer *)
let to_int d = 

  try 

    (* Convert with library function *)
    Num.int_of_num d

  (* Conversion failed because of limited precision *)
  with Failure _ -> raise (Failure "to_int")


let to_big_int d = Num.big_int_of_num (Num.floor_num d)


let of_big_int n = Num.num_of_big_int n


(* Increment a decimal by one *)
let succ d = Num.succ_num d


(* Decrement a decimal by one *)
let pred d = Num.pred_num d


(* Absolute value *)
let abs = Num.abs_num


(* Unary negation *)
let neg = Num.minus_num

(* Sum *)
let add = Num.add_num

(* Difference *)
let sub = Num.sub_num

(* Product *)
let mult = Num.mult_num

(* Quotient *)
let div = Num.div_num

(* Remainder *)
let rem = Num.mod_num

(* Equality *)
let equal = Num.eq_num

(* Comparison *)
let compare = Num.compare_num

(* Less than or equal predicate *)
let leq = Num.le_num

(* Less than predicate *)
let lt = Num.lt_num

(* Greater than or equal predicate *)
let geq = Num.ge_num

(* Greater than predicate *)
let gt = Num.gt_num

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



let ( <= ) = leq

let ( < ) = lt

let ( >= ) = geq

let ( > ) = gt

let ( = ) = equal

let ( <> ) a b = not (equal a b)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
