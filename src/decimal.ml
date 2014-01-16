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


(* Convert a numeral to an integer *)
let to_int d = 

  try 

    (* Convert with library function *)
    Num.int_of_num d

  (* Conversion failed because of limited precision *)
  with Failure _ -> raise (Failure "to_int")



(* The numeral zero *)
let zero = Num.num_of_int 0


(* The numeral one *)
let one = Num.num_of_int 1


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






(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
