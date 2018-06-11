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

let has_prefix s =
  String.length s > 2 && s.[0] = '0' && s.[1] = 'x'

let hex_digit = function
  | '0' .. '9' as c -> int_of_char c - int_of_char '0'
  | 'a' .. 'f' as c -> 10 + int_of_char c - int_of_char 'a'
  | 'A' .. 'F' as c -> 10 + int_of_char c - int_of_char 'A'
  | _ -> failwith "hex_digit"

let add_hexdigit v h =
  Big_int.add_int_big_int (hex_digit h) (Big_int.mult_int_big_int 16 v)

let to_numeral s =
  if has_prefix s then
    let rec scan value s k =
      if k < String.length s then
        scan (add_hexdigit value s.[k]) s (succ k)
      else Some value
    in scan Big_int.zero_big_int s 2
  else None

let to_decimal s =
  if has_prefix s then

    let rec vexp n s k =
      if k < String.length s then
        vexp ( n * 10 + hex_digit s.[k] ) s (succ k)
      else n
    in

    let expo s k =
      if k < String.length s then
        if s.[k] = '+' then + (vexp 0 s (succ k)) else
        if s.[k] = '-' then - (vexp 0 s (succ k)) else
          vexp 0 s k
      else 0
    in

    let exponent fk k p =
      (* each fractional digit in base 16 = 2^4 *)
      if fk > 0 then p - 4 * (k - fk - 1) else p in
    
    let rec scan value fk s k =
      if k < String.length s then
        match s.[k] with
        | '.' -> scan value k s (succ k)
        | 'p' -> value , exponent fk k (expo s (succ k))
        | _ -> scan (add_hexdigit value s.[k]) fk s (succ k)
      else value , exponent fk k 0
    in

    let value , fp = scan Big_int.zero_big_int 0 s 2 in
    let num =

      if fp > 0 then
        let ep = Big_int.power_int_positive_int 2 fp in
        Num.num_of_big_int (Big_int.mult_big_int value ep)
      else
      
      if fp < 0 then
        let ep = Big_int.power_int_positive_int 2 (-fp) in
        Num.num_of_ratio (Ratio.create_ratio value ep)
      else
          
        Num.num_of_big_int value

    in Some num
  else None
