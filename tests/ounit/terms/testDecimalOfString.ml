(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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
(** [Decimal.of_string] reads the sign of a decimal number as the sign
    of the whole number, not only of its integer part: [-0.375] is
    negative although its integer part is zero (issue #1894). *)

open OUnit2

let q n d = Decimal.div (Decimal.of_int n) (Decimal.of_int d)

let check s expected =
  let actual = Decimal.of_string s in
  assert_bool
    (Format.sprintf "of_string %S: expected %s, got %s" s
       (Decimal.string_of_decimal expected)
       (Decimal.string_of_decimal actual))
    (Decimal.equal actual expected)

let test_negative_below_one _ =
  check "-0.375" (q (-3) 8);
  check "-0.5" (q (-1) 2);
  check "-0.05" (q (-1) 20);
  check "-.5" (q (-1) 2);
  check "-0.5e1" (Decimal.of_int (-5));
  check "-0.5E-1" (q (-1) 20)

let test_negative_from_one _ =
  check "-1.375" (q (-11) 8);
  check "-1" (Decimal.of_int (-1));
  check "-2.5e-1" (q (-1) 4)

let test_non_negative _ =
  check "0.375" (q 3 8);
  check "+0.375" (q 3 8);
  check ".5" (q 1 2);
  check "1.375" (q 11 8);
  check "-0.0" (Decimal.of_int 0);
  check "0" (Decimal.of_int 0)

(* An exponent may follow the point directly when the integer part has
   digits, as in 1.e5, and the fractional part may be empty, as in 1.
   (issue #1896) *)
let test_point_then_exponent _ =
  check "1." (Decimal.of_int 1);
  check "-12." (Decimal.of_int (-12));
  check "1.e5" (Decimal.of_int 100000);
  check "1.E5" (Decimal.of_int 100000);
  check "1.e+5" (Decimal.of_int 100000);
  check "1.e-5" (q 1 100000);
  check "-2.e1" (Decimal.of_int (-20));
  check "+2.E-1" (q 1 5)

(* A string with no digits in its integer or fractional part, or with an
   exponent marker followed by no digits, is rejected, not read as zero,
   whether or not it has a sign *)
let test_no_digits _ =
  List.iter
    (fun s ->
       match Decimal.of_string s with
       | exception Invalid_argument _ -> ()
       | d ->
         assert_failure
           (Format.sprintf "of_string %S: expected an error, got %s" s
              (Decimal.string_of_decimal d)))
    [""; "-"; "+"; "."; "-."; "+."; "-e1"; "+E2"; "e1"; "--1"; "-+1";
     ".e5"; "-.e5"; "+.E1";
     "1e"; "1E+"; "1e-"; "1.e"; "1.e+"; "-3.E-"; "1.5e"; "1.5e+"]

let tests =
  "Decimal.of_string" >::: [
    "negative below one" >:: test_negative_below_one;
    "negative from one" >:: test_negative_from_one;
    "non-negative" >:: test_non_negative;
    "point then exponent" >:: test_point_then_exponent;
    "no digits" >:: test_no_digits;
  ]

let _ = run_test_tt_main tests
