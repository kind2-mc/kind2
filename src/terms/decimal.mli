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

(** Arbitrary precision real numbers

    @author Christoph Sticksel
*)

(** Type of arbitrary precision rational numbers *)
type t 

(** {1 Pretty-printing and String Representation} *)

(** Pretty-print a rational *)
val pp_print_decimal : Format.formatter -> t -> unit

(** Pretty-print a rational as an f64 (used by compilation to Rust) *)
val pp_print_decimal_as_float : Format.formatter -> t -> unit

(** Pretty-print a rational as an f64 (used by contract generation) *)
val pp_print_decimal_as_lus_real: Format.formatter -> t -> unit

(** Pretty-print a rational in scientific format with the error magnitude *)
val pp_print_decimal_approximation: Format.formatter -> t -> unit

(** Pretty-print a rational as an S-expression *)
val pp_print_decimal_sexpr : Format.formatter -> t -> unit

(** Return a string representation of a rational *)
val string_of_decimal : t -> string

(** Return an S-expression string representation of a rational *)
val string_of_decimal_sexpr : t -> string

(** {1 Conversions} *)

(** Convert an integer to a rational *)
val of_int : int -> t

(** Convert an arbitrary large integer to a rational *)
val of_big_int : Big_int.big_int -> t

(** Convert an ocaml Num to a rational *)
val of_num : Num.num -> t

(** Convert a string in floating-point notation [1.2E3] to rational number *)
val of_string : string -> t

(** Convert a rational number to a rational

    Truncates the rational number to an integer and raises the
    exception [Failure "int_of_big_int"] if the numeral cannot be
    represented as an integer.  *)
val to_int : t -> int

(** Convert a rational number to an arbitrary large integer *)
val to_big_int : t -> Big_int.big_int

(** Return true if decimal coincides with an integer *)
val is_int : t -> bool

(** Returns 0 on zero, 1 for positives and -1 for negatives.
    Works also on infinites but fails on undefined. *)
val sign : t -> int

(** Returns the rational [2^p] with signed p. *)
val epsilon : int -> t

(** Returns a signed integer [n] such that [2^(n-1) < |dec| < 2^n ]
    or [0] if [dec] is null. *)
val magnitude : t -> int

(** {1 Constants} *)

(** The rational number zero *)
val zero : t

(** The rational number one *)
val one : t

(** {1 Arithmetic operations} *)

(** Successor *)
val succ : t -> t 

(** Predecessor *)
val pred : t -> t 

(** Absolute value *)
val abs : t -> t

(** Unary negation *)
val neg : t -> t 

(** Sum *)
val add : t -> t -> t

(** Difference *)
val sub : t -> t -> t

(** Product *)
val mult : t -> t -> t

(** Quotient *)
val div : t -> t -> t

(** Remainder *)
val rem : t -> t -> t

(** {2 Infix operators} *)

(** Unary negation *)
val ( ~- ) : t -> t

(** Sum *)
val ( + ) : t -> t -> t

(** Difference *)
val ( - ) : t -> t -> t

(** Product *)
val ( * ) : t -> t -> t

(** Quotient *)
val ( / ) : t -> t -> t

(** Remainder *)
val ( mod ) : t -> t -> t


(** {1 Comparison operators} *)

(** Equality *)
val equal : t -> t -> bool

(** Comparison *)
val compare : t -> t -> int

(** Less than or equal predicate *)
val leq : t -> t -> bool

(** Less than predicate *)
val lt : t -> t -> bool

(** Greater than or equal predicate *)
val geq : t -> t -> bool

(** Greater than predicate *)
val gt : t -> t -> bool

(** {2 Infix operators} *)

(** Equality *)
val ( = ) : t -> t -> bool

(** Disequality *)
val ( <> ) : t -> t -> bool

(** Less than or equal predicate *)
val ( <= ) : t -> t -> bool

(** Less than predicate *)
val ( < ) : t -> t -> bool

(** Greater than or equal predicate *)
val ( >= ) : t -> t -> bool

(** Greater than predicate *)
val ( > ) : t -> t -> bool


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
