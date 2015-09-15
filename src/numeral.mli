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

(** Arbitrary precision integers

    @author Christoph Sticksel
*)

(** Type of arbitrary precision numerals *)
type t

(** {1 Pretty-printing and String Representation} *)

(** Pretty-print a numeral, e.g. -1 *)
val pp_print_numeral : Format.formatter -> t -> unit

(** Pretty-print a numeral in s-expression, e.g. (- 1) *)
val pp_print_numeral_sexpr : Format.formatter -> t -> unit

(** Return a string representation of a numeral *)
val string_of_numeral : t -> string

(** {1 Conversions} *)

(** Convert an integer to a numeral *)
val of_int : int -> t

(** Convert an arbitrary large integer numeral to numeral *)
val of_big_int : Big_int.big_int -> t

(** Convert a string to numeral *)
val of_string : string -> t

(** Convert a numeral to an integer 

    Raises the exception [Failure "int_of_big_int"] if the numeral
    cannot be represented as an integer. *)
val to_int : t -> int

(** Convert a numeral to an arbitrary large integer *)
val to_big_int : t -> Big_int.big_int

(** {1 Constructors} *)

(** The numeral zero *)
val zero : t

(** The numeral one *)
val one : t

(** {1 Arithmetic operations} *)

(** Successor *)
val succ : t -> t 

(** Predecessor *)
val pred : t -> t 

(** Increment a numeral in a reference by one *)
val incr : t ref -> unit

(** Decrement a numeral in a reference by one *)
val decr : t ref -> unit

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

(** Remainder

    Identical to [mod], but the latter is an infix operator. *)
val rem : t -> t -> t

(** Return smaller of two numerals *)
val min : t -> t -> t 

(** Return greater of two numerals *)
val max : t -> t -> t 


(** {2 Infix arithmetic operators} *)

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

(** {2 Infix comparison operators} *)

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
