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

(** Bit-vectors

    @author Arjun Viswanathan
*)

exception ComparingUnequalBVs
exception NonStandardBVSize

(** Constant bitvector *)
type t

(** Return the length of a bitvector as a numeral *)
val length_of_bitvector : t -> int

(** Bit-vector representing decimal 0 *)
val zero : int -> t

(** Bit-vector representing decimal 1 *)
val one : int -> t

(** Bit-vector representing hexadecimal F - all bit's are 1 *)
val f : int -> t

(** Return bits m down to n from the input bitvector *)
val bvextract : int -> int -> t -> t

(** Return input bitvector sign-extended to m bits *)
val bvsignext : int -> t -> t

(** Extend input bitvector by concatenating m zero bits *)
val bvzeroext : int -> t -> t

(** Return input bitvectors concatenated together *)
val bvconcat : t -> t -> t


(** {1 Numeral to Unsigned Bitvector}
@author Arjun Viswanathan *)

(** [num_to_ubv s n] returns size [s] unsigned bitvector converted from numeral [n] *)
val num_to_ubv : Numeral.t -> Numeral.t -> t

(** Return size 8 unsigned bitvector converted from a numeral *)
val num_to_ubv8 : Numeral.t -> t

(** Return size 16 unsigned bitvector converted from a numeral *)
val num_to_ubv16 : Numeral.t -> t

(** Return size 32 unsigned bitvector converted from a numeral *)
val num_to_ubv32 : Numeral.t -> t

(** Return size 64 unsigned bitvector converted from a numeral *)
val num_to_ubv64 : Numeral.t -> t


(** {1 Usigned Bitvector to Numeral}
@author Arjun Viswanathan*)

(** Return numeral converted from an unsigned bitvector *)
val ubv_to_num : t -> Numeral.t

(** Return numeral converted from a size 8 unsigned bitvector *)
val ubv8_to_num : t -> Numeral.t

(** Return numeral converted from a size 16 unsigned bitvector *)
val ubv16_to_num : t -> Numeral.t

(** Return numeral converted from a size 32 unsigned bitvector *)
val ubv32_to_num : t -> Numeral.t

(** Return numeral converted from a size 64 unsigned bitvector *)
val ubv64_to_num : t -> Numeral.t


(** {1 Numeral to Signed Bitvector}
@author Arjun Viswanathan*)

(** Return size 8 signed bitvector converted from a numeral *)
val num_to_bv8 : Numeral.t -> t

(** Return size 16 signed bitvector converted from a numeral *)
val num_to_bv16 : Numeral.t -> t

(** Return size 32 signed bitvector converted from a numeral *)
val num_to_bv32 : Numeral.t -> t

(** Return size 64 signed bitvector converted from a numeral *)
val num_to_bv64 : Numeral.t -> t


(** {1 Signed Bitvector to Numeral}
@author Arjun Viswanathan*)

(** Return numeral converted from a signed bitvector *)
val bv_to_num : t -> Numeral.t

(** Return numeral converted from a size 8 signed bitvector *)
val bv8_to_num : t -> Numeral.t

(** Return numeral converted from a size 16 signed bitvector *)
val bv16_to_num : t -> Numeral.t

(** Return numeral converted from a size 32 signed bitvector *)
val bv32_to_num : t -> Numeral.t

(** Return numeral converted from a size 64 signed bitvector *)
val bv64_to_num : t -> Numeral.t


(* @author Arjun Viswanathan
(** Return size 8 unsigned bitvector converted from an int *)
val int_to_ubv8 : int -> t

(** Return size 16 unsigned bitvector converted from an int *)
val int_to_ubv16 : int -> t

(** Return size 32 unsigned bitvector converted from an int *)
val int_to_ubv32 : int -> t

(** Return size 64 unsigned bitvector converted from an int *)
val int_to_ubv64 : int -> t


(** Return integer converted from a size 8 unsigned bitvector *)
val ubv8_to_int : t -> int

(** Return integer converted from a size 16 unsigned bitvector *)
val ubv16_to_int : t -> int

(** Return integer converted from a size 32 unsigned bitvector *)
val ubv32_to_int : t -> int

(** Return integer converted from a size 64 unsigned bitvector *)
val ubv64_to_int : t -> int


(** Return size 8 bitvector converted from an int *)
val int_to_bv8 : int -> t

(** Return size 16 bitvector converted from an int *)
val int_to_bv16 : int -> t

(** Return size 32 bitvector converted from an int *)
val int_to_bv32 : int -> t

(** Return size 64 bitvector converted from an int *)
val int_to_bv64 : int -> t


(** Return integer converted from a size 8 bitvector *)
val bv8_to_int : t -> int

(** Return integer converted from a size 16 bitvector *)
val bv16_to_int : t -> int

(** Return integer converted from a size 32 bitvector *)
val bv32_to_int : t -> int

(** Return integer converted from a size 64 bitvector *)
val bv64_to_int : t -> int
*)


(** {1 Arithmetic Operations}
@author Arjun Viswanathan*)

(** Function that adds two signed bitvectors *)
val sbv_add : t -> t -> t

(** Function that adds two unsigned bitvectors *)
val ubv_add : t -> t -> t

(** Function that multiplies two signed bitvectors *)
val sbv_mult : t -> t -> t

(** Function that multiplies two unsigned bitvectors *)
val ubv_mult : t -> t -> t

(** Function that divides two signed bitvectors *)
val sbv_div : t -> t -> t

(** Function that divides two unsigned bitvectors *)
val ubv_div : t -> t -> t

(** Function that finds remainder of two signed bitvectors *)
val sbv_rem : t -> t -> t

(** Function that finds remainder of two unsigned bitvectors *)
val ubv_rem : t -> t -> t

(** Function for signed bitvector subtraction *)
val sbv_sub : t -> t -> t

(** Funciton for signed bitvector negation *)
val sbv_neg : t -> t


(** {1 Logical Operations}
@author Arjun Viswanathan*)

(** Function that computes bitwise conjunction *)
val bv_and : t -> t -> t

(** Funciton that computes bitwise disjunction *)
val bv_or : t -> t -> t

(** Function that computes bitwise negation *)
val bv_not : t -> t


(** {1 Comparison Operators}
@author Arjun Viswanathan*)

(** Equality *)
val equal : t -> t -> bool

(** Unsigned lesser than *)
val ult : t -> t -> bool

(** Unsigned greater than *)
val ugt : t -> t -> bool

(** Unsigned lesser than or equal to *)
val ulte : t -> t -> bool

(** Unsigned greater than or equal to *)
val ugte : t -> t -> bool

(** Signed lesser than *)
val lt : t -> t -> bool

(** Signed greater than *)
val gt : t -> t -> bool

(** Signed lesser than or equal to *)
val lte : t -> t -> bool

(** Signed greater than or equal to *)
val gte : t -> t -> bool


(** {1 Shift Operators}
@author Arjun Viswanathan*)

(** Shift bitvector left by n times, 
    where n is specified as an unsigned BV *)
val bv_lsh : t -> t -> t

(** Shift bitvector right by n times, 
    where n is specified as an unsigned BV *)
val bv_rsh : t -> t -> t

(** Arithmetic right shift of bitvector by n times, 
    where n is specified as an unsigned BV *)
val bv_arsh : t -> t -> t


(** {1 Pretty Printing} *)

(** Pretty-print a constant bitvector in SMTLIB binary format *)
val pp_smtlib_print_bitvector_b : Format.formatter -> t -> unit

(** Pretty-print a bitvector in SMTLIB extended decimal format *)
val pp_smtlib_print_bitvector_d : Format.formatter -> t -> unit

(** Pretty-print a constant bitvector in Yices' binary format *)
val pp_yices_print_bitvector_b : Format.formatter -> t -> unit

(** Pretty-print a constant bitvector in Yices' binary format given the decimal value and size *)
val pp_yices_print_bitvector_d : Format.formatter -> Numeral.t -> Numeral.t -> unit

(** Pretty-print a constant unsigned bitvector as a Lustre machine integer *)
val pp_print_unsigned_machine_integer : Format.formatter -> t -> unit

(** Pretty-print a constant signed bitvector as a Lustre machine integer *)
val pp_print_signed_machine_integer : Format.formatter -> t -> unit

(** Pretty-print a constant bitvector in hexadeciaml format *)
val pp_print_bitvector_x : Format.formatter -> t -> unit


(** {1 Conversions} *)

(** Convert a string to a bitvector
    Binary and hexadecimal notation is accepted as #b[01]+ and
    #x[0-9a-fA-F]+ as in the SMTLIB standard *)
val bitvector_of_string : string -> t

(** Convert a hashconsed string to a bitvector, store all converted
    values in a cache *)
val bitvector_of_hstring : HString.t -> t

(** Convert a hashconsed string to a Boolean value *)
val bool_of_hstring : HString.t -> bool


(** {1 Infix Comparison Operators} *)

(** Equality *)
val ( = ) : t -> t -> bool

(** Signed lesser than *)
val ( < ) : t -> t -> bool

(** Signed greater than *)
val ( > ) : t -> t -> bool

(** Signed lesser than or equal to *)
val ( <= ) : t -> t -> bool

(** Signed greater than or equal to *)
val ( >= ) : t -> t -> bool


(** {1 Unused Functions} *)

(** Return the first bit of input bitvector b *)
val first_bit : t -> bool
