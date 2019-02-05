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



(** Constant bitvector *)
type t

(** Return bitvector resulting from repeating input bit b, (input) n times *)
val repeat_bit : bool -> int -> t

(** Return the first bit of input bitvector b *)
val first_bit : t -> bool

(** Return bits m down to n from the input bitvector *)
val bvextract : int -> int -> t -> t

(** Return input bitvector sign-extended to m bits *)
val bvsignext : int -> t -> t

(** Return input bitvectors concatenated together *)
val bvconcat : t -> t -> t


(** {Numeral to Unsigned Bitvector} *)
(** Return size 8 unsigned bitvector converted from a numeral *)
val num_to_ubv8 : Numeral.t -> t

(** Return size 16 unsigned bitvector converted from a numeral *)
val num_to_ubv16 : Numeral.t -> t

(** Return size 32 unsigned bitvector converted from a numeral *)
val num_to_ubv32 : Numeral.t -> t

(** Return size 64 unsigned bitvector converted from a numeral *)
val num_to_ubv64 : Numeral.t -> t


(** {Usigned Bitvector to Numeral} *)
(** Return numeral converted from a size 8 unsigned bitvector *)
val ubv8_to_num : t -> Numeral.t

(** Return numeral converted from a size 16 unsigned bitvector *)
val ubv16_to_num : t -> Numeral.t

(** Return numeral converted from a size 32 unsigned bitvector *)
val ubv32_to_num : t -> Numeral.t

(** Return numeral converted from a size 64 unsigned bitvector *)
val ubv64_to_num : t -> Numeral.t


(** {Numeral to Signed Bitvector} *)
(** Return size 8 signed bitvector converted from a numeral *)
val num_to_bv8 : Numeral.t -> t

(** Return size 16 signed bitvector converted from a numeral *)
val num_to_bv16 : Numeral.t -> t

(** Return size 32 signed bitvector converted from a numeral *)
val num_to_bv32 : Numeral.t -> t

(** Return size 64 signed bitvector converted from a numeral *)
val num_to_bv64 : Numeral.t -> t


(** {Signed Bitvector to Numeral} *)
(** Return numeral converted from a size 8 signed bitvector *)
val bv8_to_num : t -> Numeral.t

(** Return numeral converted from a size 16 signed bitvector *)
val bv16_to_num : t -> Numeral.t

(** Return numeral converted from a size 32 signed bitvector *)
val bv32_to_num : t -> Numeral.t

(** Return numeral converted from a size 64 signed bitvector *)
val bv64_to_num : t -> Numeral.t


(*
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


(** {Arithmetic Operations} *)
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

(** Function for signed bitvector subtraction *)
val sbv_sub : t -> t -> t


(** {Unused} *)
(** Function that inputs a list of bitvectors and returns an Some n
   if all bitvectors have size n, where n = 8,16,32,64, and None otherwise 
   Special case: it returns None for the input of an empty list of BVs.
   Used to check if non-unary BV operators operate on uniformly sized and
   validly sized inputs *)
val check_bv_uniform : t list -> int option


(** {Pretty Printing} *)
(** Pretty-print a constant bitvector in SMTLIB binary format *)
val pp_smtlib_print_bitvector_b : Format.formatter -> t -> unit

(* Pretty-print a bitvector in SMTLIB extended decimal format *)
val pp_smtlib_print_bitvector_d : Format.formatter -> Numeral.t -> Numeral.t -> unit

(** Pretty-print a constant bitvector in Yices' binary format *)
val pp_yices_print_bitvector_b : Format.formatter -> t -> unit

(** Pretty-print a constant bitvector in Yices' binary format given the decimal value and size *)
val pp_yices_print_bitvector_d : Format.formatter -> Numeral.t -> Numeral.t -> unit

(** Pretty-print a constant bitvector in hexadeciaml format *)
val pp_print_bitvector_x : Format.formatter -> t -> unit


(** {Conversions} *)
(** Convert a string to a bitvector
    Binary and hexadecimal notation is accepted as #b[01]+ and
    #x[0-9a-fA-F]+ as in the SMTLIB standard *)
val bitvector_of_string : string -> t

(** Convert a hashconsed string to a bitvector, store all converted
    values in a cache *)
val bitvector_of_hstring : HString.t -> t

(** Convert a hashconsed string to a Boolean value *)
val bool_of_hstring : HString.t -> bool

(** Return the length of a bitvector as a numeral *)
val length_of_bitvector : t -> int


(** {Comparison Operators} *)
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


(** {Infix Comparison Operators} *)
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