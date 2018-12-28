(** {1 Infinite-precision numbers and bit-vectors} *)

(** Constant bitvector *)
type t

(** Return bitvector resulting from repeating input bit b, (input) n times *)
val repeat_bit : bool -> int -> t

(* Return the first bit of input bitvector b *)
val first_bit : t -> bool

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

(** Return the length of a bitvector as a numeral *)
val length_of_bitvector : t -> int

(** Function that inputs a list of bitvectors and returns an Some n
   if all bitvectors have size n, where n = 8,16,32,64, and None otherwise 
   Special case: it returns None for the input of an empty list of BVs.
   Used to check if non-unary BV operators operate on uniformly sized and
   validly sized inputs *)
val check_bv_uniform : t list -> int option

(** Convert a string to a bitvector

    Binary and hexadecimal notation is accepted as #b[01]+ and
    #x[0-9a-fA-F]+ as in the SMTLIB standard *)
val bitvector_of_string : string -> t

(** Convert a hashconsed string to a bitvector, store all converted
    values in a cache *)
val bitvector_of_hstring : HString.t -> t

(** Convert a hashconsed string to a Boolean value *)
val bool_of_hstring : HString.t -> bool

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


(** Comparison operators *)

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


(** Infix comparison operators *)

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