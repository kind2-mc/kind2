(** {1 Infinite-precision numbers and bit-vectors} *)

(** Constant bitvector *)
type t

(** Return the length of a bitvector as a numeral *)
val length_of_bitvector : t -> int

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

(** Pretty-print a constant bitvector in Yices' binary format *)
val pp_yices_print_bitvector_b : Format.formatter -> t -> unit

(** Pretty-print a constant bitvector in hexadeciaml format *)
val pp_print_bitvector_x : Format.formatter -> t -> unit
