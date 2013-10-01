(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** General-purpose library functions 

    @author Christoph Sticksel
*)

(** {1 Infinite-precision numbers and bit-vectors} *)

(** Infinite-precision integer numeral *)
type numeral

(** Infinite-precision real decimal *)
type decimal

(** Constant bitvector *)
type bitvector

(** Add to infinite-precision numerals *)
val ( +% ) : numeral -> numeral -> numeral

(** Add to infinite-precision decimals *)
val ( +/ ) : decimal -> decimal -> decimal

(** Increment the given numeral by one *)
val incr_numeral : numeral -> numeral

(** Convert an OCaml integer to an infinite-precision integer numeral *)
val numeral_of_int : int -> numeral

(** Convert an infinite-precision real decimal to an OCaml float *)
val decimal_of_float : float -> decimal

(** Convert an infinite-precision integer numeral to an OCaml integer *)
val int_of_numeral : numeral -> int 

(* Constant zero *)
val num_zero : numeral

(* Constant one *)
val num_one : numeral

(** Convert an OCaml float to an infinite-precision real decimal *)
val float_of_decimal : decimal -> float 

(** Return the length of a bitvector as a numeral *)
val length_of_bitvector : bitvector -> numeral

(** Convert a string to an infinite-precision integer numeral 

    Integer numerals are not negative and strings must be as defined
    in the SMTLIB standard: a sequence of digits without leading zero.
    As a regular expression: [0|(\[1-9\]\[0-9\]\* )].
    
*)
val numeral_of_string : string -> numeral

(** Convert a hashconsed string to a numeral, store all converted
    values in a cache *)
val numeral_of_hstring : HString.t -> numeral

(** Convert a string to an infinite-precision real decimal 

    Real decimal are not negative and strings must be as defined in
    the SMTLIB standard: an integer numeral followed by a period
    followed by a non-empty sequence of digits. As a regular expression:
    [0|(\[1-9\]\[0-9\]\* )[.](0-9)+]. *)
val decimal_of_string : string -> decimal

(** Convert a hashconsed string to a decimal, store all converted
    values in a cache *)
val decimal_of_hstring : HString.t -> decimal

(** Convert a string to a bitvector

    Binary and hexadecimal notation is accepted as #b[01]+ and
    #x[0-9a-fA-F]+ as in the SMTLIB standard *)
val bitvector_of_string : string -> bitvector

(** Convert a hashconsed string to a bitvector, store all converted
    values in a cache *)
val bitvector_of_hstring : HString.t -> bitvector

(** Convert a hashconsed string to a Boolean value *)
val bool_of_hstring : HString.t -> bool

(** Convert an infinite-precision integer numeral to a string *)
val string_of_numeral : numeral -> string 

(** Convert an infinite-precision real decimal to a string *)
val string_of_decimal : decimal -> string

(** Pretty-print an infinite-precision integer numeral *)
val pp_print_numeral : Format.formatter -> numeral -> unit

(** Pretty-print an infinite-precision real decimal *)
val pp_print_decimal : Format.formatter -> decimal -> unit

(** Pretty-print a constant bitvector in binary format *)
val pp_print_bitvector_b : Format.formatter -> bitvector -> unit

(** Pretty-print a constant bitvector in hexadeciaml format *)
val pp_print_bitvector_x : Format.formatter -> bitvector -> unit

(** {1 Integer functions} *)

(** [safe_hash_interleave h m i] compute [m * h + i] and makes sure
    that the result does not overflow to a negtive number *)
val safe_hash_interleave : int -> int -> int -> int

(** {1 List functions} *)

(** [chain_list \[e1; e2; ...\]] is [\[\[e1; e2\]; \[e2; e3\]; ... \]] *)
val chain_list : 'a list -> 'a list list 

(** Return a list containing all values in the first list that are not
    in the second list *)
val list_subtract : 'a list -> 'a list -> 'a list 

(** From a sorted list return a list with physical duplicates removed *)
val list_uniq : 'a list -> 'a list

(** Merge two sorted lists without physical duplicates to a sorted list without
   physical duplicates *)
val list_merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

(** From two sorted lists without physical duplicates return a sorted
    list without physical duplicates containing elements in both
    lists *)
val list_inter_uniq :  ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

(** From two sorted lists without physical duplicates return a sorted
    list without physical duplicates containing elements in the first
    but not in the second list *)
val list_diff_uniq :  ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

(** For two sorted lists without physical duplicates return true if
    the first list contains a physically equal element for each element
    in the second list *)
val list_subset_uniq :  ('a -> 'a -> int) -> 'a list -> 'a list -> bool

(** Lexicographic comparison of lists *)
val compare_lists : ('a -> 'a -> int) -> 'a list -> 'a list -> int 

(** {1 Pretty-printing helpers} *)

(** Pretty-print a list with given separator 

    [pp_print_list p s f l] pretty-prints the elements in the list [l]
    by calling the pretty-printer [p] on each, separating the elements
    by printing the string [s] and marking the position after each [s]
    as a good break. Use this after opening a pretty-printing box to
    make use of the break hints.

    In order to get line breaks between the elements, do not use a
    line feed character [\n] as separator, this might mess up
    indentation. Instead wrap the list into a vertical box with the
    format string [@\[<v>%a@\]] and the empty string as separator.
*)
val pp_print_list : (Format.formatter -> 'a -> unit) -> ('b, Format.formatter, unit) format -> Format.formatter -> 'a list -> unit

(** Pretty-print an option type *)
val pp_print_option : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

(** Pretty-print into a string *)
val string_of_t : (Format.formatter -> 'a -> unit) -> 'a -> string 


(** Return the strings as a parenthesized and space separated list *)
val paren_string_of_string_list : string list -> string


(** {1 System functions} *)

(** Kind modules *)
type kind_module = [ `PDR | `BMC | `IND | `INVGEN | `INVMAN | `Interpreter ]

(** Wallclock timeout *)
exception TimeoutWall

(** CPU timeout *)
exception TimeoutVirtual

(** System signal caught *)
exception Signal of int

(** String representation of signal *)
val string_of_signal : int -> string 

(** Pretty-print the termination status of a process *)
val pp_print_process_status : Format.formatter -> Unix.process_status -> unit

(** Raise exception on signal *)
val exception_on_signal : int -> 'a

(** Pretty-print the name of a kind module *)
val pp_print_kind_module : Format.formatter -> kind_module -> unit

(** String representation of a process type *)
val string_of_kind_module : kind_module -> string 

(** Kind module of a string *)
val kind_module_of_string : string -> kind_module

(** Sleep for seconds, resolution is in ms *)
val minisleep : float -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
