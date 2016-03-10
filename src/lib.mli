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

(** General-purpose library functions 

    @author Christoph Sticksel
*)

(** {1 Helper functions} *)

(** Identity function. *)
val identity : 'a -> 'a

(** Prints the first argument and returns the second. *)
val print_pass : string -> 'a -> 'a

(** Returns true when given unit. *)
val true_of_unit : unit -> bool

(** Returns false when given unit. *)
val false_of_unit : unit -> bool

(** Returns None when given unit. *)
val none_of_unit : unit -> 'a option

(** Return true *)
val true_of_any : 'a -> bool

(** Return false *)
val false_of_any : 'a -> bool

(* Creates a directory if it does not already exist. *)
val mk_dir : string -> unit



(** {1 Option types} *)

(** Return the value of an option type, raise [Invalid_argument "get"]
    if the option value is [None] *)
val get : 'a option -> 'a

(** {1 Infinite-precision numbers and bit-vectors} *)

(** Constant bitvector *)
type bitvector

(** Return the length of a bitvector as a numeral *)
val length_of_bitvector : bitvector -> int

(** Convert a string to a bitvector

    Binary and hexadecimal notation is accepted as #b[01]+ and
    #x[0-9a-fA-F]+ as in the SMTLIB standard *)
val bitvector_of_string : string -> bitvector

(** Convert a hashconsed string to a bitvector, store all converted
    values in a cache *)
val bitvector_of_hstring : HString.t -> bitvector

(** Convert a hashconsed string to a Boolean value *)
val bool_of_hstring : HString.t -> bool

(** Pretty-print a constant bitvector in SMTLIB binary format *)
val pp_smtlib_print_bitvector_b : Format.formatter -> bitvector -> unit

(** Pretty-print a constant bitvector in Yices' binary format *)
val pp_yices_print_bitvector_b : Format.formatter -> bitvector -> unit

(** Pretty-print a constant bitvector in hexadeciaml format *)
val pp_print_bitvector_x : Format.formatter -> bitvector -> unit

(** {1 Integer functions} *)

(** [string_starts_with s1 s2] returns true if the first characters of
    [s1] up to the length of [s2] are ientical to [s2]. Return false if
    [s2] is longer than [s1]. *)
val string_starts_with : string -> string -> bool

(** {1 Integer functions} *)

(** [safe_hash_interleave h m i] compute [m * h + i] and makes sure
    that the result does not overflow to a negtive number *)
val safe_hash_interleave : int -> int -> int -> int

(** {1 List functions} *)

(** Add element to the head of the list if the option value is not [None].

    The function symbol is right-associative and infix:

    {[ Some 1 @:: None @:: Some 2 @:: [3;4] ]}

    returns

    {[ \[1;2;3;4\] ]}
*)
val ( @:: ) : 'a option -> 'a list -> 'a list 

(** Creates a size-n list equal to [f 0; f 1; ... ; f (n-1)] *)
val list_init : (int -> 'a) -> int -> 'a list

(** Returns the maximum element of a non-empty list *)
val list_max : 'a list -> 'a

(** Return the index of the first element that satisfies the predicate
    [p], raise excpetion [Not_found] if no element satisfies the
    predicate. *)
val list_index : ('a -> bool) -> 'a list -> int

(** [list_indexes l1 l2] returns the indexes in list [l2] of elements
    in list [l1] *)
val list_indexes : 'a list -> 'a list -> int list

(** [list_filter_nth l [p1; p2; ...]] returns the elements [l] at
    positions [p1], [p2] etc. *)
val list_filter_nth : 'a list -> int list -> 'a list

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

(** Given two ordered association lists with identical keys, push the
    values of each element of the first association list to the list of
    elements of the second association list.

    The returned association list is in the order of the input lists,
    the function [equal] is used to compare keys. Raise [Failure
    "list_join"] if the lists are not of identical length and the keys
    at each element are equal. *)
val list_join : ('a -> 'a -> bool) -> ('a * 'b) list -> ('a * 'b list) list -> ('a * 'b list) list

(** Lexicographic comparison of pairs *)
val compare_pairs : ('a -> 'a -> int) -> ('b -> 'b -> int) -> 'a * 'b -> 'a * 'b -> int 

(** Lexicographic comparison of lists *)
val compare_lists : ('a -> 'a -> int) -> 'a list -> 'a list -> int 

(** {1 Array functions} *)

(** Returns the maximum element of a non-empty array *)
val array_max : 'a array -> 'a

(** {1 Set functions} *)

(** Sets of integers *)
module IntegerSet : Set.S with type elt = int

(** Hashtable of integers *)
module IntegerHashtbl : Hashtbl.S with type key = int
  
(** {1 Pretty-printing helpers} *)

(** Pretty-print an array with given separator
 
 [pp_print_array elem_printer separator formatter array] calls,
 for each index [i] of the array whose corresponding element is [element], 
 [elem_printer formatter i element]. Between each of these calls
 it prints the string [separator].

 In order to get line breaks between the elements, do not use a
 line feed character [\n] as separator, this might mess up
 indentation. Instead wrap the list into a vertical box with the
 format string [@\[<v>%a@\]] and the empty string as separator.

*) 
val pp_print_arrayi : (Format.formatter -> int -> 'a -> unit) -> (unit, Format.formatter, unit) format -> Format.formatter -> 'a array -> unit

(** Pretty-print a list with given separator 

    [pp_print_list p s f l] pretty-prints the elements in the list [l]
    by calling the pretty-printer [p] on each, separating the elements
    by printing the string [s].

    In order to get line breaks between the elements, do not use a
    line feed character [\n] as separator, this might mess up
    indentation. Instead wrap the list into a vertical box with the
    format string [@\[<v>%a@\]] and the empty string as separator.
*)
val pp_print_list : (Format.formatter -> 'a -> unit) -> ('b, Format.formatter, unit) format -> Format.formatter -> 'a list -> unit

(** Pretty-print a list with given separator and maintain a counter of elements 

    See {!pp_print_list}, except that the pretty-printer is passes an
    zero-based counter for the list's elements as the argument
    preceding the list element.
*)
val pp_print_listi : (Format.formatter -> int -> 'a -> unit) -> ('b, Format.formatter, unit) format -> Format.formatter -> 'a list -> unit

(** Pretty-print an option type *)
val pp_print_option : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

(** Pretty-print if list is not empty *)
val pp_print_if_not_empty : (unit, Format.formatter, unit) format -> Format.formatter -> 'a list -> unit

(** Pretty-print into a string *)
val string_of_t : (Format.formatter -> 'a -> unit) -> 'a -> string 

(** Return the strings as a parenthesized and space separated list *)
val paren_string_of_string_list : string list -> string

(** {1 Logging} *)

(** Levels of log messages

    - [L_fatal] A severe error that will lead to an immediate abort

    - [L_error] An error event that might still allow to continue

    - [L_warn] A potentially harmful situation

    - [L_info] An informational message that highlight progress at a
      coarse-grained level

    - [L_debug] A fine-grained informational event that is useful for
      debugging but not for an end user 

    - [L_trace] A finer-grained informational event than [L_debug]

 *)
type log_level =
  | L_off
  | L_fatal
  | L_error
  | L_warn
  | L_info
  | L_debug
  | L_trace


(** Associate an integer with each level to induce a total ordering *)
val int_of_log_level : log_level -> int

val log_level_of_int : int -> log_level


(** Current formatter for output *)
val log_ppf : Format.formatter ref 

(** Ouputs all log messages to the given file *)
val log_to_file : string -> unit

(** Write all log messages to the standard output *)
val log_to_stdout : unit -> unit

(** Set log level

    Only output messages of levels with equal or higher priority *)
val set_log_level : log_level -> unit 

(** Return true if given log level is of higher or equal priority than
    current log level? *)
val output_on_level : log_level -> bool

(** Return Format.fprintf if level is is of higher or equal priority
    than current log level, otherwise return Format.ifprintf *)
val ignore_or_fprintf : log_level -> Format.formatter -> ('a, Format.formatter, unit) format -> 'a


(** {1 System functions} *)

(** Output the banner on the formatter *)
val pp_print_banner : Format.formatter -> unit -> unit

(** Output the version number on the formatter *)
val pp_print_version : Format.formatter -> unit


(** Kind modules *)
type kind_module =
  [ `IC3
  | `BMC
  | `IND
  | `IND2
  | `INVGEN
  | `INVGENOS
  | `C2I
  | `Interpreter
  | `Supervisor
  | `Parser
  | `Certif ]

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

(** String representation of a process type *)
val int_of_kind_module : kind_module -> int

(** Return a short representation of kind module *)
val suffix_of_kind_module : kind_module -> string

(** Kind module of a string *)
val kind_module_of_string : string -> kind_module

(** Sleep for seconds, resolution is in ms *)
val minisleep : float -> unit

(** Return full path to executable, search PATH environment variable
    and current working directory *)
val find_on_path : string -> string 

(** {1 Positions in the input} *)

(** A position in the input *)
type position 

(** Dummy position different from any valid position *)
val dummy_pos : position

(** Comparision on positions *)
val compare_pos : position -> position -> int

(** Return [true] if the position is not a valid position in the
    input *)
val is_dummy_pos : position -> bool

(** Pretty-print a position *)
val pp_print_position : Format.formatter -> position -> unit

(** Pretty-print a position in a concise way *)
val pp_print_pos : Format.formatter -> position -> unit

(** Return the file, line and column of a position; fail with
    [Invalid_argument "file_row_col_of_pos"] if the position is a dummy
    position *)
val file_row_col_of_pos : position -> string * int * int

(** Inverse of {!file_row_col_of_pos} *)
val pos_of_file_row_col : string * int * int -> position

(** Convert a position of the lexer to a position *)
val position_of_lexing : Lexing.position -> position


(** Pretty print a backtrace *)
val print_backtrace : Format.formatter -> Printexc.raw_backtrace -> unit


(** Extract scope from a concatenated name *)
val extract_scope_name : string -> string * string list

(** Create a directory if it does not already exists. *)
val create_dir : string -> unit

(** Copying file: [file_copy from to] copies file [from] to file [to] *)
val file_copy : string -> string -> unit

val files_cat_open : ?add_prefix:(Format.formatter -> unit) ->
  string list -> string -> Unix.file_descr

(** Get standard output of command *)
val syscall : string -> string

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
