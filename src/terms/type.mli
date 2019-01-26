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

(** Types of terms

    A type has to be hash-consed to be used in hash-consed terms.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Tells if the range actually encodes an enumerated datatype *)
type rangekind = Range | Enum

(** Type of an expression *)
type kindtype = 
  | Bool
  | Int
  | IntRange of Numeral.t * Numeral.t * rangekind
  | Real
  | UBV of int
  | BV of int 
  | Array of t * t
  | Abstr of string

(** Hashconsed type *)
and t

(** Return the value {!kindtype} in a hashconsed type *)
val node_of_type : t -> kindtype

(** {1 Hashtables, maps and sets} *)

(** Comparison function on types *)
val compare_types : t -> t -> int

(** Equality function on types *)
val equal_types : t -> t -> bool

(** Hashing function on types *)
val hash_type : t -> int

(** Hash table over types *)
module TypeHashtbl : Hashtbl.S with type key = t

(** Set over types *)
module TypeSet : Set.S with type elt = t

(** Map over types *)
module TypeMap : Map.S with type key = t


(** {1 Constructor} *)

(** Hashcons a type *)
val mk_type : kindtype -> t

(** Return the boolean type *)
val mk_bool : unit -> t

(** Return the integer type *)
val mk_int : unit -> t 

(** Return the integer range type *)
val mk_int_range : Numeral.t -> Numeral.t -> t

(** Return the real decimal type *)
val mk_real : unit -> t

(** Return the unsigned bitvector type *)
val mk_ubv : int -> t

(** Return the bitvector type *)
val mk_bv : int -> t

(** Return an array type of index sort and element sort *)
val mk_array : t -> t -> t

(** Return an abstract type *)
val mk_abstr : string -> t

(** Return an enumerated datatype type *)
val mk_enum : string option -> string list -> t

(** Import a type from a different instance into this hashcons table *)
val import : t -> t 

(** The boolean type *)
val t_bool : t

(** The integer type *)
val t_int : t

(** The real decimal type *)
val t_real : t

(** The unsigned bitvector type *)
val t_ubv : int -> t

(** The bitvector type *)
val t_bv : int -> t

(** {1 Type checking} *)

(** [check_type s t] returns [true] if [s] is a subtype of [t] *)
val check_type : t -> t -> bool


(** {1 Predicates} *)

(** Return [true] if the type is the Boolean type *)
val is_bool : t -> bool

(** Return [true] if the type is the integer type *)
val is_int : t -> bool

(** Return [true] if the type is an unsigned bitvector (integern) type *)
val is_ubitvector : t -> bool

(** Return [true] if the type is a bitvector (integern) type *)
val is_bitvector : t -> bool

(** Return [true] if the type is a bitvector (integern) type *)
val bitvectorsize : t -> int

(** Return [true] if the type is the unsigned integer8 type *)
val is_uint8 : t -> bool

(** Return [true] if the type is the unsigned integer16 type *)
val is_uint16 : t -> bool

(** Return [true] if the type is the unsigned integer32 type *)
val is_uint32 : t -> bool

(** Return [true] if the type is the unsigned integer64 type *)
val is_uint64 : t -> bool

(** Return [true] if the type is the integer8 type *)
val is_int8 : t -> bool

(** Return [true] if the type is the integer16 type *)
val is_int16 : t -> bool

(** Return [true] if the type is the integer32 type *)
val is_int32 : t -> bool

(** Return [true] if the type is the integer64 type *)
val is_int64 : t -> bool

(** Return [true] if the type is an integer range type *)
val is_int_range : t -> bool

(** Return [true] if the type is an integer range type *)
val is_enum : t -> bool

(** Return [true] if the type is the real type *)
val is_real : t -> bool

(** Return [true] if the type is an array type *)
val is_array : t -> bool

(** Return [true] if the type is abstract *)
val is_abstr : t -> bool

(** {1 Ranges} *)

(** Return bounds of an integer range type, fail with
    [Invalid_argument "bounds_of_int_range"] if the type is not an
    integer range type. *)
val bounds_of_int_range : t -> (Numeral.t * Numeral.t)


(** Generalize a type (remove actual intranges) *)
val generalize : t -> t


(** {1 Arrays } *)

(** Return type of array index *)
val index_type_of_array : t -> t 

(** Return all array index types of a nested array type *)
val all_index_types_of_array : t -> t list

(** Return type of array elements *)
val elem_type_of_array : t -> t

(** Return all array index types of a nested array type *)
val last_elem_type_of_array : t -> t

(** {1 Enumerated datatypes } *)

(** Return constructors of an enumerated datatype *)
val constructors_of_enum : t -> string list

(** Return the name of an enumerated datatype encoded as int ranges *)
val name_of_enum : t -> string option

(** Return the constructor encoded by the numeral argument *)
val get_constr_of_num : Numeral.t -> string

(** Return abstract types that have been built *)
val get_all_abstr_types : unit -> t list

(** Return the numeral encoding of a construcor of an enumerated datatype *)
val get_num_of_constr : string -> Numeral.t

(** Return the enumerated dataype to which the constructor belongs *)
val enum_of_constr : string -> t


(** {1 Pretty-printing} *)

(** Pretty-print a type *)
val pp_print_type_node : Format.formatter -> kindtype -> unit

(** Pretty-print a type *)
val pp_print_type : Format.formatter -> t -> unit

(** Pretty-print a type to the standard formatter *)
val print_type : t -> unit

(** Return a string representation of a type *)
val string_of_type : t -> string


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
