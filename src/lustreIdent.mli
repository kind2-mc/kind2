(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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


(** Lustre identifiers 

    An identifier can be indexed either by a string, which models
    access of a record field, or by an integer, which models access of
    tuple or array elements.

    In Lustre all indexes must be static at compile time, we can
    flatten all record, tuple and array expressions to expressions
    over such indexed identifiers.

    An index is a list of strings or integers, the head of the list is
    the "least significant index", that is, the one that is used first
    when derefencing an indexed identifier.

    An index is stored in terms of concrete types, not the abstract
    types of {!Numeral.t} or {!Decimal.t} it is constructed with, so
    that polymorphic comparison and equality can be used and indexes
    as well as indentifiers can be stored in association lists etc.

    @author Christoph Sticksel *)


(** An index element *)
type one_index = private

  (* String as index *)
  | StringIndex of string

  (* Integer as index *)
  | IntIndex of int


(** An index *)
type index = private one_index list 

(** An indexed identifier *)
type t = private string * index

(** A set of identifiers *)
module LustreIdentSet : Set.S with type elt = t

(** Pretty-print an identifier *)
val pp_print_ident : bool -> Format.formatter -> t -> unit 

(** Pretty-print an index *)
val pp_print_index : bool -> Format.formatter -> index -> unit 

(** Pretty-print an index element *)
val pp_print_one_index : bool -> Format.formatter -> one_index -> unit 

(** Return a string representation of an identifier *)
val string_of_ident : bool -> t -> string 

(** Return a list of strings for index *)
val scope_of_index : index -> string list

(** Return a list of strings for identifier *)
val scope_of_ident : t -> string list

(** Total order on indexes *)
val compare_index : index -> index -> int

(** Total order on indexed identifiers *)
val compare : t -> t -> int

(** Total order on indexed identifiers *)
val equal : t -> t -> bool


(** Construct an identifier with empty index of a string *)
val mk_string_index : string -> index


(** Construct a singleton index of an integer *)
val mk_int_index : Numeral.t -> index


(** Construct a singleton index of a string *)
val mk_string_ident : string -> t


(** An empty index *)
val empty_index : index

(** Construct an index of an identifier *)
val index_of_ident : t -> index 


val push_string_index : string -> t -> t 
val push_back_string_index : string -> t -> t 

val push_int_index : Numeral.t -> t -> t
val push_back_int_index : Numeral.t -> t -> t

val push_one_index : one_index -> t -> t
val push_back_one_index : one_index -> t -> t

val push_ident_index : t -> t -> t 
val push_back_ident_index : t -> t -> t 

val push_index : index -> t -> t 
val push_back_index : index -> t -> t 

val push_string_index_to_index : string -> index -> index 
val push_back_string_index_to_index : string -> index -> index 

val push_int_index_to_index : Numeral.t -> index -> index 
val push_back_int_index_to_index : Numeral.t -> index -> index 

val push_ident_index_to_index : t -> index -> index 
val push_back_ident_index_to_index : t -> index -> index 

val push_one_index_to_index : one_index -> index -> index 
val push_back_one_index_to_index : one_index -> index -> index 

val push_index_to_index : index -> index -> index 
val push_back_index_to_index : index -> index -> index 

val split_ident : t -> t * one_index list

val split_index : index -> one_index list

val index_of_one_index_list : one_index list -> index

(*

(** Construct an index of an integer *)
val index_of_int : int -> index 

(** Add an index to an identifier *)
val add_ident_index : t -> t -> t

(** Add an identifier as an index to an identifier *)
val add_index : t -> index -> t

(** Add a string as an index to an identifier *)
val add_string_index : t -> string -> t

(** Add an integer as an index to an identifier *)
val add_int_index : t -> int -> t

val add_int_to_index : index -> int -> index


val get_index_suffix : index -> index -> index
*)


(** [get_suffix i j] assumes that [i] and [j] index the same
    identifier and the indexes of [i] are a prefix of the indexes of
    [j]. Return the suffix of [j] with the common prefix with [i]
    removed, raise [Not_found] otherwise. *)
val get_suffix : t -> t -> index

(** Return [true] if identifier is reserved for itnernal use *)
val ident_is_reserved : t -> bool

(** Identifier for abstracted variable *)
val abs_ident : t

(** Identifier for oracle input *)
val oracle_ident : t

(** Identifier for observer output *)
val observer_ident : t

(** Identifier for clock initialization flag *)
val first_tick_ident : t 

(** Identifier of uninterpreted symbol for initial state constraint *)
val init_uf_string : string 

(** Identifier of uninterpreted symbol for transition relation *)
val trans_uf_string : string 

(*
(** Scope for top-level variables *)
val top_scope_index : index
*)

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
