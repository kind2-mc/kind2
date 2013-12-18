(* This file is part of the Kind verifier

 * Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
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

(** Lustre identifiers 

    An identifier can be indexed either by a string, which models
    acces of a record field, or by an integer, which models access of
    tuple or array elements.

    In Lustre all indexes must be static at compile time, we can
    flatten all record, tuple and array expressions to expressions
    over such indexed identifiers.

    An index is a list of strings or integers, the head of the list is
    the "least significant index", that is, the one that is used first
    when derefencing an indexed identifier.

    If a[i][j] is a tuple indexed in two dimensions, then the index is
    stored as the list [j; i].

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

(** Total order on indexes *)
val compare_index : index -> index -> int

(** Total order on indexed identifiers *)
val compare : t -> t -> int


(** Construct an identifier with empty index of a string *)
val mk_string_index : string -> index


(** Construct a singleton index of an integer *)
val mk_int_index : int -> index


(** Construct a singleton index of a string *)
val mk_string_ident : string -> t


(** An empty index *)
val empty_index : index

(** Construct an index of an identifier *)
val index_of_ident : t -> index 


val push_string_index : string -> t -> t 

val push_int_index : int -> t -> t

val push_one_index : one_index -> t -> t

val push_ident_index : t -> t -> t 

val push_index : index -> t -> t 


val push_string_index_to_index : string -> index -> index 

val push_int_index_to_index : int -> index -> index 

val push_ident_index_to_index : t -> index -> index 

val push_one_index_to_index : one_index -> index -> index 

val push_index_to_index : index -> index -> index 

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

(** [get_suffix i j] assumes that [i] and [j] index the same
    identifier and the indexes of [i] are a prefix of the indexes of
    [j]. Return the suffix of [j] with the common prefix with [i]
    removed, raise [Invalid_argument "get_suffix"] otherwise. *)
val get_suffix : t -> t -> index


*)



(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
