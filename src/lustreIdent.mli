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

    @author Christoph Sticksel *)


(** An identifier *)
type t

(** An index *)
type index 

val compare : t -> t -> int

(** Pretty-print an identifier *)
val pp_print_ident : Format.formatter -> t -> unit 

(** Construct an identifier of a string *)
val mk_string_id : string -> t

(** Construct an index of an identifier *)
val index_of_ident : t -> index 

(** Construct an index of an integer *)
val index_of_int : t -> index 

(** Add an index to an identifier *)
val add_ident_index : t -> t -> t

(** Add an identifier as an index to an identifier *)
val add_index : t -> index -> t

(** Add a string as an index to an identifier *)
val add_string_index : t -> string -> t

(** Add an integer as an index to an identifier *)
val add_int_index : t -> int -> t

(** [get_suffix i j] assumes that [i] and [j] index the same
    identifier and the indexes of [i] are a prefix of the indexes of
    [j]. Return the suffix of [j] with the common prefix with [i]
    removed, raise [Invalid_argument "get_suffix"] otherwise. *)
val get_suffix : t -> t -> index

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
