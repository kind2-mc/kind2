(*
This file is part of the Kind verifier

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

(** Typechecking functions, used in the parser. *)

(** Returns the type of a {!Types.typed_stream} (or other pair where the type is second) *)
val gettype : Types.typed_stream -> Types.lustre_type

(** Typing of nodes is lazy, and currently skips L_UNDET assignments.
This function returns the type if 2 types are the same, otherwise
it raises {!Exceptions.TypeMismatch} *)
val match_types : Types.typed_stream -> Types.typed_stream -> Types.lustre_type

(** Checks all types in a list, returns the type list *)
val match_types_list : Types.typed_stream list -> 
  (int * Types.lustre_type) list -> Types.lustre_type list

(** As above for ints only *)
val match_types_int : Types.typed_stream -> Types.typed_stream -> 
  Types.lustre_type

(** As above for bools only *)
val match_types_bool : Types.typed_stream -> Types.typed_stream -> 
  Types.lustre_type

(** As above, but for numeric relations *)
val match_types_nrel : Types.typed_stream -> Types.typed_stream -> 
  Types.lustre_type

(** Raises TypeMismatch if is not numeric (real or int) *)
val match_type_is_numeric : Types.typed_stream -> Types.lustre_type

(** returns the type t1 for "ite bool t1 t1" *)
val match_types_ite : Types.typed_stream -> Types.typed_stream -> 
  Types.typed_stream -> Types.lustre_type
 
 
(** Raises a TypeMismatch exception if this is not a tuple type, otherwise
[is_tuple_type x y] returns the [y]th field type. *)
val is_tuple_type : Types.typed_stream -> int -> Types.lustre_type

