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

(** Lustre types 

    @author Christoph Sticksel *)


(** A type *)
type t = private
  | Bool                        (** The Boolean type *)
  | Int                         (** The integer type *)
  | Real                        (** The real type *)
  | IntRange of (int * int)     (** An integer range type *)
  | FreeType of LustreIdent.t   (** A free (uninterpreted) type *)
  | Enum of LustreIdent.t list  (** An enumeration type *)

(** Total ordering of types *)
val compare : t -> t -> int

(** Equality of types *)
val equal : t -> t -> bool

(** Pretty-print a type *)
val pp_print_lustre_type : Format.formatter -> t -> unit 

(** Return the Boolean type *)
val t_bool : t

(** Return the integer type *)
val t_int : t

(** Return the real type *)
val t_real : t

(** Construct an integer range type *)
val mk_int_range : int -> int -> t

(** Construct a free type *)
val mk_free_type : LustreIdent.t -> t

(** Construct an enumerated type *)
val mk_enum : LustreIdent.t list -> t

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
