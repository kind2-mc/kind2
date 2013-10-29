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

(** Attributes for annotated terms

    An attribute is currently only a name for a term.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Hashconsed attribute *)
type t


(** {1 Hashtables, maps and sets} *)

(** Comparison function on attributes *)
val compare_attrs : t -> t -> int

(** Equality function on attributes *)
val equal_attrs : t -> t -> bool

(** Hashing function on attribute *)
val hash_attr : t -> int

(** Hash table over attributes *)
module AttrHashtbl : Hashtbl.S with type key = t

(** Set over attributes *)
module AttrSet : Set.S with type elt = t

(** Map over attributes *)
module AttrMap : Map.S with type key = t


(** {1 Constructor} *)

(** Return a name attribute *)
val mk_named : int -> t

(** {1 Accessor functions} *)

(** Return true if the attribute is a name *)
val is_named : t -> bool

(** Return the name in a name attribute, raises [Invalid_argument] for
    other attributes *)
val named_of_attr : t -> int

(** {1 Pretty-printing} *)

(** Pretty-print a hashconsed attribute *)
val pp_print_attr : Format.formatter -> t -> unit

(** Pretty-print a hashconsed attribute to the standard formatter *)
val print_attr : t -> unit

(** Return a string representation of a hashconsed attribute *)
val string_of_attr : t -> string 

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
