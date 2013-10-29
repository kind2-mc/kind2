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

(** Types of terms

    A type has to be hash-consed to be used in hash-consed terms.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Type of an expression *)
type kindtype = 
  | Bool
  | Int
  | IntRange of Lib.numeral * Lib.numeral
  | Real
  | BV of Lib.numeral
  | Array of t * t

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

(** Hash table over variables *)
module TypeHashtbl : Hashtbl.S with type key = t

(** Set over variables *)
module TypeSet : Set.S with type elt = t

(** Map over variables *)
module TypeMap : Map.S with type key = t


(** {1 Constructor} *)

(** Hashcons a type *)
val mk_type : kindtype -> t

(** Return the boolean type *)
val mk_bool : unit -> t

(** Return the integer type *)
val mk_int : unit -> t 

(** Return the integer range type *)
val mk_int_range : Lib.numeral -> Lib.numeral -> t

(** Return the real decimal type *)
val mk_real : unit -> t

(** Return the bitvector type *)
val mk_bv : Lib.numeral -> t

(** Return the array type *)
val mk_array : t -> t -> t

(** Import a type from a different instance into this hashcons table *)
val import : t -> t 

(** The boolean type *)
val t_bool : t

(** The integer type *)
val t_int : t

(** The real decimal type *)
val t_real : t

(** {1 Predicates} *)

(** Return [true] if the type is the Boolean type *)
val is_bool : t -> bool

(** Return [true] if the type is an integer type *)
val is_int : t -> bool

(** Return [true] if the type is the real type *)
val is_real : t -> bool

(** Return [true] if the type is a bitvector type *)
val is_bv : t -> bool

(** Return [true] if the type is an array type *)
val is_array : t -> bool

(** {1 Pretty-printing} *)

(** Pretty-print a type *)
val pp_print_type_node : Format.formatter -> kindtype -> unit

(** Pretty-print a type *)
val pp_print_type : Format.formatter -> t -> unit

(** Return a string representation of a type *)
val string_of_type : t -> string


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
