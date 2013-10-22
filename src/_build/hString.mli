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

(** Perfect shared strings by hashconsing

    @author Christoph Sticksel *)


(** Hashconsed string *)
type t 

(** {1 Hashtables, maps and sets} *)

(** Comparison function on hashconsed strings *)
val compare : t -> t -> int

(** Equality function on hashconsed strings *)
val equal : t -> t -> bool

(** Hashing function on hashconsed strings *)
val hash : t -> int

(** Hash table over hashconsed strings *)
module HStringHashtbl : Hashtbl.S with type key = t

(** Set over hashconsed strings *)
module HStringSet : Set.S with type elt = t

(** Map over hashconsed strings *)
module HStringMap : Map.S with type key = t


(** {1 Constructor} *)

(** Hashcons a string *)
val mk_hstring : string -> t

(** Import a string from a different instance into this hashcons
    table *)
val import : t -> t 

(** {1 String functions} 

    Omitted functions from the [String] module in the standard library:

    - [copy]: All strings are shared

    Modified signature: 

    - [sub]: return a string, not a hashconsed string
    - [fill], [blit]: no in-place modifications

*)

val length : t -> int
val get : t -> int -> char
val set : t -> int -> char -> t
val create : int -> t
val make : int -> char -> t
val sub : t -> int -> int -> string
val fill : t -> int -> int -> char -> t
val blit : t -> int -> t -> int -> int -> t
val concat : t -> t list -> t
val iter : (char -> unit) -> t -> unit
val iteri : (int -> char -> unit) -> t -> unit
val map : (char -> char) -> t -> t
val trim : t -> t
val escaped : t -> t
val index : t -> char -> int
val rindex : t -> char -> int
val index_from : t -> int -> char -> int
val rindex_from : t -> int -> char -> int
val contains : t -> char -> bool
val contains_from : t -> int -> char -> bool
val rcontains_from : t -> int -> char -> bool
val uppercase : t -> t
val lowercase : t -> t
val capitalize : t -> t
val uncapitalize : t -> t

(** {1 Pretty-printing} *)

(** Pretty-print a hashconsed string *)
val pp_print_hstring : Format.formatter -> t -> unit 

(** Pretty-print a hashconsed term to the standard formatter *)
val print_hstring : t -> unit 

(** Return the string *)
val string_of_hstring : t -> string 


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
