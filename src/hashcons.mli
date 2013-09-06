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

(** Hash tables for hash consing

    Hash consed values are of the following type [hash_consed]. The
    field [tag] contains a unique integer (for values hash consed with
    the same table). The field [hkey] contains the hash key of the
    value (without modulo) for possible use in other hash tables (and
    internally when hash consing tables are resized). The field [node]
    contains the value itself. The field [prop] contains properties of
    some type associated with the hashconsed value.

    Values added to a hashcons table are never garbage collected.

    @author Jean-Christophe Filliatre, Christoph Sticksel
*)

type ('a, 'b) hash_consed = private { 
  hkey : int;
  tag : int;
  node : 'a;
  prop : 'b }

val compare : ('a, 'b) hash_consed -> ('a, 'b) hash_consed -> int
val equal : ('a, 'b) hash_consed -> ('a, 'b) hash_consed -> bool
val hash : ('a, 'b) hash_consed -> int

(** {1 Generic part, using ocaml generic equality and hash function} *)

type ('a, 'b) t

val create : int -> ('a, 'b) t
(** [create n] creates an empty table of initial size [n]. The table
      will grow as needed. *)

val clear : ('a, 'b) t -> unit
(** Removes all elements from the table. *)

val hashcons : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) hash_consed
(** [hashcons t n] hash-cons the value [n] using table [t] i.e. returns
    any existing value in [t] equal to [n], if any; otherwise, allocates
    a new one hash-consed value of node [n] and returns it. 
    As a consequence the returned value is physically equal to
    any equal value already hash-consed using table [t]. *)

val iter : (('a, 'b) hash_consed -> unit) -> ('a, 'b) t -> unit
(** [iter f t] iterates [f] over all elements of [t]. *)

val fold : (('a, 'b) hash_consed -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
(** [fold f t a] computes (f xN ... (f x2 (f x1 a))...), where x1
    ... xN are the elements of t. *)

val stats : ('a, 'b) t -> int * int * int * int * int * int
(** Return statistics on the table.  The numbers are, in order:
    table length, number of entries, sum of bucket lengths,
    smallest bucket length, median bucket length, biggest bucket length. *)

(** {1 Functorial interface} *) 

module type HashedType =
  sig
    type t
    type prop
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type S =
  sig
    type key
    type prop
    type t
    exception Key_not_found of key
    val create : int -> t
    val clear : t -> unit
    val hashcons : t -> key -> prop -> (key, prop) hash_consed
    val find : t -> key -> (key, prop) hash_consed
    val iter : ((key, prop) hash_consed -> unit) -> t -> unit
    val fold : ((key, prop) hash_consed -> 'a -> 'a) -> t -> 'a -> 'a
    val stats : t -> int * int * int * int * int * int
  end

module Make(H : HashedType) : (S with type key = H.t and type prop = H.prop)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
