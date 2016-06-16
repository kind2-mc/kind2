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
