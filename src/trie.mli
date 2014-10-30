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

(** Trie over 

    Tries in this implementation contain data at the leaves only. An
    inner node contains only the subtries for each key.

    This module is inspired by Jean-Christophe Filliatre's
    implementation at
    https://www.lri.fr/~filliatr/ftp/ocaml/ds/trie.ml.html

    @author Christoph Sticksel*)


(** Input signature of a map *)
module type M = sig
  type key
  type +'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val remove : key -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end


(** Output signature is map extended with [find_prefix] *)
module type S = sig

  (** Type of keys in trie *)
  type key

  (** Type of Trie *)
  type +'a t

  (** Empty trie *)
  val empty : 'a t

  (** Return [true] if trie is empty *)
  val is_empty : 'a t -> bool

  (** Insert value for a key into the trie

      Overwrite if the value if the leaf already exists, fail if the
      sequence of keys is a prefix of a previous sequence, or if a
      previous sequence is a prefix of the given sequence. *)
  val add : key -> 'a -> 'a t -> 'a t

  (** Return the value for the key in the trie *)
  val find : key -> 'a t -> 'a

  (** Remove key from trie

      Do not fail if key does not exist. *)
  val remove : key -> 'a t -> 'a t

  (** Return [true] if there is a value for the key in the trie *)
  val mem : key -> 'a t -> bool

  (** Apply unit-valued function to each value in trie *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit

  (** Return a new trie with the function applied to the values *)
  val map : ('a -> 'b) -> 'a t -> 'b t
      
  (** Return a new trie with the function applied to the values 

      Give the key as first argument to the function. *)
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t

  (** Reduce trie to a value by applying the function to all values *)
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  (** Comparision function on tries *)
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

  (** Equality predicate on tries *)
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  (** Return the subtrie starting at the given key prefix *)
  val find_prefix : key -> 'a t -> 'a t

end


(** Trie over sequences of keys of map *)
module Make(M : M) : S with type key = M.key list
