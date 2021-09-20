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

(** Trie over lists of values

    Tries in this implementation contain data at the leaves only. An
    inner node contains only the subtries for each key.

    This module is inspired by Jean-Christophe Filliatre's
    implementation at
    https://www.lri.fr/~filliatr/ftp/ocaml/ds/trie.ml.html

    @author Christoph Sticksel*)


(** Output signature is an extended map *)
module type S = sig

  (** Type of keys in the trie *)
  type key

  (** Type of the trie *)
  type +'a t

  (** The empty trie *)
  val empty : 'a t

  (** Return [true] if the trie is empty *)
  val is_empty : 'a t -> bool

  (** Return [true] if there is a value for the key in the trie *)
  val mem : key -> 'a t -> bool

  (** Bind a value to the key in the trie

      Overwrite if the value if the leaf already exists, fail if the
      sequence of keys is a prefix of a previous sequence, or if a
      previous sequence is a prefix of the given sequence. *)
  val add : key -> 'a -> 'a t -> 'a t

  (* val singleton: key -> 'a -> 'a t *)

  (** Remove key from trie

      Do not fail if key does not exist. *)
  val remove : key -> 'a t -> 'a t

  val merge: (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

  (** Comparision function on tries *)
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

  (** Equality predicate on tries *)
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  (** Apply unit-valued function to each value in trie *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit

  (** Reduce trie to a value by applying the function to all values *)
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  (** Return [true] if the given predicate evaluates to [true] for all
      key value pairs in the trie *)
  val for_all : (key -> 'a -> bool) -> 'a t -> bool

  (** Return [true] if there is a key value pair in the trie for which
      the given predicate evaluates to [true] *)
  val exists : (key -> 'a -> bool) -> 'a t -> bool

  (** Return a trie that only contains the key value pairs that
      satisfy the predicate *)
  val filter: (key -> 'a -> bool) -> 'a t -> 'a t

  (** Return the number of bindings in the trie *)
  val cardinal : 'a t -> int

  (** Return an association list of key to bindings in the trie

      The keys are returned in lexicographic order. *)
  val bindings : 'a t -> (key * 'a) list

  val min_binding: 'a t -> (key * 'a)
  val max_binding: 'a t -> (key * 'a)

  val choose: 'a t -> (key * 'a)

  val split: key -> 'a t -> 'a t * 'a option * 'a t

  (** Return the value for the key in the trie *)
  val find : key -> 'a t -> 'a

  (** Return a new trie with the function applied to the values *)
  val map : ('a -> 'b) -> 'a t -> 'b t
      
  (** Return a new trie with the function applied to the values 

      The key is given as the first argument to the function. *)
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t

  (** Return the subtrie starting at the given key prefix *)
  val find_prefix : key -> 'a t -> 'a t

  (** Return [true] if there is a subtrie starting at the given key
      prefix *)
  val mem_prefix : key -> 'a t -> bool

  (** Return the keys in the trie

      The keys are returned in lexicographic order. *)
  val keys : 'a t -> key list

  (** Return the values in the trie

      The values are returned in lexicographic order. *)
  val values : 'a t -> 'a list

  (** Fold over two tries with identical keys

      [fold2 f t1 t2 a] applies [f] to each pair of values in of [t1]
      and [t2] that have identical keys. The keys are presented in
      lexicographic order. Raise exception [Invalid_argument
      "Trie.fold2"] if the sets of keys the trie are not equal *)
  val fold2 : (key -> 'a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
    
  (** Map over two tries with identical keys

      [map2 f t1 t2] applies [f] to each pair of values in of [t1] and
      [t2] that have identical keys and produces a new trie from the
      result. The keys are presented in lexicographic order. Raise
      exception [Invalid_argument "Trie.map2"] if the sets of keys
      the trie are not equal *)
  val map2 : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  (** Iterate over two tries with identical keys

      [iter2 f t1 t2] applies the unit valued function [f] to each
      pair of values in of [t1] and [t2] that have identical keys. The
      keys are presented in lexicographic order. Raise exception
      [Invalid_argument "Trie.iter2"] if the sets of keys the trie are
      not equal. *)
  val iter2 : (key -> 'a -> 'b -> unit) -> 'a t -> 'b t -> unit

  (** Check if all pairs of bindings in the trie satisfy the predicate 

      [for_all2 p t1 t2] returns true if [p] evaluates to true for all
      pairs of bindings in t1 and t2 with identical keys. Raise
      exception [Invalid_argument "Trie.for_all2"] if the sets of keys
      the trie are not equal. *)
  val for_all2 : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

  (** Check if there is a binding in the trie that satisfies the
      predicate

      [exists2 p t1 t2] returns true if [p] evaluates to true for at
      least one pair of bindings with identical keys in [t1]
      and[t2]. Raise exception [Invalid_argument "Trie.exists2"] if
      the sets of keys the trie are not equal. *)
  val exists2 : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

  (** Return a new trie containing only entries with keys that are not
      subsets of the given key
      
      [subsume t k] assumes that all keys in the trie [t], and the key
      [k] are sorted and do not contain duplicates. It returns a new
      trie with all entries for keys that are subsets of [k]
      removed. *)
  val subsume : 'a t -> key -> (key * 'a) list * 'a t

  (** Return [true] if there is a key in the trie such that all
      elements of that key are in the given key. 
  
      [is_subsumed t k] assumes that all keys in the trie [t], and the key
      [k] are sorted and do not contain duplicates.*)
  val is_subsumed : 'a t -> key -> bool

  (** Pretty-print bindings in the trie with a printer for key and
      value pairs

      [pp_print_trie f s p t] prints to the formatter [p] all bindings
      of the trie in lexicographic order of the keys with the printer
      [f] for key and value pairs. Each binding is separated by the
      format string [s]. *)
  val pp_print_trie : (Format.formatter -> key * 'a -> unit) ->
    (unit, Format.formatter, unit) format -> Format.formatter -> 'a t -> unit
    
end


(** Trie over sequences of keys of map *)
module Make(Ord: Map.OrderedType) : S with type key = Ord.t list
