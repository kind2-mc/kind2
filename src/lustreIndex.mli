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


(** Indexes of records, tuples and arrays in Lustre

    In Lustre some indexes must be static at compile time, we can
    flatten all record and tuple such indexed identifiers. The
    remaining indexes are array indexes.

    Array indexes are annotated with an expression denoting the
    bound. However, this bound is not considered when comparing array
    indexes, because two bounds expressions can only be evaluated in a
    context. A syntactic comparison of bound expressions will fail in
    making expressions equal that should be equal, for example in node
    calls where the size of an input is parametrized by another input.

    @author Christoph Sticksel *)


(** An index element *)
type one_index = 

  (** String as index *)
  | RecordIndex of string

  (** Integer as index *)
  | TupleIndex of int

  (** Integer as index *)
  | ListIndex of int

  (** Integer as index *)
  | ArrayIntIndex of int

  (** Variable as index *)
  | ArrayVarIndex of LustreExpr.expr

(** A sequence of indexes *)
type index = one_index list

val pp_print_one_index : bool -> Format.formatter -> one_index -> unit

val pp_print_index : bool -> Format.formatter -> index -> unit

val string_of_index : bool -> index -> string

val empty_index : index

(** A trie of indexes *)
include Trie.S with type key = index

(* Return a trie with a single element for the empty index. *)
val singleton : index -> 'a -> 'a t

val top_max_index : 'a t -> int

val equal_index : index -> index -> bool

val compare_indexes : index -> index -> int

val array_bounds_of_index : index -> LustreExpr.expr list

val array_vars_of_index : index -> StateVar.t list
