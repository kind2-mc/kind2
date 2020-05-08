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


(** Indexes for lists, records, tuples and arrays in Lustre

    In Lustre some indexes must be static at compile time, we can thus
    flatten all record, tuple and list values. The remaining indexes
    are array indexes, which we allow to be variable.

    Array indexes are annotated with an expression denoting the
    bound. However, this bound is not considered when comparing array
    indexes, because two bounds of expressions can only be evaluated
    in a context. A syntactic comparison of bound expressions will
    fail to make expressions equal that should be equal, for example
    in node calls where the size of an input is parametrized by
    another input.

    Lists in Lustre are similar to tuples, but they cannot be
    constructed, except as the inputs and outputs of node
    calls. Further, nested lists are to be flattened such that [((a,
    b), c)], [(a, (b, c))] and [(a, b, c)] are identical.

    @author Christoph Sticksel *)


(** An index element *)
type one_index = 

  (** Field name as index of a record *)
  | RecordIndex of string

  (** Integer literal as index of a tuple *)
  | TupleIndex of int

  (** Integer literal as index of a list *)
  | ListIndex of int

  (** Integer literal as index of an array *)
  | ArrayIntIndex of int

  (** Variable as index of an array of given size *)
  | ArrayVarIndex of LustreExpr.expr

  (* Index to the representation field of an abstract type *)
  | AbstractTypeIndex of string

(** A sequence of indexes *)
type index = one_index list

(** Pretty-print a single index *)
val pp_print_one_index : bool -> Format.formatter -> one_index -> unit

(** Pretty-print an list of indexes *)
val pp_print_index : bool -> Format.formatter -> index -> unit

(** Return a string representation of indexes *)
val string_of_index : bool -> index -> string

(** The empty index *)
val empty_index : index

(** A trie of indexes *)
include Trie.S with type key = index

(** Return a trie with a single element for the empty index *)
val singleton : index -> 'a -> 'a t

(** Equality of indexes *)
val equal_index : index -> index -> bool

(** Total order of indexes *)
val compare_indexes : index -> index -> int

(** {1 Helper Functions} *)

(** Return the list of bounds of the array indexes in the index *)
val array_bounds_of_index : index -> LustreExpr.expr list

(** Return the list of array variables of the array indexes in the
    index *)
val array_vars_of_index : index -> StateVar.t list

(** If the first index is a list, return the greatest integer in a
    trie of indexes. Return [(- 1)] if the index is empty and fail with
    [Invalid_argument "top_max_index"] if the first index is not a list *)
val top_max_index : 'a t -> int


val compatible_indexes : index -> index -> bool


(** Pretty print a trie of indexes *)
val pp_print_index_trie :
  bool -> (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a t -> unit


(** Pretty print a trie with expressions *)
val pp_print_trie_expr : bool -> Format.formatter -> LustreExpr.t t -> unit

val mk_scope_for_index: index -> Scope.t

