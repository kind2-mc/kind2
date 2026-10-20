(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(** Chains of nested lets regrouped by dependency level

    A formula with shared subterms is written as a chain of directly
    nested lets, often of one binding each and thousands long: by the
    translators that write MoXI, and by SMT solvers in their replies.
    Built one let at a time, such a chain takes a time that grows faster
    than the square of its length, since a let is built by traversing
    its body, and each subterm of the chain keeps the indexes of the
    variables bound around it. The bindings are regrouped instead into as
    few lets as their dependencies allow, built at once with
    {!Term.mk_let_chain}.

    A chain is a list of lets, outermost first, each a list of bindings
    of a symbol to a term. The functions are over any representation of
    symbols and terms: [name] gives the name a symbol binds, and [free]
    the names a term refers to that it does not bind itself, with any
    over-approximation of them. *)

(** [segments ~name ~free chain] is the chain split into segments, each a
    list of lets whose bindings carry a level: 1 for a binding whose term
    depends on no binding of the segment, and otherwise 1 + the highest
    level of those it depends on. In a segment, each binding can be moved
    to the let of its level without changing what any symbol refers to,
    since the lets of a segment

    - bind each symbol once,
    - bind no symbol that a term of an earlier let of the segment takes
      from the enclosing scope, and
    - have no term that refers to a symbol of its own let, which it takes
      from the enclosing scope as well.

    A let that breaks the first or the second condition starts a new
    segment, and one that breaks the third, or binds a symbol twice, is a
    segment of its own. *)
val segments :
  name:('s -> HString.t) ->
  free:('t -> HString.HStringSet.t) ->
  ('s * 't) list list ->
  ('s * int * 't) list list list

(** The lets to build the segments with, outermost first: for each
    segment in turn, one let per level with the bindings of that level in
    their order. Each binding is in the scope of the lets before its own,
    and the body of the chain in that of all of them. *)
val levels : ('s * int * 't) list list list -> ('s * 't) list list
