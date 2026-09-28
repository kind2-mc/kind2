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

(** Unrolling of recursive functions driven by counterexamples

    Outside of compositional analyses, a recursive function is unrolled a
    number of times in the transition system, and the recursive calls past
    those unrollings are left unconstrained (see [LustreTransSys]). A
    counterexample that reaches such a call may be spurious. When one does,
    the function is unrolled once more and the engines run again on the
    system built anew, with what they had established carried over (see
    [Kind2Flow]); this is not an analysis of its own. Once a function is at
    the limit set with [--rec_unrollings], a property whose counterexample
    reaches its cutoff is left unknown.

    This module keeps, for the analysis under way, the functions to unroll
    further and the properties given up on. *)

(** The number of unrollings of a recursive function in the analysis *)
val depth : Analysis.param -> Scope.t -> int

(** Forget the requests and the properties given up on: a new system is
    analyzed *)
val reset : unit -> unit

(** Forget the requests, and count the instances of the recursive
    functions of the system the engines are about to run on, to tell how
    fast the unrollings multiply them *)
val start_round : TransSys.t -> unit

(** A counterexample to the property reached the cutoffs of the functions.
    Those below the limits are requested to be unrolled further; if there
    is none, the property is given up on, and the functions at a limit
    that were not reported yet are returned, to be reported once: first
    those whose next unrolling is expected to exceed the instances allowed
    with [--rec_instances], then those at the limit set with
    [--rec_unrollings]. *)
val request :
  Analysis.param -> string -> Scope.t list ->
  [ `Requested | `At_limit of Scope.t list * Scope.t list ]

(** The functions requested to be unrolled further *)
val requested : unit -> Scope.t list

(** The recursive functions the counterexample to the property may be
    spurious for: a cutoff of theirs is reached by the counterexample, and
    the counterexample is not known to be genuine. It is genuine if the
    functions as they are violate the property with the inputs of the
    counterexample. The supervisor asks a solver for a violation with those
    inputs, evaluates the calls past the unrollings the model executes at
    their concrete arguments, with the definitions of the functions in a
    solver of their own, gives their values back to the query as facts, and
    asks again, until the model only executes calls it knows the values of
    (genuine) or there is no violation left (spurious). A function without a
    definition, a call that cannot be evaluated or a query that cannot be
    decided in time, or a round whose checks have taken their budget, leave
    the counterexample suspect. The supervisor is meant to call this. *)
val suspect :
  TransSys.t -> string -> (StateVar.t * Model.value list) list -> Scope.t list

(** Whether the property was given up on *)
val is_exhausted : string -> bool

(** Whether every property of the system is proved, disproved or given up
    on *)
val all_settled : TransSys.t -> bool
