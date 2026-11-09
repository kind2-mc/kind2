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

(** Finiteness of sets and maps, applied when a counterexample needs it

    Sets and maps are finite, but they are encoded as arrays, which may be
    infinite. The difference only shows in a counterexample to a property
    whose cone of influence has a quantifier observing a container of an
    infinite element type (see {!LustreTypeChecker.finite_risk_types}).
    The containers of those types are compiled with constraints that make
    them finite (see {!LustreNode.finite_constraints}), which cost the
    solvers, and that a proof does not need: the encoding without them has
    more behaviors than the model, so what holds of the one holds of the
    other.

    A system is therefore first built without them. A counterexample found
    on it, to a property whose cone of influence they would constrain, may
    rely on an infinite container: it is held back, and checked on the
    system with the constraints, sliced to the property, for one with the
    same inputs, which is reported instead if found in time. Otherwise the
    engines run again on the system built with the constraints, with what
    they had established carried over (see [InvarManager] and [Kind2Flow]);
    this is not an analysis of its own. From then on, every system built for
    the same top system has them.

    This module keeps the top systems whose systems have the constraints,
    the systems that were built without some, and the request made by a
    counterexample in the analysis under way. *)

(** Whether the systems built for the top system [top] have the finiteness
    constraints of their containers *)
val enabled : Scope.t -> bool

(** Give the finiteness constraints of their containers to the systems
    built from now on for the top system [top] *)
val enable : Scope.t -> unit

(** [with_enabled f] is [f ()], where the systems built in the calling
    domain have the finiteness constraints whatever their top system: for
    the check of a counterexample found without them *)
val with_enabled : (unit -> 'a) -> 'a

(** Record that the system was built without the finiteness constraints
    of some of the containers it has *)
val note_omitted : TransSys.t -> unit

(** Whether the system was built without the finiteness constraints of
    some of the containers it has *)
val omitted : TransSys.t -> bool

(** Forget the request, and the time spent checking counterexamples:
    the engines are about to run on a system *)
val start_round : unit -> unit

(** Whether the counterexamples of the round may still be checked on the
    system with the finiteness constraints, rather than the engines running
    again on it *)
val within_check_budget : unit -> bool

(** Count the time spent checking a counterexample on the system with the
    finiteness constraints *)
val spent_checking : float -> unit

(** The time limit of the solver checking a counterexample, in seconds *)
val check_timeout : int

(** Request that the engines run again on the system built with the
    finiteness constraints, for the counterexample to a property that may
    rely on an infinite container *)
val request : unit -> unit

(** Whether a counterexample requested the finiteness constraints in the
    round under way *)
val requested : unit -> bool
