(* This file is part of the Kind 2 model checker.

   Copyright (c) 2017-2018, 2021 by the Board of Trustees of the University of Iowa

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

(** Representation and generation of assumptions required for proving system properties

    @author Daniel Larraz
*)

(** Temporal assumption *)
type t

(** The assumption that does no impose any contraints over the variables

    The initial state predicate and the transition relation predicate are both true
*)
val empty : t

(** Return true if the given assumption is the empty assumption *)
val is_empty : t -> bool

(** Return the set of state variables in the initial state predicate *)
val state_vars_of_init : t -> StateVar.StateVarSet.t

(** Return the set of state variables in the transition relation predicate *)
val state_vars_of_trans : t -> StateVar.StateVarSet.t

(** Return a new assumption with each state variable replaced using the given map *)
val map_vars : (StateVar.t -> StateVar.t) -> t -> t

(** Return a Lustre expression representation of the given assumption *)
val lustre_assumption : t -> LustreExpr.t


(** Function that receives an input system, a scope, and a set of variables,
    and returns all the elements of the set that satisfies some criterion
*)
type 'a variable_filter_func = 'a InputSystem.t -> Scope.t -> Var.t list -> Var.t list

(** Return non-input variables *)
val filter_non_input: 'a variable_filter_func

(** Return non-output variables *)
val filter_non_output: 'a variable_filter_func

(** Filter functions for current and next values, respectively *)
type 'a pair_of_filters = ('a variable_filter_func * 'a variable_filter_func)

type response =
  | Success of t
  | Failure
  | Unknown

(** Return a [Success] response with a permissive non-trivial assumption that makes
    the given property valid (if any exists), [Failure] if none exists, or
    [Unknown] if some resource ran out.
*)
val generate_assumption_vg:
  'a InputSystem.t -> TransSys.t -> 'a pair_of_filters -> Property.t -> response

type 'a analyze_func =
  bool -> bool -> 
  Lib.kind_module list ->
  'a InputSystem.t ->
  Analysis.param ->
  TransSys.t ->
  unit

val generate_assumption:
  ?one_state:bool ->
  'a analyze_func ->
  'a InputSystem.t ->
  Analysis.param ->
  TransSys.t ->
  response

(** Dump a given assumption as an assume of a CoCoSpec contract into a file
.
    [dump_assumption i s a f c] receives an assumption [a] for Lustre node [s]
    from input system [i], and dumps the assumption [a] as an assume of
    a contract [c] in file [f].
*)
val dump_contract_for_assumption:
  'a InputSystem.t -> Scope.t -> t -> string -> string -> unit

