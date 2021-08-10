(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020-2021 by the Board of Trustees of the University of Iowa

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

(** Realizability Checker

    @author Daniel Larraz
*)

type 'a analyze_func =
  Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> unit

type unrealizable_result

(** Result of a realizability check *)
type realizability_result =
  | Realizable of Term.t (* Fixpoint *)
  | Unrealizable of unrealizable_result
  | Unknown

val result_to_string : realizability_result -> string

(** Checks whether there exists an implementation that satisfies a given specification

    [realizability_check s c0 v1 c1] checks whether the specification represented by
    transition system [s] is realizable or not under the assumption that [c0] is
    the list of controllable variables at offset 0, [v1] is the list of variables
    at offset 1, [c1] is the list of variables at offset 1, and all terms in [s]
    without controllable variables are assumed to hold.
*)
val realizability_check :
  TransSys.t ->
  Var.t list ->
  Var.t list ->
  Var.t list ->
  realizability_result


exception Trace_or_core_computation_failed of string

val compute_unviable_trace_and_core :
  'a analyze_func ->
  'a InputSystem.t ->
  Analysis.param ->
  TransSys.t ->
  Var.t list ->
  Var.t list ->
  unrealizable_result ->
  ((StateVar.t * Model.value list) list * ModelElement.loc_core)

