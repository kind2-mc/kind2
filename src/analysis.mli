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

(** Interface between strategy and low-level analysis 

    An analysis distinguishes exactly one system as the top system,
    and looks at its properties and its contract. Subsystems are view
    either as abstract with their contract or as concrete with their
    implementations.

    The result of an analysis indicates which properties of the top
    system are invariant, whether the system conforms to its contract
    and whether it conforms to the preconditions of all its
    subsystems. 

    Values of type {!param} are produced by a strategy and
    parameterize the input-specific transitions system generators, in
    particular the slicing ot the cone of influence.

    Values of type {!result} are produced by running an analysis of a
    generated transition system. The accumulated results are used by a
    strategey to decide the next steps.

    **NB:** The [uid] stored in an [info] must be unique because it is
    used during transition system generation to avoid name clashes in
    UFs and svars.

    @author Christoph Sticksel *)

(** Provides a different id every time. *)
val get_uid : unit -> int

(** Type of scope-wise assumptions. *)
type assumptions = Invs.t Scope.Map.t
(** Empty assumptions. *)
val assumptions_empty : assumptions
(** Merges two assumptions. *)
val assumptions_merge : assumptions -> assumptions -> assumptions
(** Assumptions of a transition system. *)
val assumptions_of_sys : TransSys.t -> assumptions
(** Fold over assumptions. *)
val assumptions_fold : (
  'a -> Scope.t -> Invs.t -> 'a
) -> 'a -> assumptions -> 'a

(** Information for the creation of a transition system *)
type info = {
  (** The top system for the analysis run *)
  top : Scope.t ;

  (** UID for the analysis. *)
  uid : int ;

  (** Systems flagged [true] are to be represented abstractly, those flagged
      [false] are to be represented by their implementation. *)
  abstraction_map : bool Scope.Map.t ;

  (** Properties that can be assumed invariant in subsystems *)
  assumptions : assumptions ;

  (** Result of the previous analysis of the top system if this analysis is a
      refinement. *)
  (* refinement_of : result option *)
}

(** Shrinks an abstraction map to the subsystems of a system. *)
val shrink_info_to_sys: info -> TransSys.t -> info

(** Parameter of an analysis. *)
type param =
  (** Analysis of the contract of a system. *)
  | ContractCheck of info
  (** First analysis of a system. *)
  | First of info
  (** Refinement of a system. Store the result of the previous analysis. *)
  | Refinement of info * result

(** Result of analysing a transistion system *)
and result = {
  (** Parameters of the analysis. *)
  param : param ;

  (** Runtime of the analysis. *)
  time : float ;

  (** System analyzed, contains property statuses and invariants. *)
  sys : TransSys.t ;

  (** [None] if system analyzed has not contracts,
      [Some true] if it does and they have been proved correct,
      [Some false] if it does and some are unknown / falsified. *)
  contract_valid : bool option ;

  (** [None] if system analyzed has not sub-requirements,
      [Some true] if it does and they have been proved correct,
      [Some false] if it does and some are unknown / falsified. *)
  requirements_valid : bool option ;
}


(* Clones an [info], only changes its [uid]. *)
val info_clone : info -> info

(* Clones a [param], only changes its [uid]. *)
val param_clone : param -> param

(** The info or a param. *)
val info_of_param : param -> info

(** Shrinks a param to a system. *)
val shrink_param_to_sys : param -> TransSys.t -> param

(** Return [true] if a scope is flagged as abstract in the [abstraction_map] of
   a [param]. Default to [false] if the node is not in the map. *)
val param_scope_is_abstract : param -> Scope.t -> bool

(** Retrieve the assumptions of a [scope] from a [param]. *)
val param_assumptions_of_scope : param -> Scope.t -> Invs.t





(** Returns a result from an analysis. *)
val mk_result : param -> TransSys.t -> float -> result

(** Returns true if all properties in the system in a [result] have been
    proved. *)
val result_is_all_proved : result -> bool

(** Returns true if some properties in the system in a [result] have been
    falsified. *)
val result_is_some_falsified : result -> bool




(** Map from [Scope.t] to [result] storing the results found this far. *)
type results

(** Creates a new [results]. *)
val mk_results : unit -> results

(** Adds a [result] to a [results]. *)
val results_add : result -> results -> results

(** Returns the list of results for a top scope.

    Raises [Not_found] if not found. *)
val results_find : Scope.t -> results -> result list

(** Returns the last result corresponding to a scope. *)
val results_last : Scope.t -> results -> result

(** Returns the total number of results stored in a [results]. Used to
    generate UIDs for [param]s. *)
val results_length : results -> int

(** Returns [None] if no properties were falsified but some could not be
    proved, [Some true] if all properties were proved, and [Some false] if
    some were falsified. *)
val results_is_safe : results -> bool option

(** Cleans the results by removing nodes that don't have any property or
contract. *)
val results_clean : results -> results





(** Pretty printer for [param]. *)
val pp_print_param: bool -> Format.formatter -> param -> unit

(** Pretty printer for [result], quiet version. *)
val pp_print_result_quiet: Format.formatter -> result -> unit

(** Pretty printer for [result]. *)
val pp_print_result: Format.formatter -> result -> unit


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
