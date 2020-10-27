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

(** A strategy returns an [Analysis.param option] which is [None] if done.
    It takes
    - the results so far, and
    - a list of scope / [bool] pairs with the scopes sorted in topological
      order, starting from the top-most one. Booleans indicate whether the
      corresponding system can be abstracted. *)

module A = Analysis

(** Information used by the strategy module. *)
type info = {
  (** Is the system refineable? ([extern] for lustre nodes.) *)
  can_refine: bool ;
  (** Does the system have a contract? *)
  has_contract: bool ;
  (** Does the system have modes? *)
  has_modes: bool ;
}

(** Takes some results and some information about (sub)systems, and returns
the next analysis to perform, if any.
The information it takes is

- a function which, given the scope of a system, returns the scope of its
  direct subsystems and its strategy info;
- a list of all the scopes of all the systems and their strategy info. *)
val next_analysis:
  A.results ->
  (Scope.t -> (Scope.t * info) list) ->
  (Scope.t * info) list ->
  A.param option

(** Takes information about a (sub)system, and returns
whether the subsystem is candidate for analysis
*)
val is_candidate_for_analysis : info -> bool

(** Works almost the same as [next_analysis], but returns a single analysis
parameter for a monolithic analysis. Only used for contract generation. *)
val monolithic:
  (Scope.t * info) list -> A.param option



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
