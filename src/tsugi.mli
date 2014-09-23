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

(* Tsugi stands for Transition System Unroller for Generalized
   Induction. It is a functor designed to perform BMC checks in order
   to implement k-induction. *)

open TypeLib

(** Type returned by a single iteration of bmc: 'k' is the k this
    result corresponds to; 'unsat_at_k' are the properties the
    negation of which is unsat at k; 'sat_at_k' are the properties the
    negation of which is sat at k with their respective models;
    'sat_no_model' is the same as 'sat_at_k' without the models;
    'continue' is a continuation launching the next bmc iteration. *)
type walk_bmc_result = {
  k : Numeral.t ;
  unsat_at_k : properties ; sat_at_k : cexs ; sat_no_model : properties ;
  continue : properties -> invariants -> walk_bmc_result
}

(** Input signature for the Make functor. *)
module type BmcFunctions =
sig

  (** Initializes the solver. Typically base would assert Init while
      Step would do nothing. *)
  val init : unit -> Term.t list

  (** Handles the result of the BMC check for this k, and returns the
      new invariants of the system. Arguments: the transition system;
      the current k value; properties the negation of which is unsat
      at k; properties the negation of which is sat at k. Returns new
      invariants. *)
  val stage_next :
    TransSys.t -> Numeral.t ->
    (string * Term.t) list ->
    ((string * Term.t) list * model) list ->
    invariants

end

(** Output signature of the Make functor. *)
module type S =
sig

  (** A single BMC iteration, starts at k=0. Parameters: the
      transition system; invariants on the system; the properties to
      check. *)
  val walk_bmc :
    TransSys.t -> invariants -> properties -> walk_bmc_result

  (** Runs the BMC loop. Parameters: the transition system, invariants
      on the system; the properties to check. NEVER RETURNS. *)
  val run_bmc :
    TransSys.t -> invariants -> properties -> unit

end

(** Functor to create a BMC module. Parameters: 'Implementation'
    implements the function defining base or step, for k-induction
    proof checks; 'Slvr' the solver module to use. *)
module Make (Implementation: BmcFunctions) (Slvr: SMTSolver.S) : S
