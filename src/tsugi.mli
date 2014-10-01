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

open Lib
open TypeLib

(** Enumerated type to select the mode BMC is launched into. *)
type bmc_mode = | Base | Step

(** Type returned by a single iteration of bmc. Fields: 'k' is the
    iteration this result correponds to; 'unfalsifiable' are the
    properties which cannot be falsified for 'k'; 'falsifiable' are
    the properties which can be falsified for 'k', along with the
    witness model; 'falsifiable_no_model' is the same as 'falsifiable'
    but without the models ; 'continue' is the function to call for
    the next iteration with the properties to prove and the new
    invariants. *)
type walk_bmc_result = {
  (* K corresponding to this result. *)
  k : Numeral.t ;
  (* Properties the negation of which is unsat at k. *)
  unfalsifiable : properties ;
  (* Properties the negation of which is sat at k, with models. *)
  falsifiable : cexs ;
  (* Properties the negation of which is sat at k, no models. *)
  falsifiable_no_model : properties ;
  (* Continuation for the next bmc iteration. *)
  continue : properties -> invariants -> walk_bmc_result
}



(** Signature for actlit modules for the make functor. Creates
    'positive' activation literals from terms, and 'negative'
    activation literals from a depth (k) and a term. Both MUST
    be injective. *)
module type InActlit = sig

  (** Creates a positive actlit as a UF. *)
  val positive : Term.t -> UfSymbol.t

  (** Creates a negative actlit as a UF. *)
  val negative : Numeral.t -> Term.t -> UfSymbol.t

end


(** Signature for the counterexamples extraction functions. *)
module type InPathExtractor = sig

  val generic: TransSys.t ->
               (Var.t list -> (Var.t * Term.t) list) ->
               Numeral.t ->
               path

  (** Extracts a counterexample for the base instance. *)
  val base : TransSys.t ->
             (Var.t list -> (Var.t * Term.t) list) ->
             Numeral.t ->
             path

  (** Extracts a counterexample for the step instance. *)
  val step : TransSys.t ->
             (Var.t list -> (Var.t * Term.t) list) ->
             Numeral.t ->
             path

end

(** Signature for communication modules. *)
module type InComm = sig

  (** Communicates results from the base instance. First argument are
      the unfalsifiable properties. Second one are the falsifiable
      ones with counterexamples. *)
  val base : TransSys.t -> Numeral.t -> properties -> cexs -> unit

  (** Communicates results from the step instance. First argument are
      the unfalsifiable properties. Second one are the falsifiable
      ones with counterexamples. *)
  val step : TransSys.t -> Numeral.t -> properties -> cexs -> unit

  (** Gets new invariants from the rest of the framework. *)
  val new_invariants : unit -> Term.t list

end



(** Signature for the output of the functor. *)
module type Out = sig

  (** Runs a BMC loop either in Base or Step mode. *)
  val run_bmc : bmc_mode -> TransSys.t -> unit

  (** A single BMC iteration, either in Base or Step mode. Starts at k
      = 0 and returns the result of the iteration and a
      continuation. *)
  val walk_bmc : bmc_mode -> TransSys.t -> properties -> walk_bmc_result

end 

(** Functor to create a BMC module. *)
module Make (Actlit: InActlit)
            (Comm: InComm)
            (PathExtract: InPathExtractor) : Out

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

