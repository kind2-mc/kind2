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

open Lib




(** Gathers the contracts, the actions a strategy can perform on the
    underlying smt solver used for test generation, and some data a
    strategy generates tests from. *)
type 'data context




(** Signature for test generation strategies.
    The idea is let the strategy work on the solver ([work] function)
    using the actions on the solver given by an [actions] record.
    Function [work] returns [false] if it is ot done, i.e. the system
    should be unrolled and [work] called again. *)
module type Sig = sig

  (** Type for the data of the strategy. *)
  type data

  (** Prefix which should be unique to a strategy. The supervisor
      should check that no two strategy have the same prefix to avoid
      test-case filename collisions. *)
  val prefix : string

  (** Name of the strategy, for logging. *)
  val name : string

  (** Creates a context for this strategy. *)
  val mk_context :
    (** Transition system we are generating tests for. *)
    TransSys.t ->
    (** Asserts actlit implications function. *)
    ( (StateVar.t * Term.t) list -> unit ) ->
    (** Checksat and get-model function. *)
    ( StateVar.t list -> Model.t option ) ->
    (** Trace comment function. *)
    ( string -> unit ) ->
    (** Result is a strategy-specific context. *)
    data context


  (** Returns true if the strategy requires succeeding input tuples
      to be different. *)
  val no_stuttering : bool

  (** Works on the k^th unrolling of the system. Returns [false] if
      the strategy is not done, i.e. its handler should unroll the
      system further and call this function again. *)
  val work : data context -> Numeral.t -> bool

end


(* |===| First class strategy modules. *)

(** First class dummy strategy module. *)
val dummy : (module Sig)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
