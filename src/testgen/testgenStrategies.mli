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
open TestgenLib



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

  (* The directory that will contain the test cases. *)
  val out_dir : string

  (** Returns true if the strategy requires succeeding input tuples
      to be different. *)
  val no_stuttering : bool

  (** Returns true if the strategy requires subsystems to be abstracted. *)
  val abstract_subsystems : bool


  (** Creates a context for this strategy. *)
  val mk_context :
    (** Transition system we are generating tests for. *)
    sys ->
    (** Declares a UF. *)
    ( actlit -> unit ) ->
    (** Asserts actlit implications function. *)
    ( ?eq:bool -> (actlit * term) list -> unit ) ->
    (** Checksat and get-values function. *)
    ( actlit list -> term list -> values option ) ->
    (** Trace comment function. *)
    ( string -> unit ) ->
    (** Result is a strategy-specific context. *)
    data context


  (** Works on the k^th unrolling of the system. Returns [false] if
      the strategy is not done, i.e. its handler should unroll the
      system further and call this function again. *)
  val work : data context -> k -> bool

(** Generates the actual test cases in csv using a [get-model] function.
    Arguments:
    - the directory to write the test case in,
    - a formatter to the xml file aggregating the test cases,
    - the context of the test generation strategy,
    - the [get-model] function. *)
  (** Generates test cases using a get_model function. *)
  val testcase_gen : string -> (
    string -> string -> string -> string list -> unit
  ) -> data context -> (
    actlit list -> model option
  ) -> unit

end


(* |===| First class strategy modules. *)

(** First class dummy strategy module. *)
val dummy : (module Sig)

(** First class unit mode switch module. *)
val unit_mode_switch : (module Sig)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
