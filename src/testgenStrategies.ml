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

module Svar = StateVar
type svar = Svar.t
type actlit = svar
type term = Term.t
type model = Var.t * term
type k = Numeral.t




(* Gathers the contracts, the actions a strategy can perform on the
   underlying smt solver used for test generation, and some data a
   strategy generates tests from. *)
type data context = {

  (* Contracts of the system we are generating tests for. *)
  contracts : (svar * string) list ;

  (* Asserts implications between some state variables --actlits--
     and some terms. Typically:
     function l -> assert(
       and(
         map(l, (fun (sv,t) -> implies(sv,t)))
       )
     ) *)
  actlit_implications : (actlit * term) list -> unit ;

  (* Checksats assuming some activation literals. Returns Some of the
     model if sat and None otherwise. *)
  checksat_getmodel : actlit list -> model option ;

  (* Prints a comment in the trace of the smt solver. *)
  trace_comment : string -> unit ;

  (* Strategy specific data. *)
  data : data ;

}



(* |===| Deconstruction helpers for [context]. *)


(* Calls the [actlit_implications] field of a [context] on its input
   list of actlit / term pair. *)
let activate { actlit_implications } = actlit_implications

(* Calls the [checksat_getmodel] field of a [context] on its input
   list of actlits. *)
let model { checksat_getmodel } = checksat_getmodel

(* Calls the [trace_comment] field of a [context] on its input
   string. *)
let comment { trace_comment } = trace_comment




(* Signature for test generation strategies.
   The idea is let the strategy work on the solver ([work] function)
   using the actions on the solver given by an [actions] record.
   Function [work] returns [false] if it is ot done, i.e. the system
   should be unrolled and [work] called again. *)
module type Sig = sig

  (* Type for the data of the strategy. *)
  type data

  (* Prefix which should be unique to a strategy. The supervisor
     should check that no two strategy have the same prefix to avoid
     test-case filename collisions. *)
  val prefix : string

  (* Creates a context for this strategy. *)
  val mk_context :
    (* Contracts. *)
    (svar * string) list ->
    (* Asserts actlit implications function. *)
    ( (actlit * term) list -> unit ) ->
    (* Checksat and get-model function. *)
    ( actlit list -> model option ) ->
    (* Trace comment function. *)
    ( string -> unit ) ->
    (* Result is a strategy-specific context. *)
    data context


  (* Returns true if the strategy requires succeeding input tuples
     to be different. *)
  val no_stuttering : bool

  (* Works on the k^th unrolling of the system. Returns [false] if
     the strategy is not done, i.e. its handler should unroll the
     system further and call this function again. *)
  val work : data context -> k -> bool

end


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
