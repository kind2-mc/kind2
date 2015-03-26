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
type model = Model.t
type k = Numeral.t




(* Gathers the contracts, the actions a strategy can perform on the
   underlying smt solver used for test generation, and some data a
   strategy generates tests from. *)
type 'data context = {

  (* System we are generating tests for. *)
  sys : TransSys.t ;

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
  data : 'data ;

}

(* Construction helper for [context]. *)
let mk_context
  data
  sys actlit_implications checksat_getmodel trace_comment =
{ sys = sys;
  actlit_implications = actlit_implications ;
  checksat_getmodel = checksat_getmodel ;
  trace_comment = trace_comment ;
  data = data ; }



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




(* |===| Counterexample to inputs csv. *)

let cex_to_inputs_csv sys cex k = match TransSys.get_source sys with
  | TransSys.Lustre nodes ->
    let path =
      Model.path_from_model (TransSys.state_vars sys) cex k
    in
    Format.printf
      "  @[<v>%a@]@."
      (LustrePath.pp_print_path_inputs_csv nodes true) path
  (* Not supporting non lustre sources. *)
  | _ -> assert false


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

  (* The name of the strategy, used for logging. *)
  val name : string

  (* Creates a context for this strategy. *)
  val mk_context :
    (* Transition system. *)
    TransSys.t ->
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


(* Dummy strategy module. *)
module Dummy : Sig = struct

  let prefix = "dummy"
  let name = "dummy"

  (* No data. *)
  type data = unit

  (* We'll just do nothing for 5 steps. *)
  let five = Numeral.of_int(5)

  (* Passing stuff to the context constructor helper. *)
  let mk_context = mk_context ()

  (* Stuttering's fine. *)
  let no_stuttering = false

  (* Dummy work function. *)
  let work context k =

    if Numeral.( k >= five )

    then (
      ( match model context [] with
        | Some cex ->
          Format.printf "@.Test case \\(^o^)/@." ;
          cex_to_inputs_csv context.sys cex k
        | None ->
          Format.printf "No test case /(T_T)\\@." ) ;
      true
    )

    else false

end

(* First class dummy strategy module. *)
let dummy = (module Dummy : Sig)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
