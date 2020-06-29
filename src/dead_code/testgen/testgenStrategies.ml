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


(* Lifting the context type from TestgenLib. *)
type 'data context = 'data TestgenLib.context


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

  (* The directory that will contain the test cases. *)
  val out_dir : string

  (* Returns true if the strategy requires succeeding input tuples
     to be different. *)
  val no_stuttering : bool

  (* Returns true if the strategy requires subsystems to be abstracted. *)
  val abstract_subsystems : bool


  (* Creates a context for this strategy. *)
  val mk_context :
    (* Transition system. *)
    TransSys.t ->
    (* Declares a UF. *)
    ( actlit -> unit ) ->
    (* Asserts actlit implications function. *)
    ( ?eq:bool -> (actlit * term) list -> unit ) ->
    (* Checksat and get-values function. *)
    ( actlit list -> term list -> values option ) ->
    (* Trace comment function. *)
    ( string -> unit ) ->
    (* Result is a strategy-specific context. *)
    data context


  (* Works on the k^th unrolling of the system. Returns [false] if
     the strategy is not done, i.e. its handler should unroll the
     system further and call this function again. *)
  val work : data context -> k -> bool

  (** Generates test cases using a get_model function. *)
  val testcase_gen : string -> (
    string -> string -> string -> string list -> unit
  ) -> data context -> (
    UfSymbol.t list -> model option
  ) -> unit

end




(* Dummy strategy module. *)
module Dummy : Sig = struct

  let prefix = "dummy"
  let name = "dummy"
  let out_dir = "dummy"
  let no_stuttering = false
  let abstract_subsystems = false

  (* No data. *)
  type data = unit

  (* We'll just do nothing for 5 steps. *)
  let five = Numeral.of_int(5)

  (* Passing stuff to the context constructor helper. *)
  let mk_context = mk_context ()

  let last_k = ref Numeral.zero

  (* Dummy work function. *)
  let work context k =
    last_k := k ;
    Numeral.( k >= five )

  let testcase_gen _ _ context get_model =
    match get_model [] with
    | None ->
      Format.printf "No test case generated.@."
    | Some(model) ->
      Format.printf
        "Logging test cases.@." ;
      cex_to_inputs_csv Format.std_formatter context.sys model !last_k


end

(* First class dummy strategy module. *)
let dummy = (module Dummy : Sig)







(* Generates test cases activating different contracts of a system. *)
module Unit_ModeSwitch : Sig = struct

  let prefix = "unit_mode_switch"
  let name = "[unit] mode switch"
  let out_dir = "unit"

  let no_stuttering = false
  let abstract_subsystems = false

  type data = contract_testcases

  let mk_context sys declare activate get_values comment =
    (* We start with a fresh actlit for the empty path. *)
    let empty_path_actlit = Actlit.fresh_actlit () in
    (* Declaring it. *)
    comment "Declaring first actlit for empty path." ;
    declare empty_path_actlit ;

    mk_context
      [ (empty_path_actlit, Numeral.(~- one), []) ]
      sys declare activate get_values comment

  let max_k () = Flags.Testgen.len () |> Numeral.of_int

  let work context k =

    let extended_data = extend_contract_testcases context k in
    context.data <- extended_data ;

    (* Format.printf
      "Testcase(s) at %a:@.  @[<v>%a@]@.@."
      Numeral.pp_print_numeral k
      (pp_print_contract_testcases_named context.sys) extended_data ; *)

    Numeral.( k >= max_k () )


  (* Generates test cases using a get_model function. *)
  let testcase_gen = TestgenLib.testcase_gen out_dir

end

(* First class unit mode switch module. *)
let unit_mode_switch = (module Unit_ModeSwitch : Sig)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
