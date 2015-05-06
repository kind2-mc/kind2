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

module Svar = StateVar
type svar = Svar.t
type actlit = UfSymbol.t
type term = Term.t
type model = Model.t
type values = (Term.t * Term.t) list
type k = Numeral.t
type contract = term


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

  (* Generates test cases using a get_model function. *)
  val testcase_gen : string -> (
    string -> string -> string -> string list -> unit
  ) -> data context -> (
    actlit list -> model option
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

  let max_k () = Flags.testgen_len () |> Numeral.of_int

  let work context k =

    let extended_data = extend_contract_testcases context k in
    context.data <- extended_data ;

    (* Format.printf
      "Testcase(s) at %a:@.  @[<v>%a@]@.@."
      Numeral.pp_print_numeral k
      (pp_print_contract_testcases_named context.sys) extended_data ; *)

    Numeral.( k >= max_k () )

  let testcase_gen dir pp_testcase context get_model =

(*     let testcase_tree =
      context.data |> List.map (fun (act,k,tc) ->
        act, k, (
          unroll_test_case [] Numeral.(k + one) tc |> List.rev
        )
      ) |> testcases_to_tree context.sys
    in

    let stdfmt = Format.formatter_of_out_channel stdout in
    Format.pp_set_margin stdfmt 1000000000 ;
    Format.pp_set_max_indent stdfmt 100000000000 ;

    Format.fprintf
      stdfmt "Reachable contracts:@,@[<v>%a@]@.@."
      pp_print_tree testcase_tree ; *)

    let gv_file = "./graph.dot" in
    let gv_file =
      Unix.openfile
        gv_file [ Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT ] 0o640
    in
    let gv_fmt =
      Unix.out_channel_of_descr gv_file |> Format.formatter_of_out_channel
    in

    Format.fprintf gv_fmt
      "digraph mode_graph {@.  \
       @[<v>" ;

    let names_of = List.fold_left
      ( fun l svar -> match
          TransSys.mode_names_of_req_svar context.sys svar
        with
        | None -> assert false
        | Some names -> names @ l )
      []
    in

    context.data |> List.fold_left (fun cpt ( (actlit,k,testcase) as tc) ->
      (* Format.printf "Test case number %d:@." cpt ; *)

      let to_graph testcase =
        let rec loop (kay, svars) = function
        | ((kay', svars') as pair) :: tail ->
          let name = names_of svars |> String.concat "__" in
          if Numeral.(kay = pred kay') then (
            let name' = names_of svars' |> String.concat "__" in
            Format.fprintf gv_fmt
              "  %s__%a -> %s__%a [label = \"%d\"];@,"
              name Numeral.pp_print_numeral kay
              name' Numeral.pp_print_numeral kay' cpt ;
            loop pair tail
          ) else (
            let kay' = Numeral.succ kay in
            Format.fprintf gv_fmt
              "  %s__%a -> %s__%a [label = \"%d\"];@,"
              name Numeral.pp_print_numeral kay
              name Numeral.pp_print_numeral kay' cpt ;
            loop (kay', svars) (pair :: tail)
          )
        | [] ->
          if Numeral.(kay = k) then () else (
            let kay' = Numeral.succ kay in
            let name = names_of svars |> String.concat "__" in
            Format.fprintf gv_fmt
              "  %s__%a -> %s__%a [label = \"%d\"];@,"
              name Numeral.pp_print_numeral kay
              name Numeral.pp_print_numeral kay' cpt ;
            loop (kay', svars) []
          )
        in

        match List.rev testcase with
        | [] -> failwith "empty testcase"
        | head :: tail -> loop head tail
      in

      Format.printf "to graph (%a)@." Numeral.pp_print_numeral k;
      to_graph testcase ;
      Format.printf "done@." ;

      let name = Format.sprintf "test_case_%d" cpt in

      let out_file = Format.sprintf "%s/%s.csv" dir name in

      description_of_contract_testcase context.sys tc
      |> pp_testcase out_file name "csv" ;

      let file =
        Unix.openfile
          out_file [ Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT ] 0o640
      in

      let out_fmt =
        Unix.out_channel_of_descr file |> Format.formatter_of_out_channel
      in

      ( match get_model [ actlit ] with
        | None -> assert false
        | Some model ->
          (* Format.printf
            "Test case of length %a activating@. @[<v>%a@]@."
            Numeral.pp_print_numeral k
            (pp_print_contract_testcase_named context.sys) testcase ;
          Format.printf "is@." ; *)
          (* Format.printf "Inputs:@." ; *)
          cex_to_inputs_csv out_fmt context.sys model k
          (* Format.printf "Outputs:@." ; *)
          (* cex_to_outputs_csv context.sys model k ; *)
          (* Format.printf "@." ; *) ) ;

      Format.fprintf out_fmt "@?" ;
      Unix.close file ;

      cpt + 1
    ) 0 |> ignore ;

    Format.fprintf gv_fmt "@]@.}@.@.@?" ;

(*     let testcase_tree =
      context.data |> List.map (fun (act,k,tc) ->
        act, k, (
          unroll_test_case [] Numeral.(k + one) tc |> List.rev
        )
      ) |> testcases_to_tree context.sys
    in

    let stdfmt = Format.formatter_of_out_channel stdout in
    Format.pp_set_margin stdfmt 1000000000 ;
    Format.pp_set_max_indent stdfmt 100000000000 ;

    Format.fprintf
      stdfmt "Reachable contracts:@,@[<v>%a@]@.@."
      pp_print_tree testcase_tree ; *)

    ()


end

(* First class unit mode switch module. *)
let unit_mode_switch = (module Unit_ModeSwitch : Sig)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
