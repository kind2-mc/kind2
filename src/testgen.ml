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

module S = SMTSolver
module Strats = TestgenStrategies

(* Reference to the solver instance. *)
let solver_ref = ref None

(* Turns an actlit uf in a term. *)
let term_of = Actlit.term_of_actlit



(* |===| Functions for the context of the strategy. *)

(* Declares a UF. *)
let declare solver = S.declare_fun solver

(* Builds actlit implications and asserts them. *)
let actlit_implications solver = function
  | [] -> ()
  | impls -> impls |> List.map (
      fun (uf, term) -> Term.mk_implies [ term_of uf ; term ]
    ) |> List.iter (S.assert_term solver)

(* Checksats and returns [Some] of the values of [terms] if sat, [None]
   otherwise. *)
let checksat_getvalues solver actlits terms =
  S.check_sat_assuming
    solver
    ( fun () -> Some (S.get_term_values solver terms) )
    ( fun () -> None )
    ( actlits |> List.map ( fun uf -> term_of uf ) )

(* Checksats and returns [Some] of the model if sat, [None] otherwise. *)
let checksat_getmodel solver actlits =
  S.check_sat_assuming
    solver
    ( fun () -> Some (S.get_model solver) )
    ( fun () -> None )
    ( actlits |> List.map ( fun uf -> term_of uf ) )

(* Prints a comment in the solver trace. *)
let comment solver = S.trace_comment solver

(* Deletes the solver and unsets the reference. *)
let delete_solver () =
  try match !solver_ref with
  | None -> ()
  | Some solver ->
    Format.printf "Deleting solver, resetting reference.@." ;
    SMTSolver.delete_instance solver |> ignore ;
    solver_ref := None
  with
  | e ->
    Event.log
      L_debug
      "TestGen @[<v>Error while deleting solver:@ %s@]"
      (Printexc.to_string e)


(* Runs a strategy until it says it's done. *)
let run_strategy sys strategy =

  (* Retrieving the strategy module. *)
  let module Strat = (val strategy : TestgenStrategies.Sig) in

  Format.printf
    "Starting run for strategy %s.@."
    Strat.name ;

  (* Failing if there is already a solver referenced. *)
  assert (!solver_ref = None) ;

  (* Creating a new solver for this run. *)
  let solver =
    S.create_instance
      ~produce_assignments:true
      (TransSys.get_scope sys)
      (TransSys.get_logic sys)
      (TransSys.get_abstraction sys)
      (Flags.smtsolver ())
  in

  (* Memorizing solver for clean exit. *)
  solver_ref := Some solver ;

  (* Initializing solver. *)
  TransSys.init_solver
    sys
    (comment solver)
    (S.define_fun solver)
    (S.declare_fun solver)
    (S.assert_term solver)
    Numeral.zero Numeral.zero ;

  (* Creating a context for the strategy. *)
  let context =
    Strat.mk_context
      sys
      (declare solver)
      (actlit_implications solver)
      (checksat_getvalues solver)
      (comment solver)
  in

  (* Runs the strategy at [k], and loops after unrolling the system
     if the strategy is not done. *)
  let rec loop_strategy k =

    Format.printf
      "At iteration %a on strategy %s.@."
      Numeral.pp_print_numeral k
      Strat.name ;

    (* Letting strategy work at [k]. *)
    let is_done = Strat.work context k in

    (* Looping if not done. *)
    if not is_done then (

      (* Increment [k]. *)
      let k = Numeral.succ k in

      (* Declare variables at [k]. *)
      TransSys.declare_vars_of_bounds
        sys
        (SMTSolver.declare_fun solver)
        (SMTSolver.assert_term solver)
        k k ;

      (* Unroll at k. *)
      TransSys.trans_of_bound sys k
      |> SMTSolver.assert_term solver ;

      loop_strategy k
    )

    (* Returning the [k] otherwise. *)
    else k

  in

  (* Going to loop, starting at zero. *)
  let final_k = loop_strategy Numeral.zero in

  (* Generating testcases. *)
  checksat_getmodel solver |> Strat.testcase_gen context ;

  (* Deleting solver, resetting solver reference. *)
  delete_solver () ;

  Format.printf
    "Strategy %s is done at %a.@."
    Strat.name
    Numeral.pp_print_numeral final_k


let main sys =

  run_strategy sys Strats.dummy ;

  Format.printf "@."


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
