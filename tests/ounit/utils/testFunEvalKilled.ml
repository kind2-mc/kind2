(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

open OUnit2

(* An evaluator warns that the solver rejected its definitions only when it
   did. When the analysis ends, the supervisor kills the solvers of the
   engines still running, among them that of an evaluator an engine is
   giving the definitions to; its reply then ends early, which fails as a
   rejection would, and was reported as one. [SMTSolver] now raises
   [Killed] for a command to a solver killed from outside. *)

open TestSolverCommon

let uf = UfSymbol.mk_uf_symbol "f" [] Type.t_int

let evaluate define =
  Flags.Smt.set_solver `Z3_SMTLIB ;
  let evaluator =
    FunEval.create ~logic:`None ~timeout_ms:60000 define
  in
  warnings_of (fun () -> FunEval.evaluate evaluator uf [])

let contains s sub =
  let n = String.length sub in
  let rec at i =
    i + n <= String.length s && (String.sub s i n = sub || at (i + 1))
  in
  at 0

(* Wait on [solver] until it is killed from another domain, as the
   supervisor kills it: Z3 answers [get-info] with one S-expression, and the
   second one asked for never comes *)
let wait_until_killed solver =
  (* As Kind 2 does: if the kill comes before the request is written, the
     write fails instead of the whole test being killed by SIGPIPE *)
  TermLib.Signals.ignore_sigpipe () ;
  let owner = (Domain.self () :> int) in
  let killer =
    Domain.spawn (fun () ->
      Unix.sleepf 0.2 ;
      SMTSolver.kill_solvers_of_domain owner)
  in
  Fun.protect ~finally:(fun () -> Domain.join killer) (fun () ->
    SMTSolver.execute_custom_command solver "get-info"
      [ SMTExpr.ArgString ":name" ] 2
    |> ignore)

(* A command cut short by the kill raises [Killed], whichever way it
   failed *)
let test_killed_command_raises_killed _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  let solver = new_solver () in
  assert_raises SMTSolver.Killed (fun () -> wait_until_killed solver) ;
  (* The process is gone: the next command fails on the closed pipe *)
  assert_raises SMTSolver.Killed (fun () -> SMTSolver.push solver)

(* The definitions are cut short by the kill *)
let test_killed_solver_is_not_a_rejection _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  let value, warnings = evaluate wait_until_killed in
  assert_bool "the call was evaluated" (value = `Unknown) ;
  assert_equal ~printer:Fun.id "" warnings

(* A solver that rejects a definition is still reported *)
let test_rejection_is_reported _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  let define solver =
    SMTSolver.declare_fun solver uf ;
    SMTSolver.declare_fun solver uf
  in
  let value, warnings = evaluate define in
  assert_bool "the call was evaluated" (value = `Unknown) ;
  assert_bool
    ("no warning of the rejection in: " ^ warnings)
    (contains warnings "rejected the definitions")

let tests = "FunEvalKilled" >::: [
  "a killed command raises Killed" >:: test_killed_command_raises_killed ;
  "a killed solver is not a rejection" >:: test_killed_solver_is_not_a_rejection ;
  "a rejection is reported" >:: test_rejection_is_reported ;
]

let () = run_test_tt_main tests
