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

(* No solver may outlive Kind 2.

   The sweep before the process exits is only final if nothing can start
   a solver behind it, and something can: an engine the supervisor gave
   up on keeps running in the background. A solver it starts after the
   sweep has nobody left to kill it, and on Windows it holds the
   standard output of Kind 2 open, so whoever reads that output waits
   for an end that never comes. *)

let new_solver () = SMTSolver.create_instance `None `Z3_SMTLIB

(* Whether the solver [new_solver] asks for can be found. The rest of
   the unit suite needs nothing installed, and a checkout without a
   solver should not start failing it. CI installs Z3 on every platform
   it tests, so this skips nowhere that matters. *)
let solver_missing () =
  match Lib.find_on_path (Flags.Smt.z3_bin ()) with
  | _ -> false
  | exception Not_found -> true

(* Reap whatever has exited and report whether a child process is still
   running. The only children here are the solvers created above. *)
let rec no_child_left deadline =
  match Unix.waitpid [ Unix.WNOHANG ] (-1) with
  | exception Unix.Unix_error (Unix.ECHILD, _, _) -> true
  | 0, _ ->
    (* Children are left, and none of them has exited. They may still be
       on their way out, so wait a little before calling it a leak. *)
    if Unix.gettimeofday () > deadline then false
    else ( Unix.sleepf 0.05 ; no_child_left deadline )
  | _ -> no_child_left deadline

let test_no_solver_outlives_the_sweep _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;

  ignore (new_solver ()) ;

  SMTSolver.destroy_all_of_process () ;

  (* Creating one now would leave it running, so it must not be possible *)
  assert_raises SMTSolver.Exiting (fun () -> ignore (new_solver ())) ;

  (* The solver started before the sweep is gone, and so is the one the
     call above got as far as starting. [waitpid] on any child is not
     supported on Windows, where the two assertions above still hold. *)
  if not Sys.win32 then
    assert_bool
      "a solver process was left running"
      (no_child_left (Unix.gettimeofday () +. 5.))

let tests = "SolverExit" >::: [
  "no solver outlives the sweep" >:: test_no_solver_outlives_the_sweep ;
]

let () = run_test_tt_main tests
