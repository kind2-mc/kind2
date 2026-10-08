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

(* Deleting a solver and killing it from outside do not both dispose of
   its process.

   [SMTSolver.delete_instance] used to test whether the solver was still
   registered and then take it out of the registry under two separate
   acquisitions of the lock. The supervisor, with
   [kill_solvers_of_domain], could take the solver out and kill its
   process in between, and the owner then went on to send [(exit)] to a
   dead process and wait for a child that was already reaped. The test
   and the removal now happen under one acquisition.

   The window is a few instructions wide, and a killer that spins on the
   registry lands in it in about one round in eight. The drivers tolerate
   most of what the owner then does to the dead process, so the double
   disposal rarely shows: this is a guard that whatever either side does
   to a solver the other has taken neither raises nor warns, not a test
   that fails for certain without the fix. *)

open TestSolverCommon

(* The warnings logged while [f] runs *)
let warnings_of f =
  let buffer = Buffer.create 256 in
  let ppf = !Lib.log_ppf in
  let level = Lib.get_log_level () in
  Lib.log_ppf := Format.formatter_of_buffer buffer ;
  Lib.set_log_level L_warn ;
  let result =
    Fun.protect
      ~finally:(fun () ->
        Format.pp_print_flush !Lib.log_ppf () ;
        Lib.log_ppf := ppf ;
        Lib.set_log_level level)
      f
  in
  result, Buffer.contents buffer

(* Solvers created and deleted while the killer runs. Each one is a
   solver process started and stopped, which bounds the count. *)
let rounds = 200

let test_delete_and_kill_do_not_both_dispose _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  (* As Kind 2 does: an [(exit)] written to a solver that is gone fails
     the write instead of killing the test with SIGPIPE *)
  TermLib.Signals.ignore_sigpipe () ;
  let owner = (Domain.self () :> int) in
  let stop = Atomic.make false in
  (* The supervisor, killing the solvers of this domain as fast as it can *)
  let killer =
    Domain.spawn (fun () ->
      while not (Atomic.get stop) do
        SMTSolver.kill_solvers_of_domain owner
      done)
  in
  let (), warnings =
    warnings_of (fun () ->
      Fun.protect
        ~finally:(fun () -> Atomic.set stop true ; Domain.join killer)
        (fun () ->
          for _ = 1 to rounds do
            let solver = new_solver () in
            SMTSolver.delete_instance solver
          done))
  in
  assert_equal ~printer:Fun.id "" warnings

let tests = "SolverDeleteRace" >::: [
  "delete and kill do not both dispose" >:: test_delete_and_kill_do_not_both_dispose ;
]

let () = run_test_tt_main tests
