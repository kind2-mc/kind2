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
   its process, and between them they close its pipes.

   [SMTSolver.delete_instance] used to test whether the solver was still
   registered and then take it out of the registry under two separate
   acquisitions of the lock. The supervisor, with
   [kill_solvers_of_domain], could take the solver out and kill its
   process in between, and the owner then went on to send [(exit)] to a
   dead process and wait for a child that was already reaped. The test
   and the removal now happen under one acquisition.

   The killer leaves the pipes of the solvers it kills open, since their
   owner may be reading them. The owner closes them when it deletes the
   solver. It used to leave them open, three descriptors for every
   solver killed from outside.

   A killer that spins on the registry takes about half the solvers
   here, a few of them inside the window. The drivers tolerate most of
   what the owner did to a dead process, so the double disposal itself
   rarely showed. The pipes left open do: they are counted, and enough
   rounds without the fix exhaust a low limit on open files. *)

open TestSolverCommon

(* Solvers created and deleted while the killer runs. Each one is a
   solver process started and stopped, which bounds the count. *)
let rounds = 200

(* The number of descriptors this process has open, where the kernel
   lists them *)
let open_descriptors () =
  match Sys.readdir "/proc/self/fd" with
  | fds -> Some (Array.length fds)
  | exception Sys_error _ -> None

let test_delete_and_kill_do_not_both_dispose _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  let before = open_descriptors () in
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
  assert_equal ~printer:Fun.id "" warnings ;
  (* The killer is joined: nothing else opens or closes descriptors *)
  match before, open_descriptors () with
  | Some before, Some after ->
    assert_equal ~printer:string_of_int ~msg:"open descriptors" before after
  | _ -> ()

let tests = "SolverDeleteRace" >::: [
  "delete and kill do not both dispose" >:: test_delete_and_kill_do_not_both_dispose ;
]

let () = run_test_tt_main tests
