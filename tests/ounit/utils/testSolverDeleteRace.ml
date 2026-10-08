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
   solver, or when it exits through [SMTSolver.destroy_all], as an engine
   stopped this way does. It used to leave them open, three descriptors
   for every solver killed from outside, for every engine of every
   analysis. So did an engine that disposed of its own solvers while the
   analysis was shutting down: they are killed outright then, rather
   than asked to exit, and the pipes to them were left open too.

   A killer that spins on the registry takes about half the solvers
   here, a few of them inside the window. The drivers tolerate most of
   what the owner did to a dead process, so the double disposal itself
   rarely showed. The pipes left open do: they are counted, and enough
   rounds without the fix exhaust a low limit on open files. *)

open TestSolverCommon

(* Solvers created and deleted while the killer runs. Each one is a
   solver process started and stopped, which bounds the count. *)
let rounds = 200

(* The number of descriptors this process has open, where the system
   lists them: [/proc/self/fd] on Linux, [/dev/fd] on macOS, where the
   default limit on open files is the lowest. Listing a directory takes
   a descriptor, counted the same way every time. *)
let open_descriptors () =
  List.find_map
    (fun dir ->
      match Sys.readdir dir with
      | fds -> Some (Array.length fds)
      | exception Sys_error _ -> None)
    [ "/proc/self/fd" ; "/dev/fd" ]

let assert_none_left_open before =
  match before, open_descriptors () with
  | Some before, Some after ->
    assert_equal ~printer:string_of_int ~msg:"open descriptors" before after
  | _ -> ()

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
  assert_none_left_open before

(* An engine that the supervisor stops by killing its solvers does not
   delete them: it exits, through [SMTSolver.destroy_all]. The pipes to
   them are closed then. *)
let test_killed_solvers_are_closed_on_exit _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  let before = open_descriptors () in
  let started = Atomic.make false in
  let stopped = Atomic.make false in
  let engine =
    Domain.spawn (fun () ->
      for _ = 1 to 5 do ignore (new_solver ()) done ;
      Atomic.set started true ;
      while not (Atomic.get stopped) do Domain.cpu_relax () done ;
      SMTSolver.destroy_all ())
  in
  while not (Atomic.get started) do Domain.cpu_relax () done ;
  (* The supervisor, as at the end of an analysis *)
  SMTSolver.kill_solvers_of_domain (Domain.get_id engine :> int) ;
  Atomic.set stopped true ;
  Domain.join engine ;
  assert_none_left_open before

(* While the analysis is shutting down, an engine kills its own solvers
   outright instead of asking them to exit. The pipes to them are
   closed all the same. *)
let test_solvers_killed_at_shutdown_are_closed _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  let before = open_descriptors () in
  let deleted = new_solver () in
  for _ = 1 to 4 do ignore (new_solver ()) done ;
  SMTSolver.set_shutting_down true ;
  Fun.protect ~finally:(fun () -> SMTSolver.set_shutting_down false)
    (fun () ->
      SMTSolver.delete_instance deleted ;
      SMTSolver.destroy_all ()) ;
  assert_none_left_open before

let tests = "SolverDeleteRace" >::: [
  "delete and kill do not both dispose" >:: test_delete_and_kill_do_not_both_dispose ;
  "killed solvers are closed on exit" >:: test_killed_solvers_are_closed_on_exit ;
  "solvers killed at shutdown are closed" >:: test_solvers_killed_at_shutdown_are_closed ;
]

let () = run_test_tt_main tests
