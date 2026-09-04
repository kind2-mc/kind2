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

(* A solver gets its own standard input, even where a standard
   descriptor of Kind 2 is free.

   Reading the input from standard input leaves descriptor 0 closed --
   the lexer closes the channel it has read to the end -- and the first
   pipe made for a solver takes it. A close-on-exec end that already is
   the descriptor it would be duplicated onto is not duplicated at all,
   so the flag survives the exec: the solver starts with no standard
   input, reads an end of file and exits, and the first thing Kind 2
   writes to it raises [Sys_error "Broken pipe"]. That is what every
   engine of [kind2 < file] reported.

   A file of its own rather than a case of [testSolverPipes]: the
   disposal below leaves the process unable to start another solver,
   which is only not felt because the runner gives each case a process. *)

open TestSolverCommon

let test_a_solver_gets_its_own_standard_input _ =
  (* The premise is a descriptor the kernel hands out as the lowest
     free number, which is not what a descriptor is on Windows *)
  skip_if Sys.win32 "descriptors are not numbered here" ;
  skip_if (solver_missing ()) "no Z3 on PATH" ;

  (* As Kind 2 does, so that a solver that is not there to be written
     to fails the write rather than killing the runner outright *)
  TermLib.Signals.ignore_sigpipe () ;

  (* Leave descriptor 0 free, the way reading the input from standard
     input does. Put it back afterwards: the rest of the run needs it
     no more than Kind 2 does, but leaving it free is not this test's
     to decide for whatever comes next. *)
  let saved = Unix.dup ~cloexec:true Unix.stdin in
  Fun.protect
    ~finally:(fun () ->
      Unix.dup2 ~cloexec:false saved Unix.stdin ;
      Unix.close saved)
    (fun () ->
      Unix.close Unix.stdin ;
      Fun.protect ~finally:SMTSolver.destroy_all_of_process (fun () ->
        let solver = new_solver () in
        (* A round trip. Writing to a solver that has exited is what
           raises, and reading its answer is the only way to see that
           it was there to give one. *)
        assert_bool
          "the solver did not answer" (SMTSolver.check_sat solver)))

let tests = "SolverStdin" >::: [
  "a solver gets its own standard input"
  >:: test_a_solver_gets_its_own_standard_input ;
]

let () = run_test_tt_main tests
