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

(* A reply the solver gave before it was killed is what it says it is.

   The kill may land between the reply being read and [SMTSolver]
   looking at it: a rejection read whole is then found on a killed
   instance. It used to be taken for the kill, and a genuine rejection
   was dropped. Only a command that fails on the dead process -- a reply
   cut short, a closed pipe -- is the kill's.

   The window is too narrow to hit on purpose, so a stand-in solver on
   the shell orders the two: it accepts every command but a declaration,
   which it rejects only once it has been killed. The reply comes from a
   child that outlives it, as soon as [z3.go] appears next to the
   script; [z3.got], made by the child once it runs, says that the
   declaration was received and the child holds the pipe, so that the
   kill is not sent before. A child that is never let go gives up after
   about ten seconds, closing the pipe, so that a broken test fails
   rather than hangs. *)
let stand_in_source = {|#!/bin/sh
while IFS= read -r line; do
  case "$line" in
    *declare-fun*)
      ( : > "$0.got"
        i=0
        while [ ! -e "$0.go" ] && [ $i -lt 1000 ]; do sleep 0.01; i=$((i+1)); done
        echo '(error "rejected")' ) &
      wait ;;
    *) echo success ;;
  esac
done
|}

(* Runs [f] with the stand-in as the [z3] on PATH, first on it, and
   with the paths of its two files *)
let with_stand_in_solver f =
  let dir = Filename.temp_dir "stand-in-solver" "" in
  let script = Filename.concat dir "z3" in
  let oc = open_out script in
  output_string oc stand_in_source ;
  close_out oc ;
  Unix.chmod script 0o700 ;
  let path = Unix.getenv "PATH" in
  Unix.putenv "PATH" (dir ^ ":" ^ path) ;
  Fun.protect
    ~finally:(fun () ->
      Unix.putenv "PATH" path ;
      Array.iter
        (fun file -> Sys.remove (Filename.concat dir file))
        (Sys.readdir dir) ;
      Sys.rmdir dir)
    (fun () -> f ~got:(script ^ ".got") ~go:(script ^ ".go"))

let wait_for_file path =
  let deadline = Unix.gettimeofday () +. 10. in
  while not (Sys.file_exists path) && Unix.gettimeofday () < deadline do
    Unix.sleepf 0.01
  done

(* Declares [uf] to [solver], the stand-in, which another domain kills
   once it has the declaration and then lets its rejection through: the
   reply is read on a killed instance *)
let declare_to_killed_stand_in ~got ~go solver =
  TermLib.Signals.ignore_sigpipe () ;
  let owner = (Domain.self () :> int) in
  let killer =
    Domain.spawn (fun () ->
      wait_for_file got ;
      SMTSolver.kill_solvers_of_domain owner ;
      close_out (open_out go))
  in
  Fun.protect ~finally:(fun () -> Domain.join killer) (fun () ->
    SMTSolver.declare_fun solver uf)

let skip_without_shell () =
  skip_if Sys.win32 "the stand-in solver is a shell script" ;
  skip_if (not (Sys.file_exists "/bin/sh")) "no /bin/sh"

(* A rejection read whole on a killed instance is a rejection; the next
   command, which fails on the dead process, is the kill's *)
let test_rejection_before_kill_is_reported _ =
  skip_without_shell () ;
  with_stand_in_solver (fun ~got ~go ->
    let solver = new_solver () in
    assert_raises (Failure "SMT solver failed: \"rejected\"") (fun () ->
      declare_to_killed_stand_in ~got ~go solver) ;
    assert_raises SMTSolver.Killed (fun () -> SMTSolver.push solver))

(* The same rejection, given as a definition, is warned about *)
let test_rejection_before_kill_is_warned _ =
  skip_without_shell () ;
  with_stand_in_solver (fun ~got ~go ->
    let value, warnings = evaluate (declare_to_killed_stand_in ~got ~go) in
    assert_bool "the call was evaluated" (value = `Unknown) ;
    assert_bool
      ("no warning of the rejection in: " ^ warnings)
      (contains warnings
         "rejected the definitions: SMT solver failed: \"rejected\""))

let tests = "FunEvalKilled" >::: [
  "a killed command raises Killed" >:: test_killed_command_raises_killed ;
  "a killed solver is not a rejection" >:: test_killed_solver_is_not_a_rejection ;
  "a rejection is reported" >:: test_rejection_is_reported ;
  "a rejection before the kill is reported"
  >:: test_rejection_before_kill_is_reported ;
  "a rejection before the kill is warned about"
  >:: test_rejection_before_kill_is_warned ;
]

let () = run_test_tt_main tests
