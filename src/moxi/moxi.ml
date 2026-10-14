(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

(* Report a fatal error as an SMT-LIB error on the standard output, on a
   single line, and exit with [code]. The message loses its final period;
   a quote in it is doubled, and a character an SMT-LIB string literal does
   not allow is replaced: white space by a space, any other by [?]. *)
let fatal_error code fmt =
  Format.kasprintf (fun msg ->
    let msg =
      if String.ends_with ~suffix:"." msg then
        String.sub msg 0 (String.length msg - 1)
      else msg
    in
    let msg =
      String.map (function
        | '\t' | '\n' | '\r' -> ' '
        | c when Char.code c < 32 || Char.code c = 127 -> '?'
        | c -> c
      ) msg
    in
    Format.printf "(error \"%s\")@."
      (String.concat "\"\"" (String.split_on_char '"' msg));
    exit code
  ) fmt

let parse_commandline_args () =
  try Flags.parse_argv ~profile:Flags.kmoxi_profile () with
  | Flags.UsageError msg -> fatal_error ExitCodes.usage_error "%s" msg
  | Flags.Error -> exit ExitCodes.usage_error

(* Prefer a main SMT solver for the logic the model sets, if the user left
   it to detection and it is found, then check and detect the solvers *)
let check_solvers logic =
  (match logic with
   | Some "QF_BV" -> Flags.Smt.prefer_solvers ~solver:`Bitwuzla_SMTLIB ()
   | _ -> ());
  try Flags.check_solvers () with
  | Flags.UnsupportedSolver msg ->
    fatal_error ExitCodes.unsupported_solver "%s" msg
  | Flags.SolverNotFound msg -> fatal_error ExitCodes.not_found_error "%s" msg

let read_and_process_input_file filename =
  if Flags.only_parse () then (
    (* Parse and type check only *)
    match MoxiInput.check_file filename with
    | Ok () -> exit ExitCodes.success
    | Error e ->
      fatal_error ExitCodes.parse_error "%a" MoxiInput.pp_print_error e
  )
  else
  match InputSystem.read_input_moxi filename with
  | Ok (in_sys, logic) -> (
    check_solvers logic ;
    Kind2Flow.run in_sys
  )
  | Error e ->
    fatal_error ExitCodes.parse_error "%a" MoxiInput.pp_print_error e


let main () =
  Lib.set_log_level L_off ;
  Printexc.record_backtrace true ;

  (* Without an input file, the model is read from the standard input *)
  parse_commandline_args () ;
  (* Signal handlers, timeout and global timer, as in kind2: without
     them a SIGTERM ends kmoxi without killing its solvers, and
     --timeout is not enforced *)
  RunSetup.setup () ;
  let filename = Flags.input_file () in
  try
    read_and_process_input_file filename
  with
  | Sys_error msg ->
    fatal_error ExitCodes.error "Error opening input file: %s" msg
  | e ->
    (* The backtrace goes to the standard error, outside of the SMT-LIB
       response *)
    let backtrace = Printexc.get_raw_backtrace () in
    if Printexc.backtrace_status () then
      Format.eprintf "Backtrace:@ %a@." print_backtrace backtrace ;
    fatal_error ExitCodes.error "Fatal error: %s" (Printexc.to_string e)
;;

main ()