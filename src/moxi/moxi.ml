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
   not allow is replaced: white space by a space, any other by [?]. So is a
   byte that is not part of a valid UTF-8 character, such as the one an
   unexpected character of the input may be. *)
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
    let msg =
      let buf = Buffer.create (String.length msg) in
      let rec utf_8 i =
        if i < String.length msg then (
          let d = String.get_utf_8_uchar msg i in
          let n = Uchar.utf_decode_length d in
          if Uchar.utf_decode_is_valid d then
            Buffer.add_string buf (String.sub msg i n)
          else Buffer.add_char buf '?' ;
          utf_8 (i + n))
      in
      utf_8 0 ;
      Buffer.contents buf
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

(* Read the input file with [read]: an error reading it, not one of the
   analysis, is reported as one about the file, which it names *)
let reading_input filename read =
  try read filename with Sys_error msg ->
    let name = if filename = "" then "the standard input" else filename in
    (* The message of the system may start with the file name already *)
    let msg =
      let prefix = filename ^ ": " in
      if filename <> "" && String.starts_with ~prefix msg then
        String.sub msg (String.length prefix)
          (String.length msg - String.length prefix)
      else msg
    in
    fatal_error ExitCodes.error "Error reading input file %s: %s" name msg

let read_and_process_input_file filename =
  if Flags.only_parse () then (
    (* Parse and type check only *)
    match reading_input filename MoxiInput.check_file with
    | Ok () -> exit ExitCodes.success
    | Error e ->
      fatal_error ExitCodes.parse_error "%a" MoxiInput.pp_print_error e
  )
  else
  match reading_input filename InputSystem.read_input_moxi with
  | Ok (in_sys, logic) -> (
    check_solvers logic ;
    Kind2Flow.run in_sys
  )
  | Error e ->
    fatal_error ExitCodes.parse_error "%a" MoxiInput.pp_print_error e


let main () =
  Lib.set_log_level L_off ;
  Printexc.record_backtrace true ;

  (* Every fatal error is reported, those of the command line and of the
     setup included *)
  try
    (* Without an input file, the model is read from the standard input *)
    parse_commandline_args () ;
    (* Signal handlers, timeout and global timer, as in kind2: without
       them a SIGTERM ends kmoxi without killing its solvers, and
       --timeout is not enforced *)
    RunSetup.setup () ;
    read_and_process_input_file (Flags.input_file ())
  with
  | e ->
    (* The backtrace goes to the standard error, outside of the SMT-LIB
       response *)
    let backtrace = Printexc.get_raw_backtrace () in
    if Printexc.backtrace_status () then
      Format.eprintf "Backtrace:@ %a@." print_backtrace backtrace ;
    fatal_error ExitCodes.error "Fatal error: %s" (Printexc.to_string e)
;;

main ()