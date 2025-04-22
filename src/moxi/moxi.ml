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

let parse_commandline_args () =
  try
    Flags.parse_argv ()
  with
  | Flags.Error -> exit ExitCodes.usage_error
  | Flags.UnsupportedSolver -> exit ExitCodes.unsupported_solver
  | Flags.SolverNotFound -> exit ExitCodes.not_found_error

let read_and_process_input_file filename =
  match InputSystem.read_input_moxi filename with
  | Some in_sys -> (
    Kind2Flow.run in_sys
  )
  | None -> exit ExitCodes.parse_error


let main () =
  Lib.set_log_level L_off ;
  Printexc.record_backtrace true ;

  if Array.length Sys.argv < 2 then (
    Format.printf "Usage: %s <file>@." Sys.argv.(0);
    exit ExitCodes.usage_error
  )
  else
    parse_commandline_args () ;
    let filename = Flags.input_file () in
    try
      read_and_process_input_file filename
    with
    | Sys_error msg ->
      Format.eprintf "Error opening input file: %s@." msg ;
      exit ExitCodes.error
    | e ->
      let backtrace = Printexc.get_raw_backtrace () in
      Format.eprintf "Fatal error:@ %s %a@."
        (Printexc.to_string e)
        (if Printexc.backtrace_status ()
          then fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
          else fun _ _ -> ()) backtrace;
      exit ExitCodes.error
;;

main ()