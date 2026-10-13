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

(* The logic declared by the first set-logic command of a MoXI file, if any.
   The file is only read up to that command, which normally comes first. *)
let declared_logic filename =
  (* Next token: a parenthesis, or a symbol (possibly |quoted|) *)
  let rec token ic =
    match In_channel.input_char ic with
    | None -> None
    | Some (' ' | '\t' | '\n' | '\r') -> token ic
    | Some ';' -> ignore (In_channel.input_line ic); token ic
    | Some (('(' | ')') as c) -> Some (String.make 1 c)
    | Some c ->
      let buf = Buffer.create 16 in
      Buffer.add_char buf c;
      let rec symbol quoted =
        match In_channel.input_char ic with
        | None -> ()
        | Some '|' when c = '|' && quoted -> Buffer.add_char buf '|'
        | Some (' ' | '\t' | '\n' | '\r' | '(' | ')' | ';') when not quoted ->
          (* A symbol ends there; whatever ends it does not matter here *)
          ()
        | Some c' -> Buffer.add_char buf c'; symbol quoted
      in
      symbol (c = '|');
      Some (Buffer.contents buf)
  in
  let rec find ic =
    match token ic with
    | None -> None
    | Some "set-logic" -> token ic
    | Some _ -> find ic
  in
  match filename with
  | "" -> None
  | _ -> (
    try In_channel.with_open_text filename find
    with Sys_error _ -> None
  )

(* SMT solvers for each declared logic: main solver, interpolating solver
   (IC3IA) and quantifier-elimination solver (IC3QE). They only apply to the
   roles not set on the command line, and a solver that is not found is left
   to the usual detection. *)
let choose_solvers () =
  let open Flags.Smt in
  match declared_logic (Flags.input_file ()) with
  | Some "QF_BV" ->
    prefer_solvers
      ~solver:`Bitwuzla_SMTLIB ~itp:`MathSAT_SMTLIB ~qe:`Z3_SMTLIB ()
  | Some ("QF_ABV" | "QF_LIA") ->
    prefer_solvers ~solver:`Z3_SMTLIB ~itp:`MathSAT_SMTLIB ~qe:`Z3_SMTLIB ()
  | _ -> ()

let parse_commandline_args () =
  try
    Flags.parse_argv
      ~profile:(Flags.with_solver_choice Flags.kmoxi_profile choose_solvers) ()
  with
  | Flags.Error -> exit ExitCodes.usage_error
  | Flags.UnsupportedSolver -> exit ExitCodes.unsupported_solver
  | Flags.SolverNotFound -> exit ExitCodes.not_found_error

let read_and_process_input_file filename =
  if Flags.only_parse () then (
    (* Parse and type check only *)
    match MoxiInput.check_file filename with
    | Ok () -> exit ExitCodes.success
    | Error e ->
      Format.eprintf "%a@." MoxiInput.pp_print_error e;
      exit ExitCodes.parse_error
  )
  else
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
  else (
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
  )
;;

main ()