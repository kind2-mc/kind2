(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(** Top level of the Kind 2 model-checker. *)

open Lib

module Signals = TermLib.Signals

(* Hide existential type parameter of to construct values of 'a InputSystem.t
   at runtime *)
type any_input =
| Input : 'a InputSystem.t -> any_input


let classify_input_stream: string -> string = fun in_file -> 
  match in_file with
   | "" -> "standard input"
   | _  -> "input file '" ^ in_file ^ "'"


(* Setup everything and returns the input system. Setup includes:
   - flag parsing,
   - debug setup,
   - log level setup,
   - smt solver setup,
   - timeout setup,
   - signal handling,
   - starting global timer,
   - parsing input file,
   - building input system. *)
let setup : unit -> any_input = fun () ->

  (* Parse command-line flags. *)
  (try
    Flags.parse_argv ()
   with Flags.Error ->
    KEvent.terminate_log () ; exit ExitCodes.error
  );

  Debug.set_dflags (Flags.debug ()) ;

  (* Formatter to write debug output to. *)
  (match Flags.debug_log () with
    (* Write to stdout by default. *)
    | None -> ()
    (* Open channel to given file and create formatter on channel. *)
    | Some f ->
      let oc = try open_out f with Sys_error msg ->
        Format.sprintf
          "Could not open debug logfile '%s': '%s'" f msg
        |> failwith
      in
      Debug.set_formatter (Format.formatter_of_out_channel oc)
  ) ;


  (* Record backtraces on log levels debug and higher. *)
  if output_on_level L_debug then Printexc.record_backtrace true ;

  (*
    /!\ ================================================================== /!\
    /!\ Must not use [vtalrm] signal, this is used internally by the OCaml /!\
    /!\                        [Threads] module.                           /!\
    /!\ ================================================================== /!\
  *)

  (* Raise exception on CTRL+C. *)
  Sys.catch_break true ;

  (* Set sigalrm handler. *)
  Signals.set_sigalrm_timeout_from_flag () ;

  (* Install generic signal handlers for other signals. *)
  Signals.set_sigint () ;
  Signals.set_sigpipe () ;
  Signals.set_sigterm () ;
  Signals.set_sigquit () ;

  (* Starting global timer. *)
  Stat.start_timer Stat.total_time ;

  let in_file = Flags.input_file () in

  KEvent.log L_info "Creating Input system from  %s." (classify_input_stream in_file);

  try
    let input_system = 
      match Flags.input_format () with
      | `Lustre -> (
        KEvent.log L_debug "Lustre input detected";
        match InputSystem.read_input_lustre (Flags.only_parse ()) in_file with
        | Some in_sys -> Input in_sys
        | None -> (
            KEvent.log L_note "No parse errors found!";
            KEvent.terminate_log ();
            exit 0
        )
      )
                   
      | `Native -> KEvent.log L_debug "Native input detected";
                   Input (InputSystem.read_input_native in_file)
                   
      | `Horn   -> KEvent.log L_fatal "Horn clauses are not supported." ;
                   KEvent.terminate_log () ;
                   exit ExitCodes.error
    in
    KEvent.log L_debug "Input System built";
    input_system
  with
  (* Could not create input system. *)
  | LustreAst.Parser_error  ->
     (* We should have printed the appropriate message so just 'gracefully' exit *)
     KEvent.terminate_log () ; exit ExitCodes.error
  | LustreInput.NoMainNode msg ->
     KEvent.log L_fatal "Error reading input file '%s': %s" in_file msg ;
     KEvent.terminate_log () ; exit ExitCodes.error
  | Sys_error msg ->
     KEvent.log L_fatal "Error opening input file '%s': %s" in_file msg ;
     KEvent.terminate_log () ; exit ExitCodes.error
  | e ->
     let backtrace = Printexc.get_raw_backtrace () in
     KEvent.log L_fatal "Error opening input file '%s':@ %s%a"
       (in_file) (Printexc.to_string e)
       (if Printexc.backtrace_status ()
        then fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
        else fun _ _ -> ()) backtrace;
     (* Terminating log and exiting with error. *)
     KEvent.terminate_log () ;
     exit ExitCodes.error  

(* Entry point *)
let main () =

  (* Set everything up and produce input system. *)
  let Input input_sys = setup () in

  (* Not launching if we're just translating contracts. *)
  match Flags.Contracts.translate_contracts () with
  | Some target -> (
    let src = Flags.input_file () in
    KEvent.log_uncond "Translating contracts to file '%s'" target ;
    try (
      InputSystem.translate_contracts_lustre src target ;
      KEvent.log_uncond "Success"
    ) with e ->
      KEvent.log L_error
        "Could not translate contracts from file '%s':@ %s"
        src (Printexc.to_string e)
  )
  | None ->
    try
      Kind2Flow.run input_sys
    with e -> (
      KEvent.log L_fatal "Caught unexpected exception: %s" (Printexc.to_string e) ;
      KEvent.terminate_log () ;
      exit ExitCodes.error
    )
;;

main ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
