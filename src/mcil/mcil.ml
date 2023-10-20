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
let setup : unit -> (TransSys.t SubSystem.t * McilInput.metadata) = fun () ->

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
    let input_system, metadata = 
      match McilInput.of_file in_file with
        | Ok res -> res
        (* TODO remove lustre reporting...*)
        | Error e -> LustreReporting.fail_at_position (McilErrors.error_position e) (McilErrors.error_message e)
    in
    KEvent.log L_debug "Input System built";
    input_system, metadata
  with
  | DolmenUtils.DolmenParseError ->
    (* Any error message has already been printed *)
    KEvent.terminate_log () ; exit ExitCodes.error
  (* Could not create input system. *)
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
  let input_sys, metadata = setup () in

  try
    McilFlow.run (Native input_sys) metadata
  with e -> (
    KEvent.log L_fatal "Caught unexpected exception: %s" (Printexc.to_string e) ;
    KEvent.terminate_log () ;
    exit ExitCodes.error
  ) ;;

main ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
