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


(* Setup everything and returns the input system. Setup includes:
   - debug setup,
   - log level setup,
   - smt solver setup,
   - timeout setup,
   - signal handling,
   - starting global timer,
   - parsing input file,
   - building input system. *)
let setup : unit -> any_input = fun () ->

  (* Formatter to write debug output to. *)
  (match Flags.debug_log () with
    (* Write to stdout by default. *)
    | None -> ()
    (* Open channel to given file and create formatter on channel. *)
    | Some f ->
      let oc = try open_out f with Sys_error msg ->
        Format.sprintf
          "Could not open debug logfile \"%s\": \"%s\"" f msg
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

  Event.log L_info "Parsing %s."
    (match in_file with
     | "" -> "standard input"
     | _ -> "input file \"" ^ in_file ^ "\"");

  try
    (* in_file |> *)
    match Flags.input_format () with
    | `Lustre -> Input (InputSystem.read_input_lustre in_file)
    | `Native -> Input (InputSystem.read_input_native in_file)
    | `Horn   ->
      Event.log L_fatal "Horn clauses are not supported." ;
      Event.terminate_log () ;
      exit ExitCodes.error
  with (* Could not create input system. *)
  | LustreAst.Parser_error ->
    (* Don't do anything for parser error, they should already have printed
    some stuff. *)
    Event.terminate_log () ;
    exit ExitCodes.error
  | e ->
    
    let backtrace = Printexc.get_raw_backtrace () in

    Event.log
      L_fatal "Error opening input file \"%s\":@ %s%a"
      (Flags.input_file ()) (Printexc.to_string e)
      (if Printexc.backtrace_status () then
         fun fmt -> Format.fprintf fmt "@\nBacktrace:@ %a" print_backtrace
       else fun _ _ -> ()) backtrace;

    (* Terminating log and exiting with error. *)
    Event.terminate_log () ;
    exit ExitCodes.error  


(* Entry point *)
let main () =

  (* Set everything up and produce input system. *)
  let Input input_sys = setup () in

  (* Notify user of silent contract loading. *)
  InputSystem.silent_contracts_of input_sys
  |> List.iter (
    function
    | (_, []) -> ()
    | (scope,contracts) ->
      Event.log L_note "Silent contract%s loaded for system %a: @[<v>%a@]"
        (if 1 < List.length contracts then "s" else "")
        Scope.pp_print_scope scope
        (pp_print_list Format.pp_print_string "@ ") contracts
  ) ;

  (* Not launching if we're just translating contracts. *)
  match Flags.Contracts.translate_contracts () with
  | Some target -> (
    let src = Flags.input_file () in
    Event.log_uncond "Translating contracts to file \"%s\"" target ;
    try (
      InputSystem.translate_contracts_lustre src target ;
      Event.log_uncond "Success"
    ) with e ->
      Event.log L_error
        "Could not translate contracts from file \"%s\":@ %s"
        src (Printexc.to_string e)
  )
  | None -> Kind2Flow.run input_sys

;;

main ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
