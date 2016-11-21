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

module ISys = InputSystem
module TSys = TransSys
module Anal = Analysis

module BMC = Base
module IND = Step
module IND2 = Step2
module TestGen = TestgenDF
module C2I = C2I
module C2Icnf = C2Icnf

module Signals = TermLib.Signals

open Lib
open Res

(* |===| Helpers. *)

(** Fold left on lists. *)
let fold = List.fold_left
(** Iterator on lists. *)
let iter = List.iter

(** Hide existential type parameter to construct values of ['a InputSystem.t]
at runtime *)
type any_input =
  | Input : 'a InputSystem.t -> any_input


(* |===| Post analysis stuff. *)


(** Signature of modules for post-analysis treatment. *)
module type PostAnal = sig
  (** Indicates whether the module is active. *)
  val is_active: unit -> bool
  (** Performs the treatment. *)
  val run:
    (** Input system. *)
    'a ISys.t ->
    (** Transition system. *)
    TSys.t ->
    (** Analysis parameter. *)
    Anal.param ->
    (** Results for the current system. *)
    Anal.result list
    (** Can fail. *)
    -> unit res
end

(** Test generation. *)
module RunTestGen: PostAnal = struct
  let is_active () = Flags.Testgen.active ()
  let run i_sys sys param results =
    Err (
      fun fmt -> Format.fprintf fmt "test generation is unimplemented"
    )
end

(** Contract generation. *)
module RunContractGen: PostAnal = struct
  let is_active () = Flags.Contracts.contract_gen ()
  let run i_sys sys param results =
    Err (
      fun fmt -> Format.fprintf fmt "contract generation unimplemented"
    )
end

(** List of post-analysis modules. *)
let post_anal = [
  (module RunTestGen: PostAnal) ;
  (module RunContractGen: PostAnal) ;
]

(** Runs the post-analysis things on a system and its results. *)
let run_post_anal i_sys sys param results =
  post_anal |> l_iter (
    fun m ->
      let module Module = (val m: PostAnal) in
      Module.run i_sys sys param results
  )


(* |===| Helpers to run stuff. *)

(** Child processes forked.
This is an association list of PID to process type. We need a
reference here, because we may need to terminate asynchronously
after an exception. *)
let child_pids = ref []

(** Renices the current process. Used for invariant generation. *)
let renice () =
  let nice =  (Flags.Invgen.renice ()) in
  if nice < 0 then
    Event.log L_info
      "[renice] ignoring negative niceness value."
  else if nice > 0 then
    let nice' = Unix.nice nice in
    Event.log L_info "[renice] renicing to %d" nice'

(** Main function of the process *)
let main_of_process = function
  | `IC3 -> IC3.main
  | `BMC -> BMC.main
  | `IND -> IND.main
  | `IND2 -> IND2.main
  | `INVGEN -> renice () ; InvGen.main true
  | `INVGENOS -> renice () ; InvGen.main false
  | `C2I -> renice () ; C2I.main
  | `Interpreter -> Flags.Interpreter.input_file () |> Interpreter.main
  | `Supervisor -> InvarManager.main child_pids
  | `Parser | `Certif -> ( fun _ _ _ -> () )

(** Cleanup function of the process *)
let on_exit_of_process = function
  | `IC3 -> IC3.on_exit
  | `BMC -> BMC.on_exit
  | `IND -> IND.on_exit
  | `IND2 -> IND2.on_exit
  | `INVGEN -> InvGen.exit
  | `INVGENOS -> InvGen.exit
  | `C2I -> C2I.on_exit
  | `Interpreter -> Interpreter.on_exit
  | `Supervisor -> InvarManager.on_exit
  | `Parser | `Certif -> ignore

(** Short name for a kind module. *)
let debug_ext_of_process = short_name_of_kind_module

(* Decides what the exit status is by looking at a transition system.

The exit status is
* 0 if some properties are unknown or k-true (timeout),
* 10 if some properties are falsifiable (unsafe),
* 20 if all properties are invariants (safe). *)
let status_of_trans_sys sys =
  (* Checking if some properties are unknown of falsifiable. *)
  let unknown, falsifiable =
    TSys.get_prop_status_all_nocands sys
    |> List.fold_left (fun (u,f) -> function
      | (n, Property.PropUnknown)
      | (n, Property.PropKTrue _) ->
        Format.eprintf "%s KU@." n;
        u+1,f
      | (n, Property.PropFalse _) ->
        Format.eprintf "%s FALSE@." n;
        u,f+1
      | _ -> u,f
    ) (0,0)
    |> fun (u,f) -> u > 0, f > 0
  in
  (* Getting relevant exit code. *)
  let exit_status =
    if unknown then ExitCodes.unknown else (
      if falsifiable then ExitCodes.unsafe
      else ExitCodes.safe
    )
  in
  (* Exit status. *)
  exit_status

(** Exit status from an optional [results]. *)
let status_of_sys sys_opt = match sys_opt with
  | None ->
    Event.log L_fatal "result analysis: no system found" ;
    Format.eprintf "NO_SYS@.";
    ExitCodes.unknown
  | Some sys -> status_of_trans_sys sys

(** Exit status from an optional [results]. *)
let status_of_results results_opt = match results_opt with
  | None ->
    Event.log L_fatal "result analysis: no system found" ;
    Format.eprintf "NO_RES@.";
    ExitCodes.unknown
  | Some results -> (
    match Analysis.results_is_safe results with
    | None ->
      Event.log L_fatal "result analysis: no safe result" ;
      Format.eprintf "NO_SAFE_RES@." ;
      ExitCodes.unknown
    | Some true -> ExitCodes.safe
    | Some false -> ExitCodes.unsafe
  )

(* Return the status code from an exception *)
let status_of_exn process status = function
  (* Normal termination. *)
  | Exit -> status
  (* Got unknown, issue error but normal termination. *)
  | SMTSolver.Unknown ->
    Event.log L_error
      "@[<v>\
        In %a: a check-sat resulted in \"unknown\".@ \
        This is most likely due to non-linear expressions in the model,@ \
        usually multiplications `v_1 * v_2` or divisions `v_1 / v_2`.@ \
        Consider running Kind 2 with `--smt_check_sat_assume off` or@ \
        abstracting non-linear expressions using contracts.\
      @]"
      pp_print_kind_module process ;
    status
  (* Termination message. *)
  | Event.Terminate ->
    Event.log L_debug "Received termination message" ;
    status
  (* Catch wallclock timeout. *)
  | TimeoutWall ->
    Event.log_timeout true ;
    status
  (* Catch CPU timeout. *)
  | TimeoutVirtual ->
    Event.log_timeout false ;
    status
  (* Signal caught. *)
  | Signal s ->
    Event.log_interruption s ;
    (* Return exit status and signal number. *)
    ExitCodes.kid_status + s
  (* Runtime failure. *)
  | Failure msg ->
    Event.log L_fatal "Runtime failure in %a: %s"
      pp_print_kind_module process msg ;
    ExitCodes.error
  (* Other exception, return exit status for error. *)
  | e ->
    Event.log L_fatal "Runtime error in %a: %s"
      pp_print_kind_module process (Printexc.to_string e) ;
    ExitCodes.error

(** Status corresponding to an exception based on an optional system. *)
let status_of_exn_sys process sys_opt =
  status_of_exn process (status_of_sys sys_opt)

(** Status corresponding to an exception based on some results. *)
let status_of_exn_results process results_opt =
  status_of_exn process (status_of_results results_opt)

(** Kill all kids violently. *)
let slaughter_kids process sys =
  Signals.ignoring_sigalrm ( fun _ ->
    (* Clean exit from invariant manager *)
    InvarManager.on_exit sys ;
    Event.log L_info "Killing all remaining child processes";

    (* Kill all child processes groups *)
    List.iter (
      fun (pid, _) ->
        Event.log L_debug "Sending SIGKILL to PID %d" pid ;
        try Unix.kill (- pid) Sys.sigkill with _ -> ()
    ) ! child_pids ;

    Event.log L_debug "Waiting for remaining child processes to terminate" ;

    let timeout = ref false in

    (
      try
        while true do
          try
            (* Wait for child process to terminate *)
            let pid, status = Unix.wait () in
            (* Remove killed process from list *)
            child_pids := List.remove_assoc pid !child_pids ;
            (* Log termination status *)
            Event.log L_debug
              "Process %d %a" pid pp_print_process_status status
          with
          (* Remember timeout to raise it later. *)
          | TimeoutWall ->
            Event.log_timeout true ;
            timeout := true
        done
      with
      (* No more child processes, this is the normal exit. *)
      | Unix.Unix_error (Unix.ECHILD, _, _) ->
        Event.log L_info "All child processes terminated." ;
        if !timeout then raise TimeoutWall
      (* Unix.wait was interrupted. *)
      | Unix.Unix_error (Unix.EINTR, _, _) ->
        (* Ignoring exit code, whatever happened does not change the
        outcome of the analysis. *)
        Signal 0 |> status_of_exn_sys process None |> ignore

      (* Exception in Unix.wait loop. *)
      | e ->
        (* Ignoring exit code, whatever happened does not change the outcome
        of the analysis. *)
        status_of_exn_sys process None e |> ignore ;
    ) ;

    if ! child_pids <> [] then
      Event.log L_fatal "Some children did not exit." ;
    (* Cleaning kids list. *)
    child_pids := [] ;
    (* Draining mailbox. *)
    Event.recv () |> ignore
  )

(** Called after everything has been cleaned up. All kids dead etc. *)
let post_clean_exit process results exn =
  (* Exit status of process depends on exception. *)
  let status = status_of_exn_results process results exn in
  (* Close tags in XML output. *)
  Event.terminate_log () ;
  (* Exit with status. *)
  exit status

(** Clean up before exit. *)
let on_exit sys process results exn =
  try slaughter_kids process sys with TimeoutWall -> () ;
  post_clean_exit process None exn


(** Call cleanup function of process and exit.
Give the exception [exn] that was raised or [Exit] on normal termination. *)
let on_exit_child ?(alone=false) sys messaging_thread process exn =
  (* Exit status of process depends on exception *)
  let status = status_of_exn process 0 exn in
  (* Call cleanup of process *)
  on_exit_of_process process (Some sys) ;
  Unix.getpid () |> Event.log L_debug "Process %d terminating" ;

  ( match messaging_thread with
    | Some t -> Event.exit t
    | None -> ()
  ) ;

  Debug.kind2 "Process %a terminating" pp_print_kind_module process ;
  Event.terminate_log () ;
  (* Log stats and statuses of properties if run as a single process *)
  (* if alone then Event.log_result sys_opt; *)
  (* Exit process with status *)
  exit status


(** Forks and runs a child process. *)
let run_process in_sys sys param messaging_setup process =
  (* Fork a new process *)
  let pid = Unix.fork () in
  match pid with
  (* We are the child process *)
  | 0 -> (
    (* Ignore SIGALRM in child process *)
    Signals.ignore_sigalrm () ;
    (* Make the process leader of a new session *)
    Unix.setsid () |> ignore ;
    let pid = Unix.getpid () in
    (* Initialize messaging system for process *)
    let messaging_thread =
      on_exit_child sys None process
      |> Event.run_process process messaging_setup
    in

    try 

      (* All log messages are sent to the invariant manager now *)
      Event.set_relay_log ();

      (* Set module currently running *)
      Event.set_module process;

      (* Record backtraces on log levels debug and higher *)
      if output_on_level L_debug then
        Printexc.record_backtrace true ;

      Event.log L_debug
        "Starting new process %a with PID %d" 
        pp_print_kind_module process
        pid;

      ( (* Change debug output to per process file *)
        match Flags.debug_log () with 
        (* Keep if output to stdout. *)
        | None -> ()
        
        (* Open channel to given file and create formatter on channel. *)
        | Some f ->
          try (* Output to f.PROCESS-PID *)
            let f' = 
              Format.sprintf "%s.%s-%d" 
                f
                (debug_ext_of_process process)
                pid
            in

            (* Open output channel to file *)
            let oc = open_out f' in

            (* Formatter writing to file *)
            let debug_formatter = Format.formatter_of_out_channel oc in
            Debug.set_formatter debug_formatter

          with
          (* Ignore and keep previous file on error *)
          | Sys_error _ -> () 

      ) ;
      (* Retrieve input system. *)
      let Input in_sys = in_sys in
      (* Run main function of process *)
      main_of_process process in_sys param sys ;
      (* Cleanup and exit *)
      on_exit_child sys (Some messaging_thread) process Exit

    with
    (* Termination message received. *)
    | Event.Terminate as e ->
      on_exit_child sys (Some messaging_thread) process e
    (* Catch all other exceptions. *)
    | e ->
      (* Get backtrace now, Printf changes it. *)
      let backtrace = Printexc.get_raw_backtrace () in
      if Printexc.backtrace_status () then (
        Event.log L_fatal
          "Caught %s in %a.@ Backtrace:@ %a"
          (Printexc.to_string e)
          pp_print_kind_module process
          print_backtrace backtrace
      ) ;
      (* Cleanup and exit *)
      on_exit_child sys (Some messaging_thread) process e

  )

  (* We are the parent process *)
  | _ ->
    (* Keep PID of child process and return *)
    child_pids := (pid, process) :: !child_pids

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)