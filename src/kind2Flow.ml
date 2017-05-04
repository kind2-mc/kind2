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

module Num = Numeral

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
(** TSys name formatter. *)
let fmt_sys = TSys.pp_print_trans_sys_name


(* |===| Helpers to run stuff. *)

(** Child processes forked.
This is an association list of PID to process type. We need a
reference here, because we may need to terminate asynchronously
after an exception. *)
let child_pids = ref []

(** Latest transition system for clean exit in case of error. *)
let latest_trans_sys = ref None

(** All the results this far. *)
let all_results = ref ( Anal.mk_results () )

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
  | `INVGEN -> renice () ; InvGen.main_bool true
  | `INVGENOS -> renice () ; InvGen.main_bool false
  | `INVGENINT -> renice () ; InvGen.main_int true
  | `INVGENINTOS -> renice () ; InvGen.main_int false
  | `INVGENREAL -> renice () ; InvGen.main_real true
  | `INVGENREALOS -> renice () ; InvGen.main_real false
  | `C2I -> renice () ; C2I.main
  | `Interpreter -> Flags.Interpreter.input_file () |> Interpreter.main
  | `Supervisor -> InvarManager.main false child_pids
  | `Parser | `Certif -> ( fun _ _ _ -> () )

(** Cleanup function of the process *)
let on_exit_of_process mdl =
  ( match mdl with
    | `IC3 -> IC3.on_exit None
    | `BMC -> BMC.on_exit None
    | `IND -> IND.on_exit None
    | `IND2 -> IND2.on_exit None
    | `INVGEN -> InvGen.exit None
    | `INVGENOS -> InvGen.exit None
    | `INVGENINT -> InvGen.exit None
    | `INVGENINTOS -> InvGen.exit None
    | `INVGENREAL -> InvGen.exit None
    | `INVGENREALOS -> InvGen.exit None
    | `C2I -> C2I.on_exit None
    | `Interpreter -> Interpreter.on_exit None
    | `Supervisor -> InvarManager.on_exit None
    | `Parser | `Certif -> ()
  ) ;
  SMTSolver.destroy_all ()

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
let status_of_sys () = match ! latest_trans_sys with
  | None -> ExitCodes.unknown
  | Some sys -> status_of_trans_sys sys

(** Exit status from an optional [results]. *)
let status_of_results () =
  match Anal.results_is_safe !all_results with
  | None ->
    Event.log L_fatal "result analysis: no safe result" ;
    (* Format.eprintf "NO_SAFE_RES@." ; *)
    ExitCodes.unknown
  | Some true -> ExitCodes.safe
  | Some false -> ExitCodes.unsafe

(* Return the status code from an exception *)
let status_of_exn process status = function
  (* Normal termination. *)
  | Exit -> status
  (* Parser error *)
  | LustreAst.Parser_error ->
    ExitCodes.error
  (* Got unknown, issue error but normal termination. *)
  | SMTSolver.Unknown ->
    Event.log L_warn "In %a: a check-sat resulted in \"unknown\".@ \
      This is most likely due to non-linear expressions in the model,@ \
      usually multiplications `v_1 * v_2` or divisions `v_1 / v_2`.@ \
      Consider running Kind 2 with `--check_sat_assume off` or@ \
      abstracting non-linear expressions using contracts.\
    " pp_print_kind_module process ;
    status
  (* Termination message. *)
  | Event.Terminate ->
    Event.log L_debug "Received termination message" ;
    status
  (* Catch wallclock timeout. *)
  | TimeoutWall -> (
    InvarManager.print_stats !latest_trans_sys ;
    Event.log_timeout true ;
    status
  )
  (* Catch CPU timeout. *)
  | TimeoutVirtual -> (
    InvarManager.print_stats !latest_trans_sys ;
    Event.log_timeout false ;
    status
  )
  (* Signal caught. *)
  | Signal s ->
    Event.log_interruption s ;
    (* Return exit status and signal number. *)
    ExitCodes.kid_status + s
  (* Runtime failure. *)
  | Failure msg -> (
    InvarManager.print_stats !latest_trans_sys ;
    Event.log L_fatal "Runtime failure in %a: %s"
      pp_print_kind_module process msg ;
    ExitCodes.error
  )
  (* Other exception, return exit status for error. *)
  | e -> (
    InvarManager.print_stats !latest_trans_sys ;
    Event.log L_fatal "Runtime error in %a: %s"
      pp_print_kind_module process (Printexc.to_string e) ;
    ExitCodes.error
  )

(** Status corresponding to an exception based on an optional system. *)
let status_of_exn_sys process sys_opt =
  status_of_sys () |> status_of_exn process

(** Status corresponding to an exception based on some results. *)
let status_of_exn_results process =
  status_of_results () |> status_of_exn process

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
  ) ;

  Signals.set_sigalrm_timeout_from_flag ()

(** Called after everything has been cleaned up. All kids dead etc. *)
let post_clean_exit process exn =
  (* Exit status of process depends on exception. *)
  let status = status_of_exn_results process exn in
  (* Close tags in XML output. *)
  Event.terminate_log () ;
  (* Kill all live solvers. *)
  SMTSolver.destroy_all () ;
  (* Exit with status. *)
  exit status

(** Clean up before exit. *)
let on_exit sys process exn =
  try
    slaughter_kids process sys;
    post_clean_exit process exn
  with TimeoutWall -> post_clean_exit process TimeoutWall


(** Call cleanup function of process and exit.
Give the exception [exn] that was raised or [Exit] on normal termination. *)
let on_exit_child ?(alone=false) messaging_thread process exn =
  (* Exit status of process depends on exception *)
  let status = status_of_exn process 0 exn in
  (* Call cleanup of process *)
  on_exit_of_process process ;
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
let run_process in_sys param sys messaging_setup process =
  (* Fork a new process. *)
  let pid = Unix.fork () in
  match pid with
  (* We are the child process. *)
  | 0 -> (
    (* Ignore SIGALRM in child process. *)
    Signals.ignore_sigalrm () ;
    (* Make the process leader of a new session. *)
    Unix.setsid () |> ignore ;
    let pid = Unix.getpid () in
    (* Initialize messaging system for process. *)
    let messaging_thread =
      on_exit_child None process
      |> Event.run_process process messaging_setup
    in

    try 

      (* All log messages are sent to the invariant manager now. *)
      Event.set_relay_log ();

      (* Set module currently running. *)
      Event.set_module process;

      (* Record backtraces on log levels debug and higher. *)
      if output_on_level L_debug then
        Printexc.record_backtrace true ;

      Event.log L_debug
        "Starting new process %a with PID %d" 
        pp_print_kind_module process
        pid;

      ( (* Change debug output to per process file. *)
        match Flags.debug_log () with 
        (* Keep if output to stdout. *)
        | None -> ()
        
        (* Open channel to given file and create formatter on channel. *)
        | Some f ->
          try (* Output to [f.PROCESS-PID]. *)
            let f' = 
              Format.sprintf "%s.%s-%d" 
                f (debug_ext_of_process process) pid
            in

            (* Open output channel to file. *)
            let oc = open_out f' in

            (* Formatter writing to file. *)
            Format.formatter_of_out_channel oc |> Debug.set_formatter

          with
          (* Ignore and keep previous file on error. *)
          | Sys_error _ -> () 

      ) ;
      (* Retrieve input system. *)
      (* let in_sys = in_sys in *)
      (* Run main function of process *)
      main_of_process process in_sys param sys ;
      (* Kill all remaining solvers. *)
      SMTSolver.destroy_all () ;
      (* Cleanup and exit *)
      on_exit_child (Some messaging_thread) process Exit

    with
    (* Termination message received. *)
    | Event.Terminate as e ->
      on_exit_child (Some messaging_thread) process e
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
      (* Cleanup and exit. *)
      on_exit_child (Some messaging_thread) process e

  )

  (* We are the parent process. *)
  | _ ->
    (* Keep PID of child process and return. *)
    child_pids := (pid, process) :: !child_pids

(** Performs an analysis. *)
let analyze ?(ignore_props = false) msg_setup modules in_sys param sys =
  Stat.start_timer Stat.analysis_time ;

  ( if TSys.has_properties sys |> not && not ignore_props then
      Event.log L_note
        "System %a has no property, skipping verification step." fmt_sys sys
    else
      let props = TSys.props_list_of_bound sys Num.zero in
      (* Issue analysis start notification. *)
      Event.log_analysis_start sys param ;
      (* Debug output system. *)
      Debug.parse "%a" TSys.pp_print_trans_sys sys ;
      (* Issue number of properties. *)
      List.length props |> Event.log L_info "%d properties." ;

      Event.log L_debug "Starting child processes." ;
      (* Start all child processes. *)
      modules |> List.iter (
        fun p -> run_process in_sys param sys msg_setup p
      ) ;
      (* Update background thread with new kids. *)
      Event.update_child_processes_list !child_pids ;

      (* Running supervisor. *)
      InvarManager.main ignore_props child_pids in_sys param sys ;

      (* Killing kids when supervisor's done. *)
      Some sys |> slaughter_kids `Supervisor
  ) ;

  let result =
    Stat.get_float Stat.analysis_time
    |> Anal.mk_result param sys
  in

  if not ignore_props then (
    let results = Anal.results_add result !all_results in
    all_results := results
  ) ;

  (* Issue analysis end notification. *)
  Event.log_analysis_end result ;
  (* Issue analysis outcome. *)
  Event.log L_info "Result: %a" Analysis.pp_print_result result

(** Runs the analyses produced by the strategy module. *)
let run in_sys =

  (* Who's active? *)
  match Flags.enabled () with

  (* Nothing's active. *)
  | [] ->
    Event.log L_fatal "Need at least one Kind 2 module active." ;
    exit ExitCodes.error

  (* Only the interpreter is active. *)
  | [m] when m = `Interpreter -> (
    match
      Analysis.mk_results () |> ISys.next_analysis_of_strategy in_sys
    with
    | Some param ->
      (* Build trans sys and slicing info. *)
      let sys, in_sys_sliced =
        ISys.trans_sys_of_analysis ~preserve_sig:true in_sys param
      in
      (* Set module currently running. *)
      Event.set_module m ;
      (* Run interpreter. *)
      Interpreter.main (
        Flags.Interpreter.input_file ()
      ) in_sys param sys ;
      (* Ignore SIGALRM from now on *)
      Signals.ignore_sigalrm () ;
      (* Cleanup before exiting process *)
      on_exit_child None m Exit
    | None ->
      failwith "Could not generate first analysis parameter."
  )

  (* Some modules, including the interpreter. *)
  | modules when List.mem `Interpreter modules ->
    Event.log L_fatal "Cannot run the interpreter with other processes." ;
    exit ExitCodes.error

  (* Some analysis modules. *)
  (* Some modules, not including the interpreter. *)
  | modules ->
    Event.log L_info
      "@[<hov>Running in parallel mode: @[<v>- %a@]@]"
      (pp_print_list pp_print_kind_module "@ - ")
      modules ;
    (* Setup messaging. *)
    let msg_setup = Event.setup () in

    (* Runs the next analysis, if any. *)
    let rec loop () =
      match ISys.next_analysis_of_strategy in_sys !all_results with
      
      | Some param ->
        (* Format.printf "param: %a@.@." Analysis.pp_print_param param ; *)
        (* Build trans sys and slicing info. *)
        let sys, in_sys_sliced =
          ISys.trans_sys_of_analysis in_sys param
        in
        (* Should we run post analysis treatment? *)
        ( match !latest_trans_sys with
          | Some old when TSys.equal_scope old sys |> not ->
            PostAnalysis.run in_sys (TSys.scope_of_trans_sys old) (
              analyze ~ignore_props:true msg_setup
            ) !all_results
          | _ -> ()
        ) ;
        latest_trans_sys := Some sys ;
        (* Analyze... *)
        analyze msg_setup modules in_sys param sys ;
        (* ...and loop. *)
        loop ()

      | None -> (
        ( match !latest_trans_sys with
          | Some sys -> PostAnalysis.run in_sys (TSys.scope_of_trans_sys sys) (
            analyze ~ignore_props:true msg_setup
          ) !all_results
          | _ -> ()
        ) ;
        latest_trans_sys := None
      )
    in

    (* Set module currently running *)
    Event.set_module `Supervisor ;
    (* Initialize messaging for invariant manager, obtain a background thread.
    No kids yet. *)
    Event.run_im msg_setup [] (on_exit None `Supervisor) |> ignore ;
    Event.log L_debug "Messaging initialized in supervisor." ;

    try (
      (* Run everything. *)
      loop () ;
      let results =
        ! all_results |> Analysis.results_clean
      in

      (* Producing a list of the last results for each system, in topological
      order. *)
      in_sys |> ISys.ordered_scopes_of
      |> List.fold_left (fun l sys ->
        try (
          match Analysis.results_find sys results with
          | last :: _ -> last :: l
          | [] ->
            Format.asprintf "Unreachable: no results at all for system %a."
              Scope.pp_print_scope sys
            |> failwith
        ) with
        | Not_found -> l
        | Failure s ->
          Event.log L_fatal "Failure: %s" s ;
          l
        | e ->
          Event.log L_fatal "%s" (Printexc.to_string e) ;
          l
      ) []
      (* Logging the end of the run. *)
      |> Event.log_run_end ;

      post_clean_exit `Supervisor Exit

    ) with e ->
      (* Get backtrace now, Printf changes it *)
      let backtrace = Printexc.get_raw_backtrace () in

      if Printexc.backtrace_status () then
        Event.log L_fatal "Caught %s in %a.@\nBacktrace:@\n%a"
          (Printexc.to_string e)
          pp_print_kind_module `Supervisor
          print_backtrace backtrace;

      on_exit None `Supervisor e

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
