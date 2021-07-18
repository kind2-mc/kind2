(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015-2019 by the Board of Trustees of the University of Iowa

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
(*module TestGen = TestgenDF*)
module C2I = C2I
(*module C2Icnf = C2Icnf*)

module Signals = TermLib.Signals

open Lib

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
    KEvent.log L_info
      "[renice] ignoring negative niceness value."
  else if nice > 0 then
    let nice' = Unix.nice nice in
    KEvent.log L_info "[renice] renicing to %d" nice'

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
  | `INVGENINT8 -> renice () ; InvGen.main_int8 true
  | `INVGENINT8OS -> renice () ; InvGen.main_int8 false
  | `INVGENINT16 -> renice () ; InvGen.main_int16 true
  | `INVGENINT16OS -> renice () ; InvGen.main_int16 false
  | `INVGENINT32 -> renice () ; InvGen.main_int32 true
  | `INVGENINT32OS -> renice () ; InvGen.main_int32 false
  | `INVGENINT64 -> renice () ; InvGen.main_int64 true
  | `INVGENINT64OS -> renice () ; InvGen.main_int64 false
  | `INVGENUINT8 -> renice () ; InvGen.main_uint8 true
  | `INVGENUINT8OS -> renice () ; InvGen.main_uint8 false
  | `INVGENUINT16 -> renice () ; InvGen.main_uint16 true
  | `INVGENUINT16OS -> renice () ; InvGen.main_uint16 false
  | `INVGENUINT32 -> renice () ; InvGen.main_uint32 true
  | `INVGENUINT32OS -> renice () ; InvGen.main_uint32 false
  | `INVGENUINT64 -> renice () ; InvGen.main_uint64 true
  | `INVGENUINT64OS -> renice () ; InvGen.main_uint64 false
  | `INVGENREAL -> renice () ; InvGen.main_real true
  | `INVGENREALOS -> renice () ; InvGen.main_real false
  | `C2I -> renice () ; C2I.main
  | `Interpreter -> Flags.Interpreter.input_file () |> Interpreter.main
  | `Supervisor -> InvarManager.main false false child_pids
  | `INVGENMACH | `INVGENMACHOS | `MCS | `CONTRACTCK
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
    | `INVGENINT8 -> InvGen.exit None
    | `INVGENINT8OS -> InvGen.exit None
    | `INVGENINT16 -> InvGen.exit None
    | `INVGENINT16OS -> InvGen.exit None
    | `INVGENINT32 -> InvGen.exit None
    | `INVGENINT32OS -> InvGen.exit None
    | `INVGENINT64 -> InvGen.exit None
    | `INVGENINT64OS -> InvGen.exit None
    | `INVGENUINT8 -> InvGen.exit None
    | `INVGENUINT8OS -> InvGen.exit None
    | `INVGENUINT16 -> InvGen.exit None
    | `INVGENUINT16OS -> InvGen.exit None
    | `INVGENUINT32 -> InvGen.exit None
    | `INVGENUINT32OS -> InvGen.exit None
    | `INVGENUINT64 -> InvGen.exit None
    | `INVGENUINT64OS -> InvGen.exit None
    | `INVGENREAL -> InvGen.exit None
    | `INVGENREALOS -> InvGen.exit None
    | `C2I -> C2I.on_exit None
    | `Interpreter -> Interpreter.on_exit None
    | `Supervisor -> InvarManager.on_exit None
    | `INVGENMACH | `INVGENMACHOS | `MCS | `CONTRACTCK
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
let status_of_results in_sys =
  let res =
    let l1 = List.length (ISys.analyzable_subsystems in_sys) in
    let l2 = Anal.results_size !all_results in
    if l1 = l2 then Anal.results_is_safe !all_results
    else None
  in
  match res with
  | None ->
    KEvent.log L_note "Incomplete analysis result: Not all properties could be proven invariant" ;
    ExitCodes.unknown
  | Some true -> ExitCodes.safe
  | Some false -> ExitCodes.unsafe

(* Return the status code from an exception *)
let status_of_exn process status = function
  (* Normal termination. *)
  | Exit -> status
  (* Parser error *)
  | LustreAst.Parser_error | Parsing.Parse_error ->
    ExitCodes.error
  (* Got unknown, issue error but normal termination. *)
  | SMTSolver.Unknown ->
    KEvent.log L_warn "In %a: a check-sat resulted in `unknown`. \
      This is most likely due to non-linear expressions in the model, \
      usually multiplications `v_1 * v_2` or divisions `v_1 / v_2`.%t"
      pp_print_kind_module process
      (fun fmt -> if Flags.Smt.check_sat_assume () then
         Format.fprintf fmt
           " Consider running Kind 2 with `--check_sat_assume false` or \
             abstracting non-linear expressions using contracts."
       else ()
      );
    status
  (* Termination message. *)
  | KEvent.Terminate ->
    KEvent.log L_debug "Received termination message" ;
    status
  (* Catch wallclock timeout. *)
  | TimeoutWall -> (
    InvarManager.print_stats !latest_trans_sys ;
    KEvent.log_timeout true ;
    status
  )
  (* Catch CPU timeout. *)
  | TimeoutVirtual -> (
    InvarManager.print_stats !latest_trans_sys ;
    KEvent.log_timeout false ;
    status
  )
  (* Signal caught. *)
  | Signal s ->
    if s = Sys.sigint then (
      InvarManager.print_stats !latest_trans_sys ;
    ) ;
    KEvent.log_interruption s ;
    (* Return exit status and signal number. *)
    ExitCodes.kid_status + s
  (* Runtime failure. *)
  | IC3.UnsupportedFeature msg -> (
    KEvent.log L_warn "%s" msg;
    status
  )
  | Failure msg -> (
    if msg = "SMT solver failed: non-linear arithmetic is not allowed in logic ALL" then (
      (* Yices 2 error *)
      KEvent.log L_error "In %a: no logic has been provided, but Yices 2 requires one when@ \
        the model contains non-linear expressions.@ \
        Consider running Kind 2 with `--smt_logic detect`\
      "
      pp_print_kind_module process;
      status
    )
    else (
      InvarManager.print_stats !latest_trans_sys ;
      KEvent.log L_fatal "Runtime failure in %a: %s"
        pp_print_kind_module process msg ;
      ExitCodes.error
    )
  )
  (* Other exception, return exit status for error. *)
  | e -> (
    InvarManager.print_stats !latest_trans_sys ;
    KEvent.log L_fatal "Runtime error in %a: %s"
      pp_print_kind_module process (Printexc.to_string e);
    ExitCodes.error
  )

(** Status corresponding to an exception based on an optional system. *)
let status_of_exn_sys process sys_opt =
  status_of_sys () |> status_of_exn process

(** Status corresponding to an exception based on some results. *)
let status_of_exn_results in_sys process =
  status_of_results in_sys |> status_of_exn process

(** Kill all kids violently. *)
let slaughter_kids process sys =
  Signals.ignoring_sigalrm ( fun _ ->
    (* Clean exit from invariant manager *)
    InvarManager.on_exit sys ;
    KEvent.log L_info "Killing all remaining child processes";

    (* Kill all child processes groups *)
    List.iter (
      fun (pid, _) ->
        KEvent.log L_debug "Sending SIGKILL to PID %d" pid ;
        try Unix.kill (- pid) Sys.sigkill with _ -> ()
    ) ! child_pids ;

    KEvent.log L_debug "Waiting for remaining child processes to terminate" ;

    let timeout = ref false in

    (
      try
        while !child_pids <> [] do
          try
            (* Wait for child process to terminate *)
            let pid, status = Unix.wait () in
            (* Remove killed process from list *)
            child_pids := List.remove_assoc pid !child_pids ;
            (* Log termination status *)
            KEvent.log L_debug
              "Process %d %a" pid pp_print_process_status status
          with
          (* Remember timeout to raise it later. *)
          | TimeoutWall ->
            KEvent.log_timeout true ;
            timeout := true
        done
      with
      (* No more child processes, this is the normal exit. *)
      | Unix.Unix_error (Unix.ECHILD, _, _) ->
        KEvent.log L_info "All child processes terminated." ;
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
      KEvent.log L_fatal "Some children did not exit." ;
    (* Cleaning kids list. *)
    child_pids := [] ;
    (* Draining mailbox. *)
    KEvent.recv () |> ignore
  ) ;

  Signals.set_sigalrm_timeout_from_flag ()

(** Called after everything has been cleaned up. All kids dead etc. *)
let post_clean_exit_with_results in_sys process exn =
  (* Exit status of process depends on exception. *)
  let status = status_of_exn_results in_sys process exn in
  (* Close tags in XML output. *)
  KEvent.terminate_log () ;
  (* Kill all live solvers. *)
  SMTSolver.destroy_all () ;
  (* Exit with status. *)
  exit status

(** Called after everything has been cleaned up *)
let post_clean_exit process exn =
  (* Exit status of process depends on exception. *)
  let status = status_of_exn process ExitCodes.unknown exn in
  (* Close tags in XML output. *)
  KEvent.terminate_log () ;
  (* Kill all live solvers. *)
  SMTSolver.destroy_all () ;
  (* Exit with status. *)
  exit status

(** Clean up before exit. *)
let on_exit_with_results in_sys sys process exn =
  try
    slaughter_kids process sys;
    post_clean_exit_with_results in_sys process exn
  with TimeoutWall -> post_clean_exit_with_results in_sys process TimeoutWall

(** Clean up before exit, for a MCS analysis. *)
let on_exit in_sys sys process exn =
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
  Unix.getpid () |> KEvent.log L_debug "Process %d terminating" ;

  ( match messaging_thread with
    | Some t -> KEvent.exit t
    | None -> ()
  ) ;

  Debug.kind2 "Process %a terminating" pp_print_kind_module process ;
  KEvent.terminate_log () ;
  (* Log stats and statuses of properties if run as a single process *)
  (* if alone then KEvent.log_result sys_opt; *)
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
    (* Remove solvers entries (they are owned by the parent) *)
    SMTSolver.delete_instance_entries () ;
    (* Initialize messaging system for process. *)
    let messaging_thread =
      on_exit_child None process
      |> KEvent.run_process process messaging_setup
    in

    try 

      (* All log messages are sent to the invariant manager now. *)
      KEvent.set_relay_log ();

      (* Set module currently running. *)
      KEvent.set_module process;

      (* Record backtraces on log levels debug and higher. *)
      if output_on_level L_debug then
        Printexc.record_backtrace true ;

      KEvent.log L_debug
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
      (* Cleanup and exit *)
      on_exit_child (Some messaging_thread) process Exit

    with
    (* Termination message received. *)
    | KEvent.Terminate as e ->
      on_exit_child (Some messaging_thread) process e
    (* Catch all other exceptions. *)
    | e ->
      (* Get backtrace now, Printf changes it. *)
      let backtrace = Printexc.get_raw_backtrace () in
      if Printexc.backtrace_status () then (
        KEvent.log L_fatal
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

let process_invgen_mach_modules sys (modules: Lib.kind_module list) : Lib.kind_module list =
  let invgenmach_modules, other_modules = modules |> List.partition (
    function `INVGENMACH | `INVGENMACHOS -> true | _ -> false)
  in
  match invgenmach_modules with
  | [] -> other_modules
  | _ -> (
    let open TermLib.FeatureSet in
    match TransSys.get_logic sys with
    | `Inferred fs when mem BV fs -> (
      let other_modules =
        if (List.mem `INVGENMACHOS invgenmach_modules) then
          `INVGENINT8OS :: `INVGENINT16OS :: `INVGENINT32OS :: `INVGENINT64OS ::
          `INVGENUINT8OS :: `INVGENUINT16OS :: `INVGENUINT32OS :: `INVGENUINT64OS
          :: other_modules
        else
          other_modules
       in
       let other_modules =
        if (List.mem `INVGENMACH invgenmach_modules) then
          `INVGENINT8 :: `INVGENINT16 :: `INVGENINT32 :: `INVGENINT64 ::
          `INVGENUINT8 :: `INVGENUINT16 :: `INVGENUINT32 :: `INVGENUINT64
          :: other_modules
        else
          other_modules
       in
       other_modules
    )
    | _ -> other_modules
  )

(** Performs an analysis. *)
let analyze msg_setup save_results ignore_props stop_if_falsified modules in_sys param sys =
  Stat.start_timer Stat.analysis_time ;

  ( if TSys.has_real_properties sys |> not && not ignore_props then
      KEvent.log L_note
        "System %a has no property, skipping verification step." fmt_sys sys
    else
      let props = TSys.props_list_of_bound sys Num.zero in
      (* Issue analysis start notification. *)
      KEvent.log_analysis_start sys param ;
      (* Debug output system. *)
      Debug.parse "%a" TSys.pp_print_trans_sys sys ;
      (* Issue number of properties. *)
      List.length props |> KEvent.log L_info "%d properties." ;

      KEvent.log L_debug "Starting child processes." ;

      (* Disable the reception of messages of the invariant manager. *)
      KEvent.update_child_processes_list [] ;
      (* Get rid of messages from the previous analysis. *)
      KEvent.purge_im msg_setup ;

      let modules = process_invgen_mach_modules sys modules in

      (* Start all child processes. *)
      modules |> List.iter (
        fun p -> run_process in_sys param sys msg_setup p
      ) ;

      (* Update background thread with new kids. *)
      KEvent.update_child_processes_list !child_pids ;

      (* Running supervisor. *)
      InvarManager.main ignore_props stop_if_falsified child_pids in_sys param sys ;

      (* Killing kids when supervisor's done. *)
      Some sys |> slaughter_kids `Supervisor
  ) ;

  let result =
    Stat.get_float Stat.analysis_time
    |> Anal.mk_result param sys
  in

  if not ignore_props && save_results then (
    let results = Anal.results_add result !all_results in
    all_results := results
  ) ;

  (* Issue analysis end notification. *)
  KEvent.log_analysis_end () ;
  (* Issue analysis outcome. *)
  KEvent.log L_info "Result: %a" Analysis.pp_print_result result


let handle_exception in_sys process e =
  (* Get backtrace now, Printf changes it *)
  let backtrace = Printexc.get_raw_backtrace () in

  if Printexc.backtrace_status () then
    KEvent.log L_fatal "Caught %s in %a.@\nBacktrace:@\n%a"
      (Printexc.to_string e)
      pp_print_kind_module process
      print_backtrace backtrace

(** Runs the analyses produced by the strategy module. *)
let run in_sys =

  (* Who's active? *)
  match Flags.enabled () with

  (* Nothing's active. *)
  | [] ->
    KEvent.log L_fatal "Need at least one Kind 2 module active." ;
    KEvent.terminate_log () ;
    exit ExitCodes.error

  (* Only the interpreter is active. *)
  | [m] when m = `Interpreter -> (
    (* Set module currently running. *)
    KEvent.set_module m ;
    try (
      let param = ISys.interpreter_param in_sys in
      (* Build trans sys and slicing info. *)
      let sys, _ =
        ISys.trans_sys_of_analysis
          ~preserve_sig:true ~slice_nodes:false in_sys param
      in
      (* Run interpreter. *)
      Interpreter.main (
        Flags.Interpreter.input_file ()
      ) in_sys param sys ;
      (* Ignore SIGALRM from now on *)
      Signals.ignore_sigalrm () ;
      (* Cleanup before exiting process *)
      on_exit_child None m Exit
    )
    with e -> on_exit_child None m e
  )

  (* Some modules, including the interpreter. *)
  | modules when List.mem `Interpreter modules ->
    KEvent.log L_fatal "Cannot run the interpreter with other processes." ;
    KEvent.terminate_log () ;
    exit ExitCodes.error

  (* Only the contract checker is active.*)
  | [m] when m = `CONTRACTCK -> (

    (* If Z3 is used for contract checking, use qe-light strategy *)
    Flags.Smt.set_z3_qe_light true ;

    try (
      let msg_setup = KEvent.setup () in
      KEvent.set_module `CONTRACTCK ;
      KEvent.run_im msg_setup [] (on_exit in_sys None `CONTRACTCK) |> ignore ;
      KEvent.log L_debug "Messaging initialized in Contract Check." ;

      match ISys.contract_check_params in_sys with
      | [] -> KEvent.log L_note "No imported nodes found, skipping contract check."
      | params -> (
        params |> List.iter (fun (param, has_contract) ->
          let scope = (Analysis.info_of_param param).top in
          (* Build trans sys and slicing info. *)
          let sys, _ =
            ISys.trans_sys_of_analysis
              (*~preserve_sig:true ~slice_nodes:false*) in_sys param
          in
          (*Format.printf "TS:@.%a@." (TSys.pp_print_subsystems true) sys;*)
          KEvent.log_contractck_analysis_start scope ;
          Stat.start_timer Stat.analysis_time ;
          let result =
            if not has_contract then
              Realizability.Realizable Term.t_true
            else
              ContractChecker.check_contract_realizability in_sys sys
          in
          match result with
          | Realizable _ ->
              KEvent.log_realizable_contract L_warn scope;
          | Unrealizable -> (
              KEvent.log_unrealizable_contract L_warn scope;

              match ContractChecker.check_contract_satisfiability sys with
              | Satisfiable ->
                  KEvent.log_satisfiable_contract L_warn scope
              | Unsatisfiable ->
                  KEvent.log_unsatisfiable_contract L_warn scope
              | Unknown ->
                  KEvent.log_unknown_satisfiability L_warn scope
          )
          | Unknown ->
              KEvent.log_unknown_realizability L_warn scope;

          KEvent.log_analysis_end ()
        )
      ) ;

      post_clean_exit `CONTRACTCK Exit
    ) with
    | TimeoutWall -> on_exit in_sys None `CONTRACTCK TimeoutWall
    | e -> (
      handle_exception in_sys `CONTRACTCK e;
      on_exit in_sys None `CONTRACTCK e
    )
  )

  (* Some modules, including the contract checker. *)
  | modules when List.mem `CONTRACTCK modules ->
    KEvent.log L_fatal "Cannot run the contract checker with other processes." ;
    KEvent.terminate_log () ;
    exit ExitCodes.error

  (* MCS is active. *)
  | modules when List.mem `MCS modules -> (

    try (
      let msg_setup = KEvent.setup () in
      KEvent.set_module `Supervisor ;
      KEvent.run_im msg_setup [] (on_exit in_sys None `Supervisor) |> ignore ;
      KEvent.log L_debug "Messaging initialized in supervisor." ;

      KEvent.set_module `MCS ;
      let params = ISys.mcs_params in_sys in
      let run_mcs param =
        (* Build trans sys and slicing info. *)
        let sys, _ =
          ISys.trans_sys_of_analysis
            (*~preserve_sig:true ~slice_nodes:false*) in_sys param
        in
        KEvent.log_analysis_start sys param ;
        Stat.start_timer Stat.analysis_time ;
        
        PostAnalysis.run_mcs_post_analysis in_sys param
          (analyze msg_setup false) sys |> ignore ;

        KEvent.log_analysis_end ()
      in
      List.iter run_mcs params ;
      post_clean_exit `Supervisor Exit
    ) with
    | TimeoutWall -> on_exit in_sys None `Supervisor TimeoutWall
    | e -> (
      handle_exception in_sys `Supervisor e ;
      on_exit in_sys None `Supervisor e
    )
  ) 

  (* Some analysis modules. *)
  (* Some modules, not including the interpreter. *)
  | modules ->

    KEvent.log L_info
      "@[<hov>Running in parallel mode: @[<v>- %a@]@]"
      (pp_print_list pp_print_kind_module "@ - ")
      modules ;
    (* Setup messaging. *)
    let msg_setup = KEvent.setup () in

    (* Runs the next analysis, if any. *)
    let rec loop () =
      match ISys.next_analysis_of_strategy in_sys !all_results with
      
      | Some param ->
        (* Format.printf "param: %a@.@." (Analysis.pp_print_param true) param ; *)
        (* Build trans sys and slicing info. *)
        let sys, in_sys_sliced =
          ISys.trans_sys_of_analysis in_sys param
        in

        (* Format.printf "%a" (TSys.pp_print_subsystems true) sys; *)

        (* Should we run post analysis treatment? *)
        ( match !latest_trans_sys with
          | Some old when TSys.equal_scope old sys |> not ->
            PostAnalysis.run in_sys (TSys.scope_of_trans_sys old) (
              analyze msg_setup false
            ) !all_results
          | _ -> ()
        ) ;
        latest_trans_sys := Some sys ;
        (* Analyze... *)
        analyze msg_setup true false false modules in_sys param sys ;
        (* ...and loop. *)
        loop ()

      | None -> (
        ( match !latest_trans_sys with
          | Some sys -> PostAnalysis.run in_sys (TSys.scope_of_trans_sys sys) (
            analyze msg_setup false
          ) !all_results
          | _ -> ()
        ) ;
        latest_trans_sys := None
      )
    in

    (* Set module currently running *)
    KEvent.set_module `Supervisor ;
    (* Initialize messaging for invariant manager, obtain a background thread.
    No kids yet. *)
    KEvent.run_im msg_setup []
      (on_exit_with_results in_sys None `Supervisor) |> ignore ;
    KEvent.log L_debug "Messaging initialized in supervisor." ;

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
          KEvent.log L_fatal "Failure: %s" s ;
          l
        | e ->
          KEvent.log L_fatal "%s" (Printexc.to_string e) ;
          l
      ) []
      (* Logging the end of the run. *)
      |> KEvent.log_run_end ;

      post_clean_exit_with_results in_sys `Supervisor Exit

    ) with
    | TimeoutWall -> on_exit_with_results in_sys None `Supervisor TimeoutWall
    | e -> (
      handle_exception in_sys `Supervisor e;
      on_exit_with_results in_sys None `Supervisor e
    )

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
