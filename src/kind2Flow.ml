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

(** Last analysis result corresponding to a scope. *)
let last_result results scope =
  try
    Ok (Anal.results_last scope results)
  with
  | Not_found -> Err (
    fun fmt ->
      Format.fprintf fmt "No result available for component %a."
        Scope.pp_print_scope scope
  )


(* |===| Post analysis stuff. *)


(** Signature of modules for post-analysis treatment. *)
module type PostAnalysis = sig
  (** Name of the treatment. (For xml logging.) *)
  val name: string
  (** Title of the treatment. (For plain text logging.) *)
  val title: string
  (** Indicates whether the module is active. *)
  val is_active: unit -> bool
  (** Performs the treatment. *)
  val run:
    (** Input system. *)
    'a ISys.t ->
    (** Analysis parameter. *)
    Anal.param ->
    (** Results for the current system. *)
    Anal.results
    (** Can fail. *)
    -> unit res
end

(** Test generation.
Generates tests for a system if system's was proved correct under the maximal
abstraction. *)
module RunTestGen: PostAnalysis = struct
  let name = "testgen"
  let title = "test generation"
  (** Error head. *)
  let head sys fmt =
    Format.fprintf fmt "Not generating tests for component %a." fmt_sys sys
  (** Checks that system was proved with the maximal abstraction. *)
  let gen_param_and_check in_sys param sys =
    let top = TSys.scope_of_trans_sys sys in

    match param with
    (* Contract check, node must be abstract. *)
    | Anal.ContractCheck _ -> Err (
      fun fmt ->
        Format.fprintf fmt
          "%t@ Cannot generate tests unless implementation is safe." (head sys)
    )
    | Anal.Refinement _ -> Err (
      fun fmt ->
        Format.fprintf fmt
          "%t@ Component was not proven correct under its maximal abstraction."
          (head sys)
    )
    | Anal.First _ ->

      if TSys.all_props_proved sys |> not then Err (
        fun fmt ->
          Format.fprintf fmt
            "%t@ Component has not been proved safe." (head sys)
      ) else (
        match InputSystem.maximal_abstraction_for_testgen in_sys top [] with
        | None -> Err (
          fun fmt ->
            Format.fprintf fmt
              "System %a has no contracts, skipping test generation."
              fmt_sys sys
        )
        | Some param -> Ok param
      )

  let is_active () = Flags.Testgen.active ()
  let run in_sys param results =
    (* Retrieve system from scope. *)
    let top = (Anal.info_of_param param).Anal.top in
    last_result results top
    |> Res.chain (fun { Anal.sys } ->
      (* Make sure there's at least one mode. *)
      match TSys.get_mode_requires sys |> snd with
      | [] -> (
        match TSys.props_list_of_bound sys Num.zero with
        | [] -> Err (
          fun fmt ->
            Format.fprintf fmt "%t@ Component has no contract." (head sys)
        )
        | _ -> Err (
          fun fmt ->
            Format.fprintf fmt "%t@ Component has no modes." (head sys)
        )
      )
      | _ -> Ok sys
    )
    |> Res.chain (gen_param_and_check in_sys param)
    |> Res.chain (
      fun param ->
        (* Create root dir if needed. *)
        Flags.output_dir () |> mk_dir ;
        let target = Flags.subdir_for top in
        (* Create system dir if needed. *)
        mk_dir target ;

        (* Tweak analysis uid to avoid clashes with future analyses. *)
        let param = match param with
          | Analysis.ContractCheck info -> Analysis.ContractCheck {
            info with Analysis.uid = info.Analysis.uid * 10000
          }
          | Analysis.First info -> Analysis.First {
            info with Analysis.uid = info.Analysis.uid * 10000
          }
          | Analysis.Refinement (info, res) -> Analysis.Refinement (
            { info with Analysis.uid = info.Analysis.uid * 10000 },
            res
          )
        in

        (* Extracting transition system. *)
        let sys, input_sys_sliced =
          InputSystem.trans_sys_of_analysis
            ~preserve_sig:true in_sys param
        in

        (* Let's do this. *)
        try (
          let tests_target = Format.sprintf "%s/%s" target Paths.testgen in
          mk_dir tests_target ;
          Event.log_uncond
            "%sGenerating tests for node \"%a\" to `%s`."
            TestGen.log_prefix Scope.pp_print_scope top tests_target ;
          let testgen_xmls =
            TestGen.main param input_sys_sliced sys tests_target
          in
          (* Yay, done. Killing stuff. *)
          TestGen.on_exit "yay" ;
          (* Generate oracle. *)
          let oracle_target = Format.sprintf "%s/%s" target Paths.oracle in
          mk_dir oracle_target ;
          Event.log_uncond
            "%sCompiling oracle to Rust for node \"%a\" to `%s`."
            TestGen.log_prefix Scope.pp_print_scope top oracle_target ;
          let name, guarantees, modes =
            InputSystem.compile_oracle_to_rust in_sys top oracle_target
          in
          Event.log_uncond
            "%sGenerating glue xml file to `%s/.`." TestGen.log_prefix target ;
          testgen_xmls
          |> List.map (fun xml -> Format.sprintf "%s/%s" Paths.testgen xml)
          |> TestGen.log_test_glue_file
            target name (Paths.oracle, guarantees, modes) Paths.implem ;
          Event.log_uncond
            "%sDone with test generation." TestGen.log_prefix ;
          Ok ()
        ) with e -> (
          TestGen.on_exit "T_T" ;
          Err (
            fun fmt ->
              Printexc.to_string e
              |> Format.fprintf fmt "during test generation:@ %s"
          )
        )
    )
end

(** Contract generation.
Generates contracts by running invariant generation techniques. *)
module RunContractGen: PostAnalysis = struct
  let name = "contractgen"
  let title = "contract generation"
  let is_active () = Flags.Contracts.contract_gen ()
  let run in_sys param results =
    let top = (Anal.info_of_param param).Anal.top in
    Event.log L_warn
      "Contract generation is a very experimental feature:@ \
      in particular, the modes it generates might not be exhaustive,@ \
      which means that Kind 2 will consider the contract unsafe.@ \
      This can be dealt with by adding a wild card mode:@ \
      mode wildcard () ;" ;
    let _, node_of_scope =
      InputSystem.contract_gen_param in_sys
    in
    (* Building transition system and slicing info. *)
    let sys, in_sys_sliced =
      ISys.contract_gen_trans_sys_of ~preserve_sig:true in_sys param
    in
    let target = Flags.subdir_for top in
    (* Create directories if they don't exist. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    let target =
      Format.asprintf "%s/kind2_contract.lus" target
    in
    LustreContractGen.generate_contracts
      in_sys_sliced param sys node_of_scope target ;
    Ok ()
end

(** Rust generation.
Compiles lustre as Rust. *)
module RunRustGen: PostAnalysis = struct
  let name = "rustgen"
  let title = "rust generation"
  let is_active () = Flags.lus_compile ()
  let run in_sys param results =
    Event.log L_warn
      "Compilation to Rust is still a rather experimental feature:@ \
      in particular, arrays are not supported." ;
    let top = (Anal.info_of_param param).Anal.top in
    let target = Flags.subdir_for top in
    (* Creating directories if needed. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    (* Implementation directory. *)
    let target = Format.sprintf "%s/%s" target Paths.implem in
    Event.log_uncond
      "  Compiling node \"%a\" to Rust in `%s`."
      Scope.pp_print_scope top target ;
    InputSystem.compile_to_rust in_sys top target ;
    Event.log_uncond "  Done compiling." ;
    Ok ()
end

(** Invariant log.
Minimizes and logs invariants used in the proof. *)
module RunInvLog: PostAnalysis = struct
  let name = "invlog"
  let title = "invariant logging"
  let is_active () = Flags.log_invs ()
  let run in_sys param results =
    Err (
      fun fmt -> Format.fprintf fmt "Invariant logging is unimplemented."
    )
end

(** Invariant log.
Certifies the last proof. *)
module RunCertif: PostAnalysis = struct
  let name = "certification"
  let title = name
  let is_active () = Flags.Certif.certif ()
  let run in_sys param results =
    let top = (Anal.info_of_param param).Anal.top in
    last_result results top |> chain (
      fun result ->
        let sys = result.Anal.sys in
        let uid = (Anal.info_of_param param).Anal.uid in
        ( if Flags.Certif.proof () then
            CertifChecker.generate_all_proofs uid in_sys sys
          else
            CertifChecker.generate_smt2_certificates uid in_sys sys
        ) ;
        Ok ()
    )
end

(** List of post-analysis modules. *)
let post_analysis = [
  (module RunTestGen: PostAnalysis) ;
  (module RunContractGen: PostAnalysis) ;
  (module RunRustGen: PostAnalysis) ;
  (module RunInvLog: PostAnalysis) ;
  (module RunCertif: PostAnalysis) ;
]

(** Runs the post-analysis things on a system and its results.
Produces a list of results, on for each thing. *)
let run_post_analysis i_sys param results =
  post_analysis |> List.iter (
    fun m ->
      let module Module = (val m: PostAnalysis) in
      if Module.is_active () then (
        Event.log_post_analysis_start Module.name Module.title ;
        (* Event.log_uncond "Running @{<b>%s@}." Module.title ; *)
        try
          ( match Module.run i_sys param results with
            | Ok () -> ()
            | Err err -> Event.log L_warn "@[<v>%t@]" err
          ) ;
          Event.log_post_analysis_end ()
        with e ->
          Event.log_post_analysis_end () ;
          raise e
      )
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
  | `INVGEN -> renice () ; InvGen.main_bool true
  | `INVGENOS -> renice () ; InvGen.main_bool false
  | `INVGENINT -> renice () ; InvGen.main_int true
  | `INVGENINTOS -> renice () ; InvGen.main_int false
  | `INVGENREAL -> renice () ; InvGen.main_real true
  | `INVGENREALOS -> renice () ; InvGen.main_real false
  | `C2I -> renice () ; C2I.main
  | `Interpreter -> Flags.Interpreter.input_file () |> Interpreter.main
  | `Supervisor -> InvarManager.main child_pids
  | `Parser | `Certif -> ( fun _ _ _ -> () )

(** Cleanup function of the process *)
let on_exit_of_process = function
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
let analyze msg_setup modules results in_sys param sys =
  Stat.start_timer Stat.analysis_time ;

  ( if TSys.has_properties sys |> not then
      Event.log L_warn
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
      InvarManager.main child_pids in_sys param sys ;

      (* Killing kids when supervisor's done. *)
      Some sys |> slaughter_kids `Supervisor
  ) ;

  let result =
    Stat.get_float Stat.analysis_time
    |> Analysis.mk_result param sys
  in
  let results = Analysis.results_add result results in

  (* Issue analysis end notification. *)
  Event.log_analysis_end result ;
  (* Issue analysis outcome. *)
  Event.log L_info "Result: %a" Analysis.pp_print_result result ;

  (* Run post-analysis things. *)
  ( try
      run_post_analysis in_sys param results
    with e ->
      Event.log L_fatal
        "Caught %s in post-analysis treatment."
        (Printexc.to_string e)
  ) ;

  results

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
        ISys.trans_sys_of_analysis in_sys param
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
    let rec loop results =
      match ISys.next_analysis_of_strategy in_sys results with
      
      | Some param ->
        (* Build trans sys and slicing info. *)
        let sys, in_sys_sliced =
          ISys.trans_sys_of_analysis in_sys param
        in
        (* Analyze... *)
        analyze msg_setup modules results in_sys param sys
        (* ...and loop. *)
        |> loop

      | None -> results
    in

    (* Set module currently running *)
    Event.set_module `Supervisor ;
    (* Initialize messaging for invariant manager, obtain a background thread.
    No kids yet. *)
    Event.run_im msg_setup [] (on_exit None `Supervisor None) |> ignore ;
    Event.log L_debug "Messaging initialized in supervisor." ;

    try (
      (* Run everything. *)
      let results =
        Analysis.mk_results () |> loop |> Analysis.results_clean
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

      post_clean_exit `Supervisor (Some results) Exit

    ) with e ->
      (* Get backtrace now, Printf changes it *)
      let backtrace = Printexc.get_raw_backtrace () in

      if Printexc.backtrace_status () then
        Event.log L_fatal "Caught %s in %a.@\nBacktrace:@\n%a"
          (Printexc.to_string e)
          pp_print_kind_module `Supervisor
          print_backtrace backtrace;

      on_exit None `Supervisor None e

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)