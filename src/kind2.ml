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

(*

module Dummy =
struct
  let main _ = failwith "not implemented"
  let on_exit _ = ()
end
*)

module BMC = Base
module IND = Step
module IND2 = Step2
module TestGen = TestgenDF
module C2I = C2I
module C2Icnf = C2Icnf
module Flow = Kind2Flow


(* Hide existential type parameter of to construct values of 'a InputSystem.t
   at runtime *)
type any_input =
| Input : 'a InputSystem.t -> any_input

let children_pgid = ref 0

(* Child processes forked

   This is an association list of PID to process type. We need a
   reference here, because we may need to terminate asynchronously
   after an exception. *)
let child_pids = ref []

(* Input system. *)
let input_sys_ref = ref None
(* Current input system. *)
let cur_input_sys = ref None
(* Current analysis params. *)
let cur_aparam = ref None
(* Current transition system. *)
let cur_trans_sys = ref None


(* let get_input_sys_ref () = *)
(*   let Input i = get !input_sys_ref in i *)

(* Generic signal handler. *)
let generic_sig_handler = Sys.Signal_handle exception_on_signal
(* Installs a generic signal handler for a signal. *)
let set_generic_handler_for s =
  Sys.set_signal s generic_sig_handler

(* Installs the relevant handler for sigalrm:
   - default if no timeout, or
   - [timeout] - [Stat.total_time] if there is one.
   Raises [TimeoutWall] if [timeout] < [Stat.total_time]. *)
let set_sigalrm_handler () =
  match Flags.timeout_wall () with

  | timeout when timeout > 0. ->

    (* Retrieving total time. *)
    let elapsed = Stat.get_float Stat.total_time in

    if timeout < elapsed then raise TimeoutWall else (

      (* Install signal handler for SIGALRM after wallclock timeout. *)
      Sys.set_signal Sys.sigalrm (Sys.Signal_handle
        (fun _ -> raise TimeoutWall)
      ) ;
      (* Set interval timer for wallclock timeout. *)
      Unix.setitimer Unix.ITIMER_REAL {
          Unix.it_interval = 0. ; Unix.it_value = timeout -. elapsed
      } |> ignore

    )

  | _ ->
    (* No timeout. *)
    let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
      Unix.setitimer
        Unix.ITIMER_REAL
        { Unix.it_interval = 0.; Unix.it_value = 0. }
    in
    (* Install generic signal handler for SIGALRM. *)
    set_generic_handler_for Sys.sigalrm

(* Renices the current process. Used for invariant generation. *)
let renice () =
  let nice =  (Flags.Invgen.renice ()) in

  if nice < 0 then
    Event.log L_info
      "Ignoring negative niceness value for invariant generation."

  else if nice > 0 then
    let nice' = Unix.nice nice in
    Event.log L_info "Renicing invariant generation to %d" nice'

(* Main function of the process *)
let main_of_process = function
  | `IC3 -> IC3.main
  | `BMC -> BMC.main
  | `IND -> IND.main
  | `IND2 -> IND2.main
  | `INVGEN -> renice () ; InvGen.main true
  | `INVGENOS -> renice () ; InvGen.main false
  | `C2I -> renice () ; C2I.main
  | `Interpreter -> Interpreter.main (Flags.Interpreter.input_file ())
  | `Supervisor -> InvarManager.main child_pids
  | `Parser | `Certif -> (fun _ _ _ -> ())

(* Cleanup function of the process *)
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

(*
(* Messaging type of the process *)
let init_messaging_of_process = function 
  | `IC3 -> Kind2Message.init_ic3
  | `BMC -> Kind2Message.init_bmc
  | `IND -> Kind2Message.init_indStep
  | `INVGEN -> Kind2Message.init_invarGen 
  | `Supervisor -> Kind2Message.init_invarManager (List.map fst !child_pids)
*)


let debug_ext_of_process = function
  | `IC3 -> "ic3"
  | `BMC -> "bmc"
  | `IND -> "ind"
  | `IND2 -> "ind2"
  | `INVGEN -> "invgenTS"
  | `INVGENOS -> "invgenOS"
  | `C2I -> "c2i"
  | `Interpreter -> "interp"
  | `Parser -> "parser"
  | `Certif -> "certif"
  | `Supervisor -> "super"

(* Exit status if timeout *)
let status_timeout = 0
(* Exit status if one property is falsifiable. *)
let status_unsafe = 10
(* Exit status if all properties are valid. *)
let status_safe = 20

(* Decides what the exit status is by looking at a transition system.

   The exit status is
   * 0 if some properties are unknown or k-true (timeout),
   * 10 if some properties are falsifiable (unsafe),
   * 20 if all properties are invariants (safe). *)
let status_of_trans_sys sys =
  (* Checking if some properties are unknown of falsifiable. *)
  let unknown, falsifiable =
    TransSys.get_prop_status_all_nocands sys
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
    if unknown then status_timeout
    else if falsifiable then status_unsafe
    else status_safe
  in
  (* Exit status. *)
  exit_status

(* Exit status if child caught a signal, the signal number is added to
   the value *)
let status_signal = 128

(* Exit status if child raised an exception *)
let status_error = 2

(* Exit status from an optional [results]. *)
let status_of_sys sys_opt = match sys_opt with
| None -> Format.eprintf "NOSYS@."; status_timeout
| Some sys -> status_of_trans_sys sys

(* Exit status from an optional [results]. *)
let status_of_results results_opt = match results_opt with
| None -> Format.eprintf "NORES@."; status_timeout
| Some results -> (
  match Analysis.results_is_safe results with
  | None -> Format.eprintf "NOSAFERES@."; status_timeout
  | Some true -> status_safe
  | Some false -> status_unsafe
)

(* Return the status code from an exception *)
let status_of_exn process status = function
  (* Normal termination *)
  | Exit -> status

  (* Got unknown, issue error but normal termination. *)
  | SMTSolver.Unknown ->
    Event.log L_error
      "In %a: a check-sat resulted in \"unknown\", exiting."
      pp_print_kind_module process ;
    status

  (* Termination message *)
  | Event.Terminate -> (

    Event.log L_debug
      "Received termination message" ;

    status

  ) 

  (* Catch wallclock timeout *)
  | TimeoutWall -> (

    Event.log_timeout true ;

    status

  ) 

  (* Catch CPU timeout *)
  | TimeoutVirtual -> (

    Event.log_timeout false ;

    status

  ) 

  (* Signal caught *)
  | Signal s -> (

    Event.log_interruption s ;

    (* Return exit status and signal number *)
    status_signal + s

  )

  | Failure msg ->
    Event.log L_fatal
      "Runtime failure in %a: %s"
      pp_print_kind_module process
      msg ;
    status_error

  (* Other exception, return exit status for error. *)
  | e ->
    Event.log L_fatal
      "Runtime error in %a: %s"
      pp_print_kind_module process
      (Printexc.to_string e) ;
    status_error

let status_of_exn_sys process sys_opt =
  status_of_exn process (status_of_sys sys_opt)

let status_of_exn_results process results_opt =
  status_of_exn process (status_of_results results_opt)

(* Kill all kids violently. *)
let slaughter_kids process sys =

  (* Ignore SIGALRM from now on *)
  Sys.set_signal Sys.sigalrm Sys.Signal_ignore ;

  (* Clean exit from invariant manager *)
  InvarManager.on_exit sys ;

  Event.log L_info "Killing all remaining child processes";

  (* Kill all child processes groups *)
  List.iter
    (function pid, _ ->

      Event.log L_debug "Sending SIGKILL to PID %d" pid ;

      try Unix.kill (- pid) Sys.sigkill with _ -> ())

    !child_pids ;

  Event.log L_debug
    "Waiting for remaining child processes to terminate" ;

  (try
     while true do
       (* Wait for child process to terminate *)
       let pid, status = Unix.wait () in
       (* Remove killed process from list *)
       child_pids := List.remove_assoc pid !child_pids ;

       (* Log termination status *)
       Event.log L_debug
         "Process %d %a" pid pp_print_process_status status
     done
   with

   (* No more child processes, this is the normal exit *)
   | Unix.Unix_error (Unix.ECHILD, _, _) ->

     Event.log L_info
       "All child processes terminated." ;

     (* Unix.wait was interrupted *)
   | Unix.Unix_error (Unix.EINTR, _, _) ->

     (* Ignoring exit code, whatever happened does not change the
        outcome of the analysis. *)
     status_of_exn_sys process None (Signal 0) |> ignore

   (* Exception in Unix.wait loop *)
   | e ->

     (* Ignoring exit code, whatever happened does not change the
        outcome of the analysis. *)
     status_of_exn_sys process None e |> ignore ;
  );

  if !child_pids <> [] then
    Event.log L_fatal "Some children did not exit.";
  
  (* Install generic signal handler for SIGALRM. *)
  set_generic_handler_for Sys.sigalrm ;

  (* Cleaning kids list. *)
  child_pids := [] ;

  (* Draining mailbox. *)
  Event.recv () |> ignore ;

  (* Restore sigalrm handler for next analysis if any. *)
  set_sigalrm_handler ()



(* Called after everything has been cleaned up. All kids dead etc. *)
let clean_exit process results exn =

  (* Exit status of process depends on exception *)
  let status = status_of_exn_results process results exn in

  (* Close tags in XML output *)
  Event.terminate_log () ;

  (* Exit with status *)
  exit status

(* Clean up before exit *)
let on_exit process results exn =

(*
  let pp_print_hashcons_stat ppf (l, c, t, s, m, g) =

    Format.fprintf
      ppf
      "Number of buckets: %d@,\
       Number of entries in table: %d@,\
       Sum of sizes of buckets: %d@,\
       Size of smallest bucket: %d@,\
       Median bucket size: %d@,\
       Size of greatest bucket: %d@,"
      l
      c
      t
      s
      m
      g

  in

  Event.log L_info
    "@[<hv>Hashconsing for state variables:@,%a@]"
    pp_print_hashcons_stat (StateVar.stats ());

  Event.log L_info
    "@[<hv>Hashconsing for variables:@,%a@]"
    pp_print_hashcons_stat (Var.stats ());

  Event.log L_info
    "@[<hv>Hashconsing for terms:@,%a@]"
    pp_print_hashcons_stat (Term.stats ());

  Event.log L_info
    "@[<hv>Hashconsing for symbols:@,%a@]"
    pp_print_hashcons_stat (Symbol.stats ());
*)

  (* Killing kids. *)
  try
    slaughter_kids process (!cur_trans_sys)
  with
    (* We're past the timeout, but we're exiting anyways. *)
    TimeoutWall -> () ;

  (* Exiting. *)
  clean_exit process None exn


(* Call cleanup function of process and exit.

   Give the exception [exn] that was raised or [Exit] on normal
   termination. *)
let on_exit_child ?(alone=false) messaging_thread process exn =

  (* Exit status of process depends on exception *)
  let status = status_of_exn process 0 exn in

  (* Call cleanup of process *)
  (on_exit_of_process process) !cur_trans_sys ;

  Event.log L_debug
    "Process %d terminating"
    (Unix.getpid ()) ;

  ( match messaging_thread with
    | Some t -> Event.exit t
    | None -> () ) ;

  Debug.kind2
    "Process %a terminating" pp_print_kind_module process ;

  (* Log stats and statuses of properties if run as a single process *)
  (* if alone then Event.log_result sys_opt; *)

  Event.terminate_log ();

  (* Exit process with status *)
  exit status



(* Fork and run a child process *)
let run_process messaging_setup process =

  (* Fork a new process *)
  let pid = Unix.fork () in

  match pid with

    (* We are the child process *)
    | 0 -> (

        (* Make the process leader of a new session *)
        ignore (Unix.setsid ());

        let pid = Unix.getpid () in

        (* Ignore SIGALRM in child process *)
        Sys.set_signal Sys.sigalrm Sys.Signal_ignore;

        (* Initialize mtessaging system for process *)
        let messaging_thread =
          Event.run_process 
            process
            messaging_setup
            (on_exit_child None process)
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

          (

            (* Change debug output to per process file *)
            match Flags.debug_log () with 

              (* Keep if output to stdout *)
              | None -> ()

              (* Open channel to given file and create formatter on
                 channel *)
              | Some f ->

                try 

                  (* Output to f.PROCESS-PID *)
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

          );

          let Input cur_in_sys = get !cur_input_sys in
          
          (* Run main function of process *)
          (main_of_process process) 
            cur_in_sys
            (get !cur_aparam)
            (get !cur_trans_sys);

          (* Cleanup and exit *)
          on_exit_child (Some messaging_thread) process Exit

        with 

          (* Termination message received *)
          | Event.Terminate as e ->
            on_exit_child (Some messaging_thread) process e

          (* Catch all other exceptions *)
          | e ->

            (* Get backtrace now, Printf changes it *)
            let backtrace = Printexc.get_raw_backtrace () in

            if Printexc.backtrace_status () then (
              Event.log L_fatal
                "Caught %s in %a.@\nBacktrace:@\n%a"
                (Printexc.to_string e)
                pp_print_kind_module process
                print_backtrace backtrace
            ) ;

            (* Cleanup and exit *)
            on_exit_child (Some messaging_thread) process e

      )

    (* We are the parent process *)
    | _ -> 

      (* Keep PID of child process and return *)
      child_pids := (pid, process) :: !child_pids


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

  (* Set sigalrm handler. *)
  set_sigalrm_handler () ;

  (*
    /!\ ================================================================== /!\
    /!\ Must not use [vtalrm] signal, this is used internally by the OCaml /!\
    /!\                        [Threads] module.                           /!\
    /!\ ================================================================== /!\
  *)

  (* Raise exception on CTRL+C. *)
  Sys.catch_break true ;

  (* Install generic signal handler for SIGINT, SIGPIPE, SIGTERM and SIGQUIT. *)
  [ Sys.sigint ; Sys.sigpipe; Sys.sigterm ; Sys.sigquit ]
  |> List.iter set_generic_handler_for ;

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
    | `Horn   -> (* InputSystem.read_input_horn *)   assert false
  with (* Could not create input system. *)
  | LustreAst.Parser_error ->
    (* Don't do anything for parser error, they should already have printed
    some stuff. *)
    Event.terminate_log () ;
    exit status_error
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

    exit status_error

let tests_path = "tests"
let oracle_path = "oracle"
let implem_path = "implem"

(* Runs test generation on the system (scope) specified by abstracting
   everything. *)
let run_testgen input_sys top =
  if Flags.Testgen.active () then (
    match InputSystem.maximal_abstraction_for_testgen input_sys top [] with
    | None ->
      Event.log L_warn
        "System %a has no contracts, skipping test generation."
        Scope.pp_print_scope top

    | Some param ->
      (* Create root dir if needed. *)
      Flags.output_dir () |> mk_dir ;
      let target = Flags.subdir_for top in
      (* Create system dir if needed. *)
      mk_dir target ;

      let param = match param with
        | Analysis.ContractCheck info -> Analysis.ContractCheck {
          info with Analysis.uid = info.Analysis.uid * 1000
        }
        | Analysis.First info -> Analysis.First {
          info with Analysis.uid = info.Analysis.uid * 1000
        }
        | Analysis.Refinement (info, res) -> Analysis.Refinement (
          { info with Analysis.uid = info.Analysis.uid * 1000 },
          res
        )
      in

      (* Extracting transition system. *)
      let sys, input_sys_sliced =
        InputSystem.trans_sys_of_analysis ~preserve_sig:true input_sys param
      in

      (* Let's do this. *)
      try (
        let tests_target = Format.sprintf "%s/%s" target tests_path in
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
        let oracle_target = Format.sprintf "%s/%s" target oracle_path in
        mk_dir oracle_target ;
        Event.log_uncond
          "%sCompiling oracle to Rust for node \"%a\" to `%s`."
          TestGen.log_prefix Scope.pp_print_scope top oracle_target ;
        let name, guarantees, modes =
          InputSystem.compile_oracle_to_rust input_sys top oracle_target
        in
        Event.log_uncond
          "%sGenerating glue xml file to `%s/.`." TestGen.log_prefix target ;
        testgen_xmls
        |> List.map (fun xml -> Format.sprintf "%s/%s" tests_path xml)
        |> TestGen.log_test_glue_file
          target name (oracle_path, guarantees, modes) implem_path ;
        Event.log_uncond
          "%sDone with test generation." TestGen.log_prefix
      ) with e -> (
        TestGen.on_exit "T_T" ;
        raise e
      )
  )

(* Compiles a system (scope) to Rust. *)
let compile_to_rust input_sys top =
  if Flags.lus_compile () then (
    (* Creating root dir if needed. *)
    Flags.output_dir () |> mk_dir ;
    let target = Flags.subdir_for top in
    (* Creating system subdir if needed. *)
    mk_dir target ;
    (* Implementation directory. *)
    let target = Format.sprintf "%s/%s" target implem_path in
    Event.log_uncond
      "[TO_RUST] Compiling node \"%a\" to Rust in `%s`."
      Scope.pp_print_scope top target ;
    InputSystem.compile_to_rust input_sys top target ;
    Event.log_uncond "[TO_RUST] Done compiling."
  )

(* Generate certificates and or proofs *)
let generate_certif_proofs uid input_sys trans_sys =
  if Flags.Certif.certif () then
    if Flags.Certif.proof () then
      CertifChecker.generate_all_proofs uid input_sys trans_sys
    else
      CertifChecker.generate_smt2_certificates uid input_sys trans_sys


(* Runs test generation and compilation if asked to. *)
let post_verif input_sys result =
  if Analysis.result_is_all_proved result then (
    let trans_sys = result.Analysis.sys in
    let top_scope = TransSys.scope_of_trans_sys trans_sys in
    run_testgen input_sys top_scope ;
    compile_to_rust input_sys top_scope;
    let uid = Analysis.(info_of_param result.param).Analysis.uid in
    generate_certif_proofs uid input_sys trans_sys;
  )

(* Launches analyses. *)
let rec run_loop msg_setup modules results =
  Stat.start_timer Stat.analysis_time ;

  let aparam, Input input_sys, trans_sys =
    get !cur_aparam, get !cur_input_sys, get !cur_trans_sys
  in

  ( match TransSys.props_list_of_bound trans_sys Numeral.zero with

    | [] ->
      if Flags.modular () |> not then
        Event.log L_warn "Current system has no properties."
      else ()

    | props ->

      (* Event.log L_fatal "Launching analysis with param %a"
        Analysis.pp_print_param aparam ; *)
      Event.log_analysis_start trans_sys aparam ;

      (* Output the transition system. *)
      Debug.parse "%a" TransSys.pp_print_trans_sys trans_sys;

      List.length props |> Event.log L_info "%d properties." ;

      Event.log L_debug "Starting child processes." ;

      (* Start all child processes. *)
      List.iter (function p -> run_process msg_setup p) modules ;

      (* Update background thread with new kids. *)
      Event.update_child_processes_list !child_pids ;

      (* Running supervisor. *)
      InvarManager.main child_pids input_sys aparam trans_sys ;

      (* Killing kids. *)
      Some trans_sys |> slaughter_kids `Supervisor
  ) ;

  let result =
    Stat.get_float Stat.analysis_time |> Analysis.mk_result aparam trans_sys
  in

  Event.log_analysis_end result ;

  Event.log L_info "Result: %a" Analysis.pp_print_result result ;

  let results = Analysis.results_add result results in

  let Input input_sys = get !input_sys_ref in
  
  match InputSystem.next_analysis_of_strategy input_sys results with

  (* No next analysis, done. *)
  | None -> results

  (* Preparing for next analysis. *)
  | Some aparam ->
    (* Extracting transition system. *)
    let trans_sys, input_sys_sliced =
      InputSystem.trans_sys_of_analysis input_sys aparam in

    (* Memorizing things. *)
    cur_aparam    := Some aparam           ;
    cur_input_sys := Some (Input input_sys_sliced) ;
    cur_trans_sys := Some trans_sys        ;

    (* Looping. *)
    run_loop msg_setup modules results


(* Looks at the modules activated and decides what to do. *)
let launch input_sys =

  let results = Analysis.mk_results () in

  let Input in_sys = input_sys in
  
  (* Retrieving params for next analysis. *)
  let aparam =
    match InputSystem.next_analysis_of_strategy in_sys results with
    | Some a -> a | None -> assert false
  in

  (* Building transition system and slicing info. *)
  let trans_sys, input_sys_sliced =
    InputSystem.trans_sys_of_analysis in_sys aparam
  in

  (* Memorizing things. *)
  cur_input_sys := Some (Input input_sys_sliced) ;
  cur_aparam    := Some aparam ;
  cur_trans_sys := Some trans_sys ;

  (* Dump transition system in native format *)
  (* if Flags.dump_native () then NativeInput.dump_native trans_sys; *)

  (* Checking what's activated. *)
  match Flags.enabled () with

  (* No modules enabled. *)
  | [] ->
    Event.log L_fatal "Need at least one process enabled." ;
    exit status_error

  (* Only the interpreter is running. *)
  | [m] when m = `Interpreter ->

    (* Set module currently running. *)
    Event.set_module m ;

    let Input cur_sys = get !cur_input_sys in
      
    (* Run interpreter. *)
    Interpreter.main
      (Flags.Interpreter.input_file ())
      cur_sys
      (get !cur_aparam)
      (get !cur_trans_sys) ;

    (* Ignore SIGALRM from now on *)
    Sys.set_signal Sys.sigalrm Sys.Signal_ignore ;

    (* Cleanup before exiting process *)
    on_exit_child None m Exit

  (* Some modules, including the interpreter. *)
  | modules when List.mem `Interpreter modules ->
    Event.log L_fatal "Cannot run the interpreter with other processes." ;
    exit status_error

  (* Some modules, not including the interpreter. *)
  | modules ->

    Event.log L_info
      "@[<hov>Running in parallel mode: @[<v>- %a@]@]"
      (pp_print_list pp_print_kind_module "@ - ")
      modules ;

    (* Setup messaging. *)
    let msg_setup = Event.setup () in

    (* Set module currently running *)
    Event.set_module `Supervisor ;

    (* Initialize messaging for invariant manager, obtain a background
       thread. No kids yet. *)
    Event.run_im msg_setup [] (on_exit `Supervisor None) |> ignore ;

    Event.log L_debug "Messaging initialized in supervisor." ;

    try

      (* Running. *)
      let results =
        run_loop msg_setup modules results |> Analysis.results_clean
      in

      (* Producing a list of the last results for each system, in topological
         order. *)
      let Input input_sys = get !input_sys_ref in
      input_sys |> InputSystem.ordered_scopes_of
      (* |> fun syss ->
        Format.printf "%d systems@.@." (List.length syss) ;
        Format.printf "systems: @[<v>%a@]@.@."
          (pp_print_list Scope.pp_print_scope "@ ") syss ;
        syss *)
      |> List.fold_left (fun l sys ->
        (* Format.printf "sys: %a@.@." Scope.pp_print_scope sys ; *)
        try (
          match Analysis.results_find sys results with
          | last :: _ ->
            (* Running post verification things. *)
            post_verif input_sys last ;
            last :: l
          | [] -> assert false
        ) with
        | Not_found -> l
        | Failure s ->
          Event.log L_fatal "Failure: %s" s;
          l
        | e ->
          Event.log L_fatal "%s" (Printexc.to_string e) ; l
      ) []
      (* Logging the end of the run. *)
      |> Event.log_run_end ;

      clean_exit `Supervisor (Some results) Exit

    with e ->
      (* Get backtrace now, Printf changes it *)
      let backtrace = Printexc.get_raw_backtrace () in

      if Printexc.backtrace_status () then
        Event.log L_fatal "Caught %s in %a.@\nBacktrace:@\n%a"
          (Printexc.to_string e)
          pp_print_kind_module `Supervisor
          print_backtrace backtrace;

      on_exit `Supervisor None e


(* Entry point *)
let main () =

  (* Set everything up and produce input system. *)
  let input_sys = setup () in
  input_sys_ref := Some input_sys ;

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
  | None -> (

    (* Are we just generating contracts?. *)
    if Flags.Contracts.contract_gen () then (
      Event.log L_warn
        "Contract generation is a very experimental feature:@ \
        in particular, the modes it generates might not be exhaustive,@ \
        which means that Kind 2 will consider the contract unsafe.@ \
        This can be dealt with by adding a wild card mode:@ \
        mode wildcard () ;" ;
      let Input input_sys = input_sys in

      let param, node_of_scope =
        InputSystem.contract_gen_param input_sys
      in

      (* Building transition system and slicing info. *)
      let trans_sys, input_sys_sliced =
        InputSystem.contract_gen_trans_sys_of
          ~preserve_sig:true input_sys param
      in

      let target =
        Flags.output_dir () |> mk_dir ;
        Flags.output_dir () |> Format.sprintf "%s/spec_by_kind2.lus"
      in

      LustreContractGen.generate_contracts
        input_sys_sliced trans_sys param node_of_scope target

    ) else
      launch input_sys
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
  
