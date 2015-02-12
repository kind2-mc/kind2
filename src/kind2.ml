(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

module Log = Log
module BMC = Base
module IND = Step
module PDR = PDR
module InvGenTS = InvGenGraph.TwoState
module InvGenOS = InvGenGraph.OneState

(* Child processes forked.

  This is an association list of PID to process type. We need a
  reference here, because we may need to terminate asynchronously
  after an exception. *)
let child_pids = ref []

(* Remembers the messaging setup for restarts. *)
let messaging_setup_opt = ref None

(* Pretty prints a kind module from a pid by looking in
   [child_pids]. *)
let pp_print_kind_module_of_pid ppf pid =
  try
    List.assoc pid !child_pids
    |> Format.fprintf
         ppf "%a" pp_print_kind_module
  with Not_found ->
    Format.fprintf ppf "unknown"

(* Reference to the top-most transition system for clean exit. *)
let trans_sys = ref None

(* Reference to the transition system currently under analysis. *)
let current_trans_sys = ref None


(* Handle events by broadcasting messages, updating local transition
   system version etc. Returns [true] iff it received at least one
   message. *)
let handle_events ?(silent_recv = false) trans_sys =

  (* Receive queued events. *)
  let events =

    if silent_recv then (
      (* Temporarily silencing log. *)
      set_log_level L_warn ;
    ) ;

    let evts = Event.recv () in

    if silent_recv then (
    (* Reactivating log. *)
      set_log_level (Flags.log_level ())
    ) ;

    evts
  in

  (* Output events. *)
  List.iter 
    (function (m, e) -> 
      Event.log
        L_debug
        "Message received from %a: %a"
        pp_print_kind_module m
        Event.pp_print_event e)
    events;

  (* Update transition system from events. *)
  Event.update_trans_sys trans_sys events |> ignore

(* Aggregates functions related to starting processes. *)
module Start = struct

  (* Renices a process. *)
  let renice_process module_string nice =
    if nice < 0 then
      (* Ignoring negative value. *)
      Event.log
        L_info
        "Ignoring negative niceness value for %s."
        module_string
    else if nice > 0 then
      (* Legal renicing value. *)
      Unix.nice nice
      |> Event.log
           L_info
           "Renicing %s to %d."
           module_string

  (* Returns the main function of a process. *)
  let main_of_process = function
    | `BMC -> BMC.main

    | `IND -> IND.main

    | `PDR -> PDR.main

    | `INVGEN ->
       (* Renicing two state invgen. *)
       Flags.invgengraph_renice ()
       |> renice_process "two state invariant generation" ;
       (* Returning main function. *)
       InvGenTS.main

    | `INVGENOS ->
       (* Renicing one state invgen. *)
       Flags.invgengraph_renice ()
       |> renice_process "one state invariant generation" ;
       (* Returning main function. *)
       InvGenOS.main

    | `Interpreter ->
       (* Launches the interpreter on the input file. *)
       Flags.interpreter_input_file ()
       |> Interpreter.main

    | `Supervisor
    | `Parser ->
       (* This should never happen. *)
       assert false

end

(* Aggregates functions related to stopping processes. *)
module Stop = struct

  (* Cleanup function of a process. *)
  let on_exit_of_process = function
    | `PDR -> PDR.on_exit
    | `BMC -> BMC.on_exit
    | `IND -> IND.on_exit
    | `INVGEN -> InvGenTS.on_exit
    | `INVGENOS -> InvGenOS.on_exit
    | `Interpreter -> Interpreter.on_exit
    | `Supervisor
    | `Parser ->
       Format.printf "Requested on_exit on supervisor or parser.\n" ;
       (* This should never happen. *)
       assert false

  (* Exit status if child terminated normally. *)
  let status_ok = 0

  (* Exit status if child caught a signal, the signal number is added
   to the value. *)
  let status_signal = 128

  (* Exit status if child raised an exception. *)
  let status_error = 2

  (* Exit status if timed out. *)
  let status_timeout = 3

  (* Returns the status corresponding to an exception, possibly
   notifying the user in the process. *)
  let status_of_exn process = function

    (* Normal termination. *)
    | Exit ->
       status_ok

    (* Termination message. *)
    | Event.Terminate ->
       Event.log
         L_info "Received termination message." ;
       status_ok

    (* Catch wallclock timeout. *)
    | TimeoutWall ->
       Event.log
         L_error "%s Wallclock timeout." timeout_tag ;
       status_timeout

    (* Catch CPU timeout. *)
    | TimeoutVirtual ->
       Event.log
         L_error "%s CPU timeout." timeout_tag ;
       status_timeout

    (* Signal caught. *)
    | Signal s ->
       ( match Event.get_module () with
         | `Supervisor ->
            Event.log
              L_fatal
              "%s Caught signal%t. Terminating."
              interruption_tag
              ( fun ppf ->
                match s with
                | 0 -> ()
                | _ -> string_of_signal s |> Format.fprintf ppf " %s" ) ;
         | _ -> () ) ;
       (* Return exit status and signal number. *)
       status_signal + s

    (* Other exception. *)
    | e ->
       (* Get backtrace now, Printf changes it. *)
       let backtrace = Printexc.get_backtrace () in
       (* Outputting info about the error. *)
       Printexc.to_string e
       |> Event.log
            L_fatal
            "%s Runtime error: %s"
            error_tag ;
       if Printexc.backtrace_status () then
         (* Outputting backtrace. *)
         Event.log
           L_debug "Backtrace:@\n%s" backtrace ;
       (* Return exit status for error. *)
       status_error

  (* Prints the final statistics of the analysis. *)
  let print_final_statistics () =

    (* Printing header. *)
    Event.log
      L_info
      "@[<v>%a@,Final statistics:@]"
      pp_print_hline () ;

    (* Printing stats for each module. *)
    Event.all_stats ()
    |> List.iter
         ( fun (mdl, stat) ->
           Event.log_stat mdl L_info stat ) ;

    (* Printing result for the properties of the top level. *)
    (* TODO: this should be factored and changed for compositional
       analysis. Probably a function printing the (sub)system(s)
       should be passed as an argument, or should be set statically by
       looking at the flags. *)
    match !current_trans_sys with
    | None -> ()
    | Some sys ->
       TransSys.get_prop_status_all_unknown sys
       |> Event.log_prop_status
            L_fatal

  (* Actually exits with an exit code. *)
  let actually_exit status =

    (* Close tags in XML output. *)
    Event.terminate_log () ;

    (* Exit with status. *)
    exit status

  (* Clean exit depending on a status. *)
  let clean_exit exit_after_killing_kids status =

    (* Log termination status. *)
    if not (!child_pids = []) then

      Event.log
        L_info
        "Processe(s) (%a) did not exit, killing them."
        (pp_print_list 
           (fun ppf (pid, _) -> Format.pp_print_int ppf pid) ",@ ") 
        !child_pids;

    (* Kill all remaining processes in the process groups of child
     processes. *)
    !child_pids
    |> List.iter
         ( fun (pid, _) ->
           try Unix.kill (- pid) Sys.sigkill
           with _ -> () ) ;

    (* Receiving last messages. *)
    ( match !current_trans_sys with
      | None -> ()
      | Some sys ->
         (* Minisleep to ensure messages send right before killing
            kids arrive. *)
         minisleep 0.01 ;

         handle_events ~silent_recv:true sys ) ;

    Event.log
      L_info
      "<TODO> Reactivate printing of final statistics." ;
    (* print_final_statistics () ; *)

    if exit_after_killing_kids then
      actually_exit status
    else (
      (* Restore signal handlers. *)

      (* Install generic signal handler for SIGINT. *)
      Sys.set_signal
        Sys.sigint
        (Sys.Signal_handle exception_on_signal) ;

      (* Install generic signal handler for SIGTERM. *)
      Sys.set_signal
        Sys.sigterm
        (Sys.Signal_handle exception_on_signal) ;

      (* Install generic signal handler for SIGQUIT. *)
      Sys.set_signal
        Sys.sigquit
        (Sys.Signal_handle exception_on_signal)
    )


  (* Clean up before exit. *)
  let on_exit exit_after_killing_kids process exn =

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

    (* Ignore SIGALRM from now on. *)
    Sys.set_signal Sys.sigalrm Sys.Signal_ignore;
    (* Ignore SIGINT from now on. *)
    Sys.set_signal Sys.sigint Sys.Signal_ignore;
    (* Ignore SIGTERM from now on. *)
    Sys.set_signal Sys.sigterm Sys.Signal_ignore;

    (* Exit status of process depends on exception. *)
    let status = status_of_exn process exn in
    
    Event.log L_info "Terminating all remaining child processes." ;

    (* Kill all child processes. *)
    List.iter 
      (function pid, _ ->
                     Unix.kill pid Sys.sigterm)

      !child_pids ;

    Event.log
      L_info
      "Waiting for remaining child processes to terminate." ;

    try

      (* Install signal handler for SIGALRM after wallclock timeout. *)
      Sys.set_signal
        Sys.sigalrm
        ( Sys.Signal_handle
            (fun _ -> raise TimeoutWall) ) ;

      (* Set interval timer for wallclock timeout. *)
      let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
        Unix.setitimer
          Unix.ITIMER_REAL 
          { Unix.it_interval = 0. ; Unix.it_value = 1. }
      in

      ( try

          while true do

            (* Wait for child process to terminate. *)
            let pid, status = Unix.wait () in

            (* Kill processes left in process group of child process. *)
            ( try Unix.kill (- pid) Sys.sigkill
              with _ -> () );

            (* Log termination status. *)
            Event.log
              L_info
              "Process %5d %a [%a]."
              pid
              pp_print_process_status status
              pp_print_kind_module_of_pid pid ;

            (* Remove killed process from list. *)
            child_pids := List.remove_assoc pid !child_pids

          done

        with TimeoutWall -> () ) ;

      clean_exit exit_after_killing_kids status

    with

    (* No more child processes, this is the normal exit. *)
    | Unix.Unix_error (Unix.ECHILD, _, _) ->

       (* Deactivate timer. *)
       let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
         Unix.setitimer
           Unix.ITIMER_REAL 
           { Unix.it_interval = 0. ; Unix.it_value = 0. }
       in

       Event.log
         L_info 
         "All child processes terminated.";

       clean_exit exit_after_killing_kids status

    (* Unix.wait was interrupted. *)
    | Unix.Unix_error (Unix.EINTR, _, _) ->

       (* Deactivate timer. *)
       let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
         Unix.setitimer
           Unix.ITIMER_REAL 
           { Unix.it_interval = 0. ; Unix.it_value = 0. }
       in

       (* Get new exit status. *)
       let status' = status_of_exn process (Signal 0) in

       clean_exit true status'

    (* Exception in Unix.wait loop. *)
    | e ->

       (* Deactivate timer. *)
       let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
         Unix.setitimer
           Unix.ITIMER_REAL 
           { Unix.it_interval = 0. ; Unix.it_value = 0. }
       in

       (* Get new exit status. *)
       let status' = status_of_exn process e in

       clean_exit true status'


  (* Call cleanup function of process and exit. 

   Give the exception [exn] that was raised or [Exit] on normal
   termination. *)
  let on_exit_child messaging_thread process exn =

    (* Exit status of process depends on exception. *)
    let status = status_of_exn process exn in

    (* Call cleanup of process. *)
    (on_exit_of_process process) !current_trans_sys ;

    (* Logging termination event. *)
    Unix.getpid ()
    |> Event.log
         L_info 
         "Process %d terminating." ;

    Event.terminate_log ();
    
    (match messaging_thread with 
     | Some t -> Event.exit t
     | None -> ());

    ( debug
        kind2
        "Process %a terminating."
        pp_print_kind_module process
      in

      (* Exit process with status. *)
      exit status )

end

(* Debug name of a process. *)
let debug_ext_of_process = suffix_of_kind_module


(* Remove terminated child processed from list of running processes.
   Return [true] if the last child processes has terminated or some
   process exited with a runtime error or was killed. *)
let rec wait_for_children child_pids =

  match 
    
    ( try
        (* Check if any child process has died, return immediately. *)
        Unix.waitpid [Unix.WNOHANG] (- 1) 

      with
        (* Catch error if there is no child process. *)
        Unix.Unix_error (Unix.ECHILD, _, _) -> 0, Unix.WEXITED 0 )

  with 

  (* No child process died. *)
  | 0, _ -> 

     (* Terminate if the last child process has died. *)
     !child_pids = []

  (* Child process exited normally. *)
  | child_pid, (Unix.WEXITED 0 as status) -> (

    Event.log
      L_info
      "Child process %d (%a) %a"
      child_pid 
      pp_print_kind_module (List.assoc child_pid !child_pids) 
      pp_print_process_status status ;

    (* Remove child process from list *)
    child_pids := List.remove_assoc child_pid !child_pids;

    (* Check if more child processes have died *)
    wait_for_children child_pids

  )

  (* Child process dies with non-zero exit status or was killed. *)
  | child_pid, status -> (

    Event.log
      L_error
      "Child process %d (%a) %a" 
      child_pid 
      pp_print_kind_module (List.assoc child_pid !child_pids) 
      pp_print_process_status status;

    (* Remove child process from list. *)
    child_pids := List.remove_assoc child_pid !child_pids;

    (* Check if more child processes have died. *)
    true

  )

(* Polling loop. *)
let rec polling_loop
          exit_after_killing_kids child_pids trans_sys = 

  handle_events trans_sys ;

  if TransSys.all_props_proved trans_sys then (
    Event.log
      L_warn
      "%s All properties proved or disproved in %.3fs."
      done_tag
      (Stat.get_float Stat.total_time) ;
    
    Stop.on_exit exit_after_killing_kids `Supervisor Exit

  ) else if
    (* Check if child processes have died and exit if necessary *)
    wait_for_children child_pids
  then
    Stop.on_exit exit_after_killing_kids `Supervisor Exit

  else (

    (* Sleep. *)
    minisleep 0.01 ;

    (* Continue polling loop. *)
    polling_loop exit_after_killing_kids child_pids trans_sys

  )



(* Fork and run a child process *)
let run_process messaging_setup process trans_sys depth_opt =

  (* Fork a new process *)
  let pid = Unix.fork () in

  match pid with 

    | 0 -> 
       (* We are the child process *)
       ( try

           (* Install generic signal handler for SIGTERM. *)
           Sys.set_signal
             Sys.sigterm
             (Sys.Signal_handle exception_on_signal) ;

           (* Install generic signal handler for SIGINT. *)
           (* Sys.set_signal *)
           (*   Sys.sigint *)
           (*   (Sys.Signal_handle exception_on_signal) ; *)

           (* Make the process leader of a new session. *)
           Unix.setsid () |> ignore ;

           let pid = Unix.getpid () in

           (* Ignore SIGALRM in child process. *)
           Sys.set_signal Sys.sigalrm Sys.Signal_ignore;

           (* Initialize messaging system for process. *)
           let messaging_thread =
             Event.run_process
               process
               messaging_setup
               (Stop.on_exit_child None process)
           in

           (* All log messages are sent to the invariant manager
              now. *)
           Event.set_relay_log ();

           (* Set module currently running. *)
           Event.set_module process;

           (* Record backtraces on log levels debug and higher. *)
           if output_on_level L_debug then
             Printexc.record_backtrace true;

           Event.log
             L_info 
             "Starting new process with PID %d" 
             pid ;

          ( (* Change debug output to per process file. *)
            match Flags.debug_log () with

              (* Keep if output to stdout. *)
              | None -> ()

              (* Open channel to given file and create formatter on
                 channel. *)
              | Some f ->

                try

                  (* Output to f.PROCESS-PID. *)
                  let f' =
                    Format.sprintf "%s.%s-%d"
                      f
                      (debug_ext_of_process process)
                      pid
                  in

                  (* Open output channel to file. *)
                  let oc = open_out f' in

                  (* Formatter writing to file. *)
                  let debug_formatter =
                    Format.formatter_of_out_channel oc
                  in

                  (* Enable each requested debug section and write to
                     formatter. *)
                  Flags.debug ()
                  |> List.iter
                       ( fun s ->
                         Debug.disable s ;
                         Debug.enable s debug_formatter )

                with

                  (* Ignore and keep previous file on error. *)
                  | Sys_error _ -> () );

          (* Run main function of process. *)
          Start.main_of_process process trans_sys depth_opt ;

          (* Cleanup and exit. *)
          Stop.on_exit_child
            (Some messaging_thread) process Exit

        with 

        (* Termination message received. *)
        | Event.Terminate as e ->
           Stop.on_exit_child None process e

        (* Propagating signal exceptions. *)
        | Signal s ->
           exception_on_signal s

        (* Catch all other exceptions. *)
        | e -> 

           (* Get backtrace now, Printf changes it. *)
           let backtrace =
             Printexc.get_backtrace ()
           in

           Event.log
             L_fatal
             "%s Runtime error: %s"
             error_tag
             (Printexc.to_string e);

           if Printexc.backtrace_status () then
             Event.log
               L_debug "Backtrace:@\n%s" backtrace ;

           (* Cleanup and exit. *)
           Stop.on_exit_child None process e

      )

    (* We are the parent process. *)
    | _ -> 

      (* Keep PID of child process and return. *)
      child_pids := (pid, process) :: !child_pids


(* Check which SMT solver is available. *)
let check_smtsolver () =

  (* SMT solver from command-line. *)
  match Flags.smtsolver () with

    (* User chose Z3. *)
    | `Z3_SMTLIB ->

       let z3_exec =
         try
           (* Check if Z3 is on the path. *)
           Flags.z3_bin () |> find_on_path
         with
         | Not_found ->
            (* Fail if not. *)
            Event.log 
              L_fatal 
              "Z3 executable %s not found."
              (Flags.z3_bin ()) ;

            exit 2
       in

       Event.log
         L_info "Using Z3 executable %s." z3_exec

    (* User chose CVC4. *)
    | `CVC4_SMTLIB -> 

       let cvc4_exec = 
         try
           (* Check if CVC4 is on the path. *)
           Flags.cvc4_bin () |> find_on_path
         with 
         | Not_found -> 
            (* Fail if not. *)
            Event.log
              L_fatal
              "CVC4 executable %s not found."
              (Flags.cvc4_bin ()) ;

            exit 2
       in

       Event.log
         L_info
         "Using CVC4 executable %s."
         cvc4_exec

    (* User chose MathSat5. *)
    | `MathSat5_SMTLIB ->

       let mathsat5_exec =
         try
           (* Check if MathSat5 is on the path. *)
           Flags.mathsat5_bin () |> find_on_path
         with
         | Not_found ->
            (* Fail if not. *)
            Event.log
              L_fatal
              "MathSat5 executable %s not found."
              (Flags.mathsat5_bin ()) ;

            exit 2
       in

       Event.log
         L_info
         "Using MathSat5 executable %s." 
         mathsat5_exec


    (* User chose Yices. *)
    | `Yices_native -> 

       let yices_exec =
         try
           (* Check if MathSat5 is on the path *)
           Flags.yices_bin () |> find_on_path
         with
         | Not_found ->
            (* Fail if not. *)
            Event.log
              L_fatal
              "Yices executable %s not found."
              (Flags.yices_bin ()) ;

            exit 2
       in

       Event.log
         L_info
         "Using Yices executable %s." 
         yices_exec


    (* User chose Yices2. *)
    | `Yices_SMTLIB ->

       (* Not supported, failing. *)
       Event.log
         L_fatal
         "Yices2 is not supported at the moment." ;

       exit 2

    (*    let yices_exec = *)
    (*      try *)
    (*        (\* Check if MathSat5 is on the path. *\) *)
    (*        Flags.yices2smt2_bin () |> find_on_path *)
    (*      with *)
    (*      | Not_found -> *)
    (*         (\* Fail if not. *\) *)
    (*         Event.log *)
    (*           L_fatal *)
    (*           "Yices2 SMT2 executable %s not found." *)
    (*           (Flags.yices2smt2_bin ()) ; *)

    (*         exit 2 *)
    (*    in *)

    (*    Event.log *)
    (*      L_info *)
    (*      "Using Yices2 SMT2 executable %s."  *)
    (*      yices_exec *)


    (* User did not choose SMT solver. *)
    | `detect ->

       try

         let z3_exec =
           (* Check if z3 is on the path. *)
           Flags.z3_bin () |> find_on_path
         in

         Event.log
           L_info "Using Z3 executable %s." z3_exec ;

         (* Z3 is on path? *)
         Flags.set_smtsolver
           `Z3_SMTLIB
           z3_exec

      with Not_found ->

        try 

          let cvc4_exec =
            (* Check if cvc4 is on the path. *)
            Flags.cvc4_bin () |> find_on_path
          in

          Event.log
            L_info
            "Using CVC4 executable %s." 
            cvc4_exec;

          (* CVC4 is on path? *)
          Flags.set_smtsolver 
            `CVC4_SMTLIB
            cvc4_exec

        with Not_found ->

          try

            let mathsat5_exec =
              (* Check if mathsat is on the path. *)
              Flags.mathsat5_bin () |> find_on_path
            in

            Event.log
              L_info
              "Using MatSat5 executable %s." 
              mathsat5_exec ;

            (* MathSat5 is on path? *)
            Flags.set_smtsolver 
              `MathSat5_SMTLIB
              mathsat5_exec

          with Not_found -> 

            try 

              let yices_exec =
                (* Check if yices is on the path. *)
                Flags.yices_bin () |> find_on_path
              in

              Event.log
                L_info
                "Using Yices executable %s." 
                yices_exec;

              (* Yices is on path? *)
              Flags.set_smtsolver
                `Yices_SMTLIB
                yices_exec
                
            with Not_found ->
              
              Event.log L_fatal "No SMT Solver found." ;
              
              exit 2

let launch_analysis
      exit_after_killing_kids
      trans_sys max_abstraction_depth_option =

  if
    (* Warn if list of properties is empty. *)
    ( TransSys.props_list_of_bound
        trans_sys
        Numeral.zero ) = []
  then Event.log
         L_warn
         "No properties to prove" ;

  (* Which modules are enabled? *)
  ( match Flags.enable () with

    | [] -> 
       (* No modules enabled. *)
       Event.log
         L_fatal "Need at least one process enabled"

    | [p] -> (
      (* Single module enabled. *)

      Event.log
        L_info
        "Running as a single process";

      (* Set module currently running. *)
      Event.set_module p ;

      (* Run main function of process. *)
      (Start.main_of_process p)
        trans_sys
        max_abstraction_depth_option ;
      
      (* Ignore SIGALRM from now on *)
      Sys.set_signal
        Sys.sigalrm Sys.Signal_ignore ;

      (* Cleanup before exiting process *)
      Stop.on_exit_child None p Exit
                         
    )

    | ps -> (
      (* Run some modules in parallel. *)
      Event.log
        L_info
        "@[<hov>Running %a in parallel mode.@]"
        (pp_print_list pp_print_kind_module ",@ ")
        ps ;

      (* Start all child processes. *)
      let start_child_processes messaging_setup =
        (* Make sure the list of currently running child processes is
           empty. *)
        assert (!child_pids = []) ;
        (* Actually starting processes and updating child processes
           list. *)
        List.iter 
          ( fun p -> 
            run_process
              messaging_setup p trans_sys max_abstraction_depth_option)
          ps ;
      in
      

      ( match !messaging_setup_opt with

        | None ->
           (* First time launching, setup messaging things. *)
           Event.log
             L_info
             "@[<v>Launching supervisor for the first time.@]" ;

           (* Initializing messaging. *)
           let messaging_setup = Event.setup () in

           (* Remembering it for restarts. *)
           messaging_setup_opt := Some messaging_setup ;

           Event.log
             L_trace
             "Messaging initialized in supervisor." ;

           (* Launching child processes. *)
           start_child_processes messaging_setup ;
           
           (* Set module currently running. *)
           Event.set_module `Supervisor ;
           Event.log L_trace "Starting supervisor." ;

           (* Initialize messaging for invariant manager, obtain a
              background thread. *)
           Event.run_im
             messaging_setup
             !child_pids
             (Stop.on_exit
                exit_after_killing_kids
                `Supervisor)

        | Some messaging_setup ->
           (* Not the first time launching, updating background
           thread. *)
           Event.log
             L_info
             "@[<v>Restarting child processes [%a].@]"
             (pp_print_list (fun ppf i -> Format.fprintf ppf "%d" i ) ",@ ")
             (List.map fst !child_pids) ;

           (* Launching child processes, updating process list. *)
           start_child_processes messaging_setup ;

           (* Updating background thread for new kids. *)
           Event.update_child_processes_list !child_pids
      ) ;

      (* Going to polling loop. *)
      polling_loop exit_after_killing_kids child_pids trans_sys ;

      (* Following is not needed, this is done in [polling_loop] when it
         exits. *)
      (* Exit without error *)
      (* Stop.on_exit *)
      (*   exit_after_killing_kids *)
      (*   `Supervisor *)
      (*   Exit *)
      ()
                   
    );

  )

let launch_modular_analysis trans_sys =

  (* All subsystems of the top node, sorted by reverse topological
     order. *)
  let all_systems = TransSys.get_all_subsystems trans_sys in

  Event.log
    L_warn
    "@[<v 8>|=====| Launching modular analysis@ in the following order:@ \
     (@[<hv>%a@])@]"
    (pp_print_list
       (fun ppf sys ->
        TransSys.get_scope sys
        |> String.concat "/"
        |> Format.fprintf ppf "%s")
       ",@ ")
    all_systems ;

  let abstract_contracts = Flags.contracts_abstract() in

  let rec analyze sys depth =
    (* Getting the system max abstraction depth. *)
    let max_depth =
      TransSys.get_max_depth sys
      |> Numeral.to_int
    in

    if depth <= max_depth then (
      (* Not over [max_depth] yet, running analysis. *)

      current_trans_sys := Some sys ;

      if not (TransSys.all_props_proved sys) then (

        ( if depth == max_depth then
            Event.log
              L_warn
              "@.|===| Launching analysis for %s, no abstraction."
              (TransSys.get_name sys)
          else
            Event.log
              L_warn
              "@.|===| Launching analysis for %s at %i/%i."
              (TransSys.get_name sys)
              depth
              max_depth ) ;

        Event.log
          L_warn
          "%a" TransSys.pp_print_trans_sys_contract_view sys ;

        if abstract_contracts then (
          match
            TransSys.abstracted_subsystems_of_depth
              sys depth
          with
          | [] ->
             Event.log L_warn "No subsystem to abstract." ;
          | abstracted ->
             Event.log
               L_warn
               "@[<hv 6>Abstracted nodes: @[<v>%a@]@]"
               (pp_print_list
                  (fun ppf s -> Format.fprintf ppf "%s" s)
                  ",@ ")
               abstracted
        ) ;

        let _ = read_line () in

        (* Launching analysis for [sys] with abstraction depth
         [depth]. *)
        launch_analysis
          (* Don't exit when analysis ends. *)
          false
          sys (Some depth)
      ) else if TransSys.get_prop_status_all sys = [] then (
        Event.log
          L_warn
          "|===| Skipping sys %s, no property to prove."
          (TransSys.get_name sys)
      ) else (
        Event.log
          L_warn
          "|===| Skipping sys %s at %d, all properties already (dis)proved."
          (TransSys.get_name sys)
          depth ;
      ) ;

      if not (TransSys.all_props_proved sys) then (

        Event.log
          L_warn
          "%s at %i: %i properties have unknown status."
          (TransSys.get_name sys)
          depth
          (TransSys.get_prop_status_all_unknown sys
           |> List.length);

        Event.log
          L_info
          "Resetting k-true properties to unknown." ;

        TransSys.reset_prop_ktrue_to_unknown sys ;

        depth + 1 |> analyze sys
      )
    )
  in

  all_systems
  |> List.iter
       ( fun sys ->

         ( if abstract_contracts then
             (* Abstracting contracts, starting at 0. *)
             0
           else
             (* Not abstracting contracts, starting directly at
                [max_depth] for [sys]. *)
             TransSys.get_max_depth sys
             |> Numeral.to_int)

         (* Launching analysis. *)
         |> analyze sys ) ;

  minisleep 0.01 ;

  (* There should be no process left at this point. *)
  assert ( !child_pids = [] ) ;

  Stop.status_of_exn `Supervisor Exit |> Stop.actually_exit
       

(* Entry point. *)
let main () =

  (* Parse command-line flags. *)
  Flags.parse_argv ();

  (* At least one debug section enabled? *)
  if Flags.debug () = [] then

    (* Initialize debug output when no debug section enabled. *)
    Debug.initialize ()

  else (

    (* Formatter to write debug output to. *)
    let debug_formatter =
      match Flags.debug_log () with

      (* Write to stdout by default. *)
      | None -> Format.std_formatter

      (* Open channel to given file and create formatter on channel. *)
      | Some f ->
         ( try open_out f with
           | Sys_error _ -> failwith "Could not open debug logfile." )
         |> Format.formatter_of_out_channel

    in

    (* Enable each requested debug section and write to formatter. *)
    Flags.debug ()
    |> List.iter 
         ( fun s ->
           Debug.enable s debug_formatter ) ;

  );

  (* Set log format to XML if requested .*)
  if Flags.log_format_xml () then
    Event.set_log_format_xml () ;

  (* No output at all? *)
  if not (Flags.log_level () = L_off) then (

    (* Temporarily set log level to info and output logo. *)
    set_log_level L_info ;
    Event.log L_info "%a" pp_print_banner ()

  );

  (* Set log level. *)
  set_log_level (Flags.log_level ()) ;

  (* Record backtraces on log levels debug and higher. *)
  if output_on_level L_debug then
    Printexc.record_backtrace true ;

  (* Check and set SMT solver. *)
  check_smtsolver () ;

  (* Wallclock timeout? *)
  if Flags.timeout_wall () > 0. then (

    (* Install signal handler for SIGALRM after wallclock timeout. *)
    Sys.set_signal 
      Sys.sigalrm 
      ( Sys.Signal_handle
          (fun _ -> raise TimeoutWall) );

    (* Set interval timer for wallclock timeout. *)
    let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
      Unix.setitimer 
        Unix.ITIMER_REAL 
        { Unix.it_interval = 0. ;
          Unix.it_value = Flags.timeout_wall () } 
    in

    ()

  ) else (

      (* Install generic signal handler for SIGALRM. *)
      Sys.set_signal 
        Sys.sigalrm 
        (Sys.Signal_handle exception_on_signal);

  );

  (* Must not use vtalrm signal, this is used internally by the OCaml
     Threads module. *)

  (* Raise exception on CTRL+C. *)
  Sys.catch_break true ;

  (* Install generic signal handler for SIGINT. *)
  Sys.set_signal
    Sys.sigint
    (Sys.Signal_handle exception_on_signal) ;

  (* Install generic signal handler for SIGTERM. *)
  Sys.set_signal
    Sys.sigterm
    (Sys.Signal_handle exception_on_signal) ;

  (* Install generic signal handler for SIGQUIT. *)
  Sys.set_signal
    Sys.sigquit
    (Sys.Signal_handle exception_on_signal) ;

  Stat.start_timer Stat.total_time ;

  try 

    Event.log
      L_info
      "Parsing input file %s."
      (Flags.input_file ()) ;

    (* Parse file into two-state transition system. *)
    trans_sys :=
      ( match Flags.input_format () with

        | `Lustre ->
          Some
            ( LustreInput.of_file
                (Flags.enable () = [`Interpreter])
                (Flags.input_file ()) )

        | `Native -> (

          (* Some (NativeInput.of_file (Flags.input_file ())) *)

          Event.log
            L_fatal
            "Native input deactivated while\
             refactoring transition system." ;
          
          assert false

        )

        | `Horn ->
          (* Horn.of_file (Flags.input_file ()) *)
          assert false ) ;

    (* Output the transition system. *)
    ( debug
        parse
        "%a"
        TransSys.pp_print_trans_sys
        (get !trans_sys)
      end ) ;

    if Flags.modular () then
      launch_modular_analysis (get !trans_sys)
    else
      launch_analysis true (get !trans_sys) None

  with

  | e ->

     (* Which modules are enabled? *)
     ( match Flags.enable () with

       | [] ->
          (* No modules enabled. *)
          ()

       | [p] ->
          (* Single module enabled. *)
          (* Cleanup before exiting process. *)
          Stop.on_exit_child None p e

       | _ ->
          ( match Event.get_module () with
            | `Supervisor ->
               Stop.on_exit true `Supervisor e
            | m ->
               Stop.on_exit_child None m e ) )

;;

main ()  
      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
