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

(*

module Dummy =
struct
  let main _ = failwith "not implemented"
  let on_exit _ = ()
end
*)

module BMC = Base
module InvGenTS = InvGenGraph.TwoState
module InvGenOS = InvGenGraph.OneState

(* module PDR = Dummy *)

let children_pgid = ref 0
  
(* Child processes forked 

   This is an association list of PID to process type. We need a
   reference here, because we may need to terminate asynchronously
   after an exception. *)
let child_pids = ref []

(* Transition system *)
let trans_sys = ref None


(* Main function of the process *)
let main_of_process = function 
  | `PDR -> PDR.main
  | `BMC -> BMC.main 
  | `IND -> Step.main

  | `INVGEN -> 

    let nice =  (Flags.invgengraph_renice ()) in

    (if nice < 0 then 

       Event.log
         L_info 
         "Ignoring negative niceness value for invariant generation."

     else

       let nice' = Unix.nice nice in

       Event.log
         L_info 
         "Renicing invariant generation to %d"
         nice');

    InvGenTS.main


  | `INVGENOS -> 

    let nice =  (Flags.invgengraph_renice ()) in

    (if nice < 0 then 

       Event.log
         L_info 
         "Ignoring negative niceness value for invariant generation."

     else

       let nice' = Unix.nice (Flags.invgengraph_renice ()) in

       Event.log
         L_info 
         "Renicing invariant generation to %d"
         nice');

    InvGenOS.main

  | `Interpreter -> Interpreter.main (Flags.interpreter_input_file ())
  | `INVMAN -> InvarManager.main child_pids
  | `Parser -> ignore
                       

(* Cleanup function of the process *)
let on_exit_of_process = function 
  | `PDR -> PDR.on_exit
  | `BMC -> BMC.on_exit 
  | `IND -> Step.on_exit
  | `INVGEN -> InvGenTS.on_exit  
  | `INVGENOS -> InvGenOS.on_exit  
  | `Interpreter -> Interpreter.on_exit
  | `INVMAN -> InvarManager.on_exit                       
  | `Parser -> ignore

(*
(* Messaging type of the process *)
let init_messaging_of_process = function 
  | `PDR -> Kind2Message.init_pdr
  | `BMC -> Kind2Message.init_bmc
  | `IND -> Kind2Message.init_indStep
  | `INVGEN -> Kind2Message.init_invarGen 
  | `INVMAN -> Kind2Message.init_invarManager (List.map fst !child_pids)
*)


let debug_ext_of_process = function 
  | `PDR -> "pdr"
  | `BMC -> "bmc"
  | `IND -> "ind"
  | `INVGEN -> "invgenTS"
  | `INVGENOS -> "invgenOS"
  | `INVMAN -> "invman"
  | `Interpreter -> "interp"
  | `Parser -> "parser"

(* Exit status if child terminated normally *)
let status_ok = 0

(* Exit status if child caught a signal, the signal number is added to
   the value *)
let status_signal = 128

(* Exit status if child raised an exception *)
let status_error = 2

(* Exit status if timed out *)
let status_timeout = 3


(* Return the status code from an exception *)
let status_of_exn process = function
  
  (* Normal termination *)
  | Exit -> status_ok

  (* Termination message *)
  | Event.Terminate ->
    
    (

      Event.log L_info
        "Received termination message";

      status_ok

    ) 

  (* Catch wallclock timeout *)
  | TimeoutWall -> 
    
    (

      Event.log L_error 
        "<Timeout> Wallclock timeout";

      status_timeout

    ) 

  (* Catch CPU timeout *)
  | TimeoutVirtual -> 

    (
      
      Event.log L_error
        "<Timeout> CPU timeout"; 

      status_timeout

    ) 
    
  (* Signal caught *)
  | Signal s -> 
    
    (
      
      Event.log L_fatal
        "<Interruption> Caught signal%t. Terminating." 
        (function ppf -> 
          match s with 
            | 0 -> () 
            | _ -> Format.fprintf ppf " %s" (string_of_signal s));
      
      (* Return exit status and signal number *)
      status_signal + s
        
    )
    
  (* Other exception *)
  | e -> 
    
    (
      
      (* Get backtrace now, Printf changes it *)
      let backtrace = Printexc.get_backtrace () in

      Event.log L_fatal
        "<Error> Runtime error: %s" 
        (Printexc.to_string e);

      if Printexc.backtrace_status () then
        Event.log L_debug "Backtrace:@\n%s" backtrace;

      (* Return exit status for error *)
      status_error 
      
    )


(* Clean up before exit *)
let on_exit process exn = 

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

  let clean_exit status =

    (* Log termination status *)
    if not (!child_pids = []) then

      Event.log L_info 
        "Some processes (%a) did not exit, killing them." 
        (pp_print_list 
           (fun ppf (pid, _) -> Format.pp_print_int ppf pid) ",@ ") 
        !child_pids;

    (* Kill all remaining processes in the process groups of child
       processes *)
    List.iter
      (fun (pid, _) -> try Unix.kill (- pid) Sys.sigkill with _ -> ())
      !child_pids;

    (* Close tags in XML output *)
    Event.terminate_log ();

    (* Exit with status *)
    exit status

  in

  (* Ignore SIGALRM from now on *)
  Sys.set_signal Sys.sigalrm Sys.Signal_ignore;

  (* Exit status of process depends on exception *)
  let status = status_of_exn process exn in

  (* Clean exit from invariant manager *)
  InvarManager.on_exit !trans_sys;
  
  Event.log L_info "Killing all remaining child processes";

  (* Kill all child processes *)
  List.iter 
    (function pid, _ -> 

      Event.log L_info "Sending SIGTERM to PID %d" pid;

      Unix.kill pid Sys.sigterm)

    !child_pids;

  Event.log L_info 
    "Waiting for remaining child processes to terminate";

  try 

    (* Install signal handler for SIGALRM after wallclock timeout *)
    Sys.set_signal 
      Sys.sigalrm 
      (Sys.Signal_handle (function _ -> raise TimeoutWall));

    (* Set interval timer for wallclock timeout *)
    let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
      Unix.setitimer 
        Unix.ITIMER_REAL 
        { Unix.it_interval = 0.; Unix.it_value = 1. } 
    in

    (try 

       while true do

         (* Wait for child process to terminate *)
         let pid, status = Unix.wait () in

         (* Kill processes left in process group of child process *)
         (try Unix.kill (- pid) Sys.sigkill with _ -> ());

         (* Remove killed process from list *)
         child_pids := List.remove_assoc pid !child_pids;

         (* Log termination status *)
         Event.log L_info 
           "Process %d %a" pid pp_print_process_status status

       done

     with TimeoutWall -> ());

    clean_exit status

  with 

    (* No more child processes, this is the normal exit *)
    | Unix.Unix_error (Unix.ECHILD, _, _) -> 

      Event.log L_info 
        "All child processes terminated.";

      clean_exit status

    (* Unix.wait was interrupted *)
    | Unix.Unix_error (Unix.EINTR, _, _) -> 

      (* Get new exit status *)
      let status' = status_of_exn process (Signal 0) in

      clean_exit status'

    (* Exception in Unix.wait loop *)
    | e -> 

      (* Get new exit status *)
      let status' = status_of_exn process e in

      clean_exit status'


(* Call cleanup function of process and exit. 

   Give the exception [exn] that was raised or [Exit] on normal
   termination *)
let on_exit_child messaging_thread process exn = 

  (* Exit status of process depends on exception *)
  let status = status_of_exn process exn in

  (* Call cleanup of process *)
  (on_exit_of_process process) !trans_sys;
  
  Event.log L_info 
    "Process %d terminating"
    (Unix.getpid ());

  Event.terminate_log ();
  
  (match messaging_thread with 
    | Some t -> Event.exit t
    | None -> ());
           
  (debug kind2 
    "Process %a terminating"
    pp_print_kind_module process
   in

  (* Exit process with status *)
  exit status)



(* Fork and run a child process *)
let run_process messaging_setup process = 

  (* Fork a new process *)
  let pid = Unix.fork () in

  match pid with 

    (* We are the child process *)
    | 0 -> 

      (

        try 

          (* Make the process leader of a new session *)
          ignore (Unix.setsid ());

          let pid = Unix.getpid () in

          (* Ignore SIGALRM in child process *)
          Sys.set_signal Sys.sigalrm Sys.Signal_ignore;

          (* Initialize messaging system for process *)
          let messaging_thread =
            Event.run_process 
              process
              messaging_setup
              (on_exit_child None process)
          in

          (* All log messages are sent to the invariant manager now *)
          Event.set_relay_log ();

          (* Set module currently running *)
          Event.set_module process;

          (* Record backtraces on log levels debug and higher *)
          if output_on_level L_debug then
            Printexc.record_backtrace true;

          Event.log L_info 
            "Starting new process with PID %d" 
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

                  (* Enable each requested debug section and write to
                     formatter *) 
                  List.iter
                    (function s -> 
                      Debug.disable s; 
                      Debug.enable s debug_formatter)
                    (Flags.debug ())

                with

                  (* Ignore and keep previous file on error *)
                  | Sys_error _ -> () 

          );

          (* Run main function of process *)
          (main_of_process process) (get !trans_sys);

          (* Cleanup and exit *)
          on_exit_child (Some messaging_thread) process Exit

        with 

          (* Termination message received *)
          | Event.Terminate as e -> on_exit_child None process e

          (* Catch all other exceptions *)
          | e -> 

            (* Get backtrace now, Printf changes it *)
            let backtrace = Printexc.get_backtrace () in

            Event.log L_fatal
              "Runtime error: %s" 
              (Printexc.to_string e);

            if Printexc.backtrace_status () then
              Event.log L_debug "Backtrace:@\n%s" backtrace;

            (* Cleanup and exit *)
            on_exit_child None process e

      )

    (* We are the parent process *)
    | _ -> 

      (* Keep PID of child process and return *)
      child_pids := (pid, process) :: !child_pids


(* Check which SMT solver is available *)  
let check_smtsolver () = 

  (* SMT solver from command-line *)
  match Flags.smtsolver () with 

    (* User chose Z3 *)
    | `Z3_SMTLIB -> 

      let z3_exec = 

        (* Check if Z3 is on the path *)
        try find_on_path (Flags.z3_bin ()) with 

          | Not_found -> 

            (* Fail if not *)
            Event.log 
              L_fatal 
              "Z3 executable %s not found."
              (Flags.z3_bin ());

            exit 2

      in

      Event.log L_info "Using Z3 executable %s." z3_exec

    (* User chose CVC4 *)
    | `CVC4_SMTLIB -> 

      let cvc4_exec = 

        (* Check if CVC4 is on the path *)
        try find_on_path (Flags.cvc4_bin ()) with 

          | Not_found -> 

            (* Fail if not *)
            Event.log 
              L_fatal
              "CVC4 executable %s not found."
              (Flags.cvc4_bin ());

            exit 2

      in

      Event.log
        L_info
        "Using CVC4 executable %s."
        cvc4_exec

    (* User chose MathSat5 *)
    | `MathSat5_SMTLIB -> 

      let mathsat5_exec = 

        (* Check if MathSat5 is on the path *)
        try find_on_path (Flags.mathsat5_bin ()) with 

          | Not_found -> 

            (* Fail if not *)
            Event.log 
              L_fatal
              "MathSat5 executable %s not found."
              (Flags.mathsat5_bin ());

            exit 2

      in

      Event.log
        L_info
        "Using MathSat5 executable %s." 
        mathsat5_exec


    (* User chose Yices *)
    | `Yices_native -> 

      let yices_exec = 

        (* Check if MathSat5 is on the path *)
        try find_on_path (Flags.yices_bin ()) with 

          | Not_found -> 

            (* Fail if not *)
            Event.log 
              L_fatal
              "Yices executable %s not found."
              (Flags.yices_bin ());

            exit 2

      in

      Event.log
        L_info
        "Using Yices executable %s." 
        yices_exec


    (* User chose Yices2 *)
    | `Yices_SMTLIB -> 

      let yices_exec = 

        (* Check if MathSat5 is on the path *)
        try find_on_path (Flags.yices2smt2_bin ()) with 

          | Not_found -> 

            (* Fail if not *)
            Event.log 
              L_fatal
              "Yices2 SMT2 executable %s not found."
              (Flags.yices2smt2_bin ());

            exit 2

      in

      Event.log
        L_info
        "Using Yices2 SMT2 executable %s." 
        yices_exec


    (* User did not choose SMT solver *)
    | `detect -> 

      try 

        let z3_exec = find_on_path (Flags.z3_bin ()) in

        Event.log L_info "Using Z3 executable %s." z3_exec;

        (* Z3 is on path? *)
        Flags.set_smtsolver 
          `Z3_SMTLIB
          z3_exec

      with Not_found -> 

        try 

          let cvc4_exec = find_on_path (Flags.cvc4_bin ()) in

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

            let mathsat5_exec = find_on_path (Flags.mathsat5_bin ()) in

            Event.log
              L_info
              "Using MatSat5 executable %s." 
              mathsat5_exec;

            (* MathSat5 is on path? *)
            Flags.set_smtsolver 
              `MathSat5_SMTLIB
              mathsat5_exec

          with Not_found -> 

            try 

              let yices_exec = find_on_path (Flags.yices_bin ()) in

              Event.log
                L_info
                "Using Yices executable %s." 
                yices_exec;

              (* Yices is on path? *)
              Flags.set_smtsolver 
                `Yices_SMTLIB
                yices_exec
                
            with Not_found -> 
              
              Event.log L_fatal "No SMT Solver found"; 
              
              exit 2
                

(* Entry point *)    
let main () =   

  (* Parse command-line flags *)
  Flags.parse_argv ();

  (* At least one debug section enabled? *)
  if Flags.debug () = [] then

    (* Initialize debug output when no debug section enabled *)
    Debug.initialize ()

  else

    (

      (* Formatter to write debug output to *)
      let debug_formatter = 

        match Flags.debug_log () with 

          (* Write to stdout by default *)
          | None -> Format.std_formatter

          (* Open channel to given file and create formatter on channel *)
          | Some f ->

            let oc = 
              try open_out f with
                | Sys_error _ -> failwith "Could not open debug logfile"
            in 
            Format.formatter_of_out_channel oc

      in

      (* Enable each requested debug section and write to formatter *)
      List.iter 
        (function s -> Debug.enable s debug_formatter)
        (Flags.debug ());

    );

  (* Set log format to XML if requested *)
  if Flags.log_format_xml () then Event.set_log_format_xml ();

  (* No output at all? *)
  if not (Flags.log_level () = L_off) then

    (

      (* Temporarily set log level to info and output logo *)
      set_log_level L_info;
      Event.log L_info "%a" pp_print_banner ()

    );

  (* Set log level *)
  set_log_level (Flags.log_level ());

  (* Record backtraces on log levels debug and higher *)
  if output_on_level L_debug then
    Printexc.record_backtrace true;

  (* Check and set SMT solver *)
  check_smtsolver ();

  (* Wallclock timeout? *)
  if Flags.timeout_wall () > 0. then

    (

      (* Install signal handler for SIGALRM after wallclock timeout *)
      Sys.set_signal 
        Sys.sigalrm 
        (Sys.Signal_handle (function _ -> raise TimeoutWall));

      (* Set interval timer for wallclock timeout *)
      let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
        Unix.setitimer 
          Unix.ITIMER_REAL 
          { Unix.it_interval = 0.; Unix.it_value = Flags.timeout_wall () } 
      in

      ()

    )

  else

    (

      (* Install generic signal handler for SIGALRM *)
      Sys.set_signal 
        Sys.sigalrm 
        (Sys.Signal_handle exception_on_signal);

    );

  (* Must not use vtalrm signal, this is used internally by the OCaml
     Threads module *)

  (* Raise exception on CTRL+C *)
  Sys.catch_break true;

  (* Install generic signal handler for SIGINT *)
  Sys.set_signal 
    Sys.sigint 
    (Sys.Signal_handle exception_on_signal);

  (* Install generic signal handler for SIGTERM *)
  Sys.set_signal 
    Sys.sigterm 
    (Sys.Signal_handle exception_on_signal);

  (* Install generic signal handler for SIGQUIT *)
  Sys.set_signal 
    Sys.sigquit 
    (Sys.Signal_handle exception_on_signal);

  Stat.start_timer Stat.total_time;

  try 

    Event.log L_info 
      "Parsing input file %s" (Flags.input_file ()); 

    (* Parse file into two-state transition system *)
    trans_sys := (match (Flags.input_format ()) with 

        | `Lustre -> 
          
          Some
            (LustreInput.of_file
               (Flags.enable () = [`Interpreter])
               (Flags.input_file ()))
            
        | `Native -> 
          
          (

          (* Some (NativeInput.of_file (Flags.input_file ())) *)

            Event.log
              L_fatal
              "Native input deactivated while refactoring transition system.";
          
            assert false

          )

        | `Horn -> 
          
          (* Horn.of_file (Flags.input_file ()) *)
          assert false);

    (* Output the transition system *)
    (debug parse
        "%a"
        TransSys.pp_print_trans_sys
        (get !trans_sys)
     end);

    if 

      (* Warn if list of properties is empty *)
      TransSys.props_list_of_bound (get !trans_sys) Numeral.zero = []

    then

      Event.log
        L_warn
        "No properties to prove";

    (* Which modules are enabled? *)
    (match Flags.enable () with

      (* No modules enabled *)
      | [] -> 
        (Event.log L_fatal "Need at least one process enabled") 

      (* Single module enabled *)
      | [p] -> 

        (

          Event.log L_info 
            "Running as a single process";

          (* Set module currently running *)
          Event.set_module p;

          (* Run main function of process *)
          (main_of_process p) (get !trans_sys);
          
          (* Ignore SIGALRM from now on *)
          Sys.set_signal Sys.sigalrm Sys.Signal_ignore;

          (* Cleanup before exiting process *)
          on_exit_child None p Exit
            
        )
        
      (* Run some modules in parallel *)
      | ps -> 
        
        (

          Event.log L_info
            "@[<hov>Running %a in parallel mode@]"
            (pp_print_list pp_print_kind_module ",@ ")
            ps;
         
          let messaging_setup = Event.setup () in

          Event.log L_trace
            "Messaging initialized in invariant manager";

          (* Start all child processes *)
          List.iter 
            (function p -> 
              run_process messaging_setup p)
            ps;
              
          (* Set module currently running *)
          Event.set_module `INVMAN;
          
          Event.log L_trace "Starting invariant manager";

          
          (* Initialize messaging for invariant manager, obtain a background
             thread *)
          let _ = 
            Event.run_im
              messaging_setup
              !child_pids
              (on_exit `INVMAN)
          in

          (* Run invariant manager *)
          InvarManager.main child_pids (get !trans_sys);
          
          (* Exit without error *)
          on_exit `INVMAN Exit
        
        );

    );

  with

    (* Exit with error *)
    | e -> 

      (* Which modules are enabled? *)
      (match Flags.enable () with

        (* No modules enabled *)
        | [] -> ()


        (* Single module enabled *)
        | [p] -> 
          
          (* Cleanup before exiting process *)
          on_exit_child None p e
            
       
        (* Run some modules in parallel *)
        | _ -> 
        
          on_exit `INVMAN e
            
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
  
