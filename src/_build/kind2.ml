(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Lib

let pp_print_banner ppf () =
    Format.fprintf ppf "%s v%s" Config.package_name Config.package_version

(*

module Dummy =
struct
  let main _ = failwith "not implemented"
  let on_exit _ = ()
end
*)

module BMC = Bmc
module IndStep = Ind
module InvGen = InvGenDummy

(* module PDR = Dummy *)
  
(* Child processes forked 

   This is an association list of PID to process type *)
let child_pids = ref []



(* Main function of the process *)
let main_of_process = function 
  | `PDR -> PDR.main
  | `BMC -> BMC.main 
  | `IND -> IndStep.main 
  | `INVGEN -> InvGen.main 
  | `Interpreter -> Interpreter.main "test.csv"
  | `INVMAN -> InvarManager.main child_pids
                       

(* Cleanup function of the process *)
let on_exit_of_process = function 
  | `PDR -> PDR.on_exit
  | `BMC -> BMC.on_exit 
  | `IND -> IndStep.on_exit 
  | `INVGEN -> InvGen.on_exit  
  | `Interpreter -> Interpreter.on_exit
  | `INVMAN -> InvarManager.on_exit                       

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
  | `INVGEN -> "invgen"
  | `INVMAN -> "invman"
  | `Interpreter -> "interp"

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

      Event.log process Event.L_info
        "Received termination message";

      status_ok

    ) 

  (* Catch wallclock timeout *)
  | TimeoutWall -> 
    
    (

      Event.log process Event.L_error 
        "Wallclock timeout";

      status_timeout

    ) 

  (* Catch CPU timeout *)
  | TimeoutVirtual -> 

    (
      
      Event.log process Event.L_error
        "CPU timeout"; 

      status_timeout

    ) 
    
  (* Signal caught *)
  | Signal s -> 
    
    (
      
      Event.log process Event.L_fatal
        "Caught signal%t. Terminating." 
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

      Event.log process Event.L_fatal
        "Runtime error: %s" 
        (Printexc.to_string e);

      if Printexc.backtrace_status () then
        Event.log process Event.L_debug "Backtrace:@\n%s" backtrace;

      (* Return exit status for error *)
      status_error 
      
    )


(* Clean up before exit *)
let on_exit process exn = 

  (* Ignore SIGALRM from now on *)
  Sys.set_signal Sys.sigalrm Sys.Signal_ignore;

  (* Exit status of process depends on exception *)
  let status = status_of_exn process exn in

  (* Clean exit from invariant manager *)
  InvarManager.on_exit ();

  Event.log process Event.L_info "Killing all remaining child processes";

  (* Kill all child processes *)
  List.iter 
    (function pid, _ -> 

      Event.log process Event.L_info "Sending SIGTERM to PID %d" pid;

      Unix.kill pid Sys.sigterm)

    !child_pids;
  
  Event.log process Event.L_info 
    "Waiting for remaining child processes to terminate";

  try 
    
    while true do
      
      (* Wait for child process to terminate *)
      let pid, status = Unix.wait () in

      (* Remove killed process from list *)
      child_pids := List.remove_assoc pid !child_pids;
      
      (* Log termination status *)
      Event.log process Event.L_info 
        "Process %d %a" pid pp_print_process_status status
        
    done;
    
  with 
    
    (* No more child processes, this is the normal exit *)
    | Unix.Unix_error (Unix.ECHILD, _, _) -> 
      
      (* Exit with status *)
      exit status
        
    (* Unix.wait was interrupted *)
    | Unix.Unix_error (Unix.EINTR, _, _) -> 

      (* Get new exit status *)
      let status' = status_of_exn process (Signal 0) in

      Event.log process Event.L_error 
        "@[<hv>Not all child processes could be terminated: @[<hov>%a@]@]"
        (pp_print_list 
           (fun ppf (p, _) -> 
              Format.fprintf ppf "%d" p)
           ",@ ")
        !child_pids;

      exit status' 

    (* Exception in Unix.wait loop *)
    | e -> 

      (* Get new exit status *)
      let status' = status_of_exn process e in

      Event.log process Event.L_error 
        "@[<hv>Not all child processes could be terminated: @[<hov>%a@]@]"
        (pp_print_list 
           (fun ppf (p, _) -> 
              Format.fprintf ppf "%d" p)
           ",@ ")
        !child_pids;

      exit status' 


(* Call cleanup function of process and exit. 

   Give the exception [exn] that was raised or [Exit] on normal
   termination *)
let on_exit_child messaging_thread process exn = 

  (* Exit status of process depends on exception *)
  let status = status_of_exn process exn in

  (* Call cleanup of process *)
  (on_exit_of_process process) ();
  
  Event.log process Event.L_info 
    "Process terminating";

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
let run_process transSys messaging_setup process = 

  (* Fork a new process *)
  let pid = Unix.fork () in

  match pid with 

    (* We are the child process *)
    | 0 -> 

      (

        try 

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

          Event.log process Event.L_info 
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
          (main_of_process process) transSys;

          (* Cleanup and exit *)
          on_exit_child (Some messaging_thread) process Exit

        with 

          (* Termination message received *)
          | Event.Terminate as e -> on_exit_child None process e

          (* Catch all other exceptions *)
          | e -> 

            (* Get backtrace now, Printf changes it *)
            let backtrace = Printexc.get_backtrace () in

            Event.log process Event.L_fatal
              "Runtime error: %s" 
              (Printexc.to_string e);

            if Printexc.backtrace_status () then
              Event.log process Event.L_debug "Backtrace:@\n%s" backtrace;

            (* Cleanup and exit *)
            on_exit_child None process e

      )

    (* We are the parent process *)
    | _ -> 

      (* Keep PID of child process and return *)
      child_pids := (pid, process) :: !child_pids

        
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
  if not (Flags.log_level () = Event.L_off) then

    (

      (* Temporarily set log level to info and output logo *)
      Event.set_log_level Event.L_info;
      Event.log `INVMAN Event.L_info "%a" pp_print_banner ()

    );

  (* Set log level *)
  Event.set_log_level (Flags.log_level ());

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
   Threads module 

  (* CPU timeout? *)
  if Flags.timeout_virtual () > 0. then

    (

      (* Install signal handler for SIGVTALRM after wallclock timeout *)
      Sys.set_signal 
        Sys.sigvtalrm 
        (Sys.Signal_handle (function _ -> raise TimeoutVirtual));

      (* Set interval timer for CPU timeout *)
      let _ (* { Unix.it_interval = i; Unix.it_value = v } *) =
        Unix.setitimer 
          Unix.ITIMER_VIRTUAL
          { Unix.it_interval = 0.; Unix.it_value = Flags.timeout_virtual () } 
      in

      ()

    )  

  else

    (

      (* Install generic signal handler for SIGVTALRM *)
      Sys.set_signal 
        Sys.sigvtalrm 
        (Sys.Signal_handle exception_on_signal);

    );
*)
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

  try 

    Event.log `INVMAN Event.L_info 
      "Parsing input file %s" (Flags.input_file ()); 

    (* Parse file into two-state transition system *)
    let transSys = OldParser.of_file (Flags.input_file ()) in

    (* Output the transition system *)
    debug parse
        "%a"
        TransSys.pp_print_trans_sys
        transSys
    in

    (* Which modules are enabled? *)
    (match Flags.enable () with

      (* No modules enabled *)
      | [] -> 
        (Event.log `INVMAN Event.L_fatal "Need at least one process enabled") 

      (* Single module enabled *)
      | [p] -> 

        (

          Event.log p Event.L_info 
            "Running as a single process";

          (* Run main function of process *)
          (main_of_process p) transSys;
          
          (* Ignore SIGALRM from now on *)
          Sys.set_signal Sys.sigalrm Sys.Signal_ignore;

          (* Cleanup before exiting process *)
          on_exit_child None p Exit
            
        )
        
      (* Run some modules in parallel *)
      | ps -> 
        
        (

          Event.log `INVMAN Event.L_info
            "@[<hov>Running %a in parallel mode@]"
            (pp_print_list pp_print_kind_module ",@ ")
            ps;
         
          let messaging_setup = Event.setup () in

          Event.log `INVMAN Event.L_trace
            "Messaging initialized in invariant manager";
          
          (* Start all child processes *)
          List.iter 
            (function p -> 
              run_process transSys messaging_setup p)
            ps;

          Event.log `INVMAN Event.L_trace "Starting invariant manager";

          (* Initialize messaging for invariant manager, obtain a background
             thread *)
          let _ = 
            Event.run_im
              messaging_setup
              !child_pids
              (on_exit `INVMAN)
          in

          (* Run invariant manager *)
          InvarManager.main child_pids transSys;
          
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
  
