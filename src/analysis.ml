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
open TermLib.Signals

module Log = Log
module BMC = Base
module IND = Step
module PDR = PDR
module InvGenTS = InvGenGraph.TwoState
module InvGenOS = InvGenGraph.OneState

let print_signal_info () =
  Format.printf
    "[%a] %a@."
    pp_print_kind_module (Event.get_module ())
    pp_print_signals () ;

(* Result returned by an analysis. *)
type analysis_result =
  | Ok | Timeout | Error of int

let pp_print_outcome fmt oc =
  Format.fprintf fmt "%s" (match oc with
    | Ok -> "ok"
    | Timeout -> "timeout"
    | Error i -> Format.sprintf "%d" i
  )

(* Debug name of a process. *)
let debug_ext_of_process = suffix_of_kind_module

(* Context of an analysis: a transition system and a list of kids. *)
type t = {
    (* Transition system being analyzed. *)
    sys : TransSys.t ;
    (* Log of the general analysis. *)
    log : Log.t ;
    (* List of kid pids / module. *)
    mutable kids: (int * kind_module) list ;
}

let context_ref = ref None

(* Pretty printer for an analysis context. *)
let pp_print_context ppf { sys ; kids } =
  Format.fprintf
    ppf
    "@[<v>sys:  %a@ kids: @[<hv>%a@]@]"
    TransSys.pp_print_trans_sys_name sys
    (pp_print_list
       ( fun fmt (pid,mdl) ->
         Format.fprintf
           ppf
           "%-10d -> %a"
           pid
           pp_print_kind_module mdl )
       "@ ")
    kids

(* Creates a new analysis context. *)
let empty_context sys log =
  { sys = sys ; log = log ; kids = [] }

(* Removes some kid pids from the context. *)
let rm_kids ({ kids } as t) pids =

  (* Removes pids from a list kids. *)
  let rec loop pids prefix = function

    | kid :: kids ->

       (* Should we remove [kid]? *)
       if List.mem (fst kid) pids then
         (* We should, are there any pids left? *)
         match
           List.filter (fun pid -> pid <> fst kid) pids
         with
         (* No more pids, done. We preserve order by chance, it's not
            necessary. *)
         | [] -> List.rev_append prefix kids
         (* Some pids left, looping. *)
         | pids_left ->
            loop pids_left prefix kids

       else
         (* We should not, looping. *)
         loop pids (kid :: prefix) kids

    | [] ->
       (* Done, making sure all pids were consumed. *)
       ( match pids with

         (* No pids left, fine. Not preserving kid order by the
            way. *)
         | [] -> prefix

         (* Some pids left, error. *)
         | _ ->
            Format.asprintf
              "attempted to remove unknown kid(s) %a"
              (pp_print_list Format.pp_print_int ", ")
              pids
            |> failwith )
  in
  t.kids <- loop pids [] kids

(* Registers a kid in the context. *)
let register_kid t pid mdl = t.kids <- (pid,mdl) :: t.kids


(* Returns the module of a kid from its pid. *)
let module_of_pid { kids } pid = List.assoc pid kids

(* Checks if the list of kids in a context is empty *)
let has_kids = function | { kids = [] } -> false | _ -> true


(* Receives messages, updates transition system and log of the
   analysis. *)
let handle_events t silent =

  (* Receive queued events. *)
  let events =
    (* If in silent mode temporarily deactivate log. *)
    if silent then set_log_level L_warn ;
    (* Actually receiving events. *)
    let events = Event.recv () in
    (* Reactivate logging if necessary. *)
    if silent then set_log_level (Flags.log_level ()) ;
    (* Returning events. *)
    events
  in

  (* Output events in debug mode. *)
  List.iter
    ( fun (mdl,evt) ->
      Event.log
        L_debug
        "Message received from %a: %a."
        pp_print_kind_module mdl
        Event.pp_print_event evt )
    events ;

  (* Update transition system from events. *)
  Event.update_trans_sys t.sys events |> ignore ;

  (* Update log from events. *)
  Log.update_of_events t.log t.sys events




(* Renices a process. *)
let renice_process mdl nice =
  if nice < 0 then
    (* Ignoring negative value. *)
    Event.log
      L_info
      "Ignoring negative niceness value for %s."
      mdl
  else if nice > 0 then
    (* Renicing and logging. *)
    Unix.nice nice
    |> Event.log L_info "Renicing %s to %d." mdl



(* Returns the main function of a kind module. *)
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
  | mdl ->
     Format.asprintf
       "module %a is not a legal analysis module"
       pp_print_kind_module mdl
     |> failwith



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
let status_of_exn = function

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
         L_info
         "Backtrace:@\n%s"
         backtrace ;
     (* Return exit status for error. *)
     status_error


let result_of_exn = function
  | Exit
  | Event.Terminate -> Ok
  | TimeoutWall ->
    Event.log
      L_error "%s Wallclock timeout." timeout_tag ;
    Timeout
  | TimeoutVirtual ->
    Event.log
      L_error "%s CPU timeout." timeout_tag ;
    Timeout
  | exn -> Error (status_of_exn exn)

(* Cleanup function of a process. *)
let on_exit_of_process t = function
  | `BMC -> BMC.on_exit (Some t.sys)
  | `IND -> IND.on_exit (Some t.sys)
  | `PDR -> PDR.on_exit (Some t.sys)
  | `INVGEN -> InvGenTS.on_exit (Some t.sys)
  | `INVGENOS -> InvGenOS.on_exit (Some t.sys)
  | mdl ->
     Format.asprintf
       "module %a is not a legal analysis module"
       pp_print_kind_module mdl
     |> failwith

(* Kills all kids. First attempts to sigterm them with a timeout. If
   some kids are still alive after that, sigkills them with no
   timeout. *)
let kill_all_kids t =

  (* Disable analysis timeout. *)
  unset_timeout () ;

  Event.log
    L_info
    "Terminating all remaining child processes." ;

  (* Kid killing loop. *)
  let rec termination_loop () =

    (* Waiting for child process to terminate. *)
    let pid, status = Unix.wait () in

    (* Killing processes left in process group of child process. *)
    ( try Unix.kill (- pid) Sys.sigkill with _ -> () ) ;

    (* Logging termination status. *)
    Event.log
      L_fatal
      "Process %a (%d, %a)."
      pp_print_process_status status
      pid
      pp_print_kind_module (List.assoc pid t.kids) ;

    (* Removing dead kid from context. *)
    rm_kids t [ pid ] ;

    termination_loop ()

  in

  (* |===| First, we send sigterm to all kids and wait one second for
           them to terminate. If some kids are still alive after this,
           we send sigkill and wait for termination. *)

  (* Sending sigterm to all kids. *)
  t.kids
  |> List.iter
       ( fun (pid, _) -> Unix.kill pid Sys.sigterm ) ;

  Event.log
    L_fatal
    "Waiting for remaining child processes to terminate." ;

  (* Don't wait for termination from sigterm for more than one
     second. *)
  set_sigalrm_timeout () ;
  set_timeout 0.3 ;

  ( try
      (* Waiting for kids to react to sigkill. *)
      termination_loop ()
    with
    (* Whatever happened, deactivate timeout. *)
    | _ -> unset_timeout () ) ;

  (* Are some kids still alive? *)
  if has_kids t |> not

  then (
    (* No, notifying user. *)
    Event.log
      L_warn
      "All child processes terminated." ;
    (* All kids are dead, everything is fine. *)
    Ok

  ) else (
    Event.log
      L_info
      "Some child processes are still alive, sig-killing them." ;

    (* Some kids are not dead, sending sigkill and waiting for
       termination. *)
    t.kids |> List.iter ( fun (pid, _) -> Unix.kill pid Sys.sigkill ) ;

    let status =
      try
        (* Going to termination loop with no timeout. *)
        termination_loop ()
      with
      (* No more child processes, this is the normal exit. *)
      | Unix.Unix_error (Unix.ECHILD, _, _) ->
         status_ok
      (* Unix wait was interrupted. *)
      | Unix.Unix_error (Unix.EINTR, _, _) ->
         status_of_exn (Signal 0)
      (* Exception in unix wait loop. *)
      | e ->
         status_of_exn e
    in

    let result =
      (* Are there any kids still alive? *)
      if has_kids t |> not

      then (
        (* No, notifying user. *)
        Event.log
          L_warn
          "All child processes terminated." ;
        (* The status from the previous termination loop should be
         ok. *)
        assert ( status = status_ok ) ;
        (* All kids are dead, everything is fine. *)
        Ok

      ) else (
        (* Some kids are still alive, can't do much more. *)
        Event.log
          L_warn
          "Some child processes are still alive after sigkill, \
           consider killing them manually." ;
        (* The status from the previous termination loop should NOT be
         ok. *)
        assert ( status <> status_ok ) ;
        Error status
      )
    in

    (* Consume all remaining messages silently. *)
    handle_events t true ;

    (* Return kid slaughter outcome. *)
    result

  )



(* Panic exit, called by the background thread. *)
let panic_exit exn =
  match !context_ref with
  | Some t when has_kids t ->
     kill_all_kids t |> ignore ;
  | _ ->
     failwith "panic exit with no kids to kill"

(* Call cleanup function of process and exit. 

   Give the exception [exn] that was raised or [Exit] on normal
   termination. *)
let on_exit_kid t messaging_thread process exn =

  (* Exit status of process depends on exception. *)
  let status = status_of_exn exn in

  (* Call cleanup of process. *)
  (on_exit_of_process t process) ;

  (* logging termination event. *)
  Unix.getpid ()
  |> Event.log
       L_info 
       "Process %a (%d) terminating."
       pp_print_kind_module process ;

  Event.terminate_log () ;
  
  ( match messaging_thread with 
    | Some t -> Event.exit t
    | None -> () ) ;

  (* Exit process with status. *)
  exit status


(* Clean exit from a context and the outcome of the analysis. *)
let on_exit t outcome =
  let slaughter_outcome = kill_all_kids t in
  ( match slaughter_outcome, outcome with
    (* Kid slaughter went ok. *)
    | Ok, res -> res
    (* Kid slaughter failed, analysis was ok. *)
    | res, Ok | res, Timeout -> res
    (* Both went wrong, this is bad. *)
    | _ ->
       failwith
         "[Panic] Analysis and child process termination \
          went wrong." )

(* Clean exit from a context and an exception. *)
let on_exit_exn t exn =
  match Event.get_module () with

  (* We are the supervisor, killing kids. *)
  | `Supervisor ->
     result_of_exn exn |> on_exit t

  (* We are a child process, exiting. *)
  | mdl ->
     on_exit_kid t None mdl exn


(* Checks if some kids have terminated. Returns true if the analysis is
   over: either all kids are done or one of them exited with an error
   status. *)
let rec wait_for_kids t =

  match
    
    ( try
        (* Check if any kid process has died, return immediately. *)
        Unix.waitpid [Unix.WNOHANG] (- 1)

      with
        (* Catch error if there is no child process. *)
        Unix.Unix_error (Unix.ECHILD, _, _) -> 0, Unix.WEXITED 0 )

  with

  (* No child process died. *)
  | 0, _ ->

     (* Terminate if the last child process has died. *)
     if has_kids t |> not then Some(Ok) else None

  (* Child process exited normally. *)
  | child_pid, (Unix.WEXITED 0 as status) -> (

    Event.log
      L_warn
      "Child process %a (%d) terminated (%a)."
      pp_print_kind_module (module_of_pid t child_pid)
      child_pid
      pp_print_process_status status ;

    ( if List.mem_assoc child_pid t.kids then
        (* Remove child process from list *)
        rm_kids t [child_pid] ) ;

    (* Check if more child processes have died *)
    wait_for_kids t

  )

  (* Child process dies with non-zero exit status or was killed. *)
  | child_pid, status -> (

    Event.log
      L_error
      "Child process %a (%d) terminated (%a)"
      pp_print_kind_module (module_of_pid t child_pid)
      child_pid
      pp_print_process_status status;

    (* Remove child process from list. *)
    rm_kids t [child_pid] ;

    (* Kill kids. *)
    Some( Error(status_error) )

  )



(* Polling loop. Handles events and checks for termination criteria. *)
let rec polling_loop t =

  (* Handle event (silent=false). *)
  handle_events t false ;


  if
    (* Check if the analysis is over. *)
    TransSys.all_props_proved t.sys
  then (
    Event.log
      L_warn
      "%s All properties proved or disproved in %.3fs."
      done_tag
      (Stat.get_float Stat.total_time) ;

    Ok

  ) else
    (* Check if all child processes have died or if one of them
       terminated abnormaly, and exit if necessary *)
    ( match wait_for_kids t with
      (* No result status, looping. *)
      | None -> minisleep 0.03 ; polling_loop t
      (* Terminating. *)
      | Some(status) -> status )



(* Fork and run a child process *)
let run_process t messaging_setup process =

  (* Fork a new process *)
  let pid = Unix.fork () in

  match pid with 

  | 0 ->
     (* We are the child process *)
     ( try

         (* Ignore sigalrm in child process. *)
         ignore_sigalrm () ;
         set_sigterm () ;

         (* All log messages are sent to the invariant manager
            now. *)
         Event.set_relay_log ();

         (* Set module currently running. *)
         Event.set_module process;

         (* Make the process leader of a new session. *)
         Unix.setsid () |> ignore ;

         let pid = Unix.getpid () in

         (* Initialize messaging system for process. *)
         let messaging_thread =
           Event.run_process
             process
             messaging_setup
             (on_exit_kid t None process)
         in

         (* Record backtraces on log levels debug and higher. *)
         if output_on_level L_debug then
           Printexc.record_backtrace true;

         Event.log
           L_debug
           "Starting new process with PID %d (%s)"
           pid
           (suffix_of_kind_module (Event.get_module ())) ;

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
         main_of_process process t.sys ;

         (* Cleanup and exit. *)
         on_exit_kid
           t (Some messaging_thread) process Exit

       with 

       (* Termination message received. *)
       | Event.Terminate as e ->
          on_exit_kid t None process e

       (* Not propagating signal exceptions. *)
       | Signal s as e ->
          on_exit_kid t None process e
          (* exception_on_signal s *)

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
          on_exit_kid t None process e

     )

  (* We are the parent process. *)
  | _ ->
     (* Keep PID of child process and return. *)
     register_kid t pid process


(* Runs an analysis on a transition system and a log, with a list of
   modules to run. Raises [Invalid_argument] if called with no
   modules. *)
let run sys log msg_setup = function
  | [] ->
     raise
       ( Invalid_argument "cannot run analysis with no modules" )
       
  | modules ->

     (* Create an analysis context. *)
     let context = empty_context sys log in
     context_ref := Some context ;

     ( try

         (* Launching all processes. *)
         modules
         |> List.iter
              ( fun modul ->
                run_process context msg_setup modul ) ;

         (* Updating background thread with the list of kids. *)
         Event.update_child_processes_list context.kids ;

         (* Going to message reception / termination checks. *)
         let outcome = polling_loop context in

         (* Reset timeout counter. *)
         unset_timeout () ;

         (* Update log with remaining unknown / k-true props. *)
         Log.close_log log sys ;

         (* Clean everything and exit analysis. *)
         let outcome = on_exit context outcome in

         (* There should be no kid left alive. *)
         assert (context.kids = []) ;

         (* Reset timeout counter. *)
         unset_timeout () ;

         minisleep 0.3 ;

         (* Consume all remaining messages silently. *)
         handle_events context true ;

         outcome

       with
       | e ->

          (* Update log with remaining unknown / k-true props. *)
          Log.close_log log sys ;

          (* Reset timeout. *)
          unset_timeout () ;

          (* Clean exit, killing everyone if we are the supervisor. *)
          let outcome = on_exit_exn context e in

          (* Reset timeout. *)
          unset_timeout () ;

          minisleep 0.3 ;

          (* If we are a kid, the previous line killed the
             process. The following only applies to the supervisor. *)

          (* There should be no kid left alive. *)
          assert (context.kids = []) ;

          (* Consume all remaining messages silently. *)
          handle_events context true ;

          (* Returning result status. *)
          outcome )

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
