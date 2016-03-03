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
        
open Lib

let print_stats trans_sys =
  
  Event.log
    L_debug
    "@[<v>%a@,\
     Final statistics:@]"
    Pretty.print_line ();
  
  List.iter 
    (fun (mdl, stat) -> Event.log_stat mdl L_debug stat)
    (Event.all_stats ());
  
  (match trans_sys with | None -> () | Some trans_sys ->
    Event.log_prop_status 
      L_fatal
      (TransSys.get_prop_status_all trans_sys))

let on_exit trans_sys =

  print_stats trans_sys ;
    
  try 
    
    (* Send termination message to all worker processes *)
    Event.terminate () ;

  (* Skip if running as a single process *)
  with Messaging.NotInitialized -> ()


(* List of modules to monitor, and do actions in case they crashes *) 
let monitor_modules = [`BMC; `IND]

(* modules for which other modules needs them to be active to function
   properly *)
let needed_by = function
  | `BMC -> [`IND; `IND2];
  | `IND -> [`BMC]
  | _ -> []

(* Set of core modules. The analysis goes on if at least one of them is
   active *)
let core_module = function
  | `IND | `BMC | `IC3 -> true
  | _ -> false


let pids_depend_on m child_pids =
  let deps = needed_by m in
  List.filter (fun (_, md) -> List.mem md deps) child_pids

(* Terminate a module and then kill it if it did not exit. *)
let term_kill (pid, dep) =
  Event.log L_warn "Terminating useless %a (PID %d)"
    pp_print_kind_module dep pid;
  (try Unix.kill pid Sys.sigterm with _ -> ());
  minisleep 0.1; 
  (try
     Unix.kill (- pid) Sys.sigkill;
     Event.log L_warn "Killed not responding useless %a (PID %d)"
       pp_print_kind_module dep pid;
   with _ -> ())

(* Kill engines that are not needed anymore because some of their dependencies
   have crashed. This function returns a boolean that is true when it is no
   longer necessary to continue the analysis because core components have
   crahsed.  *)
let kill_useless_engines child_pids =
  List.iter (fun m ->
      if not (List.exists (fun (_,x) -> x = m) child_pids) then
        List.iter term_kill (pids_depend_on m child_pids)
    ) monitor_modules;
  not (List.exists (fun (_,m) -> core_module m) child_pids)

  

(* Remove terminated child processed from list of running processes

   Return [true] if the last child processes has terminated or some
   process exited with a runtime error or was killed. *)
let rec wait_for_children child_pids = 

  match 
    
    (try 

       (* Check if any child process has died, return immediately *)
       Unix.waitpid [Unix.WNOHANG] (- 1) 

     (* Catch error if there is no child process *)
     with Unix.Unix_error (Unix.ECHILD, _, _) -> 0, Unix.WEXITED 0)

  with 

    (* No child process died *)
    | 0, _ -> 

      (* Terminate if the last child process has died *)
      !child_pids = []

    (* Child process exited normally *)
    | child_pid, (Unix.WEXITED 0 as status) -> 

      (

        Event.log L_info
          "Child process %d (%a) %a" 
          child_pid 
          pp_print_kind_module (List.assoc child_pid !child_pids) 
          pp_print_process_status status;

        (* Remove child process from list *)
        child_pids := List.remove_assoc child_pid !child_pids;

        (* Check if more child processes have died *)
        wait_for_children child_pids

      )

    (* Child process dies with non-zero exit status or was killed *)
    | child_pid, status -> 

      (Event.log L_warn
         "Child process %d (%a) %a" 
         child_pid 
         pp_print_kind_module (List.assoc child_pid !child_pids) 
         pp_print_process_status status;

       (* Remove child process from list *)
       child_pids := List.remove_assoc child_pid !child_pids;

       (* Check if more child processes have died *)
       kill_useless_engines !child_pids ||
       wait_for_children child_pids

      )


let handle_events input_sys aparam trans_sys = 

  (* Receive queued events *)
  let events = Event.recv () in

  (* Output events *)
  List.iter 
    (function (m, e) -> 
      Event.log
        L_debug
        "Message received from %a: %a"
        pp_print_kind_module m
        Event.pp_print_event e)
    events;

  (* Update transition system from events *)
  let _ =
    Event.update_trans_sys input_sys aparam trans_sys events
  in

  ()

(* Polling loop *)
let rec loop done_at child_pids input_sys aparam trans_sys = 

  handle_events input_sys aparam trans_sys;

  let done_at' =

    (* All properties proved? *)
    if TransSys.all_props_proved trans_sys then 

      (

        ( 

          (* Has is_done been true in the last iteration? *)
          match done_at with

            | None -> 

              (* Message after is_done becomes true first time *)
              Event.log L_info
                "<Done> All properties proved or disproved in %.3fs."
                (Stat.get_float Stat.total_time);

              Event.terminate ();

              Some (Unix.gettimeofday ())

            | Some t ->

              (* Message after if is_done has been true in the last
                 iteration *)
              Event.log L_info
                "All properties proved or disproved,@ \
                 waiting for children to terminate.";

              Some t

        );

      )

    else 

      None

  in

  if 

    (* Check if child processes have died and exit if necessary *)
    wait_for_children child_pids
    ||
    (match done_at with 
      | None -> false
      | Some t -> (Unix.gettimeofday () -. t) > 0.3)

  then 

    (

      (* Get messages after termination of all processes *)
      handle_events input_sys aparam trans_sys ;

      (* All properties proved? *)
      if TransSys.all_props_proved trans_sys then
        Event.terminate ()

    ) 

  else

    (

      (* Sleep *)
      minisleep 0.01;

      (* Continue polling loop *)
      loop done_at' child_pids input_sys aparam trans_sys

    )
  

(* Entry point *)
let main child_pids input_sys aparam trans_sys =

  (* Run main loop *)
  loop None child_pids input_sys aparam trans_sys

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
