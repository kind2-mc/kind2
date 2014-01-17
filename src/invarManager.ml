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

let on_exit () =

  try 

    (* Send termination message to all worker processes *)
    Event.terminate ();

  (* Skip if running as a single process *)
  with Messaging.NotInitialized -> ()


(* Wait for child processes to die and remove from list of running processes,

   Return [true] if the last child processes has died or if one
   process exited normally, signalling an answer *)
let rec wait_for_children child_pids = 

  (* TODO: Can we use SIGCHLG? Don't periodically do waitpid, but handle
     signal and raise an exception. *)

  try 

    (* Check if any child process has died, return immediately *)
    match Unix.waitpid [Unix.WNOHANG] (- 1) with 

      (* No child process died *)
      | 0, _ -> false

      (* Child process exited normally *)
      | child_pid, (Unix.WEXITED 0 as status) -> 
        
        (

          Event.log `INVMAN Event.L_info
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

        (Event.log `INVMAN Event.L_error
           "Child process %d (%a) %a" 
           child_pid 
           pp_print_kind_module (List.assoc child_pid !child_pids) 
           pp_print_process_status status;

         (* Remove child process from list *)
         child_pids := List.remove_assoc child_pid !child_pids;

         (* Check if more child processes have died *)
         (* wait_for_children child_pids *)
         true

        )

  with Unix.Unix_error (Unix.ECHILD, _, _) -> 

    (* Terminate if the last child process has died *)
    !child_pids = []


let handle_event transSys = function 

  | Event.Invariant (m, i) -> 

    (

      (* Check if received invariant is a property *)
      let props_valid, props' =
        List.partition
          (function (p, t) -> Term.equal i t)
          transSys.TransSys.props
      in
      
      (* Log property as proved *)
      List.iter (Event.log_proved m None) (List.map fst props_valid);

      transSys.TransSys.props <- props';

      transSys.TransSys.props_valid <- 
        transSys.TransSys.props_valid @ props_valid;
      
      if props' = [] then 

        ( 

          Event.log `INVMAN Event.L_info "All properties proved or disproved";

          Event.terminate ()

        )

    )

  (* Output property as disproved *)
  | Event.Disproved (m, k, p) -> 

    (

      (* Remove disproved property from list *)
      let props_invalid, props' =
        List.partition
          (function (n, _) -> p = n)
          transSys.TransSys.props
      in
      
      (* Log property as disproved *)
      List.iter (Event.log_disproved m k) (List.map fst props_invalid);

      transSys.TransSys.props <- props';

      transSys.TransSys.props_invalid <- 
        transSys.TransSys.props_invalid @ props_invalid;
      
      if props' = [] then 

        ( 

          Event.log `INVMAN Event.L_info "All properties proved or disproved";

          Event.terminate ()

        )

    )

  (* Output property as disproved *)
  | Event.Proved (m, k, p) -> 

    (

      (* Remove proved property from list *)
      let props_valid, props' =
        List.partition
          (function (n, _) -> p = n)
          transSys.TransSys.props
      in
      
      (* Log property as proved *)
      List.iter (Event.log_proved m k) (List.map fst props_valid);

      transSys.TransSys.props <- props';

      transSys.TransSys.props_valid <- 
        transSys.TransSys.props_valid @ props_valid;
      
      if props' = [] then 

        ( 

          Event.log `INVMAN Event.L_info "All properties proved or disproved";

          Event.terminate ()

        )

    )

  | Event.BMCState _ -> ()


(* Polling loop *)
let rec loop child_pids transSys = 

  List.iter 
    (function e -> 
      Event.log `INVMAN Event.L_debug "%a" Event.pp_print_event e;
      handle_event transSys e)
    (Event.recv ());

  (* Check if child processes have died and exit if necessary *)
  if wait_for_children child_pids then () else 

    (

      (* Sleep *)
      minisleep 0.01;

      (* Continue polling loop *)
      loop child_pids transSys

    )
  

(* Entry point *)
let main child_pids transSys =

  (* Run main loop *)
  loop child_pids transSys

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
