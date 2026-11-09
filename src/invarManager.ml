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

(* The property [name] of [trans_sys] to slice the nodes to, as IC3IA
   does: one that was in the input system, when the nodes are sliced *)
let slice_target trans_sys name =
  if Flags.slice_nodes () <> `On then None
  else
    let prop = TransSys.property_of_name trans_sys name in
    match prop.Property.prop_source with
    | Property.Instantiated _
    | Property.Assumption _
    | Property.Generated (None, _, _) -> None
    | _ -> Some prop

(* The systems sliced to the properties of [trans_sys], built in its round,
   by property name: a system is built once for every use *)
let sliced_cache : (TransSys.t * (string, TransSys.t option) Hashtbl.t) option ref =
  ref None

(* The system of the analysis sliced to the property, as IC3IA builds it
   (see [slice_target]) *)
let sliced_to_property input_sys aparam trans_sys name () =
  let cache =
    match !sliced_cache with
    | Some (sys, cache) when sys == trans_sys -> cache
    | _ ->
      let cache = Hashtbl.create 7 in
      sliced_cache := Some (trans_sys, cache) ;
      cache
  in
  match Hashtbl.find_opt cache name with
  | Some sliced -> sliced
  | None ->
    let sliced =
      match slice_target trans_sys name with
      | None -> None
      | Some prop ->
        match
          InputSystem.trans_sys_of_analysis ~slice_to_prop:prop input_sys
            (Analysis.param_clone aparam)
        with
        | sys, _ -> Some sys
        | exception (Failure _ | Invalid_argument _ | Not_found) -> None
    in
    Hashtbl.replace cache name sliced ;
    sliced

(* The counterexample [cex] to the property [p] of [trans_sys], a system
   that leaves out the finiteness constraints of some containers, as a
   counterexample of the system with them, if one with the same inputs is
   found in time (see [FiniteSets]): the system sliced to the property
   (see [slice_target]) with the constraints, unrolled to the length of
   the counterexample, with the inputs and the constants fixed to their
   values in it (the arrays of unknown size, the sets among them, are left
   free), and the property false at its last step. The new counterexample
   is the path of its model, over the variables of that system, and its
   containers are finite. *)
let finite_counterexample input_sys aparam trans_sys p cex =
  if not (FiniteSets.within_check_budget ()) then None
  else
    let started = Unix.gettimeofday () in
    Fun.protect
      ~finally:(fun () ->
        FiniteSets.spent_checking (Unix.gettimeofday () -. started))
    @@ fun () ->
    let slice_to_prop = slice_target trans_sys p in
    match
      FiniteSets.with_enabled (fun () ->
        fst
          (InputSystem.trans_sys_of_analysis ?slice_to_prop input_sys
             (Analysis.param_clone aparam)))
    with
    | exception (Failure _ | Invalid_argument _ | Not_found) -> None
    | sys ->
      let k = match cex with (_, values) :: _ -> List.length values - 1 | [] -> 0 in
      let state_vars = StateVar.StateVarSet.of_list (TransSys.state_vars sys) in
      let var_at sv i = Term.mk_var (Var.mk_state_var_instance sv (Numeral.of_int i)) in
      match
        SMTSolver.create_instance ~timeout:FiniteSets.check_timeout
          ~produce_models:true (TransSys.get_logic sys) (Flags.Smt.solver ())
      with
      | exception (Failure _ | Unix.Unix_error _ | Sys_error _) -> None
      | solver ->
        Fun.protect ~finally:(fun () -> SMTSolver.delete_instance solver)
        @@ fun () ->
        try
          let k' = Numeral.of_int k in
          RecUnrolling.declare_and_init solver sys k' ;
          for i = 1 to k do
            TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) sys
              (Numeral.of_int i)
            |> SMTSolver.assert_term solver
          done ;
          cex |> List.iter (fun (sv, values) ->
            if (StateVar.is_input sv || StateVar.is_const sv)
            && StateVar.StateVarSet.mem sv state_vars then
              values |> List.iteri (fun i value ->
                RecUnrolling.fix_value (var_at sv i) value
                |> List.iter (SMTSolver.assert_term solver))) ;
          TransSys.get_prop_term sys p
          |> Term.bump_state k'
          |> Term.mk_not
          |> SMTSolver.assert_term solver ;
          if not (SMTSolver.check_sat solver) then None
          else
            (* The whole path, the containers included, as the engines
               read it *)
            let model =
              SMTSolver.get_var_values
                ~array_limit:(`Omit SMTSolver.max_array_elements)
                solver
                (TransSys.get_state_var_bounds sys)
                (TransSys.vars_of_bounds sys Numeral.zero k')
            in
            Some
              (Model.path_from_model (TransSys.state_vars sys) model k'
               |> Model.path_to_list)
        with
        | SMTSolver.Timeout | SMTSolver.Unknown | SMTSolver.Killed
        | SMTSolver.Died _ | Failure _ | Invalid_argument _ | Not_found
        | Unix.Unix_error _ | End_of_file | Sys_error _ -> None

let handle_events input_sys aparam trans_sys = 

  (* Receive queued events *)
  let events = KEvent.recv () in

  (* A property found false by a counterexample that reaches a recursive
     call past the unrollings of its function, whose outputs are
     unconstrained, and whose violation depends on them: the counterexample
     may be spurious, and the event is dropped. The function is unrolled
     further and the engines run again (see [RecUnrolling] and
     [Kind2Flow]), or, when it is at the limit, the property is left
     unknown. *)
  let events =
    events |> List.filter_map (function
      | (m, KEvent.PropStatus (p, Property.PropFalse cex)) -> (
        (* On Windows the wall clock timeout is only ever noticed by the
           polling loop; a query to a solver is a process to start and
           wait for, and a round can bring dozens of counterexamples at
           once, so the clock is looked at before each. *)
        ( if Sys.win32 then
            let timeout = Flags.timeout_wall () in
            Stat.update_time Stat.total_time ;
            if timeout > 0. && Stat.get_float Stat.total_time > timeout then
              raise TimeoutWall ) ;
        (* A counterexample on a system that leaves out the finiteness
           constraints of containers in the cone of influence of the
           property may rely on an infinite container. It is reported when
           the engine found its containers finite in its model. Otherwise
           it is checked on the system with the constraints, which gives
           one with the same inputs if there is one; failing that, it is
           dropped, and the engines run again on that system (see
           [FiniteSets]), on which it is found again if it is genuine *)
        let cex =
          if TransSys.omits_finiteness trans_sys
          && (match sliced_to_property input_sys aparam trans_sys p () with
              | Some sliced -> TransSys.omits_finiteness sliced
              | None -> true)
          then
            match finite_counterexample input_sys aparam trans_sys p cex with
            | Some cex -> Some cex
            | None -> FiniteSets.request () ; None
          else Some cex
        in
        match cex with
        | None -> None
        | Some cex ->
        match RecUnrolling.suspect trans_sys p cex with
        | [] ->
          (* Reported: whether refining the recursive functions whose
             contracts abstract them may rule the counterexample out *)
          RecUnrolling.check_abstractions
            ~sliced:(sliced_to_property input_sys aparam trans_sys p)
            trans_sys p cex ;
          Some (m, KEvent.PropStatus (p, Property.PropFalse cex))
        | reached ->
          ( match RecUnrolling.request aparam p reached with
            | `At_limit (too_many, at_limit) ->
              if too_many <> [] then
                KEvent.log L_warn
                  "@[<hov>Counterexamples reach a recursive call of %a left \
                   unconstrained, and unrolling the function further would \
                   create more than %d instances of it, the limit;@ the \
                   properties they falsify are left unknown.@]"
                  (pp_print_list (KEvent.pp_print_user_node_name input_sys) ", ")
                  too_many
                  (Flags.Contracts.rec_instances ()) ;
              if at_limit <> [] then
                KEvent.log L_warn
                  "@[<hov>Counterexamples reach a recursive call of %a left \
                   unconstrained after %d unrollings, the limit;@ the \
                   properties they falsify are left unknown.@]"
                  (pp_print_list (KEvent.pp_print_user_node_name input_sys) ", ")
                  at_limit
                  (Flags.Contracts.rec_unrollings ())
            | `Requested -> () ) ;
          None
      )
      | event -> Some event)
  in

  (* Output events *)
  List.iter 
    (function (m, e) -> 
      KEvent.log
        L_debug
        "Message received from %a: %a"
        pp_print_kind_module m
        KEvent.pp_print_event e)
    events;

  (* Update transition system from events *)
  let _ =
    KEvent.update_trans_sys input_sys aparam trans_sys events
  in

  ()

let print_stats trans_sys =
  
  KEvent.log
    L_debug
    "@[<v>%a@,\
     Final statistics:@]"
    Pretty.print_line ();
  
  List.iter 
    (fun (mdl, stat) -> KEvent.log_stat mdl L_debug stat)
    (KEvent.all_stats ());
  
  match trans_sys with
  | None -> ()
  | Some trans_sys ->
    let status_kinds = TransSys.get_prop_status_and_kind_all_nocands trans_sys in
    KEvent.log_prop_status L_fatal trans_sys status_kinds


let on_exit trans_sys =

  print_stats trans_sys ;
    
  try 
    (* Send termination message to all worker processes *)
    KEvent.terminate () ;

    (* if trans_sys <> None then handle_events (get trans_sys); *)
      
  (* Skip if analysisning as a single process *)
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
  | `IND | `BMC | `IC3QE | `IC3IA -> true
  | _ -> false


let pids_depend_on m child_pids =
  let deps = needed_by m in
  List.filter (fun (_, md) -> List.mem md deps) child_pids

(* Terminate an engine, and kill the solvers of its domain to unblock
   it if it did not exit. *)
let term_kill (id, dep) =
  KEvent.log L_warn "Terminating useless %a (%d)"
    pp_print_kind_module dep id;
  KEvent.terminate_worker id;
  minisleep 0.1;
  (match EngineDomains.find id with
   | Some c ->
     EngineDomains.kill_solvers c;
     KEvent.log L_warn "Killed solvers of not responding useless %a (%d)"
       pp_print_kind_module dep id
   | None -> ())

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

let check_pending_processes run_process pending_processes sys child_pids =
  pending_processes := !pending_processes |> List.filter (function
    | ProcessCall.IC3IA_Call (_, _, prop, _) -> (
      match TransSys.get_prop_status sys prop.prop_name with
      | PropUnknown | PropKTrue _ -> true
      | _ -> false
    )
    | _ -> assert false
  ) ;
  match !pending_processes with
  | [] -> ()
  | _ -> (
    let num_of_ic3ia_modules =
      !child_pids |> List.filter (function
        | (_, `IC3IA) -> true
        | _ -> false
      )
      |> List.length
    in
    let diff = Flags.IC3IA.max_processes () - num_of_ic3ia_modules in
    if diff > 0 then
      let to_run, pending =
        list_split diff !pending_processes
      in
      pending_processes := pending ;
      List.iter (fun m -> run_process m) to_run ;
  )


(* Remove terminated engines from the list of running engines

   Return [true] if the last engine has terminated or some engine
   terminated with a runtime error. *)
let wait_for_children run_process pending_processes sys child_pids =

  match EngineDomains.take_finished () with

    (* No engine terminated *)
    | [] ->

      (* Terminate if the last engine has terminated *)
      !child_pids = []

    | finished -> (

      (* Process every engine that terminated *)
      let crashed =
        finished |> List.fold_left (fun crashed child ->

          let child_id = EngineDomains.id child in

          let crashed_too =
            match EngineDomains.outcome child with
            | EngineDomains.Done None
              when MemoryWatch.stopped_for_memory child_id ->
              (* Stopped for the memory its solvers took: the engines
                 that depend on it cannot conclude without it *)
              KEvent.log L_info
                "Child process %d (%a) stopped for memory"
                child_id
                pp_print_kind_module (EngineDomains.mdl child) ;
              true
            | EngineDomains.Done None ->
              KEvent.log L_info
                "Child process %d (%a) terminated normally"
                child_id
                pp_print_kind_module (EngineDomains.mdl child) ;
              false
            | EngineDomains.Done (Some e) ->
              KEvent.log L_warn
                "Child process %d (%a) terminated on exception: %s"
                child_id
                pp_print_kind_module (EngineDomains.mdl child)
                (Printexc.to_string e) ;
              true
            | EngineDomains.Running -> assert false
          in

          (* Remove engine from list *)
          child_pids := List.remove_assoc child_id !child_pids ;

          check_pending_processes run_process pending_processes sys child_pids ;

          crashed || crashed_too

        ) false
      in

      (* If some engine crashed, terminate the engines that depend on
         it, and stop the analysis if no core engine is left *)
      (crashed && kill_useless_engines !child_pids) ||
      !child_pids = []

    )

(* Polling loop *)
let rec loop
  run_process pending_processes
  ignore_props stop_if_falsified done_at timeout_analysis_reached
  child_pids input_sys aparam trans_sys
=

  handle_events input_sys aparam trans_sys ;

  (* Stop the engine whose solvers take the memory, if they are about
     to run the analysis out of it *)
  MemoryWatch.check () ;

  (* On Windows there is no SIGALRM-based wall clock timeout: enforce
     it here. [handle_events] has just refreshed the total time. *)
  ( if Sys.win32 then
      let timeout = Flags.timeout_wall () in
      if timeout > 0. && Stat.get_float Stat.total_time > timeout then
        raise TimeoutWall ) ;

  let done_at' =

    (* All properties proved, disproved or given up on? Or a recursive
       function to unroll further, on which the engines are to be run
       again (see [RecUnrolling])? *)
    let deepening = RecUnrolling.requested () <> [] || FiniteSets.requested () in
    if (RecUnrolling.all_settled trans_sys && not ignore_props)
    || (TransSys.at_least_one_prop_falsified trans_sys && stop_if_falsified)
    || deepening
    then (

      (* Has is_done been true in the last iteration? *)
      match done_at with

      | None ->
          (* Message after is_done becomes true first time *)
          if deepening then
            KEvent.log L_info
              "<Done> @[<v>\
                %s after %.3fs.@ \
                Waiting for children to terminate.\
              @]"
              (if RecUnrolling.requested () <> []
               then "Recursive functions to unroll further"
               else "Finiteness constraints of sets and maps to apply")
              (Stat.get_float Stat.total_time)
          else
            KEvent.log L_info
              "<Done> @[<v>\
                All properties proved or disproved in %.3fs.@ \
                Waiting for children to terminate.\
              @]"
              (Stat.get_float Stat.total_time) ;

          (* Solvers of terminating engines are killed outright instead
             of shut down gracefully, as the engine processes and their
             solvers used to be killed. Solvers of the running engines
             are killed right away to unblock engines that are inside a
             solver call and would not see the termination message. *)
          EngineDomains.set_terminating true ;
          KEvent.terminate () ;
          EngineDomains.live () |> List.iter EngineDomains.kill_solvers ;
          Some (Unix.gettimeofday ())

      | Some t -> Some t

    ) else if timeout_analysis_reached () then (

      match done_at with

      | None ->

        let timeout_analysis = Flags.timeout_analysis () in

        KEvent.log L_info
          "<Done> @[<v>\
            Reached analysis timeout (%1.0f)@ \
            Waiting for children to terminate.
          @]" timeout_analysis ;

        EngineDomains.set_terminating true ;
        KEvent.terminate () ;
        EngineDomains.live () |> List.iter EngineDomains.kill_solvers ;
        Some (Unix.gettimeofday ())

      | Some t -> Some t

    ) else None

  in

  (* Check if child processes have died and exit if necessary *)
  if wait_for_children run_process pending_processes trans_sys child_pids || (
    match done_at with 
    | None -> false
    | Some t -> (Unix.gettimeofday () -. t) > 0.3
  ) then (

    (* Get messages after termination of all processes *)
    handle_events input_sys aparam trans_sys ;

    (* All properties proved? *)
    if TransSys.all_props_proved trans_sys then KEvent.terminate ()

    (* Have we reached the run timeout? *)
  ) else (

    (* Sleep *)
    minisleep 0.01 ;

    (* Continue polling loop *)
    loop
      run_process pending_processes
      ignore_props stop_if_falsified done_at' timeout_analysis_reached
      child_pids input_sys aparam trans_sys

  )
  

(* Entry point *)
let main run_process pending_processes ignore_props stop_if_falsified child_pids input_sys aparam trans_sys =
  (* Building the function checking whether we reached the analysis timeout. *)
  let timeout_analysis = Flags.timeout_analysis () in
  let timeout_analysis_reached =
    if timeout_analysis > 0.0 then (
      fun () ->
        Stat.get_float Stat.analysis_time > timeout_analysis
    ) else (
      fun () -> false
    )
  in

  let pending_processes = ref pending_processes in

  (* Run main loop *)
  loop
    run_process pending_processes
    ignore_props stop_if_falsified None timeout_analysis_reached
    child_pids input_sys aparam trans_sys

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
