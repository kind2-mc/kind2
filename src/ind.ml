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

(** Induction checking

    @author Paul Meng
*)

let on_exit () = ()

let main _ = ()

(* Commented out new code, needs adaption to compile




open Lib

(* Use configured SMT solver *)
module INDSolver = SMTSolver.Make (Config.SMTSolver)

(* High-level methods for BMC solver *)
module S = SolverMethods.Make (INDSolver)

(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)

(* Current step in BMC. *)
let bmcK = ref 0

(* Solver instance if created *)
let ref_solver = ref None

(* Output statistics *)
let pp_print_stat ppf = 

  Format.fprintf
    ppf
    "Statistics of %a module:@.@.%t@.%t@.%t"
    pp_print_kind_module `IND
    Stat.pp_print_misc_stats
    Stat.pp_print_ind_stats
    Stat.pp_print_smt_stats


(* Clean up before exit *)
let on_exit () =

  (* Stop all timers *)
  Stat.ind_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  Event.stat 
    `IND 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.ind_stats_title, Stat.ind_stats;
     Stat.smt_stats_title, Stat.smt_stats];

  (* Delete solver instance if created *)
  (try 
     match !ref_solver with 
       | Some solver -> 
         S.delete_solver solver; 
         ref_solver := None
       | None -> ()
   with 
     | e -> 
       Event.log `IND Event.L_error 
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


(** Get a list of all state variables up to k steps from transition system. *)
let rec get_state_vars_upto_k ts k acc = 
  
        if (k < 0) then
                acc
        else
                (
                (* Get the variables in state k*)
    let acc' = 
      List.map (
        fun state_var ->
          Var.mk_state_var_instance state_var (Numeral.of_int k)
      ) (TransSys.state_vars ts)
                in
                get_state_vars_upto_k ts (k-1) acc'@acc
                )
                
                
(** Push transition system upto k-1 step*)
let rec aux ts k solver =
        if k <> 1 then
                (
                        S.assert_term solver (TransSys.constr_of_bound (k-1) ts);
                        aux ts (k-1) solver
                )
                
(** Make a list of terms upto k-1*)             
let rec mk_terms_upto_k_1 t k acc =
        if k = 0 then
                acc
        else
                (
                  mk_terms_upto_k_1 t (k-1) ((TransSys.bump_state (k-1) t)::acc)
                )
                
                        
(** Check for messages and update associated lists*)
let update solver ts propertiesToCheck assumedProps invariants k reset=
        
        (* Side effect: Terminate when ControlMessage TERM is received.*)
        let messages = Event.recv () in
        
        List.fold_left (
   fun (propertiesToCheck, assumedProps, invariants, restart) message ->
      match message with

      | (Event.Invariant (_, inv)) ->
                                S.assert_term solver (Term.mk_and (mk_terms_upto_k_1 inv k []));
        (propertiesToCheck, assumedProps, inv::invariants, reset)
                                
                                (*Check bmc state and eliminated disproved properties*)
                        | Event.BMCState (bmcK', disprovedPropsList) ->
                                
                                bmcK := bmcK';
                                
                                let invalidPropsList =
                                        List.filter (
                                                fun (name, prop) ->
                                                        List.mem name disprovedPropsList
                                                        ) ts.TransSys.props 
                                in
                                                        
                                ts.TransSys.props_invalid <- invalidPropsList@ts.TransSys.props_invalid;
                                
                                (* If there is a assumed property disproved by BMC, add all the assumed properties back to check again.*)                               
                                if (List.exists (fun (_, p) -> List.mem (fst p) disprovedPropsList) assumedProps) then
                                        (       

                                                ((list_subtract (propertiesToCheck@(List.map snd assumedProps)) ts.TransSys.props_invalid), [], invariants, true)
                                        )
                                        
                                (*Otherwise, assert assumed properties upto k-1 and send out the valid properties*)
                                else
                                        (
                                                let (validProps, assumedProps') = 
                                                        List.partition (
                                                                fun (l, p) -> 
                                                                        bmcK' >= l
                                                        ) assumedProps 
                                                in
                                                 
                                                let assumedPropsUptok_1 = 
                                                        List.map (
                                                                fun (_, prop) ->
                                                                        (mk_terms_upto_k_1 (snd prop) k [])
                                                        ) assumedProps'
                                                in
                                                                
                                                S.assert_term solver (Term.mk_and (List.flatten assumedPropsUptok_1));  
                                                
                                                List.iter (fun (l, p) -> 
                                                        (debug ind "Property %s proved at inductive step k = %d" (fst p) l end);
                                                  Event.proved `IND (Some l) p) validProps;
                                                
                                                (propertiesToCheck, assumedProps', invariants, reset)
                                        )
                                        
                                
                                (* Add proved properties to transys props_valid*)
                        | (Event.Proved (_, _, p)) ->
                                let (name, prop) = (List.find (fun x -> fst x = p) propertiesToCheck) in                                        
                                ts.TransSys.props_valid <- (name, prop) :: ts.TransSys.props_valid;
                                S.assert_term solver (Term.mk_and (mk_terms_upto_k_1 prop k []));
                                
                                ((List.filter (fun x -> fst x <> p) propertiesToCheck), assumedProps, invariants, reset)
                                
                                (* Add disproved properties to transys props_invalid*)
                        | (Event.Disproved (_, _, p)) ->                        
                                ts.TransSys.props_invalid <- (List.find (fun x -> fst x = p) ts.TransSys.props) :: ts.TransSys.props_invalid;
                                
                                (* If there exist a disproved property in the assumed property list, *)
                                (* we add the entire assumed properties back to the properties list to check again*)
                                (* otherwise, we continue by eliminating the invalid properties*)
                                if (List.exists (
                                                fun (k, prop) -> 
                                                        fst prop = p) assumedProps) then
                                        (
                                                (list_subtract (propertiesToCheck@(List.map snd assumedProps)) ts.TransSys.props_invalid, [], invariants, true)
                                        )
                                else
                                        (list_subtract propertiesToCheck ts.TransSys.props_invalid, assumedProps, invariants, reset)
                                        
      (* Irrelevant message received. *)
      | _ ->
        (propertiesToCheck, assumedProps, invariants, reset)
                                    
  ) 
        (propertiesToCheck, assumedProps, invariants, reset)
        messages

(** Eliminate properties that are not implied by the transition system at step k*)
let filter_properties solver ts k props =
                
                (*just current k is enough*)
                let state_vars = get_state_vars_upto_k ts k [] in
                
    (* Get the model falsify the conjuction of all properties in the props *)
    let model = S.get_model solver state_vars in    
                        
                (*bump the properties to k*)    
    List.partition(     
      fun (name, prop) -> 
        Eval.bool_of_value (Eval.eval_term (TransSys.bump_state k prop) model)
    ) props

(** Induction starts*)
let rec ind solver ts preK k propertiesToCheck propertiesToCheckNextK assumedProperties invariants =
        
        Event.log `IND Event.L_info "Inductive step loop at k=%d" k;
        
        Stat.set k Stat.ind_k;
  Stat.update_time Stat.ind_total_time; 
        
        (debug ind "Inductive step at k = %d" k end);
        
        let (propertiesToCheck', assumedProperties', invariants', reset') =
                update solver ts propertiesToCheck assumedProperties invariants k false
        in
        
        (* Restart induction process if one of assumed properties is disproved*)        
        if reset' then
                (
                        restart ts k invariants
                );
                
        if List.length propertiesToCheck' <> 0 then
                (
                        (* If the induction process checks for a new k, push the transition system to the new k and assert all invariants*)
                        if preK <> k then
                                (
                  (* Assert invariants and valid properties at step k. Then push the transition function from (k-1)th step 
           to kth step T(k-1, k), then begin the check. *)
                        S.assert_term solver (TransSys.bump_state k (Term.mk_and (List.map snd (List.map snd assumedProperties'))));
                S.assert_term solver (TransSys.bump_state k (Term.mk_and invariants'));
                        S.assert_term solver (TransSys.bump_state k (Term.mk_and (List.map snd ts.TransSys.props_valid)));
                        S.assert_term solver (TransSys.constr_of_bound k ts);
                                        
                                );
                        S.push solver;          
                        (* Instantiate the properties upto step k-1 and at step k *)
      let propsUptoK_1 = 
                List.map 
                (
                        fun (name, prop) ->
                                (mk_terms_upto_k_1 prop k [])
                ) propertiesToCheck' 
                                in
                                
                        let propsAtK = 
                List.map 
                (
                        fun (name, prop) ->
                                TransSys.bump_state k prop
                ) propertiesToCheck' 
                        in
                                
        S.assert_term solver (Term.mk_and (List.concat propsUptoK_1));
        S.assert_term solver (Term.mk_not (Term.mk_and propsAtK));
                        
                        (* If the transitions system does not entail the propertiesToCheck*)
                        if (S.check_sat solver) then
                                (
                                        let (propertiesToCheck', propertiesToCheckNextK') = 
                                                filter_properties solver ts k propertiesToCheck' 
                                        in
                                        
                                        List.iter
                                        (
                                                fun (name, prop) ->
                                                        (debug ind "Property %s falsified at induction step k = %d" name k end);
                                        ) propertiesToCheckNextK';
                                        S.pop solver;
                                        ind solver ts k k propertiesToCheck' (propertiesToCheckNextK@propertiesToCheckNextK') assumedProperties' invariants'
                                )
                                
                        (* If the transitions system entails the propertiesToCheck*)
                        else
                                (
                                        (* If BMC already pass induction k*)
                                        if !bmcK >= k then
                                                (
                                                        List.iter(fun (name, prop) -> (debug ind "Property %s proved at inductive step k = %d" name k end);) (propertiesToCheck'@(List.map snd assumedProperties'));
                                                        List.iter (Event.proved `IND (Some k)) ((propertiesToCheck'@(List.map snd assumedProperties')));
                                                        if List.length propertiesToCheckNextK <> 0 then
                                                                (
                                                                        S.pop solver;
                                                                        ind solver ts k (k+1) propertiesToCheckNextK [] [] invariants'
                                                                )
                                                                
                                                )
                                        else 
                                                (
                                                        let assumedProps = List.map (fun p -> (k, p)) propertiesToCheck' in 
                                                        if List.length propertiesToCheckNextK <> 0 then
                                                                (
                                                                        S.pop solver;
                                                                        ind solver ts k (k+1) propertiesToCheckNextK [] (assumedProps@assumedProperties') invariants'
                                                                )
                                                        else
                                                                (
                                                                        (*write a reccursive function!!!!!!!!*)
                                                                        while ((!bmcK < k) || List.length assumedProperties <> 0) do
                                                                                (
                                                                                        (*minisleep 0.5 sec to wait for BMC to catch up*)
                                                                                        Lib.minisleep 0.5;
                                                                                        
                                                                                        let (propsToCheck, assumedProps, inv, reset') = 
                                                                                                update solver ts [] (assumedProps@assumedProperties') invariants' k false
                                                                                        in

                                                                                        if List.length propsToCheck <> 0 then
                                                                                                (
                                                                                                        S.pop solver;
                                                                                                        ind solver ts k k propsToCheck [] [] invariants'
                                                                                                ) 
                                                                                        
                                                                                )done;
                                                                                List.iter(fun (name, prop) -> (debug ind "Property %s holds at induction step k = %d" name k end);) (propertiesToCheck'@(List.map snd assumedProperties'));
                                                                )
                                                )
                                )
                )
        (* If there remains any properties to check*)
        else if List.length propertiesToCheckNextK <> 0 then
                (
                        ind solver ts k (k+1) propertiesToCheckNextK [] assumedProperties invariants'
                )
        else
                (
                        (debug ind
        "All good properties proved or disproved!"
        end);
                )
                
(**Restart induction process whenever an assumed property is disproved*)
and restart ts k invariants= 
  Event.log `IND Event.L_info "Restart inductive step";
  Stat.incr Stat.ind_restarts;
  (* Delete solver instance *)
  (match !ref_solver with 
    | Some s -> S.delete_solver s
    | None -> ());
                        
        let propertiesToCheck = (list_subtract (list_subtract ts.TransSys.props ts.TransSys.props_valid) ts.TransSys.props_invalid) in
        
  init ts propertiesToCheck invariants k true

(** Initilize the induction step*)
and init transSys propertiesToCheck invariants k reset =

    (* Determine logic for the SMT solver *)
    let logic = TransSys.get_logic transSys in

    (* Create solver instance *)
    let solver = 
      S.new_solver ~produce_assignments:true logic
    in
  
    (* Create a reference for the solver. Only used in on_exit. *)
    ref_solver := Some solver;
                
                if reset then
                        (
                                aux transSys k solver;
                                ind solver transSys (k-1) k propertiesToCheck [] [] invariants
                        )
                else
                        (
                                ind solver transSys 0 1 propertiesToCheck [] [] []      
                        )

(* Entry point *)
let main transSys =

  Stat.start_timer Stat.ind_total_time;

  let propertiesToCheck = transSys.TransSys.props in
        
        init transSys propertiesToCheck [] 1 false;


 
*)


(*
let main () =

  (* Parse command-line flags *)
  Flags.parse_argv ();
  
  (* At least one debug section enabled? *)
  if not (Flags.debug () = []) then
    
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

    );

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

    );

  let ts = OldParser.of_file (Flags.input_file ()) in

  (* Output the transition system *)
  (debug ind
    "%a"
    TransSys.pp_print_trans_sys
    ts
    end);
    
  let property_pairs = ts.TransSys.props in
  let premises = List.map snd property_pairs in

  kind_ind ts property_pairs premises
;;

main ()
*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
