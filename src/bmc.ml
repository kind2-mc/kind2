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

(** The bounded model checking

    @author Paul Meng
*)

open Lib


(* Use configured SMT solver *)
module BMCSolver = SMTSolver.Make (Config.SMTSolver)


(* High-level methods for BMC solver *)
module S = SolverMethods.Make (BMCSolver)


(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)


(* Solver instance if created *)
let ref_solver = ref None


(* Output statistics *)
let pp_print_stat ppf = 

  Format.fprintf
    ppf
    "Statistics of %a module:@.@.%t@.%t@.%t"
    pp_print_kind_module `BMC
    Stat.pp_print_misc_stats
    Stat.pp_print_bmc_stats
    Stat.pp_print_smt_stats


(* Clean up before exit *)
let on_exit () =
    
  (* Stop all timers *)
  Stat.bmc_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  Event.stat 
    `BMC 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.bmc_stats_title, Stat.bmc_stats;
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
       Event.log `BMC Event.L_error
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


(* ********************************************************************** *)
(* Counterexample traces                                                  *)
(* ********************************************************************** *)


(* Print out the trace of one variable from the counter example *)
let rec pp_print_trace ppf = function

  | (abstract_var, k, i, counter_example) ->

    if (k >= i) then    

      (
        
        Format.fprintf 
          ppf 
          "%a    " 
          Term.pp_print_term 
          (List.assoc 
             (Var.mk_state_var_instance abstract_var (Numeral.of_int i)) 
             counter_example);
        
        pp_print_trace ppf (abstract_var, k, i + 1, counter_example)
      
      )
      
    else 
      
      (
        
        (* End the line when finished *)
        Format.fprintf ppf "\n@." 
          
      )
      

(* Print out the counter example *)
let rec pp_print_counter_example ppf = function 
  
  | ([], k, counter_example) -> ()
    
  | (abstract_var :: tl, k, counter_example) ->
    
    Format.fprintf ppf "%a    " StateVar.pp_print_state_var abstract_var;
    pp_print_trace ppf (abstract_var, k, 0, counter_example);
    pp_print_counter_example ppf (tl, k, counter_example)
                
                

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
                
                
(** Make a list of invariant upto k-1*)         
let rec mk_invariants_upto_k_1 inv k acc =
        if k = 0 then
                acc
        else
                (
                  mk_invariants_upto_k_1 inv (k-1) ((Term.bump_state (k-1) inv)::acc)
                )
                
(** Eliminate properties that are not implied by the transition system at step k*)
let rec filter_invalid_properties solver ts k props =

                let state_vars = get_state_vars_upto_k ts k [] in
                
    (* Get the model falsify the conjuction of all properties in the props *)
    let model = S.get_model solver state_vars in    
                        
                (*bump the properties to k*)
    (* props' are the properties still hold, disprovedProps are 
       the properties that have been falsified by the model *)
    let (props', disprovedProps) = 
      List.partition(     
        fun (name, prop) -> 
          Eval.bool_of_value (Eval.eval_term (TransSys.bump_state k prop) model)
      ) props 
    in

                (* Print out the counter example *)             
                List.iter (fun x -> debug bmc "disproved property: %s" (fst x) end;) disprovedProps;
    (debug bmc
      "@[<hv>The counter_example is:\n@[<hv>%a@]@]@."
      pp_print_counter_example
      ((TransSys.state_vars ts), k, model) end);        
                                
    List.iter (Event.disproved `BMC (Some k)) (List.map fst disprovedProps);
                Event.bmcstate k (List.map fst disprovedProps);
       
    (* return the properties might hold at step k and continue to check for step k*)
    props'


(** Bounded model checking *)
let rec bmc solver ts k properties invariants =

  Event.log `BMC Event.L_info "BMC loop at k=%d" k;

  Event.progress `BMC k;

  Stat.set k Stat.bmc_k;

  Stat.update_time Stat.bmc_total_time;
        
        (* Side effect: Terminate when ControlMessage TERM is received.*)
        let messages = Event.recv () in
  
  let (properties',invariants') =
                List.fold_left (
    fun (properties, invariants) message ->
      match message with
        (* Add invariant to a temparary list when it's received. *)
      | (Event.Invariant (_, inv)) ->
                                S.assert_term solver (Term.mk_and (mk_invariants_upto_k_1 inv k []));
        (properties, inv::invariants);

                                (* Add proved properties to transys props_valid*)
                        | (Event.Proved (_, _, p)) ->
                                
                                (debug bmc
          "Proved property: %s" p
          end); 
                                        
                                let (name, prop) = (List.find (fun x -> fst x = p) properties) in                                       
                                ts.TransSys.props_valid <- (name, prop) :: ts.TransSys.props_valid;
                                S.assert_term solver (Term.mk_and (mk_invariants_upto_k_1 prop k []));
                                ((List.filter (fun x -> fst x <> p) properties), invariants);
                                
                                (* Add disproved properties to transys props_invalid*)
                        | (Event.Disproved (_, _, p)) ->                
                                
                                (debug bmc
          "Disproved: property: %s" p
          end); 
                                                        
                                ts.TransSys.props_invalid <- (List.find (fun x -> fst x = p) properties) :: ts.TransSys.props_invalid;
                                ((List.filter (fun x -> fst x <> p) properties), invariants);
      (* Irrelevant message received. *)
      | _ ->
        (properties, invariants);      
  ) (properties, invariants) messages;
        in
        

        let validProps = List.map snd ts.TransSys.props_valid in
        
  S.assert_term solver (TransSys.bump_state k (Term.mk_and invariants'));
        S.assert_term solver (TransSys.bump_state k (Term.mk_and validProps));
  S.push solver;
        (* Instantiate the properties at step k *)
  let propsAtK = 
                List.map 
                (
                        fun (prop_name, prop) -> 
                                TransSys.bump_state k prop
                ) properties' 
                        
        in 

  S.assert_term solver (Term.mk_not (Term.mk_and propsAtK));
        
  if (S.check_sat solver) then
  (
    (* Filter out the properties which doesn't hold for the kth step. *)
                (* And continue to check the rest of properties for current k*)
    let properties'' = filter_invalid_properties solver ts k properties in
                if List.length properties'' <> 0 then
                        (
                                S.pop solver;
                bmc solver ts k properties'' invariants'
                        )
                else
                        (
                                (debug bmc
          "No more properties need to check!"
          end);
                        )
                               
  )
      
  (* If the conjuncted property holds, push the transition function T(k, k + 1) 
     then continue to check for (k + 1) step *)
  else 
  (
                Event.bmcstate k [];
    S.pop solver;
          S.assert_term solver (TransSys.constr_of_bound (k+1) ts);
    bmc solver ts (k + 1) properties' invariants'
  )
  

(* Entry point *)
let main transSys =

  Stat.start_timer Stat.bmc_total_time;

  match transSys.TransSys.props with
    
    (* Terminate when there is nothing to check *)
    | [] -> Event.log `BMC Event.L_error "No property to check"

    | properties ->
    
      (* Determine logic for the SMT solver *)
      let logic = TransSys.get_logic transSys in

      (* Create solver instance *)
      let solver = 
        S.new_solver ~produce_assignments:true logic
      in
      
      (* Create a reference for the solver. Only used in on_exit. *)
      ref_solver := Some solver;
      
      (* Provide the initial case *)
      S.assert_term solver (TransSys.init_of_bound 0 transSys);

      (* Enter the bounded model checking loop begin with the initial state. *)
      bmc solver transSys 0 properties []
  
(*
(* Test function *)
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

(*
  let i = Term.mk_sym "__i" Type.Int in

  let v1 = UfSymbol.mk_uf_symbol "v1" [Type.Int] Type.Int true in
  (* 
  let v2 = UfSymbol.mk_uf_symbol "v2" [Type.Int] Type.Int true in
  let v3 = UfSymbol.mk_uf_symbol "v3" [Type.Int] Type.Int true in
  *)

  let v1_0 = Term.mk_uf v1 [Term.mk_pred i] in
  let v1_1 = Term.mk_uf v1 [i] in

  
  let z =
  { 
    TransSys.state_index = i;

    TransSys.vars = [];

    TransSys.init = 
      [Term.mk_eq [v1_1; Term.mk_num_of_int 0]];

    TransSys.constr =
      [Term.mk_eq [v1_1; Term.mk_plus [v1_0; Term.mk_num_of_int 1]]];

    TransSys.trans =
      [];

    TransSys.props =
      [
        ("p1", Term.mk_lt [v1_1; (Term.mk_num_of_int (10))])
        ; ("p2", Term.mk_lt [v1_1; (Term.mk_num_of_int (15))])
      ];
  } in
*)

  
  let z = OldParser.of_file (Flags.input_file ()) in
  

  (* Output the transition system *)
  (debug bmc
    "%a"
    TransSys.pp_print_trans_sys
    z
   end);

  kind_bmc z z.TransSys.props
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
