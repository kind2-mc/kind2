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
let print_stats () = 

  Event.stat 
    `BMC 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.bmc_stats_title, Stat.bmc_stats;
     Stat.smt_stats_title, Stat.smt_stats]


(* Clean up before exit *)
let on_exit () =

  (* Stop all timers *)
  Stat.bmc_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats ();

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

    if Numeral.(k >= i) then    

      (
        
        Format.fprintf 
          ppf 
          "%a    " 
          Term.pp_print_term 
          (List.assoc 
             (Var.mk_state_var_instance abstract_var i) 
             counter_example);
        
        pp_print_trace ppf (abstract_var, k, (Numeral.succ i), counter_example)
      
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
    pp_print_trace ppf (abstract_var, k, Numeral.zero, counter_example);
    pp_print_counter_example ppf (tl, k, counter_example)
                
    
                
(* Make a list of invariant upto k-1*)         
let rec mk_invariants_upto_k_1 inv k acc =
  
  if Numeral.(k = zero) then

    acc

  else
      
    mk_invariants_upto_k_1 
      inv
      Numeral.(k - one)
      ((Term.bump_state Numeral.(k - one) inv) :: acc)
                

(* Eliminate properties that are not implied by the transition system
   at step k *)
let rec filter_invalid_properties solver ts k props =

  let uf_defs = ts.TransSys.uf_defs in

  let state_vars = TransSys.vars_of_bounds ts Numeral.zero k in
                
  (* Get the model falsify the conjuction of all properties in the props *)
  let model = S.get_model solver state_vars in    
  
  (* bump the properties to k *)

  (* props' are the properties still hold, disprovedProps are the
     properties that have been falsified by the model *)
  let (props', disprovedProps) = 
    List.partition
      (fun (name, prop) -> 
         Eval.bool_of_value
           (Eval.eval_term uf_defs model (Term.bump_state k prop))) 
      props 
  in
  
  (* Print out the counter example *)             
  debug bmc
      "@[<v>%a@]"
      (pp_print_list 
         (fun ppf x -> Format.fprintf ppf "disproved property: %s" (fst x))
         "@,")
      disprovedProps
  in

  debug bmc
      "@[<hv>The counter_example is:\n@[<hv>%a@]@]@."
      pp_print_counter_example
      ((TransSys.state_vars ts), k, model)
  in
  
  List.iter 
    (Event.prop_status `BMC (PropKFalse (Numeral.to_int k)))
    (List.map fst disprovedProps);
(*
  Event.bmcstate (Numeral.to_int k) (List.map fst disprovedProps);
*)   
  (* return the properties might hold at step k and continue to check
        for step k *)
  props'


(** Bounded model checking *)
let rec bmc solver ts k properties invariants =

  Event.log `BMC Event.L_info "BMC loop at k=%d" (Numeral.to_int k);

  Event.progress `BMC (Numeral.to_int k);

  Stat.set (Numeral.to_int k) Stat.bmc_k;

  Stat.update_time Stat.bmc_total_time;

        
  (* Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = Event.recv () in

  let (properties',invariants') =
    
    List.fold_left
      (fun (properties, invariants) message ->
         match message with

           (* Add invariant to a temparary list when it's received. *)
           | Event.Invariant inv ->

             S.assert_term 
               solver 
               (Term.mk_and (mk_invariants_upto_k_1 inv k []));

             (properties, inv::invariants)

           (* Add proved properties to transys props_valid *)
           | Event.PropStatus (p, PropInvariant) ->
             (debug bmc
                 "Proved property: %s" p
              in
              
              let (name, prop) =
                try List.find (fun x -> fst x = p) ts.TransSys.props with
                | Not_found -> debug bmc "bmc Not found exception in line 238" in
                raise Not_found
              in                                       

              TransSys.add_valid_prop ts (name, prop);

              S.assert_term
                solver
                (Term.mk_and (mk_invariants_upto_k_1 prop k [])));

             ((List.filter (fun x -> fst x <> p) properties), invariants)
             
           (* Add disproved properties to transys props_invalid *)
           | Event.PropStatus (p, PropFalse)
           | Event.PropStatus (p, PropKFalse _) ->

             (debug bmc
                 "Disproved: property: %s" p
              in

              TransSys.add_invalid_prop 
                ts
                (try List.find (fun x -> fst x = p) ts.TransSys.props with
                | Not_found -> debug bmc "Not found exception in line 258 bmc." in
                raise Not_found);

              ((List.filter (fun x -> fst x <> p) properties), invariants))
             
           (* Irrelevant message received. *)
           | _ -> (properties, invariants)) 

      (properties, invariants) 
      messages
  in

  let validProps = List.map snd ts.TransSys.props_valid in
        
  S.assert_term solver (Term.bump_state k (Term.mk_and invariants'));

  S.assert_term solver (Term.bump_state k (Term.mk_and validProps));
  
  S.push solver;

  (* Instantiate the properties at step k *)
  let propsAtK = 
    List.map 
      (fun (prop_name, prop) -> Term.bump_state k prop)
      properties' 
  in 

  S.assert_term solver (Term.mk_not (Term.mk_and propsAtK));
  
  if (S.check_sat solver) then

    (

      (* Filter out the properties which doesn't hold at the kth step. *)
      (* And continue to check the rest of properties for current k*)
      match filter_invalid_properties solver ts k properties with 
      
        | [] -> 
          (debug bmc
              "No more properties need to check!"
           in
           
           ())
          
        | properties'' ->
          (S.pop solver;
           
           bmc solver ts k properties'' invariants')

    )
      
  (* If the conjuncted property holds, push the transition function
     T(k, k + 1) then continue to check for (k + 1) step *)
  else 

    (
(*
      Event.bmcstate (Numeral.to_int k) [];
*)

     S.pop solver;

     S.assert_term solver (TransSys.trans_of_bound (Numeral.succ k) ts);

     bmc solver ts (Numeral.succ k) properties' invariants')
    

(* Entry point *)
let main trans_sys =

  Stat.start_timer Stat.bmc_total_time;
  
  match trans_sys.TransSys.props with
    
    (* Terminate when there is nothing to check *)
    | [] -> Event.log `BMC Event.L_error "No property to check"
              
    | properties ->
      
      (* Determine logic for the SMT solver *)
      let logic = TransSys.get_logic trans_sys in
      
      (* Create solver instance *)
      let solver = 
        S.new_solver ~produce_assignments:true logic
      in

      (* Create a reference for the solver. Only used in on_exit. *)
      ref_solver := Some solver;
      
      (* Declare uninterpreted function symbols *)
      TransSys.iter_state_var_declarations
        trans_sys
        (S.declare_fun solver);
      
      (* Define functions *)
      TransSys.iter_uf_definitions
        trans_sys
        (S.define_fun solver);

      (* Provide the initial case *)
      S.assert_term solver (TransSys.init_of_bound Numeral.zero trans_sys);
      
      (* Enter the bounded model checking loop begin with the initial state. *)
      bmc solver trans_sys Numeral.zero properties []

  
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
