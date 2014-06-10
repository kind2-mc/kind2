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
let on_exit _ =

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


(* Assert term for instants 0..k *)
let assert_upto_k solver k term = 
  Term.bump_and_apply_k 
    (S.assert_term solver)
    k
    term


(* Add falsified properties to props_kfalse until the remaining
   properties are true, or there are no more properties left. 

   Assuptions: 
   - The path constraint, and the invariants have been asserted.
   - There is a fresh scope level on the context

   Assert negated conjunction of the properties on the current scope
   level. It is not necessary to remove the conjunction from previous
   queries, since it will be subsumed by the current query.
*)
let rec bmc_step_loop solver trans_sys k props_kfalse properties = 

  (* Assert negated properties ~(P_1[x_k] & ... & P_n[x_k]) *)
  S.assert_term solver
    (Term.bump_state k (Term.negate (Term.mk_and (List.map snd properties))));

  (* Are all properties entailed? *)
  if 

    (debug bmc
        "@[<v>Current context@,@[<hv>%a@]@]"
        HStringSExpr.pp_print_sexpr_list
        (let r, a = 
          S.T.execute_custom_command solver "get-assertions" [] 1 
         in
         S.fail_on_smt_error r;
         a)
     in
     
     S.check_sat solver)

  then 

    (

      (* Definitions of predicates *)
      let uf_defs = TransSys.uf_defs trans_sys in

      (* Which properties are false in k steps? *)
      let props_unknown, props_kfalse' = 

        List.partition

          (fun (_, p) -> 

             (* Property at step k *)
             let p_k = Term.bump_state k p in

             (* Variables in property at step k *)
             let p_k_vars = Var.VarSet.elements (Term.vars_of_term p_k) in

             (* Model for variables of property at step k *)
             let p_k_model = S.get_model solver p_k_vars in
             
             (* Distinguish properties by truth value at step k *)
             Eval.bool_of_value (Eval.eval_term uf_defs p_k_model p_k))

          properties

      in
      
      (* Get counterexample from model *)
      let cex = TransSys.path_from_model trans_sys (S.get_model solver) k in

      (* Properties falsified with counterexample *)
      let props_kfalse'' = (cex, props_kfalse') :: props_kfalse in

      (* All properties falsified? *)
      if props_unknown = [] then 

        (

          (* Remove negated properties after check *)
          S.pop solver;

          (* All remaining properties are false in k steps *)
          (props_unknown, props_kfalse'')

        )

      else
        
        (* Continue with properties that may be true *)
        bmc_step_loop 
          solver
          trans_sys
          k
          props_kfalse''
          props_unknown

    )

  else

    (

      (* Remove negated properties after check *)
      S.pop solver;

      (* Assert k-true properties as invariants *)
      List.iter 
        (fun (_, t) -> 
           S.assert_term solver (Term.bump_state k t))
        properties;

      (* All remaining properties are true in k steps *)
      (properties, props_kfalse))
    

(* Check which properties are true in k steps 

   If [check_ts_props] is true, check in received messages whether
   another process has proved or disproved a named property, and remove
   it. Otherwise, discard messages from other processes about
   properties.

   This function does not have side effects such as sending messages,
   thus can safely be called to check properties not in the transition
   system. *)
let bmc_step check_ts_props solver trans_sys k properties = 

  let k_minus_one = Numeral.pred k in

  (* Receive queued messages 

     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = Event.recv () in

  (* Update transition system from messages *)
  let invariants_recvd, prop_status, _ = 
    TransSys.update_from_events trans_sys messages 
  in

  (* Assert received invariants up to k-1 *)
  List.iter 
    (fun (_, t) -> assert_upto_k solver k_minus_one t) 
    invariants_recvd;

  (* Checking properties of the transition system? *)
  let properties' = if check_ts_props then

      (* Filter out proved or disproved properties by other modules *)
      List.filter
        (fun (p, _) -> 
           if 
             (List.exists 
                (fun (_, (q, s)) -> q = p && prop_status_known s)
                prop_status)
           then
             (debug bmc 
                 "Property %s proved or disproved by other module"
                 p
              in
              false)
           else
             true)
        properties

    else

      (* Do not remove properties *)
      properties

  in

  (* Do not assert T[-1,0] *)
  if Numeral.(k > zero) then

      (* Assert transition system T[x_k-1,x_k] *)
      S.assert_term
        solver
        (TransSys.trans_of_bound trans_sys k);

  (* Assert invariants C[x_k] *)
  S.assert_term
    solver
    (TransSys.invars_of_bound trans_sys k);

  (* Push context before check *)
  S.push solver;

  (* Check which properties are true in step k *)
  bmc_step_loop solver trans_sys k [] properties'


(* Bounded model checking on the properties of the transition
   system 

   Check which properties are falsified at bound k, send messages
   about disproved properties and k-valid properties. Then continue
   for bound k+1 until all properties have been proved (per messages
   from other processes) or disproved (per messages from other
   processes or BMC)), or until a maximum bound has been reached. *)
let rec bmc solver trans_sys k = function 

  (* Exit when maximal number of iterations reached *) 
  | _ when (Numeral.to_int k) > Flags.bmc_max () && Flags.bmc_max () > 0 -> 

    Event.log
      `BMC
      Event.L_info
      "BMC reached maximal number of iterations"

  (* Exit when all properties proved or disproved *) 
  | [] -> ()

  | properties -> 

    (* Output current step *)
    Event.log `BMC Event.L_info "BMC loop at k=%d" (Numeral.to_int k);

    Event.progress `BMC (Numeral.to_int k);

    Stat.set (Numeral.to_int k) Stat.bmc_k;
    
    Stat.update_time Stat.bmc_total_time;

    (* Check which properties are true after k steps *)
    let props_ktrue, props_kfalse = 
      bmc_step true solver trans_sys k properties
    in
    
    (* Broadcast status of properties true in k steps *)
    List.iter
      (fun (n, _) -> 
         TransSys.prop_ktrue trans_sys (Numeral.to_int k) n;
         Event.prop_status `BMC (PropKTrue (Numeral.to_int k)) n)
      props_ktrue;

    (* Broadcast status of properties falsified in k steps *)
    List.iter

      (fun (c, p) -> 

         (* Each property is false by itself *)
         List.iter 
           (fun (n, _) -> 
              TransSys.prop_kfalse trans_sys (Numeral.to_int k) n;
              Event.prop_status `BMC (PropKFalse (Numeral.to_int k)) n)
           p;

         (* Properties are falsified with the same counterexample *)
         Event.counterexample `BMC (List.map fst p) c)

      props_kfalse;
    
    (* Output statistics *)
    if Event.output_on_level Event.L_info then print_stats ();

    (* Continue with properties not falsified in k steps *)
    bmc solver trans_sys (Numeral.succ k) props_ktrue


(* Entry point *)
let main trans_sys =

  Stat.start_timer Stat.bmc_total_time;
  
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

  (* Assert initial state constraint *)
  S.assert_term solver (TransSys.init_of_bound trans_sys Numeral.zero);
  
  (* Enter the bounded model checking loop *)
  bmc 
    solver
    trans_sys
    Numeral.zero
    (TransSys.props_list_of_bound trans_sys Numeral.zero)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
