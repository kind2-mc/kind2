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
module INDSolver = SMTSolver.Make (Config.SMTSolver)

(* High-level methods for BMC solver *)
module S = SolverMethods.Make (INDSolver)


exception Restart


(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)

(* Solver instance if created *)
let ref_solver = ref None


(* Output statistics *)
let print_stats () =

  Event.stat 
    `IND 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.ind_stats_title, Stat.ind_stats;
     Stat.smt_stats_title, Stat.smt_stats]


(* Clean up before exit *)
let on_exit () =

  (* Stop all timers *)
  Stat.ind_stop_timers ();
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
       Event.log `IND Event.L_error 
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


let main _ = ()

(*

(* Assert term for instants 0..k *)
let assert_upto_k solver k term = 
  Term.bump_and_apply_k 
    (S.assert_term solver)
    k
    term


(* Give a solver with a satisfiable context, return a pair of lists *)
let partition_props solver props k = 

  List.partition
    (fun (_, p) -> 
       
       (* Property at instant k *)
       let t_k = Term.bump_state k p in

       (* Get value of property term *)
       match S.get_values solver [t_k] with
         | [(t, v)] when v == Term.t_true && t == t_k -> true
         | [(t, v)] when v == Term.t_false && t == t_k -> false
         | _ -> assert false)

    props


let handle_events trans_sys invars bmc_k k_valid_props =

  (* Receive all queued messages 

     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = Event.recv () in
  
  List.fold_left 
    (function (invars, bmc_k, k_valid_props) -> function
       
       (* Invariant discovered by other module *)
       | Event.Invariant inv -> 
         
         (debug indStep
             "@[<hv>Received invariant@ @[<hv>%a@]@]"
             Term.pp_print_term inv 
          in
          
          (* Add invariant to the transition system *)
          TransSys.add_invariant trans_sys inv);
          
         (* Return invariant and previous k in BMC *)
         (inv :: invars, bmc_k, k_valid_props)
         
       (* BMC at k *)
       | Event.BMCState (bmc_k', k_valid_props) -> 

         (* Return new k in BMC and the not yet disproved properties *)
         (invars, bmc_k', k_valid_props)

       (* Property has been proved by other module *)
       | Event.Proved (_, _, prop_name) -> 
         
         (debug indStep
             "@[<hv>Received proved property %s@]"
             prop_name
          in

          (try 
             
             (* Get property term from name *)
             let prop_term = 
               List.assoc prop_name trans_sys.TransSys.props
             in

             (* Add invariant to the transition system *)
             TransSys.add_valid_prop trans_sys (prop_name, prop_term);
          
             (* Return property as invariant and previous k in BMC *)
             (prop_term :: invars, bmc_k, k_valid_props)

           (* Skip if property not found *)
           with Not_found -> (invars, bmc_k, k_valid_props)))
         
       (* Property has been disproved by other module *)
       | Event.Disproved (_, _, prop) -> 

         (* Restart upon disproved property *)
         raise (Disproved prop)
           
    )
    (invars, bmc_k, k_valid_props)
    messages


let rec ind_step_loop 
    solver
    trans_sys  
    (invars, bmc_k, k_valid_props)
    props_not_ind_k
    props_unknown 
    k_plus_one =

  (* Get new invariants and state of BMC *)
  let invars', bmc_k, k_valid_props = 
    handle_events trans_sys invars bmc_k k_valid_props 
  in

  if 

    (* One of the assumed properties is not k-valid *)
    List.exists
      (fun (n, _) -> not (List.mem n k_valid_props))
      (props_not_ind_k @ props_unknown)

  then 

    raise Restart;

  (* Assert invariants received for all instants 0..k+1 *)
  List.iter (assert_upto_k solver k_plus_one) invars';

  (* Conjunction of unknown properties *)
  let props_unknown_term = Term.mk_and (List.map snd props_unknown) in

  (* Assert negation of unknown properties P[x_k+1] *)
  S.assert_term
    solver
    (Term.bump_state k_plus_one props_unknown_term);

  (* Are the unknown properties entailed? *)
  if (S.check_sat solver) then

    (

      (* TODO: Check for compressible path here

         Pop context before asserting compression formula, then push
         again and recurse to ind_step_loop *)

      (* Properties still unknown and properties not k-inductive *)
      let props_unknown', props_not_ind_k' =
        partition_props solver props_unknown k_plus_one
      in

      (* No more potentially k-inductive properties *)
      if props_unknown' = [] then 

        (

          (* Pop assertions from entailment checks *)
          S.pop solver;

          (* Assert invariants on popped scope for all instants
             0..k+1 *)
          List.iter (assert_upto_k solver k_plus_one) (invars @ invars');

          (* No properties k-inductive *)
          ([], props_not_ind_k @ props_not_ind_k')

        )

      else

        (debug indStep
            "Properties %a not %a-inductive"
            (pp_print_list 
               (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
               ",@ ")
            props_unknown'
            Numeral.pp_print_numeral (Numeral.pred k_plus_one)
         in
         
         (* Recurse to test unknown proeprties for k-inductiveness *)
         ind_step_loop 
           solver
           trans_sys
           (invars @ invars', bmc_k, k_valid_props)
           (props_not_ind_k @ props_not_ind_k')
           props_unknown' 
           k_plus_one )
           
    )

  else

    (
      
      (* Pop assertions from entailment checks *)
      S.pop solver;

      (* Assert invariants on popped scope for all instants 0..k+1 *)
      List.iter (assert_upto_k solver k_plus_one) (invars @ invars');

      (* Found some properties k-inductive *)
      (props_unknown, props_not_ind_k)

    )

(* Inductive step for given [k]

   Assume: Solver context contains 
   - transition relation T[x_0,x_1] ... T[x_k-1,x_k], 
   - Invariants C[x_0] ... C[x_k]
   - properties in [props_unknown] P[x_0] ... P[x_k]

   Extend this solver context to k+1, and check which properties in
   [props_unknown] are k-inductive. 

   Return a pair of lists, where the first list contains properties
   that are k-inductive, and the second list properties that are not
   k-inductive. *)
let ind_step 
    solver
    trans_sys
    props_unknown 
    k =

  (* Increment k *)
  let k_plus_one = Numeral.succ k in

  (* Conjunction of unknown properties *)
  let props_unknown_term = Term.mk_and (List.map snd props_unknown) in

  (* Assert transition system T[x_k,x_k+1] *)
  S.assert_term
    solver
    (TransSys.trans_of_bound k_plus_one trans_sys);

  (* Assert invariants C[x_k+1] *)
  S.assert_term
    solver
    (TransSys.invars_of_bound k_plus_one trans_sys);

  (* Assert valid properties P_v[x_k+1] *)
  S.assert_term
    solver
    (TransSys.props_valid_of_bound k_plus_one trans_sys);

  (* Assert unknown properties P[x_k] *)
  S.assert_term
    solver
    (Term.bump_state k props_unknown_term);

  (* Push context before entailment checks *)
  S.push solver;

  ind_step_loop 
    solver
    0
    trans_sys
    []
    []
    props_unknown 
    k_plus_one 



let rec induction solver trans_sys props props_unknown k =

  try 

    (* Find properties that are k-inductive *)
    let bmc_k, props_valid, props_unknown' =
      ind_step 
        solver 
        trans_sys
        props_unknown
        k
    in
    
    (* TODO: Check if there is no counterexample of length <= k to a
       property proved k-inductive *)

    (* *)
    induction 
      solver
      trans_sys
      props_unknown' 
      (Numeral.succ k)
    

  with Disproved prop -> 

    S.pop solver;
    S.pop solver;

    let _, prop_term = 
      List.find 
        
        trans_sys.TransSys.props 
    in        

    let props' = 
      List.filter
        (fun (n, _) -> n = prop)
        props
    in

    induction 
      solver
      trans_sys
      props_unknown 
      (Numeral.succ k)


(* Entry point *)
let main trans_sys =

  Stat.start_timer Stat.ind_total_time;

  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic trans_sys in

  (* Create solver instance *)
  let solver = 
    S.new_solver ~produce_assignments:true logic
  in

  (* Create a reference for the solver to clean up on exit *)
  ref_solver := Some solver;

  (* Declare uninterpreted function symbols *)
  TransSys.iter_state_var_declarations
    trans_sys
    (S.declare_fun solver);

  (* Define functions *)
  TransSys.iter_uf_definitions
    trans_sys
    (S.define_fun solver);

  induction
    solver
    trans_sys
    trans_sys.TransSys.props
    Numeral.zero
*)

  
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
