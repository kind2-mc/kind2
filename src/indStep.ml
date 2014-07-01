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
module INDSolver = SMTSolver.Make (SMTLIBSolver)

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
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.ind_stats_title, Stat.ind_stats;
     Stat.smt_stats_title, Stat.smt_stats]


(* Clean up before exit *)
let on_exit _ =

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
       Event.log Event.L_error 
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


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


let rec ind_step_loop 
    solver
    trans_sys  
    props_k_ind
    props_not_k_ind
    props_unknown 
    k_plus_one =

  (* Receive queued messages 

     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = Event.recv () in

  (* Update transition system from messages *)
  let invariants_recvd, _, _ = 
    TransSys.update_from_events trans_sys messages 
  in

  (* Assert invariants received for all instants 0..k+1 *)
  List.iter
    (fun (_, t) -> assert_upto_k solver k_plus_one t) 
    invariants_recvd;

  (* Conjunction of unknown properties *)
  let props_unknown_term = Term.mk_and (List.map snd props_unknown) in

  (* Assert negation of unknown properties P[x_k+1] *)
  S.assert_term
    solver
    (Term.negate 
       (Term.bump_state k_plus_one props_unknown_term));

  (* Are the unknown properties entailed? *)
  if 

    (debug indStep
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

      (* Get inductive counterexample from model *)
      let cex = 
        TransSys.path_from_model 
          trans_sys 
          (S.get_model solver) 
          k_plus_one 
      in

      (* Is inductive counterexample compressible? *)
      match 

        if not (Flags.ind_compress ()) then [] else 
          Compress.check_and_block cex 

      with
        
        | [] -> 

          (

            (* Properties still unknown and properties not k-inductive *)
            let props_unknown', props_not_k_ind' =
              partition_props solver props_unknown k_plus_one
            in

            (* No more potentially k-inductive properties *)
            if props_unknown' = [] then 

              (

                (* Pop assertions from entailment checks *)
                S.pop solver;

                (* Assert received invariants on previous scope for
                   all instants 0..k+1 *)
                List.iter
                  (fun (_, t) -> assert_upto_k solver k_plus_one t) 
                  invariants_recvd;

                (* No properties k-inductive *)
                (props_k_ind, props_not_k_ind @ props_not_k_ind')

              )

            else

              (debug indStep
                  "Properties %a not %a-inductive"
                  (pp_print_list 
                     (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
                     ",@ ")
                  props_not_k_ind'
                  Numeral.pp_print_numeral (Numeral.pred k_plus_one)
               in

               (* Recurse to test unknown properties for k-inductiveness *)
               ind_step_loop 
                 solver
                 trans_sys
                 props_k_ind
                 (props_not_k_ind @ props_not_k_ind')
                 props_unknown' 
                 k_plus_one)

          )


        | block_terms -> 

          (

            (* Block compressible path *)
            List.iter 
              (S.assert_term solver)
              block_terms;

            (* Check again *)
            ind_step_loop 
              solver
              trans_sys
              props_k_ind
              props_not_k_ind
              props_unknown
              k_plus_one

          )

    )

  else

    (

      (debug indStep
          "Properties %a maybe %a-inductive"
          (pp_print_list 
             (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
             ",@ ")
          props_unknown
          Numeral.pp_print_numeral (Numeral.pred k_plus_one)
       in

       Event.log
         Event.L_info
         "Properties %a maybe %a-inductive"
         (pp_print_list 
            (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
            ",@ ")
         props_unknown
         Numeral.pp_print_numeral (Numeral.pred k_plus_one);

       (* Pop assertions from entailment checks *)
       S.pop solver);

      (* Assert invariants on popped scope for all instants 0..k+1 *)
      List.iter
        (fun (_, t) -> assert_upto_k solver k_plus_one t) 
        invariants_recvd;

      (* Assert tentatively k-inductive properties P[x_k+1] *)
      S.assert_term
        solver
        (Term.bump_state
           k_plus_one
           (Term.mk_and (List.map snd props_unknown)));

      (* Found some properties k-inductive *)
      (props_k_ind @ props_unknown, props_not_k_ind)

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
    props_k_ind
    props_unknown 
    k =

  (* Increment k *)
  let k_plus_one = Numeral.succ k in

  (* Conjunction of unknown properties *)
  let props_term = 
    Term.mk_and
      (List.map snd props_unknown)
  in

  (* Assert transition system T[x_k,x_k+1] *)
  S.assert_term
    solver
    (TransSys.trans_of_bound trans_sys k_plus_one);

  (* Assert invariants C[x_k+1] *)
  S.assert_term
    solver
    (TransSys.invars_of_bound trans_sys k_plus_one);

  (* Assert tentatively k-inductive properties P[x_k+1] *)
  S.assert_term
    solver
    (Term.bump_state
       k_plus_one
       (Term.mk_and (List.map snd props_k_ind)));

  (* Assert unknown and tentatively inductive properties P[x_k] *)
  S.assert_term
    solver
    (Term.bump_state k props_term);

  (* Push context before entailment checks *)
  S.push solver;

  ind_step_loop 
    solver
    trans_sys
    props_k_ind
    []
    props_unknown 
    k_plus_one 



let rec induction solver trans_sys props_k_ind props_unknown k =

  if 

    (* Maximal number of iterations reached? *) 
    (Numeral.to_int k) > Flags.bmc_max () && Flags.bmc_max () > 0 

  then

    (

      (* Exit *)
      Event.log
        Event.L_info
        "Inductive step procedure reached maximal number of iterations"

    ) 

  else

    (

      (* Output current step *)
      Event.log
        Event.L_info
        "Inductive step loop at k=%d"
        (Numeral.to_int k);

      Event.progress (Numeral.to_int k);

      Stat.set (Numeral.to_int k) Stat.ind_k;

      Stat.update_time Stat.ind_total_time;

      (* Find properties that are k-inductive *)
      let props_k_ind', props_unknown' =
        ind_step 
          solver 
          trans_sys
          props_k_ind
          props_unknown
          k
      in

      (* Properties as premises that are disproved *)
      let props_disproved, props' = 
        List.partition
          (fun (n, _) -> TransSys.is_disproved trans_sys n)
          (props_k_ind' @ props_unknown')
      in

      try 

        (* No property must be disproved *) 
        if not (props_disproved = []) then raise Restart else 
          Event.log
            Event.L_info
            "No premises false in Inductive step";

        if 

          (* All properties proved? *)
          props_unknown' = []

        then

          (

            (* Loop to wait for all properties to be proved k-valid *)
            let rec aux () =

              if 

                (* All premises must be invariant or k-valid *)
                List.for_all
                  (fun (n, _) -> 
                     match TransSys.prop_status trans_sys n with
                       | PropInvariant -> true
                       | PropKTrue l when l >= (Numeral.to_int k) -> true
                       | PropFalse
                       | PropKFalse _ -> raise Restart
                       | _ -> false)
                  (props_k_ind @ props_k_ind')

              then

                (* Send proved properties and terminate *)
                List.iter
                  (fun (n, _) -> Event.prop_status PropInvariant n)
                  props_k_ind'

              else

                (

                  Event.log 
                    Event.L_info
                    "All properties k-invariant, waiting for premises \
                     to be proved k-valid";

                  (* Delay *)
                  minisleep 0.01;

                  (* Update transition system from messages *)
                  let _ = 
                    TransSys.update_from_events
                      trans_sys 
                      (Event.recv ())
                  in 

                  (* Check again *)
                  aux ()

                )

            in

            (* Check if all properties are k-valid and wait if not *)
            aux ()

          )

        else

          (

            (* Output statistics *)
            if Event.output_on_level Event.L_info then print_stats ();

            (* Continue to prove remaining properties k+1-inductive *)
            induction 
              solver
              trans_sys
              props_k_ind'
              props_unknown' 
              (Numeral.succ k))

      with Restart -> 

        (

          (* Exit *)
          Event.log
            Event.L_info
            "Premise of inductive step procedure is false. Restarting.";

          Stat.incr Stat.ind_restarts;

          (* Remove all assertions *)
          S.pop solver;

          (* New context for assertions to be removed on restart *)
          S.push solver;

          (* Restart with not disproved properties *)
          induction 
            solver
            trans_sys
            []
            props'
            Numeral.zero

        )

    )

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

  Compress.init (S.declare_fun solver) trans_sys;

  (* Assert invariants C[x_0] 

     Asserted before push, will be preserved after restart *)
  S.assert_term
    solver
    (TransSys.invars_of_bound trans_sys Numeral.zero);

  (* New context for assertions to be removed on restart *)
  S.push solver;
  
  induction
    solver
    trans_sys
    []
    (TransSys.props_list_of_bound trans_sys Numeral.zero)
    Numeral.zero

  
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
