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
open TermLib
open Actlit

let solver_ref = ref None

(* Output statistics *)
let print_stats () =

  Event.stat 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.ind_stats_title, Stat.ind_stats;
     Stat.smt_stats_title, Stat.smt_stats]

(* Clean up before exit *)
let on_exit _ =

  (* Stopping all timers. *)
  Stat.ind_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats () ;

  (* Deleting solver instance if created. *)
  (try
      match !solver_ref with
      | None -> ()
      | Some solver ->
         SMTSolver.delete_instance solver |> ignore ;
         solver_ref := None
    with
    | e -> 
       Event.log L_error
                 "IND @[<v>Error deleting solver_init:@ %s@]"
                 (Printexc.to_string e))

let stop () = ()

(* Returns true if the input property is not an invariant and has not
   been disproved. *)
let is_unknown trans (s,_) =
  match TransSys.get_prop_status trans s with
  | Property.PropInvariant
  | Property.PropFalse _ -> false
  | _ -> true

(* Removes proved and disproved properties from a list of
   properties. *)
let clean_unknowns trans = List.filter (is_unknown trans)

(* Splits the input list of properties in three lists: disproved, true
   up to k, and others. ALSO, REMOVES PROVED PROPERTIES. *)
let split_unfalsifiable_rm_proved trans k =
  List.fold_left
    ( fun (dis,true_k,others) ((s,_) as p) ->
      match TransSys.get_prop_status trans s with
      | Property.PropInvariant ->
         (dis, true_k, others)
      | Property.PropFalse _ ->
         (p :: dis, true_k, others)
      | Property.PropKTrue n when n >= k ->
         (dis, p :: true_k, others)
      | _ ->
         (dis, true_k, p :: others) )
    ([], [], [])

(* Cleans unknown properties and the unfalsifiable properties found by
   step. The input list is of type (Numeral.t * properties) list, REV
   SORTED ON NUMERAL.  Returns the properties confirmed by base, the
   new unknown properties, and the new unfalsifiable ones. *)
let clean_properties trans unknowns unfalsifiables =
  let unknowns' = clean_unknowns trans unknowns in

  let rec loop confirmed = function
    | (k, unfls_k) :: tail as list ->

       (* Handling unfalsifiable properties at k. *)
       ( match split_unfalsifiable_rm_proved trans k unfls_k with

         | ([], confirmed', []) ->
            (* Only confirmed properties, base is above k so we loop. *)
            loop (List.rev_append confirmed' confirmed) tail

         | ([], confirmed', unfls_k') ->
            (* No disproved or confirmed properties. No need to loop
             since base has not been above this k yet. *)
            (
              (* Unfalsifiable properties confirmed by base. *)
              List.rev_append confirmed' confirmed,
              (* Unknown properties are the same as before after
                 clean. *)
              unknowns',
              (* Unfalsifiable properties. Reversed to restore the
                 inverse order. *)
              List.rev ((k,unfls_k') :: tail)
            )

         | (_, _, _) ->
            (* Some properties are disproved. All unfalsifiable
             properties in tail should be backtracked, as well as
             the ones for this k. *)
            let unknowns'' =
              list
              |> List.fold_left
                   ( fun unknws (_, props) ->
                     props
                     (* Cleaning props and appending. *)
                     |> List.fold_left
                          ( fun unknws' prop ->
                            if is_unknown trans prop then
                              (* Prop is neither proved or
                                 disproved. *)
                              prop :: unknws'
                            else
                              (* Prop has been proved or disproved. *)
                              unknws'
                          )
                          unknws
                   )
                   unknowns'
            in

            (
              (* Properties confirmed by base for a smaller k still
                 hold. *)
              confirmed,
              (* New unknown properties after the backtrack. *)
              unknowns'',
              (* No more unfalsifiable properties. *)
              []
            )
       )

    | [] -> (
      (* Properties confirmed by base. *)
      confirmed,
      (* No backtracking, unknown is unchanged. *)
      unknowns',
      (* No more unfalsifiable properties. *)
      []
    )
  in

  loop [] (List.rev unfalsifiables)

(* Deactivates an actlit by asserting its negation. *)
let deactivate solver actlit =
  actlit |> Term.mk_not |> SMTSolver.assert_term solver

(* Creating a fresh actlit for path compression. *)
let path_comp_actlit = fresh_actlit ()
(* Term version. *)
let path_comp_act_term = path_comp_actlit |> term_of_actlit

(* Evaluates a list of terms at zero, then at 1 etc. up to [k].
   If a term@i evaluates to [false], asserts it and returns [true].
   otherwise returns [false].
   In short, attempts to block the model represented by [eval] with a
   term from [terms] at [i] where [0 <= i <= k]. *)
let eval_terms_assert_first_false trans solver eval k =

  (* Unrolls terms of the list at [k], asserting the first one
     evaluating to false and in that case returning [true]. If all
     terms@k evaluate to [true], returns false. *)
  let rec loop_at_k k' = function
    | term :: tail ->
      (* Bumping term at [k]. *)
      let term_at_k = Term.bump_state k' term in
      ( try
          if eval term_at_k
          (* Term evaluates to true, recursing. *)
          then
            loop_at_k k' tail
          (* Term evaluates to false, asserting it and returning true. *)
          else (
            SMTSolver.assert_term solver term_at_k ;
            true
          )
        with
          | Invalid_argument _ ->
            (* This should only happen when the term is two state and
               [k'] is 0. *)
            (* The term was not evaluable in this model, skipping it. *)
            loop_at_k k' tail )
    | [] -> false
  in

  let rec loop_all_k k' =
    if Numeral.(k' > k) then false
    else (
      (* Attempting to block the model represented by [eval]. *)
      let blocked = loop_at_k k' (TransSys.invars_of_bound trans Numeral.zero) in
      if blocked
      (* Blocked, returning. *)
      then true
      (* Not blocked, incrementing [k]. *)
      else loop_all_k Numeral.(k' + one)
    )
  in

  (* Timing the blocking for stats. *)
  Stat.start_timer Stat.ind_lazy_invariants_time ;
  let result = loop_all_k Numeral.zero in
  Stat.record_time Stat.ind_lazy_invariants_time ;

  if result then Stat.incr Stat.ind_lazy_invariants_count ;

  result

(* Check-sat and splits properties.. *)
let split trans solver k to_split actlits =
  
  (* Function to run if sat. *)
  let if_sat _ =
    
    (* Extract a model *)
    let model = 

      (* Do we need the full model? *)
      if (Flags.ind_compress ()) || (Flags.ind_lazy_invariants ()) then 

        (* Get model for all variables *)
        SMTSolver.get_model solver
        
      else
        
        (* We only need the model at [k] *)
        TransSys.vars_of_bounds trans k k
        |> (SMTSolver.get_var_values solver)
        
    in

    Some model

(*
    (* Get-model function. *)
    let get_model = SMTSolver.get_model solver in
    
    (* Getting counterexample for path compression is needed. *)
    let cex =
      if Flags.ind_compress () then
        Model.path_from_model (TransSys.state_vars trans) get_model k
      else 
        Model.create_path 7
    in
    
    (* Getting model for evaluation. *)
    let model =
      if Flags.ind_lazy_invariants () then
        (* Lazy invariant mode, we need the full model. *)
        TransSys.vars_of_bounds trans Numeral.zero k |> get_model
      else
        (* Not in lazy invariant mode, we only need model at [0]. *)
        TransSys.vars_of_bounds trans k k |> get_model
    in
    
    Some (cex, model)
*)

  in

  (* Function to run if unsat. *)
  let if_unsat _ = None in

  (* Appending to the list of actlits. *)
  let all_actlits = path_comp_act_term :: actlits in

  (* Loops as long as counterexamples can be compressed. *)
  let rec loop () = 
    match
      (* Check sat assuming with actlits. *)
      SMTSolver.check_sat_assuming
        solver if_sat if_unsat all_actlits
    with

    | Some model ->
        
      (* Evaluation function. *)
      let term_to_val =
        Eval.eval_term (TransSys.uf_defs trans) model
      in
      (* Bool evaluation function. *)
      let eval term =
        term_to_val term |> Eval.bool_of_value
      in

      (* Attempting to block counterexample with invariants. *)
      let blocked_by_invariant =
        if Flags.ind_lazy_invariants () then
          (* We are in lazy invariants mode, trying to block model. *)
          eval_terms_assert_first_false trans solver eval k
        else false
      in

      if blocked_by_invariant
      (* Blocked model with an invariant, rechecking
         satisfiability. *)
      then loop ()
      else
      
        (* Attempting to compress path. *)
        ( match
            if not (Flags.ind_compress ()) then [] else
               let cex = 
                Model.path_from_model
                  (TransSys.state_vars trans) 
                  model 
                  k 
              in
              Compress.check_and_block
                (SMTSolver.declare_fun solver) trans cex
          with

            | [] ->
              (* Splitting properties. *)
              let new_to_split, new_falsifiable =
                List.partition
                  ( fun (_, (_, term)) ->
                    Term.bump_state k term |> eval )
                  to_split in
              (* Building result. *)
              Some (new_to_split, new_falsifiable)

            | compressor ->
              (* Path compressing, building term and asserting it. *)
              Term.mk_or
                [ path_comp_act_term |> Term.mk_not ;
                  compressor |> Term.mk_and ]
                |> SMTSolver.assert_term solver ;
              (* Rechecking satisfiability. *)
              loop () )

    | None ->
      (* Returning the unsat result. *)
      None
  in

  loop ()

(* Splits its input list of properties between those that can be
   falsified and those that cannot. Optimistics at k are added with
   the negation of the properties to split and are activated by the
   same actlit. This makes backtracking easy since positive actlits
   are not overloaded. *)
let split_closure
  trans solver k optimistic_actlits optimistic_terms to_split =

  let rec loop falsifiable list =

    (* Checking if we should terminate. *)
    Event.check_termination () ;

    (* Building negative term. *)
    let neg_term =
      list |> List.map (fun pair -> snd pair |> snd)
      |> Term.mk_and |> Term.mk_not |> Term.bump_state k in

    (* Adding optimistic properties at k. *)
    let term =
      neg_term ::
        ( optimistic_terms
          |> List.map
               (fun (_, (_, t)) -> t |> Term.bump_state k) )
      |> Term.mk_and
    in

    (* Getting a fresh actlit for it. *)
    let actlit = fresh_actlit () in

    (* Declaring actlit. *)
    actlit |> SMTSolver.declare_fun solver ;

    (* Transforming it to a term. *)
    let actlit_term = actlit |> term_of_actlit in

    (* Asserting implication. *)
    Term.mk_implies [ actlit_term ; term ]
    |> SMTSolver.assert_term solver ;

    (* Getting positive actlits for the list of properties, appending
       them to the optimistic actlits and adding the negative
       actlit. *)
    let all_actlits =
      actlit_term :: (
        list |> List.fold_left (
          fun l (_,(actlit, t)) -> actlit :: l
        ) optimistic_actlits
      )
    in

    (* Splitting. *)
    match split trans solver k list all_actlits with

    | None ->
       (* Unsat. *)
       (* Deactivating negative actlit. *)
       deactivate solver actlit_term ;
       (* Returning result. *)
       list, falsifiable

    | Some ([], new_falsifiable) ->
       (* Sat, no more properties to split. *)
       (* Deactivating negative actlit. *)
       deactivate solver actlit_term ;
       (* Returning result. *)
       [], List.rev_append new_falsifiable falsifiable

    | Some (new_list, new_falsifiable) ->
       (* Sat. *)
       (* Deactivating negative actlit. *)
       deactivate solver actlit_term ;
       (* Looping to split remaining properties. *)
       loop (List.rev_append new_falsifiable falsifiable) new_list
  in

  loop [] to_split


(* Performs the next iteration after updating the context. Assumes the
   solver is in the follwing state:

   actlit(prop) => prop@i
     for all 0 <= i <= k-2 and prop      in 'unknowns'
                                        and 'unfalsifiables';

   invariant@i
     for all 0 <= i <= k-1 and invariant in 'invariants';

   T[i-1,i]
     for all 1 <= i < k.

   List 'unfalsifiables' has type (Numeral.t * properties) list and
   links unfalsifiable properties with the k at which they were found
   to be unfalsifiable.  It should be sorted by decreasing k. *)
let rec next input_sys aparam trans solver k unfalsifiables unknowns =

  (* Getting new invariants and updating transition system. *)
  let new_invariants =
    (* Receiving messages. *)
    Event.recv ()
    (* Updating transition system. *)
    |> Event.update_trans_sys input_sys aparam trans
    (* Extracting invariant module/term pairs. *)
    |> fst
  in

  (* Cleaning unknowns and unfalsifiables. *)
  let confirmed, unknowns', unfalsifiables' =
    clean_properties trans unknowns unfalsifiables
  in

  let unknowns': (string * (Term.t * Term.t)) list = unknowns' in

  (* Communicating confirmed properties. *)
  confirmed |> List.iter (fun (s,_) ->
    Event.prop_status Property.PropInvariant input_sys aparam trans s
  ) ;

  (* Adding confirmed properties to the system. *)
  confirmed |> List.iter (fun (_,(_, term)) ->
    TransSys.add_invariant trans term
  ) ;

  (* Adding confirmed properties to new invariants. *)
  let new_invariants' =
    confirmed |> List.fold_left (
      fun invs (_,(_, term)) -> term :: invs
    ) new_invariants
  in

  match unknowns', unfalsifiables' with
  | [], [] ->
     (* Nothing left to do. *)
     stop ()
  | [], _ ->
     (* Need to wait for base confirmation. *)
     minisleep 0.001 ;
     next input_sys aparam trans solver k unfalsifiables' unknowns'
  | _ ->

     (* Integer version of k. *)
     let k_int = Numeral.to_int k in

     (* Notifying framework of our progress. *)
     Stat.set k_int Stat.ind_k ;
     Event.progress k_int ;
     Stat.update_time Stat.ind_total_time ;

     (* Notifying compression *)
     if Flags.ind_compress () then
       Compress.incr_k () ;

     (* k+1. *)
     let k_p_1 = Numeral.succ k in
     
     (* Declaring unrolled vars at k+1. *)
     TransSys.declare_vars_of_bounds
       trans (SMTSolver.declare_fun solver) k_p_1 k_p_1 ;

     (* Asserting transition relation. *)
     (* TransSys.trans_fun_of trans k k_p_1 *)
     TransSys.trans_of_bound trans k_p_1
     |> SMTSolver.assert_term solver
     |> ignore ;

     (* Asserting invariants if we are not in lazy invariants mode. *)
     if not (Flags.ind_lazy_invariants ()) then (
       (* Asserting new invariants from 0 to k. *)
       ( match new_invariants' with
         | [] -> ()
         | _ ->
            Term.mk_and new_invariants'
            |> Term.bump_and_apply_k
                 (SMTSolver.assert_term solver) k ) ;

       (* Asserts all invariants at k+1. *)
       TransSys.invars_of_bound trans k_p_1
       |> Term.mk_and
       |> SMTSolver.assert_term solver ;
     ) ;

     (* Asserting positive implications at k for unknowns. *)
     unknowns' |> List.iter (fun (_, (actlit, term)) ->
        (* Building implication. *)
        Term.mk_implies [ actlit ; Term.bump_state k term ]
        |> SMTSolver.assert_term solver
      ) ;
     

     (* Actlits, properties and implications at k for unfalsifiables. *)
     let unfalsifiable_actlits, unfalsifiable_props, unfalsifiable_impls =
       unfalsifiables
       |> List.fold_left (
          fun (actlits, props, impls) (_, p) ->
            let actlits', props', impls' =
              p |> List.fold_left (
                fun (actlits,props,impls) ((_, (actlit, term)) as p) ->
                  (* Actlits. *)
                  actlit :: actlits,
                  (* Property. *)
                  p :: props,
                  (* Implication. *)
                  ( Term.mk_implies
                      [ actlit ; Term.bump_state k term ]
                  ) :: impls
              )
              ([],[],[])
            in

            List.rev_append actlits' actlits,
            List.rev_append props' props,
            List.rev_append impls' impls
        ) ([],[],[])
     in

     (* Asserting unfalsifiable implications at k. *)
     unfalsifiable_impls
     |> Term.mk_and
     |> SMTSolver.assert_term solver ;

     (* Output current progress. *)
     Event.log
       L_info
       "IND @[<v>at k = %i@,\
                 %i unknowns@,\
                 %i unfalsifiables.@]"
       (Numeral.to_int k)
       (List.length unknowns') (List.length unfalsifiable_props);

     (* Splitting. *)
     let unfalsifiables_at_k, falsifiables_at_k =
       split_closure
         trans solver k_p_1
         unfalsifiable_actlits
         unfalsifiable_props
         unknowns'
     in

     (* Output statistics *)
     print_stats () ;

     (* Int k plus one. *)
     let k_p_1_int = Numeral.to_int k_p_1 in

     (* Checking if we have reached max k. *)
     if Flags.bmc_max () > 0 && k_p_1_int > Flags.bmc_max () then
       Event.log
         L_info
         "IND @[<v>reached maximal number of iterations.@]"
     else
       (* Looping. *)
       next
         input_sys aparam trans solver k_p_1
         (* Adding the new unfalsifiables. *)
         ( (k_int, unfalsifiables_at_k) :: unfalsifiables' )
         (* Iterating on the properties left. *)
         falsifiables_at_k
         


(* Initializes the solver for the first check. *)
let launch input_sys aparam trans =
  (* Starting the timer. *)
  Stat.start_timer Stat.ind_total_time;

  (* Getting properties. *)
  let unknowns =
    (TransSys.props_list_of_bound trans Numeral.zero)
  in

  (* Creating solver. *)
  let solver =
    SMTSolver.create_instance ~produce_assignments:true
      (TransSys.get_logic trans) (Flags.smtsolver ())
  in

  (* Memorizing solver for clean on_exit. *)
  solver_ref := Some solver ;

  (* Declaring uninterpreted function symbols. *)
  (* TransSys.iter_state_var_declarations *)
  (*   trans *)
  (*   (SMTSolver.declare_fun solver) ; *)

  (* Declaring path compression actlit. *)
  path_comp_actlit |> SMTSolver.declare_fun solver ;

  if Flags.ind_compress () then
    (* Declaring path compression function. *)
    Compress.init (SMTSolver.declare_fun solver) trans ;

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    trans
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    Numeral.(~- one) Numeral.zero ;

  (* Invariants of the system at 0. *)
  TransSys.invars_of_bound trans Numeral.zero
  |> Term.mk_and
  |> SMTSolver.assert_term solver ;

  (* Declaring positive actlits. *)
  let unknowns =
    unknowns |> List.map (fun (s, prop) ->
      let actlit = fresh_actlit () in
      SMTSolver.declare_fun solver actlit ;
      (s, (term_of_actlit actlit, prop))
    )
  in

  (* Launching step. *)
  next input_sys aparam trans solver Numeral.zero [] unknowns

(* Runs the step instance. *)
let main input_sys aparam trans = 

  if not (List.mem `BMC (Flags.enable ())) then

    Event.log 
      L_warn 
      "@[<v>Inductive step without BMC will not be able to prove or@ \
       disprove any properties.@,\
       Use both options --enable BMC --enable IND together.@]";
      
  launch input_sys aparam trans


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

