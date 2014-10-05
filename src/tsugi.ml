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

(* Tsugi stands for Transition System Unroller for Generalized
   Induction. It is a functor designed to perform BMC checks in order
   to implement k-induction. *)

open Lib
open TypeLib

module Solver = SolverMethods.Make(SMTSolver.Make(SMTLIBSolver))

(* Enumerated type to choose between base and step. *)
type bmc_mode = | Base | Step

(* Passed to 'next' at the beginning of an iteration. *)
type context_update = {
  (* New invariants INCLUDING new invariant properties. *)
  new_invariants : Term.t list ;
  (* New valid properties which SHOULD ALSO BE in 'new_invs'. *)
  new_valid : properties ;
  (* New falsified properties. *)
  new_falsified : properties ;
  (* New properties unfalsifiable in step waiting for base
     confirmation. *)
  new_optimistic : properties
}

(* Type returned by a single iteration of bmc. *)
type walk_bmc_result = {
  (* K corresponding to this result. *)
  k : Numeral.t ;
  (* Properties the negation of which is unsat at k. *)
  unfalsifiable : properties ;
  (* Properties the negation of which is sat at k, with models. *)
  falsifiable : cexs ;
  (* Properties the negation of which is sat at k, no
     counterexample. *)
  falsifiable_no_cex : properties ;
  (* Properties optimistically assumed to hold. *)
  optimistic : properties ;
  (* Continuation for the next bmc iteration. *)
  continue : properties -> context_update -> walk_bmc_result ;
  (* Kills the solver. *)
  kill : unit -> unit
}

(* Signature for actlit modules for the make functor. *)
module type InActlit = sig

  (* Creates a positive actlit as a UF. *)
  val positive : Term.t -> UfSymbol.t

  (* Creates a negative actlit as a UF. *)
  val negative : Numeral.t -> Term.t -> UfSymbol.t

end

(* Signature for the counterexamples extraction functions. *)
module type InPathExtractor = sig

  val generic: TransSys.t ->
               (Var.t list -> (Var.t * Term.t) list) ->
               Numeral.t ->
               path

  (* Extracts a counterexample for the base instance. *)
  val base : TransSys.t ->
             (Var.t list -> (Var.t * Term.t) list) ->
             Numeral.t ->
             path

  (* Extracts a counterexample for the step instance. *)
  val step : TransSys.t ->
             (Var.t list -> (Var.t * Term.t) list) ->
             Numeral.t ->
             path

end


(* Signature for communication modules. *)
module type InComm = sig

  (* Communicates results from the base instance. *)
  val base :
    TransSys.t -> Numeral.t -> properties -> cexs ->
    context_update

  (* Communicates results from the step instance. *)
  val step :
    TransSys.t -> Numeral.t -> properties -> cexs -> properties ->
    context_update

  (* Waits for confirmation for base for 'optimistic' at k. *)
  val step_confirm :
    TransSys.t -> Numeral.t -> properties -> context_update option

end


(* Signature for the output of the functor. *)
module type Out = sig

  (* Runs a BMC loop either in Base or Step mode. *)
  val run_bmc : bmc_mode -> TransSys.t -> unit

  (* A single BMC iteration, either in Base or Step mode. Starts at k
     = 0 and returns the result of the iteration and a
     continuation. *)
  val walk_bmc : bmc_mode -> TransSys.t -> properties -> walk_bmc_result

end 

module Make (Actlit: InActlit)
            (Comm: InComm)
            (PathExtract: InPathExtractor) : Out = struct

  let kill_solver = Solver.delete_solver

  (* Turns an actlit (UF) to a term. *)
  let term_of_actlit actlit = Term.mk_uf actlit []

  (* Asserts init at zero. *)
  let assert_init trans solver =
    TransSys.init_of_bound trans Numeral.zero
    |> Solver.assert_term solver
    |> ignore

  (* Builds the positive implication of a property at k. *)
  let positive_implication k prop =
    let actlit = Actlit.positive prop |> term_of_actlit in
    Term.mk_or [ Term.mk_not actlit ;
                 prop |> Term.bump_state k ]

  (* Filters the list of input properties while building the
     positive implications and prepends everything to 'l' and
     'l_impl'. *)
  let positive_implications_filter_prepend k shall_keep l l_impl =
    List.fold_left
      ( fun (list,impl_list) ((_,term) as prop) ->
        if shall_keep prop
        then
          ( prop :: list,
            (positive_implication k term) :: impl_list )
        else (list, impl_list) )
      (l,l_impl)

  (* Filters the list of input properties while building the
     positive implications. *)
  let positive_implications_filter k shall_keep =
    positive_implications_filter_prepend k shall_keep [] []

  (* Returns the list of positive activators for the input property
     list. *)
  let positive_activators =
    List.map
      ( fun (_, prop) -> Actlit.positive prop |> term_of_actlit )

  (* Creates positive activators for the input list prepending them
   to some list at the same time. *)
  let positive_activators_prepend list =
    List.fold_left
      ( fun prefix (_, prop) ->
        (Actlit.positive prop |> term_of_actlit) :: prefix )
      list

  (* Builds the negative implication of the input term, asserts it and
   returns the activation literal. *)
  let assert_negative_implication_term solver k term =

    (* Activation literal. *)
    let actlit = term |> Actlit.negative k in

    (* Declaring it. *)
    actlit |> Solver.declare_fun solver ;

    (* Term version of the actlit. *)
    let actlit_term = actlit |> term_of_actlit in

    (* Bulding the negative implication. *)
    let negative_implication =
      Term.mk_or [ actlit_term |> Term.mk_not ; term ]
    in

    (* Asserting it. *)
    negative_implication
    |> Solver.assert_term solver
    |> ignore ;

    (* Returning actlit. *)
    actlit_term

  (* Builds the term (and optimistic (not (and unknown))) at k, asserts
   that the negative actlit of that term implies it, and returns the
   negative actlit. 'unknown' should not be empty. *)
  let assert_negative_implication
        solver k optimistic unknown =
    assert (unknown <> []) ;

    (* One of the unknown properties should be false. *)
    let negated =
      unknown |> List.map snd |> Term.mk_and |> Term.mk_not
    in

    (* Building the conjunction and calling helper. *)
    negated :: (List.map snd optimistic)
    |> Term.mk_and
    |> Term.bump_state k
    |> assert_negative_implication_term solver k

  (* Splits the input properties between those those that are falsified
   and those that are not if the list of actlits is satisfiable,
   returns all of them otherwise. *)
  let split
        trans solver k actlits falsifiable falsifiable_no_cex unknown =

    (* Function to run if sat. *)
    let if_sat () =
      (* Get the model. *)
      let model =
        TransSys.vars_of_bounds trans k k
        |> Solver.get_model solver
      in
      (* Extracting the actual counterexample. *)
      let cex =
        PathExtract.generic trans (Solver.get_model solver) k
      in
      (* UF definitions. *)
      let uf_defs = TransSys.uf_defs trans in
      (* Evaluation function. *)
      let eval t =
        Eval.eval_term uf_defs model t
        |> Eval.bool_of_value
      in
      (* Split properties. *)
      let new_unknown, new_falsifiable_head, new_falsifiable_no_cex =
        unknown
        |> List.fold_left
	     ( fun (uknwn, fls, flsnm) ((_,term) as prop) ->
	       if Term.bump_state k term |> eval then
	         (prop :: uknwn), fls, flsnm
	       else
	         uknwn, prop :: fls, prop :: flsnm )
	     ( [], [],  falsifiable_no_cex )
      in
      (* Building result tuple. *)
      ( new_unknown,
        (* Sat so no unsatisfiable properties. *)
        [],
        (new_falsifiable_head, cex) :: falsifiable,
        new_falsifiable_no_cex )
    in

    (* Function to run if unsat. *)
    let if_unsat () =
      ( [], unknown, falsifiable, falsifiable_no_cex )
    in

    (* Check sat assuming with all literals. *)
    Solver.check_sat_assuming solver if_sat if_unsat actlits
                              

  (* Splits the input properties between those that are falsifiable at k
   and those which are not, assuming that 'optimistic' holds at k. *)
  let split_closure solver trans k optimistic unknown =

    (* Actually splits 'list'. *)
    let rec loop falsifiable falsifiable_no_cex list =

      (* Asserting the negative implication and getting the activation
       literal. *)
      let negative_actlit =
        assert_negative_implication solver k optimistic list
      in

      (* Building the list of positive actlits for 'unknown'. *)
      let unknown_actlits = positive_activators unknown in

      (* Building the positive actlits for 'optimistic', prepending
       to the unknown actlits at the same time. *)
      let positive_actlits =
        positive_activators_prepend unknown_actlits optimistic
      in

      (* Adding negative actlit. *)
      let all_actlits = negative_actlit :: positive_actlits in

      (* Splitting. *)
      match split
	      trans solver k
              all_actlits falsifiable falsifiable_no_cex list
      with
      | (
        [], new_unfalsifiable, new_falsifiable, new_falsifiable_no_cex
      ) ->
         (new_unfalsifiable, new_falsifiable, new_falsifiable_no_cex)
      | (
        new_unknown, [], new_falsifiable, new_falsifiable_no_cex
      ) ->
         loop new_falsifiable new_falsifiable_no_cex new_unknown
      | _ -> raise (Failure "This should never happen.")
    in

    (* Computing the closure. *)
    loop [] [] unknown


  (* Sets the solver up for the next 'split_closure' call. The state
     of the solver when entering 'next' is:
     unknown and optimistic positive implications:
       0 .. k-2
     invs:
       0 .. k-1 *)
  let rec next
            solver trans k
            (* Invariants. *)
            invs
            (* Properties unfalsifiable for some k waiting for base
               confirmation. *)
            optimistic
            (* Unknown properties. *)
            unknown
            (* Context update. *)
            { new_invariants ;
              new_valid ;
              new_falsified ;
              new_optimistic } =

    (* 'k' should be greater than one. *)
    assert Numeral.(k >= one) ;

    (* k - 1. *)
    let k_minus_one = Numeral.(k - one) in

    match new_falsified with
    | _ :: _ ->
       (* New falsified things, cancelling optimistic properties and
          backtracking. *)
       let shall_keep p = List.mem p new_falsified in
       let new_unknown =
         (* Cleaning optimistic. *)
         let new_optimistic = optimistic |> List.filter shall_keep in
         (* Cleaning unknown and prepend to 'new_optimistic' at the
            same time. *)
         unknown
         |> List.fold_left
              ( fun list prop ->
                if shall_keep prop then prop :: list else list )
              new_optimistic
       in

       (* Restarting with new, clean 'unknown'. *)
       next
         solver trans k_minus_one
         invs [] new_unknown
         (* Discarding 'new_optimistic', they were in 'unknown'
            and do not make sense because of falsified props. *)
         { new_invariants = new_invariants ;
           new_valid = new_valid ;
           new_falsified = [] ;
           new_optimistic = [] }

    | _ ->
       (* No falsified things, we can go on. *)

       (* Cleaning 'unknown', generating implications. *)
       let nu_unknown, unknown_implications =
         unknown
         |> positive_implications_filter
              k_minus_one
              (fun p -> not (List.mem p new_valid)
                        || not (List.mem p new_optimistic))
       in

       (* Cleaning 'optimistic', adding implications to
          'unknown_implications'. *)
       let clean_optimistic, optimistic_and_unknown_implications =
         optimistic
         |> positive_implications_filter_prepend
              k_minus_one
              (fun p -> List.mem p new_valid)
              []
              unknown_implications
       in

       (* Generating implications for 'new_optimistic', prepending to
          'clean_optimistic' and
          'optimistic_and_unknown_implications'. *)
       let nu_optimistic, all_implications =
         new_optimistic
         |> positive_implications_filter_prepend
              k_minus_one
              (fun p -> true)
              clean_optimistic
              optimistic_and_unknown_implications
       in

       (* Asserting T[x_k-1, x_k]. *)
       TransSys.trans_of_bound trans k
       |> Solver.assert_term solver
       |> ignore ;

       (* Asserting all implications. *)
       all_implications
       |> Term.mk_and
       |> Solver.assert_term solver
       |> ignore ;

       (* Merging old and new invariants, and asserting them. *)
       let nu_invs =
         
         (* Asserting new invariants from 0 to k. *)
         let assert_new_invariants terms =
           terms
           |> Term.mk_and
           |> Term.bump_and_apply_k
                (Solver.assert_term solver) k
         in

         (* Asserting (old) invariants at k. *)
         let assert_old_invariants terms =
           terms
           |> Term.mk_and
           |> Term.bump_state k
           |> Solver.assert_term solver
         in

         (* Merging old and new invariants. *)
         (match new_invariants, invs with
          | [], [] -> []
          | _, [] ->
             assert_new_invariants new_invariants ;
             new_invariants
          | [], _ ->
             assert_old_invariants invs ;
             invs
          | _, _ ->
             assert_new_invariants new_invariants ;
             assert_old_invariants invs ;
             List.rev_append new_invariants invs)

       in

       (* Building the continuation for the next iteration. *)
       let continuation =
         next solver trans Numeral.(k + one) nu_invs nu_optimistic
       in

       (* Splitting falsifiable and unfalsifiable things. *)
       let unfalsifiable, falsifiable, falsifiable_no_cex =
         split_closure
           solver trans k
           nu_optimistic nu_unknown
       in

       (* Returning the result and the continuation. *)
       { (* K-1 by kind2 conventions. *)
         k = k ;
         unfalsifiable = unfalsifiable ;
         falsifiable = falsifiable ;
         falsifiable_no_cex = falsifiable_no_cex ;
         optimistic = nu_optimistic ;
         continue = continuation ;
         kill = (fun () -> Solver.delete_solver solver) }

  let update_trans trans =
    Event.recv ()
    |> Event.update_trans_sys_tsugi trans

  let rec stage_next_base
            trans
            { k;
              unfalsifiable; falsifiable; falsifiable_no_cex;
              optimistic; continue; kill } =

    (* Updating transition system and retrieving new things. *)
    let (new_invariants, new_valid, new_falsified) =
      update_trans trans
    in

    let status_k_true = TransSys.PropKTrue(Numeral.to_int k) in

    (* Broadcast status of properties true in k steps. *)
    List.iter
      ( fun (s, _) ->
        Event.prop_status status_k_true trans s )
      unfalsifiable ;

    (* Broadcast status of properties falsified in k steps. *)
    List.iter
      ( fun (p, cex) ->
        List.iter
          ( fun (s, _) ->
            Event.prop_status (TransSys.PropFalse cex) trans s )
          p )
      falsifiable ;

    match unfalsifiable with
    | [] ->
       debug tsugi
             "[Base] No more property to falsify, stopping."
       in
       kill ()
    | _ ->

       (* Notify we are starting k + 1. *)
       let k_p_1 = (Numeral.to_int k) + 1 in
       Event.progress k_p_1 ;
       Stat.set k_p_1 Stat.bmc_k ;
       Stat.update_time Stat.bmc_total_time ;

       stage_next_base
         trans
         ( continue
             (unfalsifiable
              |> List.filter
                   (fun p ->
                    not (List.mem p falsifiable_no_cex)))
             { new_invariants = new_invariants ;
               new_valid = new_valid ;
               new_falsified = new_falsified ;
               new_optimistic = [] } )

  (* Checks if a property is true up to 'k_step'. *)
  let holds_in_base trans k_step (prop,_) =
    match TransSys.get_prop_status trans prop with
    | TransSys.PropKTrue k' ->
       debug tsugi "Holds at %i / %i" k' (Numeral.to_int k_step) in
       k' >= (Numeral.to_int k_step) - 1
    | _ -> false

  let step_confirm trans k toConfirm =

    let rec confirm invariants valid = function
      | [] ->
         (* Nothing to confirm. *)
         None
      | list ->

         (* Updating transition system. *)
         let (new_invariants, new_valid, new_falsified) =
           update_trans trans
         in

         let nu_invariants, nu_valid =
           List.rev_append new_invariants invariants,
           List.rev_append new_valid valid
         in

         match new_falsified with
         | _ :: _ ->
            debug tsugi "Falsified." in
            (* New falsified properties, step needs to backtrack. *)
            Some
              { (* New invariants. *)
                new_invariants = nu_invariants ;
                (* New invariant properties. *)
                new_valid = nu_valid ;
                (* New falsified properties. *)
                new_falsified = new_falsified ;
                (* New optimistic properties. *)
                new_optimistic = [] }

         | [] ->
            debug tsugi "No Falsified, looping." in
            Lib.minisleep 0.001 ;
            (* Looping. *)
            confirm
              nu_invariants
              nu_valid
              (* Removing properties that hold in base or are actually
                 invariants. *)
              (list
               |> List.filter
                    ( fun prop ->
                      not (holds_in_base trans k prop)
                      && not (List.mem prop new_valid) ))
    in

    confirm [] [] toConfirm


  let rec stage_next_step
            trans
            { k;
              unfalsifiable; falsifiable; falsifiable_no_cex;
              optimistic; continue; kill } =

    (* Updating transition system. *)
    let new_invariants, new_valid, new_falsified =
      update_trans trans
    in

    match new_falsified, falsifiable, optimistic, unfalsifiable with
    | _ :: _, _, _, _ ->
       (* Some properties were falsified, backtracking. *)
       stage_next_base
         trans
         (continue
            falsifiable_no_cex
            { new_invariants = new_invariants ;
              new_valid = new_valid ;
              new_falsified = new_falsified ;
              new_optimistic = [] })
    | _, [], [], [] ->
       debug tsugi
             "[Step] Nothing left to prove, stopping."
       in
       kill ()
    | _, [], _, _ ->
       debug tsugi
             "[Step] All properties are unfalsifiable."
       in
       let to_confirm = List.rev_append unfalsifiable optimistic in
       (match step_confirm 
                trans k to_confirm
        with
        | Some new_context ->
           Event.log
             L_info
             "[Step] Falsified properties, backtracking." ;
           continue falsifiable_no_cex new_context
           |> stage_next_base trans
        | _ ->
           List.iter
             (fun (n, _) ->
              Event.prop_status TransSys.PropInvariant trans n)
             to_confirm ;
           kill ())

    | _ ->
       (* Notify we are starting k+1 (actually k by kind's
          conventions). *)
       let k_int = (Numeral.to_int k) in
       Event.progress k_int ;
       Stat.set k_int Stat.ind_k ;
       Stat.update_time Stat.ind_total_time ;

       stage_next_step
         trans
         (continue
            falsifiable_no_cex
            { new_invariants = new_invariants ;
              new_valid = new_valid ;
              new_falsified = new_falsified ;
              new_optimistic = unfalsifiable })


  (* A single BMC iteration, starts at k=0 and returns a
     continuation. *)
  let walk_bmc bmc_mode trans props =

    (* Creating solver. *)
    let solver =
      TransSys.get_logic trans
      |> Solver.new_solver ~produce_assignments:true
    in

    (* Declare uninterpreted function symbols *)
    TransSys.iter_state_var_declarations
      trans
      (Solver.declare_fun solver) ;

    (* Declaring positive actlits. *)
    List.iter
      ( fun (_, prop) ->
        Actlit.positive prop |> Solver.declare_fun solver )
      props ;

    (* Define functions *)
    TransSys.iter_uf_definitions
      trans
      (Solver.define_fun solver) ;

    match bmc_mode with
    | Base ->
       Stat.start_timer Stat.bmc_total_time ;

       (* Notify framework we are starting base. *)
       Event.progress 0 ;
       Stat.set 0 Stat.bmc_k ;
       (* If in base mode assert init... *)
       assert_init trans solver ;
       (* then go to split closure for k = 0. *)
       let unfalsifiable, falsifiable, falsifiable_no_cex =
         split_closure
           solver trans Numeral.zero
           [] props
       in

       { k = Numeral.zero ;
         unfalsifiable = unfalsifiable ;
         falsifiable = falsifiable ;
         falsifiable_no_cex = falsifiable_no_cex ;
         optimistic = [] ;
         continue = next solver trans Numeral.one [] [] ;
         kill = (fun () -> Solver.delete_solver solver) }

    | Step ->
       Stat.start_timer Stat.ind_total_time ;

       (* Notify framework we are starting step. *)
       Event.progress 0 ;
       Stat.set 0 Stat.ind_k ;

       (* For step, call next for k = 1. *)
       (next
          solver
          trans
          Numeral.one
          []
          []
          props
          { new_invariants = [] ;
            new_valid = [] ;
            new_falsified = [] ;
            new_optimistic = [] })

  (* Runs the BMC loop. *)
  let run_bmc bmc_mode trans =
    (* | Base -> *)

    (*    ( fun loop *)
    (*          { k ; unfalsifiable ; falsifiable ; *)
    (*            falsifiable_no_cex ; optimistic ; *)
    (*            continue ; kill } -> *)

    (*      (\* In the base case, just continue with the unfalsifiable *)
    (*         properties. *\) *)
    (*      match unfalsifiable with *)
    (*      | [] -> *)
    (*         Event.log *)
    (*           L_info *)
    (*           "[Base] No more property to check, stopping." ; *)
    (*         kill () *)
                 
    (*      | _  -> *)
    (*         (\* Launching next iteration. *\) *)
    (*         continue unfalsifiable *)
    (*                  (Comm.base *)
    (*                     trans k unfalsifiable falsifiable) *)
    (*         |> loop ) *)

    (* | Step -> *)

    (*    ( fun loop *)
    (*          { k ; unfalsifiable ; falsifiable ; *)
    (*            falsifiable_no_cex ; optimistic ; *)
    (*            continue ; kill } -> *)

    (*        (\* In the step case, continue with the falsifiable *)
    (*           properties. *\) *)
    (*        match unfalsifiable, falsifiable_no_cex, optimistic with *)

    (*        | [], [], [] -> *)
    (*           Event.log *)
    (*             L_info *)
    (*             "[Step] No more property to prove, stopping." ; *)
    (*           kill () *)

    (*        | [], [], _ -> *)
    (*           Event.log *)
    (*             L_info *)
    (*             "[Step] Nothing to do, waiting for base confirmation." ; *)
    (*           (match Comm.step_confirm trans k optimistic with *)
    (*            | Some new_context -> *)
    (*               Event.log *)
    (*                 L_info *)
    (*                 "[Step] Falsified properties, backtracking." ; *)
    (*               continue [] new_context *)
    (*               |> loop *)
    (*            | _ -> *)
    (*               Event.log *)
    (*                 L_info *)
    (*                 "[Step] Base confirmation received, stopping." ; *)
    (*               kill ()) *)

    (*        | _, _, _ -> *)
    (*           debug tsugi "[Step] Continuing to next." in *)
    (*           (\* Launching next iteration. *\) *)
    (*           continue *)
    (*             falsifiable_no_cex *)
    (*             (Comm.step *)
    (*                trans *)
    (*                Numeral.(k-one) *)
    (*                unfalsifiable *)
    (*                falsifiable *)
    (*                optimistic) *)
    (*           |> loop) *)
    (* in *)

    (* (\* BMC loop. *\) *)
    (* let rec evil_loop trans bmc_result = *)
    (*   (\* Launching next iteration. *\) *)
    (*   stage_next (evil_loop trans) bmc_result *)
    (* in *)

    (* Unrolling the properties at zero. *)
    let props = (TransSys.props_list_of_bound trans Numeral.zero) in

    (* Notify that we are starting. *)
    (* Building the first continuation and entering the evil loop. *)
    (walk_bmc bmc_mode trans props)
    |> (match bmc_mode with
        | Base -> stage_next_base trans
        | Step -> stage_next_step trans)

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

