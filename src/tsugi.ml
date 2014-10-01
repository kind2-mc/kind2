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
  new_pending : properties ;
  (* Properties unfalsifiable in step waiting for base
     confirmation. *)
  pending : bool
}

(* Type returned by a single iteration of bmc. *)
type walk_bmc_result = {
  (* K corresponding to this result. *)
  k : Numeral.t ;
  (* Properties the negation of which is unsat at k. *)
  unfalsifiable : properties ;
  (* Properties the negation of which is sat at k, with models. *)
  falsifiable : cexs ;
  (* Properties the negation of which is sat at k, no models. *)
  falsifiable_no_model : properties ;
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
  val base : TransSys.t -> Numeral.t -> properties -> cexs -> context_update

  (* Communicates results from the step instance. *)
  val step : TransSys.t -> Numeral.t -> properties -> cexs -> context_update

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


  (* Adds an implication between a positive literal and a property from
     'k_min' to 'k_max'. Assumes 'k_min' <= 'k_max'. *)
  let positive_activation k_min k_max assert_term terms =

    assert Numeral.(k_min <= k_max) ;

    (* Bumps 'term' to 'k', prepends it to 'list', decrements 'k' and
       recurses until 'k' is less than 'k_min'. *)
    let rec inner_loop list term k =
      if Numeral.(k < k_min) then list
      else
        inner_loop ((Term.bump_state k term) :: list) term Numeral.(k - one)
    in

    (* Builds the conjunction of all the positive implications of the
       input list of terms 'ts' between 'k_min' and 'k_max'. *)
    let rec loop conj ts =
      match ts,conj with
      | (_, prop) :: tail, _ ->

         (* Building activation literal on the property. *)
         let actlit = Actlit.positive prop |> term_of_actlit in

         (* Building implication. *)
         let impl = Term.mk_or [ Term.mk_not actlit ; prop ] in

         (* Adding bumped terms to the conjunction. *)
         let new_conj = inner_loop conj impl k_max in

         (* Adding it to the conjunction and looping. *)
         loop new_conj tail

      | _, [] -> 
         (* Nothing to assert. *)
         ()

      | _, _ ->
         (* Asserting the big conjunction. *)
         conj |> Term.mk_and |> assert_term |> ignore
    in

    loop [] terms


  (* Deactivates terms by asserting the negation of their positive
     actlits. *)
  let positive_deactivation assert_term terms =

    (* Builds the conjunction of all the positive implications of the
       input list of terms 'ts' between 'k_min' and 'k_max'. *)
    let rec loop conj ts =
      match ts,conj with
      | (_, prop) :: tail, _ ->

         (* Building deactivation term. *)
         let deact =
           Actlit.positive prop |> term_of_actlit |> Term.mk_not
         in

         (* Adding it to the conjunction and looping. *)
         loop (deact :: conj) tail

      | _, [] -> 
         (* Nothing to assert. *)
         ()

      | _, _ ->
         (* Asserting the big conjunction. *)
         conj |> Term.mk_and |> assert_term |> ignore
    in

    loop [] terms


  (* Returns the list of all activators for the input properties. *)
  let positive_activators =
    List.map
      ( fun (_, prop) -> Actlit.positive prop |> term_of_actlit )


  (* Asserts init at zero. *)
  let assert_init solver trans =
    TransSys.init_of_bound trans Numeral.zero
    |> Solver.assert_term solver
    |> ignore


  (* Splits the input properties between those that are falsifiable
     and those which are not. The implications should be asserted
     --see 'next'. Also returns the continuation it was given. *)
  let split_closure solver trans k opt_props props { continue } =

    let rec loop unknown unfalsifiable falsifiable falsifiable_no_model =

      (* Building the negation of the conjunction of the properties at
         k. *)
      let negative_properties =
        unknown
        |> List.map (fun (_,p) -> Term.bump_state k p)
        |> Term.mk_and
        |> Term.mk_not
      in

      (* Creating the negative actlit. *)
      let negative_actlit = Actlit.negative k negative_properties in
      (* Declaring it. *)
      Solver.declare_fun solver negative_actlit ;
      (* Building the term out of the negative actlit UF. *)
      let neg_actlit_term = term_of_actlit negative_actlit in

      (* Asserting the negative implication. *)
      Term.mk_or
        [ neg_actlit_term |> Term.mk_not ; negative_properties ]
      |> Solver.assert_term solver ;

      (* Building the list of positive actlits on 'props' (not
         'unknown') and the optimistic actlits.
         This could be optimized by directly passing it as an
         argument to split_closure.*)
      let positive_actlits =
        props
        |> List.rev_append opt_props
        |> positive_activators
      in

      (* Gathering all the activation literals. *)
      let all_actlits = neg_actlit_term :: positive_actlits in

      (* Function to run if sat. *)
      let if_sat () =

        (* Get the model. *)
        let model = 
          TransSys.vars_of_bounds trans k k
          |> Solver.get_model solver
        in
        let path =
          PathExtract.generic trans (Solver.get_model solver) k
        in
        let uf_defs = TransSys.uf_defs trans in
        (* Evaluation function. *)
        let eval t = Eval.bool_of_value(Eval.eval_term uf_defs model t) in

        (* Split properties. *)
        let (new_unknown, new_falsifiable) =
          List.partition (fun prop -> eval (Term.bump_state k (snd prop))) unknown
        in

        ( new_unknown,
          unfalsifiable,
          (new_falsifiable, path) :: falsifiable,
          List.concat [new_falsifiable ; falsifiable_no_model ] )
      in

      (* Function to run if unsat. *)
      let if_unsat () =
        ( [], unknown, falsifiable, falsifiable_no_model )
      in


      let (
        new_unknown,
        new_unfalsifiable,
        new_falsifiable,
        new_falsifiable_no_model
      ) =

        (* Check sat assuming with all literals. *)
        Solver.check_sat_assuming solver if_sat if_unsat all_actlits

      in

      match new_unknown with
      | [] ->
         { k = k ;
           unfalsifiable = new_unfalsifiable ;
           falsifiable = new_falsifiable ;
           falsifiable_no_model = new_falsifiable_no_model ;
           continue = continue ;
           kill = (fun () -> Solver.delete_solver solver) }
      | _ -> loop new_unknown
                  new_unfalsifiable
                  new_falsifiable
                  new_falsifiable_no_model
    in

    loop props [] [] []


  let rec next
            solver
            trans
            k
            (* Invariants. *)
            invs
            (* Properties unfalsifiable for some k waiting for base
               confirmation. *)
            pending
            (* Unknown properties. *)
            unknown
            (* Context update. *)
            { new_invariants ;
              new_valid ;
              new_falsified ;
              new_pending } =

    (* We need to remove new valid and falsified properties from
       'unknown' and 'pending'. *)
    let shall_keep =
      (fun prop -> not (List.mem prop new_valid || List.mem prop new_pending))
    in

    (* Cleaning 'pending'. *)
    let clean_pending = List.filter shall_keep pending in

    (* Cleaning 'unknown'. *)
    let clean_unknown = List.filter shall_keep unknown in

    (* Asserting transition relation for k > 0. *)
    if Numeral.(k > zero) then (

      (* k - 1. *)
      let k_minus_one = Numeral.(k - one) in

      (* T[x_k-1, x_k]. *)
      TransSys.trans_of_bound trans k
      |> Solver.assert_term solver
      |> ignore ;

      (* Positive implications for new pending properties at k - 1 and
         k. *)
      new_pending
      |> positive_activation
           k_minus_one k (Solver.assert_term solver) ;

      (* Positive implications for pending properties at k. *)
      clean_pending
      |> positive_activation
           k k (Solver.assert_term solver) ;

      (* Positive implications for unknown properties at k - 1. *)
      clean_unknown
      |> positive_activation
           k_minus_one k_minus_one (Solver.assert_term solver) ;
    ) ;


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

      match new_invariants, invs with
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
         List.rev_append new_invariants invs

    in

    (* Merging old and new pending properties. *)
    let nu_pending = List.rev_append new_pending clean_pending in

    (* Deactivating falsified properties. *)
    new_falsified
    |> positive_deactivation (Solver.assert_term solver) ;



    (* Building the continuation for the next iteration. *)
    let continuation =
      next solver trans Numeral.(k + one) nu_invs nu_pending
    in

    (* Splitting falsifiable and unfalsifiable things, and passing the
       continuation. *)
    split_closure
      solver
      trans
      k
      nu_pending
      clean_unknown
      { k = k ;
        unfalsifiable = [] ;
        falsifiable = [] ;
        falsifiable_no_model = [] ;
        continue = continuation ;
        kill = (fun () -> Solver.delete_solver solver) }



  (* A single BMC iteration, starts at k=0 and returns a continuation. *)
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
      ( fun (_, prop) -> Actlit.positive prop |> Solver.declare_fun solver )
      props ;

    (* Define functions *)
    TransSys.iter_uf_definitions
      trans
      (Solver.define_fun solver) ;

    let k =
      match bmc_mode with
      | Base ->
         (* If in base mode assert init. *)
         assert_init solver trans ;
         Numeral.zero
      | Step -> Numeral.one
    in

    next solver
         trans
         k
         []
         []
         props
         { new_invariants = [] ;
           new_valid = [] ;
           new_falsified = [] ;
           new_pending = [] ;
           pending = false }



  (* Runs the BMC loop. *)
  let run_bmc bmc_mode trans =

    let rec step_finish_loop kill k { pending } =
      if pending then step_finish_loop kill k (Comm.step trans k [] [])
      else kill ()
    in

    (* Launches the next iteration based on the results of the
       previous one. *)
    let rec stage_next =
      match bmc_mode with
      | Base ->
         ( fun loop
               { k ; unfalsifiable ; falsifiable ;
                 falsifiable_no_model ; continue ; kill } ->
           (* In the base case, just continue with the unfalsifiable
              properties. *)
           match unfalsifiable with
           | [] -> kill ()
           | _  -> continue unfalsifiable
                            (Comm.base trans k unfalsifiable falsifiable)
                   |> loop )

      | Step ->
         ( fun loop
               { k ; unfalsifiable ; falsifiable ;
                 falsifiable_no_model ; continue ; kill } ->
           (* In the step case, continue with the falsifiable
              properties. *)
           match falsifiable_no_model with
           | [] ->
              step_finish_loop
                kill
                Numeral.(k - one)
                (Comm.step trans Numeral.(k-one) unfalsifiable falsifiable)
           | _ -> continue
                    falsifiable_no_model
                    (Comm.step trans Numeral.(k-one) unfalsifiable falsifiable)
                  |> loop )
    in

    (* BMC loop. *)
    let rec evil_loop trans bmc_result =
      (* Launching next iteration. *)
      stage_next (evil_loop trans) bmc_result
    in

    (* Unrolling the properties at zero. *)
    let props = (TransSys.props_list_of_bound trans Numeral.zero) in

    (* Building the first continuation and entering the evil loop. *)
    walk_bmc bmc_mode trans props |> evil_loop trans

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

