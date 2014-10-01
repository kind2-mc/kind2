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

type bmc_mode = | Base | Step

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
  continue : properties -> invariants -> walk_bmc_result
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
  val base : TransSys.t -> Numeral.t -> properties -> cexs -> unit

  (* Communicates results from the step instance. *)
  val step : TransSys.t -> Numeral.t -> properties -> cexs -> unit

  (* Gets new invariants from the rest of the framework. *)
  val new_invariants : unit -> Term.t list

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

  (* Turns an actlit (UF) to a term. *)
  let term_of_actlit actlit = Term.mk_uf actlit []


  (* Adds an implication between a positive literal and a property at
     k-1. *)
  let positive_activation k assert_term list =
    (* K must be greater than one. *)
    assert Numeral.(geq k one) ;

    let rec loop conj = function
      | (_, prop) :: tail ->
         (* Bumping to k-1. *)
         let prop_k_m_one = Term.bump_state Numeral.(k-one) prop in

         (* Building activation literal on the property NOT bumped for
            positive actlit reuse. *)
         let actlit = Actlit.positive prop |> term_of_actlit in

         (* Building implication. *)
         let impl = Term.mk_or [ Term.mk_not actlit ; prop_k_m_one ] in

         (* Adding it to the conjunction and looping. *)
         loop (impl :: conj) tail
      | [] -> conj
    in

    loop [] list
    |> Term.mk_and
    |> assert_term
    |> ignore


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
  let split_closure solver trans k props { continue } =
    let rec loop unknown unfalsifiable falsifiable falsifiable_no_model =

      (* k as int. *)
      let k_int = Numeral.to_int k in

      (* Building not the conjunction of the properties at k. *)
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

      (* Building the list of positive actlits on props, not
           unknown. *)
      let positive_actlits = positive_activators props in

      (* Gathering all the activation literals. *)
      let all_actlits = neg_actlit_term :: positive_actlits in

      (* Function to run if sat. *)
      let if_sat () =
        debug tsugi "[%3i] Sat, getting model." k_int in

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
        debug tsugi "  Splitting properties." in
        let (new_unknown, new_falsifiable) =
          List.partition (fun prop -> eval (Term.bump_state k (snd prop))) unknown
        in

        debug tsugi
          "  > %2i falsifiable properties, and" (List.length new_falsifiable)
        in
        debug tsugi "  > %2i unknown properties." (List.length new_unknown) in

        ( new_unknown,
          unfalsifiable,
          (new_falsifiable, path) :: falsifiable,
          List.concat [new_falsifiable ; falsifiable_no_model ] )
      in

      (* Function to run if unsat. *)
      let if_unsat () =
        debug tsugi "[%3i] Unsat." k_int in
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
           continue = continue }
      | _ -> loop new_unknown
                  new_unfalsifiable
                  new_falsifiable
                  new_falsifiable_no_model
    in

    loop props [] [] []
         

  let rec next solver trans k invs props new_invs =

    (* Asserting transition relation for k > 0. *)
    if Numeral.(k > zero) then
      (* T[x_k-1, x_k]. *)
      let _ = TransSys.trans_of_bound trans k
              |> Solver.assert_term solver
              |> ignore
      in
      (* Asserting positive literals. *)
      positive_activation k (Solver.assert_term solver) props ; ;

    (* Asserting new invariants from 0 to k. *)
    new_invs
    |> Term.mk_and
    |> Term.bump_and_apply_k
         (Solver.assert_term solver) k ;

    (* Asserting (old) invariants at k. *)
    invs
    |> Term.mk_and
    |> Term.bump_state k
    |> Solver.assert_term solver ;


    (* Merging all the invariants. *)
    let nu_invs = List.rev_append new_invs invs in

    (* Building the continuation for the next iteration. *)
    let continuation = next solver trans Numeral.(k + one) nu_invs in

    (* Splitting falsifiable and unfalsifiable things, and passing the
       continuation. *)
    split_closure
      solver
      trans
      k
      props
      { k = k ;
        unfalsifiable = [] ;
        falsifiable = [] ;
        falsifiable_no_model = [] ;
        continue = continuation }



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

    let _ = 
      match bmc_mode with
      | Base ->
         (* If in base mode assert init. *)
         assert_init solver trans ;
      | Step -> ()
    in

    next solver trans Numeral.zero [] props []



  (* Runs the BMC loop. *)
  let run_bmc bmc_mode trans =

    (* Communicate the result of this iteration to the rest of the
       framework. *)
    let communicate =
      match bmc_mode with
      | Base -> Comm.base trans
      | Step -> Comm.step trans
    in

    (* Launches the next iteration based on the results of the
       previous one. *)
    let launch_next loop =
      match bmc_mode with
      | Base ->
         ( fun { k ; unfalsifiable ; falsifiable_no_model ; continue } ->
           (* In the base case, just continue with the unfalsifiable
              properties. *)
           match unfalsifiable with
           | [] -> ()
           | _  -> continue unfalsifiable (Comm.new_invariants ())
                   |> loop )

      | Step ->
         ( fun { k ; unfalsifiable ; falsifiable_no_model ; continue } ->
           (* In the step case, continue with the falsifiable
              properties. *)
           match falsifiable_no_model with
           | [] -> ()
           | falsified  -> continue falsified (Comm.new_invariants ())
                           |> loop )
    in

    (* BMC loop. *)
    let rec evil_loop trans
                      ({ k ; unfalsifiable ; falsifiable } as bmc_result) =

      (* Communicating. *)
      communicate k unfalsifiable falsifiable ;

      (* Launching next iteration. *)
      launch_next (evil_loop trans) bmc_result
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

