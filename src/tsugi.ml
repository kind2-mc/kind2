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
module type In = sig

  (* Creates a positive actlit as a UF. *)
  val positive : Term.t -> UfSymbol.t

  (* Creates a negative actlit as a UF. *)
  val negative : Numeral.t -> Term.t -> UfSymbol.t

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

module Make (Actlit: In) : Out = struct


  (* Turns an actlit (UF) to a term. *)
  let term_of_actlit actlit = Term.mk_uf actlit []


  (* Adds an implication between a positive literal and a property at
   k-1. K must be greater than one (always the case in step). *)
  let positive_activation k list (_, property) =
    (* K must be greater than one. *)
    assert Numeral.(geq k one) ;

    (* Bumping to k-1. *)
    let prop_k_m_one = Term.bump_state Numeral.(k-one) property in

    (* Bulding activation literal. *)
    let actlit = Actlit.positive property |> term_of_actlit in

    (* Building implication. *)
    let impl = Term.mk_or [ Term.mk_not actlit ; prop_k_m_one ] in

    (* Prepending implication to list. *)
    impl :: list


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
  let split_closure solver trans k actlit_fun props { continue } =
    let rec loop unknown unfalsifiable falsifiable falsifiable_no_model =

      let if_sat () =
        (* Get the model. *)
        let model =
          TransSys.vars_of_bounds trans k k
          |> Solver.get_model solver
        in
        let uf_defs = TransSys.uf_defs trans in
        (* Evaluation function. *)
        let eval t = Eval.bool_of_value(Eval.eval_term uf_defs model t) in
        (* Split properties. *)
        let (new_falsifiable, new_unknown) =
          List.partition (fun prop -> eval (snd prop)) unknown
        in
        ( new_unknown,
          unfalsifiable,
          (new_falsifiable, model) :: falsifiable,
          List.concat [new_falsifiable ; falsifiable_no_model ] )
      in

      let if_unsat () =
        ( [], unknown, falsifiable, falsifiable_no_model )
      in

      let (
        new_unknown,
        new_unfalsifiable,
        new_falsifiable,
        new_falsifiable_no_model
      ) =

        (* Building the list of negative activation literals and
         asserting it. *)
        let negative_actlits =
          List.map
            (fun prop -> term_of_actlit (Actlit.negative k (snd prop)))
            unknown
        in

        (* Building the list of positive activation literals in step,
         doing nothing in base. *)
        let positive_actlits = actlit_fun props in

        (* Gathering all the activation literals. *)
        let all_actlits =
          List.rev_append positive_actlits negative_actlits
        in

        (* Check sat assuming with all literals. *)
        Solver.check_sat_assuming solver if_sat if_unsat all_actlits

      in

      match new_unknown with
      | [] -> { k = k ;
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
         

  let rec next solver trans k actlit actlit_split invs props new_invs =

    (* Asserting transition relation for k > 0. *)
    if Numeral.(k > zero) then
      (* T[x_k-1, x_k]. *)
      TransSys.trans_of_bound trans k
      |> Solver.assert_term solver ;

    (* Asserting new invariants from 0 to k. *)
    new_invs
    |> List.iter
         ( fun inv ->
           Term.bump_and_apply_k
             (Solver.assert_term solver) k inv ) ;

    (* Asserting (old) invariants at k. *)
    invs
    |> List.iter
         ( fun inv ->
           Term.bump_state k inv
           |> Solver.assert_term solver
           |> ignore ) ;

    (* Merging new invariants and old ones. *)
    let nu_invs = [new_invs ; invs] |> List.concat in

    (* Constructing a list of implications to assert, declaring
       negative activation literals as side-effect. *)
    props
    |> List.fold_left
         ( fun list prop ->

           (* Building negative activation literal. *)
           let act_lit = Actlit.negative k (snd prop) in

           (* Bumping proposition at k. *)
           let prop_at_k = Term.bump_state k (snd prop) in

           (* Declaring the negative activation literal. *)
           act_lit |> Solver.declare_fun solver |> ignore ;

           (* Building implication. *)
           let impl = Term.mk_or
                        [ Term.mk_not (term_of_actlit act_lit) ;
                          Term.mk_not prop_at_k ]
           in

           (* Adding implication at k for positive literal if in the
            step instance. *)
           actlit k (impl :: list) prop)

         []
    (* Asserting the resulting list of implications as a
       conjunction. *)
    |> (fun list -> Term.mk_and list |> Solver.assert_term solver) ;

    (* Building the continuation for the next iteration. *)
    let continuation =
      next solver trans Numeral.(k + one) actlit actlit_split nu_invs
    in

    (* Splitting falsifiable and unfalsifiable things, and passing the
       continuation. *)
    split_closure
      solver
      trans
      k
      actlit_split
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

    (* Initializing the solver. *)
    (* Implementation.init () *)
    (* |> List.iter (Solver.assert_term solver) ; *)

    (* Declare uninterpreted function symbols *)
    TransSys.iter_state_var_declarations
      trans
      (Solver.declare_fun solver);
    
    (* Define functions *)
    TransSys.iter_uf_definitions
      trans
      (Solver.define_fun solver);

    assert_init solver trans ;

    let actlit_fun, actlit_split_fun =
      match bmc_mode with
      | Base ->
         (fun k list prop -> list), (fun props -> [])
      | Step ->
         positive_activation, positive_activators
    in

    next
      solver trans Numeral.zero actlit_fun actlit_split_fun [] props []



  (* Runs the BMC loop. *)
  let run_bmc bmc_mode trans =

    let rec loop trans { k ;
                         unfalsifiable ;
                         falsifiable ;
                         falsifiable_no_model ;
                         continue } =
      (* Preparing for the next iteration. *)
      continue unfalsifiable []
      |> loop trans
    in

    let evil_loop () =
      (* Unrolling the properties at zero. *)
      let props = (TransSys.props_list_of_bound trans Numeral.zero) in

      (* Building the first continuation and entering the loop. *)
      walk_bmc bmc_mode trans props
      |> loop trans
    in

    evil_loop ()

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

