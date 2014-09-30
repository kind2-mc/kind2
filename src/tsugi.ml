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






(* Helper functions to generate activation literals. *)

let string_of_term term = string_of_int (Term.hash term)

let positive_act_lit term =
  let string =
    String.concat "" [ "pos_" ; string_of_term term ]
  in
  UfSymbol.mk_uf_symbol string [] (Type.mk_bool ())

let negative_act_lit term k =
  let string =
    String.concat
      ""
      [ "neg_" ; string_of_term term ; "_at_" ; string_of_int (Numeral.to_int k) ]
  in
  UfSymbol.mk_uf_symbol string [] (Type.mk_bool ())

let term_of_act_lit lit = Term.mk_uf lit []


(* Asserts init at zero. *)
let assert_init solver trans =
  TransSys.init_of_bound trans Numeral.zero
  |> Solver.assert_term solver
  |> ignore

(* Simple split for Base. *)
let split_closure solver trans props { k ; continue } =  
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
      new_unknown, new_unfalsifiable, new_falsifiable, new_falsifiable_no_model
    ) = 
      (* Building the list of all the negative literals. *)
      List.map (fun prop -> term_of_act_lit (negative_act_lit (snd prop) k)) unknown
      (* Check-sat-assuming the activation literals. *)
      |> Solver.check_sat_assuming solver if_sat if_unsat
    in

    match new_unknown with
    | [] -> {
      k = k ;
      unfalsifiable = new_unfalsifiable ;
      falsifiable = new_falsifiable ;
      falsifiable_no_model = new_falsifiable_no_model ;
      continue = continue
    }
    | _ ->
       loop new_unknown new_unfalsifiable new_falsifiable new_falsifiable_no_model
  in

  loop props [] [] []
        

let rec next solver trans k invs props new_invs =

  debug tsugi
    "Running next for k = %i." (Numeral.to_int k)
  in

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

  (* Declaring new negative activation literals and asserting the activation. *)
  props
  |> List.iter
       ( fun prop -> let act_lit = negative_act_lit (snd prop) k in
                     let prop_at_k = Term.bump_state k (snd prop) in
                     
                     act_lit |> Solver.declare_fun solver |> ignore ;

                     Term.mk_or
                       [ Term.mk_not (term_of_act_lit act_lit) ; (Term.mk_not prop_at_k) ]
                     |> Solver.assert_term solver
                     |> ignore ) ;

  (* Splitting falsifiable and unfalsifiable things, and return a continuation. *)
  split_closure
    solver trans props {
      k = k ;
      unfalsifiable = [] ;
      falsifiable = [] ;
      falsifiable_no_model = [] ;
      continue =
        (next solver trans Numeral.(k + one) nu_invs)
    }



(* A single BMC iteration, starts at k=0 and returns a continuation. *)
let walk_bmc trans invs props =

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

  next solver trans Numeral.zero invs props []



(* Runs the BMC loop. *)
let run_bmc trans invs =

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
    walk_bmc trans invs (TransSys.props_list_of_bound trans Numeral.zero)
    |> loop trans
  in

  evil_loop ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

