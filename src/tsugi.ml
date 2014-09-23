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

(* Type returned by a single iteration of bmc. *)
type walk_bmc_result = {
  (* K corresponding to this result. *)
  k : Numeral.t ;
  (* Properties the negation of which is unsat at k. *)
  unsat_at_k : properties ;
  (* Properties the negation of which is sat at k, with models. *)
  sat_at_k : cexs ;
  (* Properties the negation of which is sat at k, no models. *)
  sat_no_model : properties ;
  (* Continuation for the next bmc iteration. *)
  continue : properties -> invariants -> walk_bmc_result
}

(* Input signature for the Make functor. *)
module type BmcFunctions =
sig

  (* Initializes the solver. Typically base would assert base while
     step would do nothing. *)
  val init : unit -> Term.t list

  (* Handles the result of the BMC check for this k, and returns
     the new invariants of the system. *)
  val stage_next :
    TransSys.t -> Numeral.t ->
    properties -> cexs -> invariants

end

(* Output signature of the Make functor. *)
module type S =
sig

  (* A single BMC iteration, starts at k=0 and returns a continuation. *)
  val walk_bmc :
    TransSys.t -> invariants -> properties -> walk_bmc_result

  (* Runs the BMC loop. *)
  val run_bmc :
    TransSys.t -> invariants -> properties -> unit

end

(* Functor to create a generic BMC. *)
module Make (Implementation: BmcFunctions) (Slvr: SMTSolver.S) : S =
struct

  module Solver = SolverMethods.Make (Slvr)

  let rec next solver trans k invs props new_invs =

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

    let nu_invs = [new_invs ; invs] |> List.concat in

    (* Returning result and continuation. *)
    { k = k ;
      unsat_at_k = [] ;
      sat_at_k = [] ;
      sat_no_model = [] ;
      continue =
        next solver trans Numeral.(k + one) nu_invs }



  (* A single BMC iteration, starts at k=0 and returns a continuation. *)
  let walk_bmc trans invs props =

    (* Creating solver. *)
    let solver =
      TransSys.get_logic trans |> Solver.new_solver
    in

    (* Initializing the solver. *)
    Implementation.init ()
    |> List.iter (Solver.assert_term solver) ;

    next solver trans Numeral.zero invs props []



  (* Runs the BMC loop. *)
  let run_bmc trans invs props =

    let rec loop trans { k            ;
                         unsat_at_k   ;
                         sat_at_k     ;
                         sat_no_model ;
                         continue     } =
      (* Preparing for the next iteration. *)
      Implementation.stage_next trans k unsat_at_k sat_at_k
      |> continue sat_no_model
    in

    let evil_loop =
      walk_bmc trans invs props
      |> loop trans
    in

    ()

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

