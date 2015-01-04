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
open SMTExpr


(* Use configured SMT solver *)
module Solver = SolverMethods.Make(SMTSolver.Make(SMTLIBSolver))


(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)


(* Solver instance if created *)
let ref_solver = ref None

let interp solver trans_sys k =
  
  Event.log
    L_info
    "Interpolating at step ";
  
  let rec trans i hi acc =
    if i >= hi then
      acc
    else
      trans (i+1) hi ((TransSys.trans_of_bound trans_sys (Numeral.of_int i)) :: acc)
  in

  let rec props i hi acc = 
    if i >= hi then
      acc
    else
      props (i+1) hi ((TransSys.props_of_bound trans_sys (Numeral.of_int i)) :: acc)
  in


  let rec interp i r_i = 
    
    if i > k then () else (

      Solver.push solver;

      let a = Term.mk_and (r_i :: trans 1 i []) in
      let negprops = Term.negate (Term.mk_and (props i k [])) in
      let b = Term.mk_and (negprops :: trans i k []) in
      
      let n1 = Solver.assert_named_term_wr solver a in
      let n2 = Solver.assert_named_term_wr solver b in
      if Solver.check_sat solver then (
        Event.log
          L_info
          "Reached end";
        ()
      )
      else (
        Event.log
          L_info
          "Found interpolant";
        let p = Solver.get_interpolants solver [ArgString n1; ArgString n2] in
        
        Solver.pop solver;
        interp (i+1) (Term.mk_or [p;r_i])
      )
    )

  in

  interp 2 (TransSys.init_of_bound trans_sys Numeral.zero)
;;


let on_exit _ =

  (* Delete solver instance if created. *)
  (try
      match !ref_solver with
      | None -> ()
      | Some solver ->
         Solver.delete_solver solver |> ignore ;
         ref_solver := None
    with
    | e -> 
       Event.log L_error
                 "Error deleting solver_init: %s" 
                 (Printexc.to_string e))

(* Entry point *)
let main trans_sys =

  Flags.set_smtsolver 
    `SMTInterpol_SMTLIB
    (Flags.smtinterpol_bin ());

  Event.log
    L_info
    "Starting interpolator";
  
  Stat.start_timer Stat.bmc_total_time;
  
  (* Determine logic for the SMT solver *)
  let logic = `QF_UFLIA in

  Event.log
    L_info
    "Creating solver instance";
  
  (* Create solver instance *)
  let solver = 
    Solver.new_solver ~produce_proofs:true logic
  in
  
  (* Create a reference for the solver. Only used in on_exit. *)
  ref_solver := Some solver;
  
  (* Declare uninterpreted function symbols *)
  TransSys.iter_state_var_declarations
    trans_sys
    (Solver.declare_fun solver);
  
  (* Define functions *)
  TransSys.iter_uf_definitions
    trans_sys
    (Solver.define_fun solver);

  (* Assert initial state constraint *)
  Solver.assert_term solver (TransSys.init_of_bound trans_sys Numeral.zero);

  Event.log
    L_info
    "Calling main interpolation loop";
  
  (* Enter the bounded model checking loop *)
  interp 
    solver 
    trans_sys 
    5
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
