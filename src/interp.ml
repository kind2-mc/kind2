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
open Actlit


(* Use configured SMT solver *)
module Solver = SolverMethods.Make(SMTSolver.Make(SMTLIBSolver))


(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)


(* Solver instance if created *)
let ref_solver = ref None

let interp solver trans_sys =

  (* Invariants if the system at 0. *)
  let invariants =
    TransSys.invars_of_bound trans_sys Numeral.zero
  in
  
  
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


  let rec interp i k r_i interpolants = 
    
    if i > k then interpolants else (
      
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
        interpolants
      )
      else (
        Event.log
          L_info
          "Found interpolant";
        let p = Solver.get_interpolants solver [ArgString n1; ArgString n2] in
        
        Solver.pop solver;
        interp (i+1) k (Term.mk_or [p;r_i]) (p :: interpolants)
      )
    )

  in
  
  let rec aux k acc = 
    if k > Flags.interp_max () then
      acc 
    else
      aux (k+1) ((interp 2 k (TransSys.init_of_bound trans_sys Numeral.zero) []) @ acc)
  in
  
  aux 2 []  
;;


let on_exit _ =
  
  InvGenGraph.OneState.no_more_lsd ();


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

  Event.log
    L_info
    "Starting interpolator";
  
  Stat.start_timer Stat.bmc_total_time;
  
  (* Determine logic for the SMT solver *)
  let logic = `QF_UFLIA in

  let tmp = Flags.smtsolver () in

  Flags.set_smtsolver `Smtinterpol_SMTLIB "java";

  assert (Flags.smtsolver () = `Smtinterpol_SMTLIB);
  
  (* Create solver instance *)
  let solver = 
    Solver.new_solver ~produce_proofs:true logic
  in

  Flags.set_smtsolver tmp "z3";
  
  (* Create a reference for the solver. Only used in on_exit. *)
  ref_solver := Some solver;
  
  
  (* Getting properties. *)
  let unknowns =
    (TransSys.props_list_of_bound trans_sys Numeral.zero)
  in


  (* Declaring positive actlits. *)
  List.iter
    (fun (_, prop) ->
     generate_actlit prop
     |> Solver.declare_fun solver)
    unknowns ;

  (* Defining uf's and declaring variables. *)
  TransSys.init_define_fun_declare_vars_of_bounds
    trans_sys
    (Solver.define_fun solver)
    (Solver.declare_fun solver)
    Numeral.(~- one) (Numeral.of_int (Flags.interp_max ()))  ;
  

  (* Asserting init. *)
  TransSys.init_of_bound trans_sys Numeral.zero
  |> Solver.assert_term solver
  |> ignore ;


  (* Enter the bounded model checking loop *)
  let candidates = interp 
                     solver 
                     trans_sys 
  in

  let system_candidates =
    InvGenGraph.OneState.mine_system
      true true true trans_sys
  in

  List.length candidates
  |> Event.log L_info "Found %i interpolants:";
  
  List.iter (
      fun t -> Event.log L_info "%s" (Term.string_of_term t)
    ) candidates;


  let invariants', ignore' =
    InvGenGraph.OneState.mine_terms_run
      trans_sys Term.TermSet.empty (Numeral.of_int 10) candidates system_candidates
  in

  (* Bla. *)
  Term.TermSet.cardinal invariants'
  |> Event.log L_info "Found %i invariants: ";

  List.iter (
      fun t -> Event.log L_info "%s" (Term.string_of_term t)
    ) (Term.TermSet.elements invariants');
    
    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
