(* This file is part of the Kind 2 model checker.

   Copyright (c) 2018 by the Board of Trustees of the University of Iowa

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


let assert_context solver premises =
  match SMTSolver.kind solver with
  | `CVC4_SMTLIB -> (
    SMTSolver.assert_term solver premises
  )
  | _ -> ()


let rec get_disjuncts term =
  match Term.destruct term with
  | Term.T.App (s, args) when s == Symbol.s_or ->
     List.map get_disjuncts args |> List.flatten
  | _ -> [term]


let simplify_abduct solver premises term =

  let term = Simplify.simplify_term [] term in
  if SMTSolver.kind solver = `CVC4_SMTLIB then
    (* We have already taken into account the context in assert_context *)
    term
  else (
    let disjuncts = get_disjuncts term in
    SMTSolver.push solver;
    SMTSolver.assert_term solver premises;
    let res = disjuncts |> List.filter (fun dj ->
      let actlit_symb = UfSymbol.mk_fresh_uf_symbol [] (Type.mk_bool ()) in
      let actlit = Term.mk_uf actlit_symb [] in
      SMTSolver.declare_fun solver actlit_symb;
      SMTSolver.assert_term solver (Term.mk_implies [actlit; dj]);
      let res = SMTSolver.check_sat_assuming solver 
        (fun _ -> true) (fun _ -> false) [actlit] in
        SMTSolver.assert_term solver (Term.mk_not actlit);
        res
      )
      |> Term.mk_or
    in

    SMTSolver.pop solver;

    res
  )

let abduce solver forall_vars premises conclusion =

  let impl = Term.mk_implies [premises; conclusion] in

  match forall_vars with
  | [] -> (

    impl
    |> SMTSolver.simplify_term solver
    |> Simplify.remove_ite

  ) 
  | _ -> (

    let forall_term = Term.mk_forall forall_vars impl in

    SMTSolver.get_qe_term solver forall_term
    |> Term.mk_and
    |> SMTSolver.simplify_term solver
    |> Simplify.remove_ite
    
  )


let abduce_simpl solver forall_vars premises conclusion =

  let impl = Term.mk_implies [premises; conclusion] in

  match forall_vars with
  | [] -> (

    impl
    |> SMTSolver.simplify_term solver
    |> simplify_abduct solver premises
    |> Simplify.remove_ite

  ) 
  | _ -> (
    
    assert_context solver premises ;

    let forall_term = Term.mk_forall forall_vars impl in

    let res =
      SMTSolver.get_qe_term solver forall_term
      |> Term.mk_and
      |> SMTSolver.simplify_term solver
    in

    (* Debug.abduction "  Simplifying abductive..."; *)

    res
    |> simplify_abduct solver premises
    |> Simplify.remove_ite
  )

