(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(* The value of a nested array read element by element, as
   [SMTSolver.get_var_values] reads an array whose value is not a constant
   array with stores. Each index used to be built with the index sort of
   the outermost dimension: with bit-vector indices of different widths,
   the inner selects were ill-sorted, and the solver rejected them. *)

open OUnit2
open TestSolverCommon

let ubv w i =
  Term.mk_ubv (Bitvector.num_to_ubv (Numeral.of_int w) (Numeral.of_int i))

let assert_bv expected t =
  assert_equal
    ~printer:(Format.asprintf "%a" Bitvector.pp_print_unsigned_machine_integer)
    (Term.bitvector_of_term expected) (Term.bitvector_of_term t)

(* [Array (_ BitVec outer) (Array (_ BitVec inner) (_ BitVec 3))], with
   [t[1][2] = 5] *)
let check outer inner _ =
  skip_if (solver_missing ()) "no Z3 on PATH" ;
  let elem = Type.mk_array (Type.mk_ubv 3) (Type.mk_ubv inner) in
  let ty = Type.mk_array elem (Type.mk_ubv outer) in
  let name = Printf.sprintf "t_%d_%d" outer inner in
  let sv = StateVar.mk_state_var name ["nested"] ty in
  let v = Var.mk_state_var_instance sv Numeral.zero in
  let element =
    Term.mk_select (Term.mk_select (Term.mk_var v) (ubv outer 1)) (ubv inner 2)
  in
  let bounds = StateVar.StateVarHashtbl.create 1 in
  StateVar.StateVarHashtbl.add bounds sv
    (List.map (fun w ->
       LustreExpr.Fixed (LustreExpr.mk_int_expr (Numeral.of_int (1 lsl w))))
       [outer; inner]) ;
  Flags.Arrays.set_smt true ;
  let solver = new_solver () in
  let model =
    Fun.protect ~finally:(fun () -> SMTSolver.delete_instance solver)
      (fun () ->
        Var.declare_vars (SMTSolver.declare_fun solver) [v] ;
        SMTSolver.assert_term solver (Term.mk_eq [ element ; ubv 3 5 ]) ;
        assert_bool "sat" (SMTSolver.check_sat solver) ;
        SMTSolver.get_var_values solver bounds [v])
  in
  match Var.VarHashtbl.find model v with
  | Model.Map m ->
    assert_equal ~printer:string_of_int
      ((1 lsl outer) * (1 lsl inner)) (Model.MIL.cardinal m) ;
    (* The element is found at its own indices, the outer one first, each
       as a number in [0, 2^w) *)
    assert_bv (ubv 3 5) (Model.MIL.find [1; 2] m) ;
    (* and so is it when the select is evaluated in the model *)
    assert_bv (ubv 3 5) (Simplify.simplify_term_model [] model element)
  | _ -> assert_failure "the array was not read element by element"

let tests = "NestedArrayModel" >::: [
  "outer index narrower than the inner one" >:: check 1 2 ;
  "outer index wider than the inner one" >:: check 3 2 ;
  "indices of the same width" >:: check 2 2 ;
]

let () = run_test_tt_main tests
