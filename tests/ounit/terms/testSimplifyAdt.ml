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
(** Evaluation of datatype testers and selectors in a model.

    A selector applied to a value built with its constructor evaluates to the
    field, as a numeral when the field is one: the integer invariant
    generator evaluates candidate terms such as [- (A_0 m)] with [Eval] and
    reads the result as a numeral, which it is not if the field comes back
    as an opaque atom (the product "(* (- 1) 0)" then reaches
    [Eval.num_of_value]). Applied to a value built with another constructor,
    a selector has no value and stays as it is. *)

open OUnit2

let t_int = Type.t_int

(* datatype T = A (v: int) | B (i: int), with its constructors as the
   uninterpreted functions named after them, as LustreNodeGen builds them *)
let t_T = Type.mk_datatype "T" [ ("A", [t_int]); ("B", [t_int]) ]
let uf_A = UfSymbol.mk_uf_symbol "A" [t_int] t_T
let uf_B = UfSymbol.mk_uf_symbol "B" [t_int] t_T
let mk_A n = Term.mk_uf uf_A [Term.mk_num_of_int n]
let mk_B n = Term.mk_uf uf_B [Term.mk_num_of_int n]

(* The selector of the field of A, and the tester of A *)
let sel_A_0 t = Term.mk_selector "A_0" t_int t
let is_A t = Term.mk_is_constructor "A" t

(* A state variable of type T and its instance in the current state *)
let sv_m = StateVar.mk_state_var "m" ["test"] t_T
let v_m = Var.mk_state_var_instance sv_m Numeral.zero
let t_m = Term.mk_var v_m

let model_where_m_is value = Model.of_list [ (v_m, Model.Term value) ]

let eval model term = Eval.eval_term [] model term

let assert_num ~msg expected model term =
  (* Numerals and terms are compared with their own equality: the
     polymorphic comparison of [assert_equal] raises on them *)
  assert_equal ~msg ~cmp:Numeral.equal ~printer:Numeral.string_of_numeral
    (Numeral.of_int expected) (eval model term |> Eval.num_of_value)

(* A_0 m with m = A 5 is 5 *)
let test_selector_of_matching_value _ =
  assert_num ~msg:"the field" 5 (model_where_m_is (mk_A 5)) (sel_A_0 t_m)

(* The field is a numeral of the normal form, so arithmetic over it is
   carried out: - (A_0 m) with m = A 0 is 0, not the product "(* (- 1) 0)" *)
let test_negated_selector_is_a_numeral _ =
  assert_num ~msg:"minus the field" 0
    (model_where_m_is (mk_A 0)) (Term.mk_minus [sel_A_0 t_m]);
  assert_num ~msg:"minus the field" (-5)
    (model_where_m_is (mk_A 5)) (Term.mk_minus [sel_A_0 t_m]);
  assert_num ~msg:"the field plus one" 6
    (model_where_m_is (mk_A 5))
    (Term.mk_plus [sel_A_0 t_m; Term.mk_num_of_int 1])

(* A_0 m with m = B 6 has no value: it stays the selector applied to B 6 *)
let test_selector_of_other_constructor_stays _ =
  let model = model_where_m_is (mk_B 6) in
  match eval model (sel_A_0 t_m) with
  | Eval.ValTerm t ->
    assert_equal ~msg:"the selector applied to the value" ~cmp:Term.equal
      ~printer:(Format.asprintf "%a" Term.pp_print_term)
      (sel_A_0 (mk_B 6)) t
  | _ -> assert_failure "a selector applied to another constructor has a value"

(* A tester evaluates to a Boolean either way *)
let test_tester _ =
  assert_equal ~msg:"A is A" true
    (eval (model_where_m_is (mk_A 5)) (is_A t_m) |> Eval.bool_of_value);
  assert_equal ~msg:"B is not A" false
    (eval (model_where_m_is (mk_B 6)) (is_A t_m) |> Eval.bool_of_value)

let tests =
  "Simplify: datatype testers and selectors in a model" >::: [
    "selector of a matching value" >:: test_selector_of_matching_value;
    "negated selector is a numeral" >:: test_negated_selector_is_a_numeral;
    "selector of another constructor stays" >::
      test_selector_of_other_constructor_stays;
    "tester" >:: test_tester;
  ]

let () = run_test_tt_main tests
