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
(** Evaluation of equations between arrays in a model.

    An activated node call that takes an array as input passes it through a
    shadow variable, so its transition relation equates two arrays. QE
    generalization in IC3QE evaluates that equation with [Eval], which made
    [Simplify.relation] fail an assertion: it only takes integers, reals and
    bitvectors. Arrays in the model are not evaluated, so an equation between
    them is true if its arguments are the same term, and stays as it is
    otherwise, like an equation between datatype values. *)

open OUnit2

let t_array = Type.mk_array Type.t_int Type.t_int

(* Two state variables of array type and their instances in the current
   state *)
let mk_array_var name =
  let sv = StateVar.mk_state_var name ["test"] t_array in
  Var.mk_state_var_instance sv Numeral.zero

let v_a = mk_array_var "a"
let v_b = mk_array_var "b"
let t_a = Term.mk_var v_a
let t_b = Term.mk_var v_b

(* An array of size 3 with all elements equal to n, as the model holds it *)
let map_of n =
  List.fold_left
    (fun m i -> Model.MIL.add [i] (Term.mk_num_of_int n) m)
    Model.MIL.empty [0; 1; 2]

let model = Model.of_list [ (v_a, Model.Map (map_of 0)); (v_b, Model.Map (map_of 1)) ]

let eval term = Eval.eval_term [] model term

let pp_value ppf v = Term.pp_print_term ppf (Eval.term_of_value v)

let assert_value ~msg expected term =
  assert_equal ~msg ~cmp:Term.equal
    ~printer:(Format.asprintf "%a" Term.pp_print_term)
    expected (eval term |> Eval.term_of_value)

(* a = a is true *)
let test_equation_same_array _ =
  assert_value ~msg:"a = a" Term.t_true (Term.mk_eq [t_a; t_a]);
  assert_value ~msg:"a = a = a" Term.t_true (Term.mk_eq [t_a; t_a; t_a])

(* a = b stays as it is *)
let test_equation_other_array _ =
  let eq = Term.mk_eq [t_a; t_b] in
  assert_value ~msg:"a = b" eq eq;
  let eq3 = Term.mk_eq [t_a; t_b; t_a] in
  assert_value ~msg:"a = b = a" eq3 eq3

(* An equation under a Boolean operator is evaluated as an atom *)
let test_equation_in_conjunction _ =
  let eq = Term.mk_eq [t_a; t_b] in
  let term = Term.mk_and [Term.mk_eq [t_a; t_a]; eq] in
  match eval term with
  | Eval.ValTerm t ->
    assert_equal ~msg:"conjunction" ~cmp:Term.equal
      ~printer:(Format.asprintf "%a" Term.pp_print_term) eq t
  | v ->
    assert_failure (Format.asprintf "unexpected value %a" pp_value v)

let tests =
  "Simplify: equations between arrays in a model" >::: [
    "equation with the same array" >:: test_equation_same_array;
    "equation with another array" >:: test_equation_other_array;
    "equation in a conjunction" >:: test_equation_in_conjunction;
  ]

let () = run_test_tt_main tests
