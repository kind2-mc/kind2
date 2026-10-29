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
(** Values of arrays, as solvers give them: constant arrays with stores.

    [TermLib.canonical_array_value] gives a value a form that is the same
    term for two values of the same array: a store an outer store of the
    same index overrides is dropped, so is a store of the value of the
    constant array, and the stores are in the order of their indices. Over a
    finite index type whose indices the stores cover at least half of, the
    constant array has the most frequent value of the elements: z3 gives the
    array of 1-bit indices whose two elements are 3 as
    (store (store ((as const ..) 5) #b0 3) #b1 3).

    [Simplify] compares two array values by their canonical forms, so an
    equation between two values of the same array is true, however their
    stores are built, and false between values of two different arrays. A
    select from a constant array is its value. *)

open OUnit2

let ubv w n = Term.mk_ubv (Bitvector.num_to_ubv (Numeral.of_int w) (Numeral.of_int n))
let num = Term.mk_num_of_int

let t_int_array = Type.mk_array Type.t_int Type.t_int
let const_int v = Term.mk_const_array t_int_array (num v)

(* An array of 1-bit indices and 4-bit elements *)
let t_bv_array = Type.mk_array (Type.t_ubv 4) (Type.t_ubv 1)
let const_bv v = Term.mk_const_array t_bv_array (ubv 4 v)

let store a i v = Term.mk_store a i v

let pp = Format.asprintf "%a" Term.pp_print_term

let assert_same ~msg ty a b =
  assert_equal ~msg ~cmp:Term.equal ~printer:pp
    (TermLib.canonical_array_value ty a)
    (TermLib.canonical_array_value ty b)

let assert_different ~msg ty a b =
  assert_bool msg
    (not (Term.equal
            (TermLib.canonical_array_value ty a)
            (TermLib.canonical_array_value ty b)))

let test_order _ =
  assert_same ~msg:"stores in either order" t_int_array
    (store (store (const_int 0) (num 1) (num 5)) (num 0) (num 7))
    (store (store (const_int 0) (num 0) (num 7)) (num 1) (num 5))

let test_overridden _ =
  assert_same ~msg:"an overridden store" t_int_array
    (store (store (const_int 0) (num 0) (num 3)) (num 0) (num 7))
    (store (const_int 0) (num 0) (num 7)) ;
  assert_same ~msg:"a store of the default" t_int_array
    (store (const_int 0) (num 2) (num 0))
    (const_int 0)

let test_finite_index _ =
  assert_same ~msg:"every index stored" t_bv_array
    (store (store (const_bv 5) (ubv 1 0) (ubv 4 3)) (ubv 1 1) (ubv 4 3))
    (const_bv 3) ;
  assert_different ~msg:"different arrays" t_bv_array
    (store (const_bv 5) (ubv 1 0) (ubv 4 3))
    (const_bv 3)

let test_different _ =
  assert_different ~msg:"different values at an index" t_int_array
    (store (const_int 0) (num 1) (num 5))
    (store (const_int 0) (num 1) (num 6)) ;
  assert_different ~msg:"different defaults" t_int_array
    (const_int 0) (const_int 1)

(* Two arrays in a model, a = [0 := 7; 1 := 5] and b = [1 := 5], with
   their values in canonical form, as models have them *)
let mk_var name =
  Var.mk_state_var_instance
    (StateVar.mk_state_var name ["test"] t_int_array) Numeral.zero
let v_a = mk_var "a"
let v_b = mk_var "b"
let t_a = Term.mk_var v_a
let t_b = Term.mk_var v_b
let model =
  let canonical t = Model.Term (TermLib.canonical_array_value t_int_array t) in
  Model.of_list [
    (v_a, canonical (store (store (const_int 0) (num 0) (num 7)) (num 1) (num 5))) ;
    (v_b, canonical (store (const_int 0) (num 1) (num 5))) ]

let eval term = Eval.eval_term [] model term

let assert_bool_value ~msg expected term =
  match eval term with
  | Eval.ValBool b -> assert_equal ~msg ~printer:string_of_bool expected b
  | Eval.ValTerm t -> assert_failure (msg ^ ": not a Boolean value: " ^ pp t)
  | _ -> assert_failure (msg ^ ": not a Boolean value")

let test_equations _ =
  (* store(b, 0, 7) builds the stores of b and 0 in another order than a *)
  assert_bool_value ~msg:"a = store(b, 0, 7)" true
    (Term.mk_eq [ t_a ; store t_b (num 0) (num 7) ]) ;
  assert_bool_value ~msg:"a = b" false (Term.mk_eq [ t_a ; t_b ]) ;
  assert_bool_value ~msg:"a = a" true (Term.mk_eq [ t_a ; t_a ])

let test_selects _ =
  let value t =
    match eval t with
    | Eval.ValNum n -> Numeral.to_int n
    | _ -> assert_failure "not a numeral"
  in
  assert_equal ~msg:"a[0]" ~printer:string_of_int 7
    (value (Term.mk_select t_a (num 0))) ;
  assert_equal ~msg:"a[1]" ~printer:string_of_int 5
    (value (Term.mk_select t_a (num 1))) ;
  assert_equal ~msg:"a[2], from the constant array" ~printer:string_of_int 0
    (value (Term.mk_select t_a (num 2)))

(* The equations of the elements of a value, which IC3 constrains a state
   of a counterexample path to, since some solvers do not take an equation
   with a constant array *)
let assert_eqs ~msg expected actual =
  let printer = function
    | None -> "None"
    | Some l -> String.concat "; " (List.map pp l)
  in
  assert_equal ~msg ~printer
    ~cmp:(Option.equal (List.equal Term.equal)) expected actual

let test_element_equations _ =
  let a = Term.mk_var (Var.mk_free_var (HString.mk_hstring "a") t_bv_array) in
  let eq i v = Term.mk_eq [ Term.mk_select a (ubv 1 i); ubv 4 v ] in
  assert_eqs ~msg:"an array of two elements"
    (Some [ eq 0 3; eq 1 5 ])
    (TermLib.array_value_eqs 2 t_bv_array a
       (store (const_bv 5) (ubv 1 0) (ubv 4 3))) ;
  assert_eqs ~msg:"more elements than the limit" None
    (TermLib.array_value_eqs 1 t_bv_array a (const_bv 5)) ;
  (* An array of arrays, of 2 x 2 elements *)
  let t_nested = Type.mk_array t_bv_array (Type.t_ubv 1) in
  let n = Term.mk_var (Var.mk_free_var (HString.mk_hstring "n") t_nested) in
  let inner = store (const_bv 5) (ubv 1 1) (ubv 4 3) in
  let eq i j v =
    Term.mk_eq
      [ Term.mk_select (Term.mk_select n (ubv 1 i)) (ubv 1 j); ubv 4 v ]
  in
  assert_eqs ~msg:"an array of arrays"
    (Some [ eq 0 0 5; eq 0 1 5; eq 1 0 5; eq 1 1 3 ])
    (TermLib.array_value_eqs 4 t_nested n
       (store (Term.mk_const_array t_nested (const_bv 5)) (ubv 1 1) inner)) ;
  assert_eqs ~msg:"an index type that is not finite" None
    (TermLib.array_value_eqs 4 t_int_array t_a (const_int 0))

let tests =
  "Values of arrays: canonical forms and evaluation" >::: [
    "stores in either order" >:: test_order;
    "overridden stores and stores of the default" >:: test_overridden;
    "finite index type" >:: test_finite_index;
    "different arrays" >:: test_different;
    "equations between array values" >:: test_equations;
    "selects from array values" >:: test_selects;
    "equations of the elements of a value" >:: test_element_equations;
  ]

let () = run_test_tt_main tests
