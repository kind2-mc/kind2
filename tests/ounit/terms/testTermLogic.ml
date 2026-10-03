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
(** The logic of quantified terms.

    The logic of a term has to cover the sorts of all the variables its
    quantifiers bind, including those the body of the quantifier does not
    mention. Otherwise the solver is given a declaration of a sort its logic
    does not have. *)

open OUnit2

let t_bool = Type.t_bool
let t_int = Type.t_int
let t_real = Type.t_real

let sv_a = StateVar.mk_state_var "a" ["test"] t_bool
let t_a = Term.mk_var (Var.mk_state_var_instance sv_a Numeral.zero)

let logic t = TermLib.logic_of_term [] t

let has feature t = TermLib.FeatureSet.mem feature (logic t)

(* forall (x: int; x: bool) (x or a): the bool binder shadows the int one,
   which the body then does not mention (issue #1470) *)
let test_shadowed_binder _ =
  let x_int = Var.mk_fresh_var t_int in
  let x_bool = Var.mk_fresh_var t_bool in
  let t =
    Term.mk_forall [x_int]
      (Term.mk_forall [x_bool] (Term.mk_or [Term.mk_var x_bool; t_a]))
  in
  assert_bool "integer arithmetic" (has TermLib.IA t);
  assert_bool "quantifiers" (has TermLib.Q t)

(* exists (x: real; y: bool) (y and a): a binder the body does not use *)
let test_unused_binder _ =
  let x = Var.mk_fresh_var t_real in
  let y = Var.mk_fresh_var t_bool in
  let t = Term.mk_exists [x; y] (Term.mk_and [Term.mk_var y; t_a]) in
  assert_bool "real arithmetic" (has TermLib.RA t)

(* a => forall (b: bool) exists (i: int) b: an unused binder in a quantifier
   nested in another one, under a connective *)
let test_nested_unused_binder _ =
  let b = Var.mk_fresh_var t_bool in
  let i = Var.mk_fresh_var t_int in
  let t =
    Term.mk_implies
      [t_a; Term.mk_forall [b] (Term.mk_exists [i] (Term.mk_var b))]
  in
  assert_bool "integer arithmetic" (has TermLib.IA t)

let tests =
  "TermLib: logic of quantified terms" >::: [
    "shadowed binder" >:: test_shadowed_binder;
    "unused binder" >:: test_unused_binder;
    "nested unused binder" >:: test_nested_unused_binder;
  ]

let () = run_test_tt_main tests
