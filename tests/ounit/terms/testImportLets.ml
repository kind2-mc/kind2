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
(** Importing a term with a long chain of lets.

    A term an engine receives from another is imported into the
    hashcons table by rebuilding it bottom up. An invariant a solver
    computed is a chain of thousands of nested lets, and the import must
    rebuild each node once, not the body of every let once per let
    above it. Imported in the domain that built it, a term is the very
    term it was. *)

open OUnit2

let t_int = Type.t_int
let var name = Var.mk_free_var (HString.mk_hstring name) t_int
let v t = Term.mk_var t
let num i = Term.mk_num_of_int i
let plus l = Term.mk_plus l

let sv_a = StateVar.mk_state_var "a" ["test"] t_int
let t_a = Term.mk_var (Var.mk_state_var_instance sv_a Numeral.zero)

(* d_1 = a + 1; d_i = d_(i-1) + 1 in d_n + d_1 *)
let chain n =
  let d i = var (Printf.sprintf "d%d" i) in
  let levels =
    List.init n (fun i ->
      let i = i + 1 in
      [d i, (if i = 1 then plus [t_a; num 1] else plus [v (d (i - 1)); num 1])])
  in
  Term.mk_let_chain levels (plus [v (d n); v (d 1)])

let test_long_chain _ =
  let n = 5000 in
  let t = chain n in
  let start = Unix.gettimeofday () in
  let t' = Term.import t in
  let elapsed = Unix.gettimeofday () -. start in
  assert_bool
    (Printf.sprintf "importing %d nested lets took %.1f s" n elapsed)
    (elapsed < 10.) ;
  assert_bool "the imported term is the term" (t' == t)

let test_quantifier _ =
  let x = var "x" in
  let t = Term.mk_forall [x] (Term.mk_leq [v x; t_a]) in
  assert_bool "the imported term is the term" (Term.import t == t)

let suite =
  "import lets" >::: [
    "long chain" >:: test_long_chain ;
    "quantifier" >:: test_quantifier ;
  ]

let () = run_test_tt_main suite
