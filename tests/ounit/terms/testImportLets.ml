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

let timed f = let start = Unix.gettimeofday () in let r = f () in r, Unix.gettimeofday () -. start

(* Imported in the domain that built it, the term is the very term; and
   twice the lets take less than three times the time: the import is
   linear in the length of the chain *)
let test_long_chain _ =
  let n = 2500 in
  let t1, t2 = chain n, chain (2 * n) in
  let time t =
    let t', s = timed (fun () -> Term.import t) in
    assert_bool "the imported term is the term" (t' == t) ;
    s
  in
  let time t = min (time t) (time t) in
  let s1, s2 = time t1, time t2 in
  assert_bool
    (Printf.sprintf "%d lets: %.2f s, %d lets: %.2f s" n s1 (2 * n) s2)
    (s2 < 3. *. s1 +. 0.05)

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
