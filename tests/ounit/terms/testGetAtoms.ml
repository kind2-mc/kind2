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
(** The atoms of a term with a long chain of lets.

    An interpolant from a solver is a chain of thousands of nested lets,
    and IC3IA takes its atoms as predicates. The atoms must be those of
    the formula the lets denote, found in a time that grows with the
    size of the chain, not with its square or worse. *)

open OUnit2

let t_int = Type.t_int
let t_bool = Type.t_bool
let var name ty = Var.mk_free_var (HString.mk_hstring name) ty
let v t = Term.mk_var t
let num i = Term.mk_num_of_int i

let sv_a = StateVar.mk_state_var "a" ["test"] t_int
let t_a = Term.mk_var (Var.mk_state_var_instance sv_a Numeral.zero)

(* d_1 = a > 1; d_i = d_(i-1) and a > i in d_n: the atoms are a > i *)
let chain n =
  let d i = var (Printf.sprintf "d%d" i) t_bool in
  let atom i = Term.mk_gt [t_a; num i] in
  let levels =
    List.init n (fun i ->
      let i = i + 1 in
      [d i, (if i = 1 then atom 1 else Term.mk_and [v (d (i - 1)); atom i])])
  in
  Term.mk_let_chain levels (v (d n))

let timed f = let start = Unix.gettimeofday () in let r = f () in r, Unix.gettimeofday () -. start

let test_atoms _ =
  let n = 200 in
  let atoms = Term.get_atoms (chain n) in
  assert_equal ~printer:string_of_int n (Term.TermSet.cardinal atoms) ;
  for i = 1 to n do
    assert_bool (Printf.sprintf "a > %d is an atom" i)
      (Term.TermSet.mem (Term.mk_gt [t_a; num i]) atoms)
  done

(* Twice the lets take less than three times the time: linear, not
   quadratic or cubic *)
let test_linear _ =
  let n = 1000 in
  let t1, t2 = chain n, chain (2 * n) in
  let time t = snd (timed (fun () -> Term.get_atoms t)) in
  let time t = min (time t) (time t) in
  let s1, s2 = time t1, time t2 in
  assert_bool
    (Printf.sprintf "%d lets: %.2f s, %d lets: %.2f s" n s1 (2 * n) s2)
    (s2 < 3. *. s1 +. 0.05)

(* d1 = a + 1; d_i = d_(i-1) + d_(i-1) in d_n > 0: the one atom is a tree
   of 2^n leaves, and is returned with lets for its shared subterms, as
   compact as the chain, and the same formula *)
let test_shared _ =
  let n = 18 in
  let d i = var (Printf.sprintf "e%d" i) t_int in
  let levels =
    List.init n (fun i ->
      let i = i + 1 in
      [d i, (if i = 1 then Term.mk_plus [t_a; num 1]
             else Term.mk_plus [v (d (i - 1)); v (d (i - 1))])])
  in
  let t = Term.mk_let_chain levels (Term.mk_gt [v (d n); num 0]) in
  let atoms = Term.get_atoms t in
  assert_equal ~printer:string_of_int 1 (Term.TermSet.cardinal atoms) ;
  let atom = Term.TermSet.choose atoms in
  let printed = Format.asprintf "%a" Term.pp_print_term atom in
  let input = Format.asprintf "%a" Term.pp_print_term t in
  assert_bool
    (Printf.sprintf "the atom prints in %d characters, the term in %d"
       (String.length printed) (String.length input))
    (String.length printed < 4 * String.length input) ;
  let expand = Term.eval_t (fun flat _ -> Term.construct flat) in
  assert_bool "the atom with its lets substituted is the formula"
    (expand atom == expand t)

let suite =
  "get_atoms" >::: [
    "atoms" >:: test_atoms ;
    "linear" >:: test_linear ;
    "shared" >:: test_shared ;
  ]

let () = run_test_tt_main suite
