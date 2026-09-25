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
(** Merging collections of invariants.

    [Invs.merge] keeps the one-state and the two-state invariants of both of
    its arguments, each in its own table. It used to start the two-state table
    of the result from the one-state invariants of the second argument, which
    lost the two-state invariants of the first. *)

open OUnit2

let mk_sv name = StateVar.mk_state_var name ["test"] Type.t_bool

(* A one-state invariant over x, and a two-state one relating y to its
   previous value *)
let sv_x = mk_sv "x"
let sv_y = mk_sv "y"
let at sv offset = Term.mk_var (Var.mk_state_var_instance sv offset)
let os_inv = at sv_x Numeral.zero
let ts_inv = Term.mk_implies [at sv_y Numeral.(~- one); at sv_y Numeral.zero]
let cert inv = (1, inv)

let invs ~os ~ts =
  let res = Invs.empty () in
  List.iter (fun inv -> Invs.add_os res inv (cert inv)) os ;
  List.iter (fun inv -> Invs.add_ts res inv (cert inv)) ts ;
  res

let printer set =
  Term.TermSet.elements set |> List.map Term.string_of_term |> String.concat ", "

let check ~os ~ts invs =
  assert_equal ~cmp:Term.TermSet.equal ~printer
    (Term.TermSet.of_list os) (Invs.get_os invs) ;
  assert_equal ~cmp:Term.TermSet.equal ~printer
    (Term.TermSet.of_list ts) (Invs.get_ts invs)

let tests = "Invs.merge" >::: [
  "keeps the two-state invariants of the first argument" >:: (fun _ ->
    Invs.merge (invs ~os:[] ~ts:[ts_inv]) (invs ~os:[] ~ts:[])
    |> check ~os:[] ~ts:[ts_inv]);
  "keeps the one-state invariants of the second argument one-state" >:: (fun _ ->
    Invs.merge (invs ~os:[] ~ts:[]) (invs ~os:[os_inv] ~ts:[])
    |> check ~os:[os_inv] ~ts:[]);
  "keeps both kinds from both arguments" >:: (fun _ ->
    Invs.merge (invs ~os:[os_inv] ~ts:[]) (invs ~os:[] ~ts:[ts_inv])
    |> check ~os:[os_inv] ~ts:[ts_inv]);
]

let _ = run_test_tt_main tests
