(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

module Num = Numeral
module Smt = SMTSolver


(** Asserts some terms from [k] to [k'-1]. *)
let assert_between solver k k' term =
  let rec loop i =
    if Num.(i < k') then (
      Term.bump_state i term |> Smt.assert_term solver ;
      Num.succ i |> loop
    )
  in
  loop k

(** Asserts some terms from [0] to [k-1]. *)
let assert_0_to solver =
  assert_between solver Num.zero

(** Asserts some terms from [1] to [k-1]. *)
let assert_1_to solver =
  assert_between solver Num.one

(** Asserts some new one- and two-state invariant up to [k-1], starting at
  * [0] for one-state invariants,
  * [1] for two-state invariants. *)
let assert_new_invs_to solver k (os,ts) =
  ( match Term.TermSet.elements os with
    | [] -> ()
    | nu -> Term.mk_and nu |> assert_0_to solver k
  ) ;
  ( match Term.TermSet.elements ts with
    | [] -> ()
    | nu -> Term.mk_and nu |> assert_1_to solver k
  )


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)