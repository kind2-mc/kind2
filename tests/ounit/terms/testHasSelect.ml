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
(** [Term.has_select] tells whether a select occurs in a term, as
    [Term.select_symbols_of_term] would find one, wherever it occurs: in
    an argument, in the term or the body of a let, under a quantifier, in
    an annotated term, or in a subterm shared by several others. *)

open OUnit2

let t_int = Type.t_int
let t_arr = Type.mk_array t_int t_int

let var name ty = Var.mk_free_var (HString.mk_hstring name) ty
let x = var "x" t_int
let y = var "y" t_int
let a = var "a" t_arr
let v t = Term.mk_var t
let num i = Term.mk_num_of_int i
let plus l = Term.mk_plus l
let sel = Term.mk_select (v a) (v x)

let check name t expected =
  let found =
    not (Symbol.SymbolSet.is_empty (Term.select_symbols_of_term t))
  in
  assert_equal ~msg:(name ^ ": select_symbols_of_term") expected found;
  assert_equal ~msg:(name ^ ": has_select") expected (Term.has_select t)

let test_without _ =
  check "variable" (v x) false;
  check "constant" (num 1) false;
  check "application" (plus [v x; v y; num 1]) false;
  check "array variable" (Term.mk_eq [v a; v a]) false;
  check "let" (Term.mk_let [y, plus [v x; num 1]] (plus [v y; v y])) false;
  check "quantifier" (Term.mk_forall [y] (Term.mk_eq [v y; v x])) false

let test_with _ =
  check "top" sel true;
  check "argument" (plus [v x; sel]) true;
  check "nested" (plus [v x; plus [num 1; Term.mk_select (v a) sel]]) true;
  check "let term" (Term.mk_let [y, sel] (plus [v y; num 1])) true;
  check "let body" (Term.mk_let [y, num 1] (plus [v y; sel])) true;
  check "quantifier"
    (Term.mk_exists [y] (Term.mk_eq [Term.mk_select (v a) (v y); v x])) true;
  check "annotated"
    (Term.mk_named_unsafe (Term.mk_eq [sel; v x]) "n" 0) true

let test_shared _ =
  (* A term in which one subterm, holding the select or not, is shared
     2^18 times: visited once, it is answered at once *)
  let rec deep t n = if n = 0 then t else deep (plus [t; t]) (n - 1) in
  check "shared without" (deep (v x) 18) false;
  check "shared with" (deep sel 18) true;
  check "shared with at the end" (plus [deep (v x) 20; sel]) true

let suite =
  "has_select" >::: [
    "without a select" >:: test_without;
    "with a select" >:: test_with;
    "shared subterms" >:: test_shared;
  ]

let () = run_test_tt_main suite
