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
(** Testers and selectors of a datatype in the S-expressions a solver
    answers with (see #1561).

    A solver eliminates a variable of a recursive datatype with testers and
    selectors, which are not declared as uninterpreted functions, and can
    leave a quantifier over a variable of the datatype, whose sort it names.
    The driver reads both back as the symbols of the datatype. *)

open OUnit2

let term_of_string s =
  SExprParser.sexp SExprLexer.main (Lexing.from_string s)
  |> GenericSMTLIBDriver.expr_of_string_sexpr

(* datatype L = Nil | Cons (Cons_0: int, Cons_1: L), a constant y of it,
   and a function f over it *)
let l =
  Type.mk_datatype "L"
    [ ("Nil", []); ("Cons", [ Type.t_int; Type.mk_datatype_ref "L" ]) ]

let y = UfSymbol.mk_uf_symbol "y" [] l
let _f = UfSymbol.mk_uf_symbol "f" [ l ] Type.t_int

let y_term = Term.mk_uf y []

let assert_term expected s =
  assert_equal ~cmp:Term.equal ~printer:Term.string_of_term expected
    (term_of_string s)

let test_tester _ =
  assert_term (Term.mk_is_constructor "Cons" y_term) "((_ is Cons) y)"

(* The form of a tester before SMT-LIB 2.6 *)
let test_tester_legacy _ =
  assert_term (Term.mk_is_constructor "Cons" y_term) "(is-Cons y)"

(* A selector has the type of its field, a self-reference the datatype *)
let test_selector _ =
  assert_term (Term.mk_selector "Cons_0" Type.t_int y_term) "(Cons_0 y)" ;
  assert_term (Term.mk_selector "Cons_1" l y_term) "(Cons_1 y)"

(* A variable bound in the term has the datatype its sort names, so that a
   selector applied to it is one *)
let test_bound_variable _ =
  let t =
    term_of_string
      "(exists ((x!0 L)) (and (= (Cons_1 x!0) y) (> (f x!0) (Cons_0 y))))"
  in
  assert_bool (Term.string_of_term t) (Term.is_exists t)

(* An undeclared symbol is reported as itself, not as one of its arguments *)
let test_undeclared _ =
  assert_raises
    (Failure "Undeclared uninterpreted function symbol g in S-expression")
    (fun () -> term_of_string "(g (h y) y)")

let suite =
  "sexpr datatypes" >::: [
    "tester" >:: test_tester ;
    "legacy tester" >:: test_tester_legacy ;
    "selector" >:: test_selector ;
    "bound variable" >:: test_bound_variable ;
    "undeclared" >:: test_undeclared ;
  ]

let () = run_test_tt_main suite
