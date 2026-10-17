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
(** Let bindings in the S-expressions a solver answers with.

    A solver writes a formula with shared subterms, an interpolant or a
    model value, as a chain of nested lets, one binding each, thousands
    long. The driver builds the chain at once, with the bindings grouped
    into as few lets as their dependencies allow, so the terms must be
    the ones the nested lets denote, whatever symbols the lets shadow or
    take from their own let, and a long chain must take a time that does
    not grow with the square of its length. *)

open OUnit2

let term_of_string s =
  SExprParser.sexp SExprLexer.main (Lexing.from_string s)
  |> GenericSMTLIBDriver.expr_of_string_sexpr

let value t =
  Eval.eval_term [] (Model.create 7) t |> Eval.num_of_value |> Numeral.to_int

let assert_value expected s =
  let t = term_of_string s in
  assert_equal ~printer:string_of_int
    ~msg:(Format.asprintf "%s gives %a" s Term.pp_print_term t)
    expected (value t)

(* Bindings that depend on the lets before them are regrouped by level *)
let test_dependent _ =
  assert_value 4 "(let ((a 1)) (let ((b 2)) (let ((c (+ a b))) (+ c a))))"

(* A symbol bound twice: the second let takes the first binding, the body
   the third *)
let test_shadowing _ =
  assert_value 5 "(let ((a 1)) (let ((b (+ a 1))) (let ((a 3)) (+ a b))))"

(* A binding takes a symbol from the enclosing scope that its own let
   binds: the bindings of a let are simultaneous *)
let test_own_let _ =
  assert_value 3 "(let ((a 1)) (let ((a (+ a 1)) (b a)) (+ a b)))"

(* A let with several independent bindings, and one with several
   bindings on them *)
let test_simultaneous _ =
  assert_value 9
    "(let ((a 1) (b 2)) (let ((c (+ a b)) (d (* a b))) (+ c d (* 2 b))))"

(* A chain of [n] lets, each binding [d_i] to a term of [x]: one let, as
   the bindings are independent, or if [dependent] to [d_(i-1)]: one let
   per binding *)
let chain ~dependent n =
  let buf = Buffer.create (64 * n) in
  Buffer.add_string buf "(let ((d1 1)) " ;
  for i = 2 to n do
    Buffer.add_string buf
      (if dependent then Printf.sprintf "(let ((d%d (+ d%d 1))) " i (i - 1)
       else Printf.sprintf "(let ((d%d %d)) " i i)
  done ;
  Buffer.add_string buf (Printf.sprintf "(+ d%d d1)" n) ;
  Buffer.add_string buf (String.make n ')') ;
  Buffer.contents buf

(* The bytes [f] allocates: a measure of its work that does not depend on
   the machine, unlike its time *)
let allocated f =
  let before = Gc.allocated_bytes () in
  let r = f () in
  r, Gc.allocated_bytes () -. before

(* Independent bindings are regrouped into one let *)
let test_independent _ =
  let n = 5000 in
  let t = term_of_string (chain ~dependent:false n) in
  (match Term.node_of_term t with
   | Term.T.Let (_, bound) ->
     assert_equal ~printer:string_of_int ~msg:"bindings of the one let"
       n (List.length bound)
   | _ -> assert_failure "not a let") ;
  assert_equal ~printer:string_of_int (n + 1) (value t)

(* A chain of dependent bindings is converted with a work that grows with
   its length, not with its square: twice the lets allocate less than
   three times the bytes (a quadratic conversion allocates four times) *)
let test_dependent_chain _ =
  let n = 2500 in
  let s1, s2 = chain ~dependent:true n, chain ~dependent:true (2 * n) in
  let _, a1 = allocated (fun () -> term_of_string s1) in
  let t2, a2 = allocated (fun () -> term_of_string s2) in
  assert_bool
    (Printf.sprintf "%d lets: %.0f MB, %d lets: %.0f MB"
       n (a1 /. 1e6) (2 * n) (a2 /. 1e6))
    (a2 < 3. *. a1 +. 1e6) ;
  assert_equal ~printer:string_of_int (2 * n + 1) (value t2)

let suite =
  "sexpr lets" >::: [
    "dependent" >:: test_dependent ;
    "shadowing" >:: test_shadowing ;
    "own let" >:: test_own_let ;
    "simultaneous" >:: test_simultaneous ;
    "independent" >:: test_independent ;
    "dependent chain" >:: test_dependent_chain ;
  ]

let () = run_test_tt_main suite
