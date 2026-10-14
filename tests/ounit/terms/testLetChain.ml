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
(** Chains of let bindings.

    [Term.mk_let_chain] builds a chain of lets with one traversal of each
    term. Terms are hashconsed, so it must return the very term that the
    nested [Term.mk_let] give, with the variables of each let bound in the
    lets after it and in the body, and a variable that two lets bind bound
    by the innermost one in scope.

    The evaluation of a term looks up the terms of its let bindings in a
    context of the variables in scope; the values must be those of the
    nested lets, whatever variables shadow others. *)

open OUnit2

let t_int = Type.t_int

let var name = Var.mk_free_var (HString.mk_hstring name) t_int
let x = var "x"
let y = var "y"
let z = var "z"
let w = var "w"
let v t = Term.mk_var t
let num i = Term.mk_num_of_int i
let plus l = Term.mk_plus l

let sv_a = StateVar.mk_state_var "a" ["test"] t_int
let t_a = Term.mk_var (Var.mk_state_var_instance sv_a Numeral.zero)

let nested levels body =
  List.fold_right (fun b t -> Term.mk_let b t) levels body

let assert_same levels body =
  let chain = Term.mk_let_chain levels body in
  let expected = nested levels body in
  assert_bool
    (Format.asprintf "@[<v>chain:@ %a@ nested lets:@ %a@]"
       Term.pp_print_term chain Term.pp_print_term expected)
    (chain == expected)

let value t =
  Eval.eval_term [] (Model.create 7) t |> Eval.num_of_value |> Numeral.to_int

(* x = 1; y = x + 1; z = x + y in z + a *)
let test_dependent _ =
  assert_same
    [[x, num 1]; [y, plus [v x; num 1]]; [z, plus [v x; v y]]]
    (plus [v z; t_a])

(* Several variables per let, each depending on variables of the lets
   before it, and a variable of the first let used in the body *)
let test_simultaneous _ =
  assert_same
    [[x, num 1; y, num 2]; [z, plus [v x; v y]; w, v y]]
    (plus [v z; v w; v x])

(* x is bound by the first and the third let: the second takes the first,
   and the body the third *)
let test_shadowing _ =
  let levels =
    [[x, num 1]; [y, plus [v x; num 10]]; [x, plus [v y; num 100]]]
  in
  let body = plus [v x; v y] in
  assert_same levels body;
  assert_equal ~printer:string_of_int 122
    (value (Term.mk_let_chain levels body))

(* A term of a binding with a let of its own, which shadows a variable of
   the chain in its body only *)
let test_let_in_bound_term _ =
  let levels =
    [[x, num 1]; [y, Term.mk_let [x, num 10] (plus [v x; num 1])]]
  in
  let body = plus [v x; v y] in
  assert_same levels body;
  assert_equal ~printer:string_of_int 12
    (value (Term.mk_let_chain levels body))

(* A variable no let binds stays free, and an empty chain is the body *)
let test_free _ =
  assert_same [[x, num 1]] (plus [v x; v w]);
  assert_same [] (plus [v x; v w])

(* Expressions of random chains: sums of constants and variables *)
type expr = Num of int | Var of int | Plus of expr * expr

(* Chains of random lets over few variables, so that lets often rebind a
   variable, compared with the nested lets, and their values with those
   the chains have, computed here *)
let test_random _ =
  let vars = [| x; y; z; w |] in
  let st = Random.State.make [| 1795 |] in
  let rec term = function
    | Num i -> num i
    | Var i -> v vars.(i)
    | Plus (a, b) -> plus [term a; term b]
  in
  (* The value of an expression, where [env] gives the value of each
     variable in scope, the innermost binding first *)
  let rec eval env = function
    | Num i -> i
    | Var i -> List.assoc i env
    | Plus (a, b) -> eval env a + eval env b
  in
  (* An expression over the variables in [scope] *)
  let rec expr scope depth =
    if depth = 0 || Random.State.int st 3 = 0 then
      if scope = [] || Random.State.bool st then Num (Random.State.int st 5)
      else Var (List.nth scope (Random.State.int st (List.length scope)))
    else Plus (expr scope (depth - 1), expr scope (depth - 1))
  in
  for _ = 1 to 200 do
    (* The lets, with the bindings of each, and the values of the
       variables in scope after them *)
    let rec chain scope env k =
      if k = 0 then [], scope, env
      else
        (* Distinct variables in one let, whose terms are in the scope of
           the lets before it *)
        let b =
          List.init (1 + Random.State.int st 2) (fun _ ->
            Random.State.int st (Array.length vars))
          |> List.sort_uniq compare
          |> List.map (fun i -> i, expr scope 2)
        in
        let env' = List.map (fun (i, e) -> i, eval env e) b @ env in
        let scope' = List.sort_uniq compare (List.map fst b @ scope) in
        let rest, scope, env = chain scope' env' (k - 1) in
        b :: rest, scope, env
    in
    let lets, scope, env = chain [] [] (1 + Random.State.int st 12) in
    let body = expr scope 3 in
    let levels =
      List.map (List.map (fun (i, e) -> vars.(i), term e)) lets
    in
    assert_same levels (term body);
    assert_equal ~printer:string_of_int (eval env body)
      (value (Term.mk_let_chain levels (term body)))
  done

(* A long chain, which the nested lets take a time quadratic in its
   length to build *)
let test_long _ =
  let n = 3000 in
  let xs = Array.init n (fun i -> var (Printf.sprintf "e%d" i)) in
  let levels =
    List.init n (fun i ->
      [xs.(i), if i = 0 then t_a else plus [v xs.(i - 1); num 1]])
  in
  let t = Term.mk_let_chain levels (v xs.(n - 1)) in
  assert_bool "a chain" (Term.is_let t)

let suite =
  "let chains" >::: [
    "dependent bindings" >:: test_dependent;
    "simultaneous bindings" >:: test_simultaneous;
    "shadowing" >:: test_shadowing;
    "let in a bound term" >:: test_let_in_bound_term;
    "free variables" >:: test_free;
    "random chains" >:: test_random;
    "long chain" >:: test_long;
  ]

let () = run_test_tt_main suite
