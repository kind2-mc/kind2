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
(** The evaluation of terms with let bindings.

    [Term.eval_t] evaluates the term of a let binding when the body first
    needs the variable, and keeps its value for the other occurrences. It
    finds the binding of a variable in a context of the variables in
    scope; the value must be that of the innermost binding of the
    variable, the terms of a let being evaluated in the scope around it.
    Folding under a quantifier opens it, adding variables that stand for
    those it binds to the same context. *)

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

let value t =
  Eval.eval_term [] (Model.create 7) t |> Eval.num_of_value |> Numeral.to_int

let assert_value expected t =
  assert_equal ~printer:string_of_int expected (value t)

(* let x = 1 in let y = x + 10 in let x = y + 100 in x + y: the third let
   shadows the first *)
let test_shadowing _ =
  assert_value 122
    (Term.mk_let [x, num 1]
       (Term.mk_let [y, plus [v x; num 10]]
          (Term.mk_let [x, plus [v y; num 100]] (plus [v x; v y]))))

(* let x = 1, y = 2 in let x = y, y = x in 10 * x + y: the terms of a let
   are evaluated in the scope around it, so the second let swaps x and y *)
let test_simultaneous _ =
  assert_value 21
    (Term.mk_let [x, num 1; y, num 2]
       (Term.mk_let [x, v y; y, v x]
          (plus [Term.mk_times [num 10; v x]; v y])))

(* A variable used in several places, inside lets of the body that bind
   other variables, has the value of its binding in each *)
let test_reused _ =
  assert_value 9
    (Term.mk_let [x, plus [num 1; num 2]]
       (plus [v x; Term.mk_let [y, v x] (plus [v x; v y])]))

(* A let in the term of a binding, which shadows a variable of the
   enclosing lets for its body only *)
let test_let_in_bound_term _ =
  assert_value 12
    (Term.mk_let [x, num 1]
       (Term.mk_let [y, Term.mk_let [x, num 10] (plus [v x; num 1])]
          (plus [v x; v y])))

(* Expressions of random nested lets *)
type expr =
  | Num of int
  | Var of int
  | Plus of expr * expr
  | Let of (int * expr) list * expr

(* Random nested lets over few variables, so that lets often shadow one
   another, whose values are those computed here *)
let test_random _ =
  let vars = [| x; y; z; w |] in
  let st = Random.State.make [| 1796 |] in
  let rec term = function
    | Num i -> num i
    | Var i -> v vars.(i)
    | Plus (a, b) -> plus [term a; term b]
    | Let (b, e) -> Term.mk_let (List.map (fun (i, e) -> vars.(i), term e) b) (term e)
  in
  (* [env] gives the value of each variable in scope, innermost first *)
  let rec eval env = function
    | Num i -> i
    | Var i -> List.assoc i env
    | Plus (a, b) -> eval env a + eval env b
    | Let (b, e) -> eval (List.map (fun (i, e) -> i, eval env e) b @ env) e
  in
  (* An expression over the variables in [scope] *)
  let rec expr scope depth =
    match Random.State.int st 4 with
    | _ when depth = 0 ->
      if scope = [] || Random.State.bool st then Num (Random.State.int st 5)
      else Var (List.nth scope (Random.State.int st (List.length scope)))
    | 0 -> Num (Random.State.int st 5)
    | 1 when scope <> [] ->
      Var (List.nth scope (Random.State.int st (List.length scope)))
    | 2 -> Plus (expr scope (depth - 1), expr scope (depth - 1))
    | _ ->
      (* Distinct variables in one let *)
      let b =
        List.init (1 + Random.State.int st 2) (fun _ ->
          Random.State.int st (Array.length vars))
        |> List.sort_uniq compare
        |> List.map (fun i -> i, expr scope (depth - 1))
      in
      Let (b, expr (List.sort_uniq compare (List.map fst b @ scope)) (depth - 1))
  in
  for _ = 1 to 300 do
    let e = expr [] 6 in
    assert_value (eval [] e) (term e)
  done

(* Lets and quantifiers in each other: the variables of the term are the
   free ones, z and w, and none that a let or a quantifier binds *)
let test_quantifiers _ =
  let q = Var.mk_fresh_var t_int in
  let gt a b = Term.mk_gt [a; b] in
  let assert_vars expected t =
    assert_bool
      (Format.asprintf "variables of %a" Term.pp_print_term t)
      (Var.VarSet.equal (Var.VarSet.of_list expected) (Term.vars_of_term t))
  in
  (* forall q. let x = q + z in let y = 5 in x + y > w *)
  assert_vars [z; w]
    (Term.mk_forall [q]
       (Term.mk_let [x, plus [v q; v z]]
          (Term.mk_let [y, num 5] (gt (plus [v x; v y]) (v w)))));
  (* let x = z + 1 in forall q. q > x and exists q. q > w *)
  assert_vars [z; w]
    (Term.mk_let [x, plus [v z; num 1]]
       (Term.mk_and
          [Term.mk_forall [q] (gt (v q) (v x));
           Term.mk_exists [q] (gt (v q) (v w))]));
  (* let x = (exists q. q > z) in let y = w in (x and y > 0): a quantifier
     in a bound term, evaluated when the body needs x *)
  assert_vars [z; w]
    (Term.mk_let [x, Term.mk_exists [q] (gt (v q) (v z))]
       (Term.mk_let [y, v w] (Term.mk_and [v x; gt (v y) (num 0)])))

(* A long chain of lets, each of which refers to the outermost one:
   x_0 = 1 and x_i = x_(i-1) + x_0, so x_n = n + 1. With the context in a
   list, each lookup of x_0 took a time linear in i *)
let test_long_chain _ =
  let n = 20000 in
  let xs = Array.init (n + 1) (fun i -> var (Printf.sprintf "x%d" i)) in
  let levels =
    List.init (n + 1) (fun i ->
      [xs.(i), if i = 0 then num 1 else plus [v xs.(i - 1); v xs.(0)]])
  in
  assert_value (n + 1) (Term.mk_let_chain levels (v xs.(n)))

let suite =
  "evaluation of lets" >::: [
    "shadowing" >:: test_shadowing;
    "simultaneous bindings" >:: test_simultaneous;
    "reused variable" >:: test_reused;
    "let in a bound term" >:: test_let_in_bound_term;
    "random lets" >:: test_random;
    "lets and quantifiers" >:: test_quantifiers;
    "long chain" >:: test_long_chain;
  ]

let () = run_test_tt_main suite
