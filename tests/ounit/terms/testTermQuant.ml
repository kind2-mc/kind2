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
(** Folding over quantified terms.

    [Term.eval_t ~fail_on_quantifiers:false] folds a term whose subterms may be
    quantified. Folding under a quantifier opens it, replacing the variables it
    binds by variables that stand for them, so that the folded function only
    ever meets free variables. *)

open OUnit2

let t_bool = Type.t_bool
let t_int = Type.t_int

(* A state variable, and the variable for its instance in the current state *)
let mk_sv name ty =
  StateVar.mk_state_var name ["test"] ty

let sv_x = mk_sv "x" t_bool
let v_x = Var.mk_state_var_instance sv_x Numeral.zero
let t_x = Term.mk_var v_x

let sv_a = mk_sv "a" (Type.mk_array t_bool t_int)
let v_a = Var.mk_state_var_instance sv_a Numeral.zero
let t_a = Term.mk_var v_a

(* forall (b: bool) b -- the body is the bound variable and nothing else *)
let bare_bound_body () =
  let b = Var.mk_fresh_var t_bool in
  Term.mk_forall [b] (Term.mk_var b)

(* forall (b: bool) (b or x) *)
let bound_and_free () =
  let b = Var.mk_fresh_var t_bool in
  Term.mk_forall [b] (Term.mk_or [Term.mk_var b; t_x])

(* forall (b1: bool) forall (b2: bool) b2 -- binds at depth 2 as well as 1 *)
let nested_bound_body () =
  let b1 = Var.mk_fresh_var t_bool in
  let b2 = Var.mk_fresh_var t_bool in
  Term.mk_forall [b1] (Term.mk_forall [b2] (Term.mk_var b2))

(* forall (i: int) a[i] *)
let bound_index () =
  let i = Var.mk_fresh_var t_int in
  Term.mk_forall [i] (Term.mk_select t_a (Term.mk_var i))

(* A quantifier whose body is a bare bound variable used to fail an assertion
   in Ltree.fold: nothing was folded for the variable, so the fold ended with
   an empty result stack. *)
let test_bare_bound_variable _ =
  let t = bare_bound_body () in
  assert_equal ~msg:"no variables of its own" true
    (Var.VarSet.is_empty (Term.vars_of_term t));
  assert_equal ~msg:"no state variables" true
    (StateVar.StateVarSet.is_empty (Term.state_vars_of_term t))

(* The variables a quantifier binds are not variables of the term it occurs
   in; the ones it does not bind are. *)
let test_bound_variables_are_not_free _ =
  let t = bound_and_free () in
  (* Compared as sets: these are hash-consed, so the polymorphic comparison
     [assert_equal] would otherwise use raises on them *)
  assert_equal ~msg:"exactly the free variable" true
    (Var.VarSet.equal (Var.VarSet.singleton v_x) (Term.vars_of_term t));
  assert_equal ~msg:"exactly the free state variable" true
    (StateVar.StateVarSet.equal
      (StateVar.StateVarSet.singleton sv_x) (Term.state_vars_of_term t))

(* Folding a term twice must give the same answer. Opening a binder with a
   variable made fresh each time would not: the two folds would report
   different variables for the same term. *)
let test_folding_is_deterministic _ =
  let t = bound_and_free () in
  assert_equal ~msg:"same variables both times" true
    (Var.VarSet.equal (Term.vars_of_term t) (Term.vars_of_term t));
  let u = bound_index () in
  assert_equal ~msg:"same select terms both times" true
    (Term.TermSet.equal (Term.select_terms u) (Term.select_terms u))

(* Passing over a bound variable without folding a value for it left the
   result stack short, and the enclosing application was rebuilt without that
   argument -- here, a select of an array with no index. *)
let test_application_arity_is_kept _ =
  let selects = Term.select_terms (bound_index ()) in
  assert_equal ~msg:"one select" 1 (Term.TermSet.cardinal selects);
  let s = Term.TermSet.choose selects in
  assert_equal ~msg:"select of an array at an index" 2
    (List.length (Term.node_args_of_term s))

(* A variable standing for a bound one belongs to the domain that made it.

   The table taking a type and a binding depth to one of these is copied when
   a domain splits. A shallow copy of a table whose values are themselves
   tables goes on sharing the inner ones, so a domain could be handed a
   variable another domain had made and had registered only there. Not
   knowing it for a binder variable, it would report it among the variables of
   the term it was folding. *)
let test_binder_variables_are_per_domain _ =
  (* The parent folds at depth 1, so the tables are not empty when a domain
     splits from it *)
  let _ = Term.vars_of_term (bare_bound_body ()) in
  (* One domain folds at depth 2 *)
  let a = Domain.spawn (fun () -> Term.vars_of_term (nested_bound_body ())) in
  assert_equal ~msg:"no variables of its own, in the domain that split first"
    true (Var.VarSet.is_empty (Domain.join a));
  (* A second domain folds at the same depth. If it were handed the first
     domain's variable it would not know it for a binder variable. *)
  let b = Domain.spawn (fun () ->
    let vars = Term.vars_of_term (nested_bound_body ()) in
    let v = Var.mk_binder_var t_bool 2 in
    (Var.VarSet.is_empty vars, Var.is_binder_var v))
  in
  let no_vars, recognised = Domain.join b in
  assert_equal ~msg:"a binder variable is known for one in its own domain"
    true recognised;
  assert_equal ~msg:"so it is not reported among the variables of the term"
    true no_vars

(* A quantifier is still refused when the caller asks for it to be. *)
let test_fail_on_quantifiers _ =
  let t = bare_bound_body () in
  assert_raises (Invalid_argument "Ltree.fold : quantified term")
    (fun () ->
      Term.eval_t (fun _ _ -> ()) t)

let tests =
  "Term: folding over quantified terms" >::: [
    "body is a bare bound variable" >:: test_bare_bound_variable;
    "bound variables are not free" >:: test_bound_variables_are_not_free;
    "folding is deterministic" >:: test_folding_is_deterministic;
    "application arity is kept" >:: test_application_arity_is_kept;
    "binder variables are per domain" >:: test_binder_variables_are_per_domain;
    "quantifiers still refused when asked" >:: test_fail_on_quantifiers;
  ]

let () = run_test_tt_main tests
