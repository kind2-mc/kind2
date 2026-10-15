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
(** The case split of atoms over variables of enumeration sorts.

    kmoxi prints the invariant of a certificate with every atom that uses a
    variable of an enumeration sort other than in an equation with its
    values written by cases over the values of these variables, since the
    engines take such a value for the integer that encodes it
    ([MoxiResults.split_enum_atoms]). The other variables of the atom are
    kept in each case: they used to be evaluated at the defaults of their
    types, and [n = c] was split into [c = red]. *)

open OUnit2

let color = Type.mk_enum "TestColor" [ "test_red" ; "test_green" ; "test_blue" ]

let mk_var name ty =
  Var.mk_state_var_instance (StateVar.mk_state_var name ["test"] ty)
    Numeral.zero

let v_c = mk_var "c" color
let v_n = mk_var "n" Type.t_int
let c = Term.mk_var v_c
let n = Term.mk_var v_n

let value name = Term.mk_constr name

let pp = Format.asprintf "%a" Term.pp_print_term

(* The cases of the split, as the value of [c] and what remains *)
let cases t =
  let split = MoxiResults.split_enum_atoms t in
  let disjuncts =
    match Term.destruct split with
    | Term.T.App (s, args) when Symbol.node_of_symbol s = `OR -> args
    | _ -> [ split ]
  in
  disjuncts

(* The term is equivalent to the expected one in every value of [c] and of
   [n] in a range *)
let assert_equivalent ~msg expected t =
  let split = MoxiResults.split_enum_atoms t in
  List.iter (fun cv ->
    List.iter (fun nv ->
      let model =
        Model.of_list
          [ (v_c, Model.Term (value cv)) ; (v_n, Model.Term (Term.mk_num_of_int nv)) ]
      in
      let eval t = Eval.eval_term [] model t |> Eval.bool_of_value in
      assert_equal ~msg:(Format.sprintf "%s, c = %s, n = %d: %s" msg cv nv (pp split))
        ~printer:string_of_bool (eval expected) (eval split)
    ) [ -1 ; 0 ; 1 ; 2 ; 3 ]
  ) [ "test_red" ; "test_green" ; "test_blue" ]

let test_mixed_equation _ =
  let t = Term.mk_eq [ n ; c ] in
  assert_equivalent ~msg:"n = c" t t ;
  assert_equal ~msg:"three cases" ~printer:string_of_int 3 (List.length (cases t))

let test_mixed_relation _ =
  let t = Term.mk_leq [ c ; n ] in
  assert_equivalent ~msg:"c <= n" t t

let test_enum_only _ =
  (* 2 - c >= 0 holds for every value, c - 1 >= 0 for green and blue *)
  let t = Term.mk_geq [ Term.mk_minus [ c ; Term.mk_num_of_int 1 ] ; Term.mk_num_of_int 0 ] in
  assert_equivalent ~msg:"c - 1 >= 0" t t ;
  (* No variable but c is left, and no arithmetic over it *)
  List.iter (fun d ->
    assert_bool ("no residual: " ^ pp d)
      (Var.VarSet.for_all (fun v -> Var.equal_vars v v_c) (Term.vars_of_term d)))
    (cases t)

let test_equation_kept _ =
  (* An equation with a value is printed as it is *)
  let t = Term.mk_eq [ c ; value "test_blue" ] in
  assert_equal ~msg:"c = blue" ~cmp:Term.equal ~printer:pp t
    (MoxiResults.split_enum_atoms t)

let tests =
  "Case split of atoms over enumeration sorts" >::: [
    "mixed equation" >:: test_mixed_equation;
    "mixed relation" >:: test_mixed_relation;
    "atom over the enumeration only" >:: test_enum_only;
    "equation with a value" >:: test_equation_kept;
  ]

let () = run_test_tt_main tests
