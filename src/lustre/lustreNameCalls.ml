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

(** Assign fresh local variables to the results of call statements.

    A call statement such as [double(n-1);] is parsed into an equation with an
    empty left-hand side (see lustreParser.mly). This pass introduces, for each
    returned value, a fresh local variable to hold the (otherwise discarded)
    result, so that distinct call statements never share a left-hand side.

    The fresh variables are named with the [GI.discarded_output] suffix and are
    exempt from the "must be defined in every branch" check performed when
    if/when blocks are desugared (see lustreDesugarIfBlocks.ml). This pass must
    therefore run after type checking (types are needed to declare the fresh
    locals) but before if/when blocks are desugared. *)

module R = Res
module A = LustreAst
module Chk = LustreTypeChecker
module GI = GeneratedIdentifiers

let (let*) = R.(>>=)

(** [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

(** Create a fresh local variable name for a discarded call result. *)
let mk_fresh_discarded_var () =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  HString.concat2 prefix (HString.mk_hstring ("_" ^ GI.discarded_output))

(** Given the inferred type of a call, produce the left-hand side struct items
    and the corresponding fresh local declarations (one per returned value). *)
let fresh_lhs_and_decls pos ty =
  let mk_one ty =
    let v = mk_fresh_discarded_var () in
    (A.SingleIdent (pos, v), A.NodeVarDecl (pos, (pos, v, ty, A.ClockTrue)))
  in
  match ty with
  | A.GroupType (_, tys) -> List.map mk_one tys
  | ty -> [mk_one ty]

(** Replace the empty left-hand side of a call statement with fresh locals,
    recursing through if/when/frame blocks. Returns the rewritten item together
    with the new local declarations it introduces. *)
let rec name_calls_item ctx node_id ni =
  match ni with
  | A.Body (A.Equation (pos, A.StructDef (lpos, []), rhs)) ->
    let* ty, _, _ = Chk.infer_type_expr ctx (Some node_id) rhs in
    let items_and_decls = fresh_lhs_and_decls lpos ty in
    let lhs = A.StructDef (lpos, List.map fst items_and_decls) in
    R.ok (A.Body (A.Equation (pos, lhs, rhs)), List.map snd items_and_decls)
  | A.IfBlock (pos, e, l1, l2) ->
    let* l1, d1 = name_calls_items ctx node_id l1 in
    let* l2, d2 = name_calls_items ctx node_id l2 in
    R.ok (A.IfBlock (pos, e, l1, l2), d1 @ d2)
  | A.WhenBlock (pos, e, l1, l2) ->
    let* l1, d1 = name_calls_items ctx node_id l1 in
    let* l2, d2 = name_calls_items ctx node_id l2 in
    R.ok (A.WhenBlock (pos, e, l1, l2), d1 @ d2)
  | A.FrameBlock (pos, vars, nes, nis) ->
    (* Frame block equations (nes) always have an explicit left-hand side. *)
    let* nis, d = name_calls_items ctx node_id nis in
    R.ok (A.FrameBlock (pos, vars, nes, nis), d)
  | _ -> R.ok (ni, [])

and name_calls_items ctx node_id nis =
  let* res = R.seq (List.map (name_calls_item ctx node_id) nis) in
  let nis, decls = List.split res in
  R.ok (nis, List.flatten decls)

let name_calls_decl ctx decl =
  match decl with
  | A.FuncDecl (s, (node_id, b, opac, nps, cctds, ctds, nlds, nis, co), attrs) ->
    let ctx = Chk.add_full_node_ctx ctx node_id nps cctds ctds nlds in
    let* nis, decls = name_calls_items ctx node_id nis in
    R.ok (A.FuncDecl
      (s, (node_id, b, opac, nps, cctds, ctds, decls @ nlds, nis, co), attrs))
  | A.NodeDecl (s, (node_id, b, opac, nps, cctds, ctds, nlds, nis, co)) ->
    let ctx = Chk.add_full_node_ctx ctx node_id nps cctds ctds nlds in
    let* nis, decls = name_calls_items ctx node_id nis in
    R.ok (A.NodeDecl
      (s, (node_id, b, opac, nps, cctds, ctds, decls @ nlds, nis, co)))
  | _ -> R.ok decl

(** Introduce fresh local variables for the results of call statements in all
    node and function declarations. *)
let name_calls ctx decls =
  R.seq (List.map (name_calls_decl ctx) decls)
