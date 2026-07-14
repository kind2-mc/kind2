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

(** Desugars the [last] operator.

    [last x], where [x] is a variable in scope, may only occur in an expression
    within a frame block. It denotes the previous value of [x], initialized by
    the frame.

    For each frame block, every variable [x] referenced through [last] is
    replaced by a fresh internal local variable [last_x] defined (on the base
    clock, outside the frame block) by
      [last_x = init_x -> pre x]
    where [init_x] is the frame's initialization expression for [x] (or just
    [pre x] when [x] has no initialization).

    This mirrors the semantics of manually introducing such a local variable
    (see the [when_last2.lus] example).
 *)

module A = LustreAst
module R = Res
module AH = LustreAstHelpers
module GI = GeneratedIdentifiers

let (let*) = R.(>>=)

type error_kind =
  | MisplacedLastError of HString.t
  | UnknownIdentifier of HString.t

let error_message = function
  | MisplacedLastError id ->
    "The 'last' operator can only be used within a frame block (found 'last "
    ^ HString.string_of_hstring id ^ "')."
  | UnknownIdentifier id ->
    "Unknown identifier '" ^ HString.string_of_hstring id ^ "'"

type error = [
  | `LustreDesugarLastError of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreDesugarLastError (pos, kind))

(* Counter for fresh last-variable names. The leading digit guarantees the
   generated names cannot clash with user-written identifiers. *)
let i = ref 0

let mk_fresh_last_name x =
  let name =
    (string_of_int !i) ^ "_" ^ GI.last_local ^ "_" ^ (HString.string_of_hstring x)
  in
  i := !i + 1;
  HString.mk_hstring name

(** Returns the fresh local name associated with frame variable [x], creating it
    (and recording it in [acc], together with the position of its first use) on
    first use. [acc] preserves insertion order. *)
let get_or_create acc pos x =
  match List.assoc_opt x !acc with
  | Some (n, _) -> n
  | None -> let n = mk_fresh_last_name x in acc := !acc @ [(x, (n, pos))]; n

(** Replaces every [last x] occurring in [e] with a reference to its fresh local
    variable, recording the needed last-variables in [acc]. *)
let rec replace_last acc e =
  let r = replace_last acc in
  match e with
  | A.Last (pos, x) -> A.Ident (pos, get_or_create acc pos x)
  | Ident _ | ModeRef _ | Const _
  | EmptyMap (_, None) | EmptySet (_, None) -> e
  | EmptyMap (p, Some (kt, vt)) -> EmptyMap (p, Some (kt, vt))
  | EmptySet (p, Some ty) -> EmptySet (p, Some ty)
  | FieldProject (pos, e, idx, ty_opt) -> FieldProject (pos, r e, idx, ty_opt)
  | Extract (pos, e, idx1, idx2) -> Extract (pos, r e, idx1, idx2)
  | UnaryOp (pos, op, e) -> UnaryOp (pos, op, r e)
  | ADTTerm (pos, tis, id, es) -> ADTTerm (pos, tis, id, List.map r es)
  | Match (pos, e, arms, ty_opt) ->
    Match (pos, r e, List.map (fun (pat, arm_e) -> (pat, r arm_e)) arms, ty_opt)
  | BinaryOp (pos, op, e1, e2) -> BinaryOp (pos, op, r e1, r e2)
  | TernaryOp (pos, op, e1, e2, e3) -> TernaryOp (pos, op, r e1, r e2, r e3)
  | ConvOp (pos, op, e) -> ConvOp (pos, op, r e)
  | CompOp (pos, op, e1, e2) -> CompOp (pos, op, r e1, r e2)
  | AnyOp (pos, ti, e) -> AnyOp (pos, ti, r e)
  | ChooseOp (pos, ti, e) -> ChooseOp (pos, ti, r e)
  | Quantifier (pos, q, tis, e) -> Quantifier (pos, q, tis, r e)
  | RecordExpr (pos, ident, ps, expr_list) ->
    RecordExpr (pos, ident, ps, List.map (fun (i, e) -> (i, r e)) expr_list)
  | GroupExpr (pos, kind, expr_list) ->
    GroupExpr (pos, kind, List.map r expr_list)
  | StructUpdate (pos, e1, idx, Some e2) ->
    StructUpdate (pos, r e1, idx, Some (r e2))
  | StructUpdate (pos, e1, idx, None) ->
    StructUpdate (pos, r e1, idx, None)
  | ArrayConstr (pos, e1, e2) -> ArrayConstr (pos, r e1, r e2)
  | IndexAccess (pos, e1, e2, kind) -> IndexAccess (pos, r e1, r e2, kind)
  | When (pos, e, clock) -> When (pos, r e, clock)
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    Condact (pos, r e1, r e2, id, List.map r expr_list1, List.map r expr_list2)
  | Activate (pos, ident, e1, e2, expr_list) ->
    Activate (pos, ident, r e1, r e2, List.map r expr_list)
  | Merge (pos, ident, expr_list) ->
    Merge (pos, ident, List.map (fun (i, e) -> (i, r e)) expr_list)
  | RestartEvery (pos, ident, expr_list, e) ->
    RestartEvery (pos, ident, List.map r expr_list, r e)
  | Pre (pos, e) -> Pre (pos, r e)
  | Arrow (pos, e1, e2) -> Arrow (pos, r e1, r e2)
  | TypeAscription (pos, e, ty) -> TypeAscription (pos, r e, ty)
  | Call (pos, ty_args, id, expr_list) ->
    Call (pos, ty_args, id, List.map r expr_list)
  | A.ADTTester (pos, e, c) -> A.ADTTester (pos, r e, c)

let replace_last_eq acc = function
  | A.Assert (pos, e) -> A.Assert (pos, replace_last acc e)
  | A.Equation (pos, lhs, e) -> A.Equation (pos, lhs, replace_last acc e)

let replace_last_prop_kind acc = function
  | A.Provided e -> A.Provided (replace_last acc e)
  | k -> k

(** Replaces [last] in all expressions reachable from the node item [ni]
    (recursing into nested if/when/frame blocks). *)
let rec replace_last_ni acc ni = match ni with
  | A.Body eq -> A.Body (replace_last_eq acc eq)
  | A.IfBlock (pos, e, nis1, nis2) ->
    A.IfBlock (pos, replace_last acc e,
               List.map (replace_last_ni acc) nis1,
               List.map (replace_last_ni acc) nis2)
  | A.WhenBlock (pos, e, nis1, nis2) ->
    A.WhenBlock (pos, replace_last acc e,
                 List.map (replace_last_ni acc) nis1,
                 List.map (replace_last_ni acc) nis2)
  | A.FrameBlock (pos, vars, nes, nis) ->
    A.FrameBlock (pos, vars, List.map (replace_last_eq acc) nes,
                  List.map (replace_last_ni acc) nis)
  | A.AnnotProperty (pos, name, e, k) ->
    A.AnnotProperty (pos, name, replace_last acc e, replace_last_prop_kind acc k)
  | A.AnnotMain _ | A.Auto _ -> ni

(* {1 Detecting misplaced last operators} *)

let rec find_last_expr e = match e with
  | A.Last (pos, x) -> Some (pos, x)
  | Ident _ | ModeRef _ | Const _
  | EmptyMap _ | EmptySet _ -> None
  | FieldProject (_, e, _, _) | Extract (_, e, _, _)
  | UnaryOp (_, _, e) | ConvOp (_, _, e)
  | AnyOp (_, _, e) | ChooseOp (_, _, e) | Quantifier (_, _, _, e)
  | When (_, e, _) | Pre (_, e) | TypeAscription (_, e, _) -> find_last_expr e
  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2)
  | ArrayConstr (_, e1, e2) | IndexAccess (_, e1, e2, _)
  | Arrow (_, e1, e2) -> find_last_first [e1; e2]
  | TernaryOp (_, _, e1, e2, e3) -> find_last_first [e1; e2; e3]
  | RecordExpr (_, _, _, l) | Merge (_, _, l) ->
    find_last_first (List.map snd l)
  | GroupExpr (_, _, l) | Call (_, _, _, l) -> find_last_first l
  | StructUpdate (_, e1, _, Some e2) -> find_last_first [e1; e2]
  | StructUpdate (_, e1, _, None) -> find_last_expr e1
  | Condact (_, e1, e2, _, l1, l2) -> find_last_first ([e1; e2] @ l1 @ l2)
  | Activate (_, _, e1, e2, l) -> find_last_first ([e1; e2] @ l)
  | RestartEvery (_, _, l, e) -> find_last_first (e :: l)
  | ADTTerm (_, _, _, l) -> find_last_first l
  | Match (_, e, arms, _) -> find_last_first (e :: List.map snd arms)
  | ADTTester (_, e, _) -> find_last_expr e

and find_last_first = function
  | [] -> None
  | e :: es -> (match find_last_expr e with Some r -> Some r | None -> find_last_first es)

let find_last_eq = function
  | A.Assert (_, e) | A.Equation (_, _, e) -> find_last_expr e

(** Looks for a (misplaced) [last] in a node item that is not a frame block,
    descending into nested if/when blocks but not frame blocks (which handle
    [last] themselves). *)
let rec find_last_ni ni = match ni with
  | A.Body eq -> find_last_eq eq
  | A.IfBlock (_, e, nis1, nis2) | A.WhenBlock (_, e, nis1, nis2) ->
    (match find_last_expr e with
     | Some r -> Some r
     | None -> find_last_nis (nis1 @ nis2))
  | A.FrameBlock _ -> None
  | A.AnnotProperty (_, _, e, A.Provided e2) ->
    (match find_last_expr e with Some r -> Some r | None -> find_last_expr e2)
  | A.AnnotProperty (_, _, e, _) -> find_last_expr e
  | A.AnnotMain _ | A.Auto _ -> None

and find_last_nis nis =
  List.fold_left
    (fun acc ni -> match acc with Some _ -> acc | None -> find_last_ni ni)
    None nis

(* {1 Type lookup} *)

(* Build a lookup table from variable name to declared type using the node's
   inputs, outputs and (variable) locals. *)
let mk_type_lookup cctds ctds nlds =
  let inputs = List.map (fun (_, id, ty, _, _) -> (id, ty)) cctds in
  let outputs = List.map (fun (_, id, ty, _) -> (id, ty)) ctds in
  let locals = List.filter_map (function
    | A.NodeVarDecl (_, (_, id, ty, _)) -> Some (id, ty)
    | A.NodeConstDecl _ -> None) nlds
  in
  inputs @ outputs @ locals

(** Generates, for each recorded last-variable, its fresh local declaration and
    defining equation [last_x = init_x -> pre x]. *)
let gen_last_defs f_pos type_lookup nes last_vars =
  R.seq (List.map (fun (x, (last_name, pos)) ->
    match List.assoc_opt x type_lookup with
    | None -> mk_error pos (UnknownIdentifier x)
    | Some ty ->
      let pre_x = A.Pre (f_pos, A.Ident (f_pos, x)) in
      (* Initialization from the frame block, if any. *)
      let init = List.find_map (function
        | A.Equation (_, A.StructDef (_, [A.SingleIdent (_, id)]), e) when id = x -> Some e
        | A.Equation (_, A.StructDef (_, [A.ArrayDef (_, id, _)]), e) when id = x -> Some e
        | _ -> None) nes
      in
      let rhs = match init with
        | Some init -> A.Arrow (AH.pos_of_expr init, init, pre_x)
        | None -> pre_x
      in
      let decl = A.NodeVarDecl (f_pos, (f_pos, last_name, ty, A.ClockTrue)) in
      let eq =
        A.Body (A.Equation (f_pos,
          A.StructDef (f_pos, [A.SingleIdent (f_pos, last_name)]), rhs))
      in
      R.ok (decl, eq)
  ) last_vars)

(* {1 Node processing} *)

(** Processes a single (top-level) node item, returning the new local
    declarations, the (possibly several) replacement node items, after
    desugaring any [last] operators. *)
let desugar_node_item type_lookup ni = match ni with
  | A.FrameBlock (pos, vars, nes, nis) ->
    let acc = ref [] in
    let nes = List.map (replace_last_eq acc) nes in
    let nis = List.map (replace_last_ni acc) nis in
    let* defs = gen_last_defs pos type_lookup nes !acc in
    let decls = List.map fst defs in
    let last_eqs = List.map snd defs in
    R.ok (decls, last_eqs @ [A.FrameBlock (pos, vars, nes, nis)])
  | _ ->
    (match find_last_ni ni with
     | Some (pos, x) -> mk_error pos (MisplacedLastError x)
     | None -> R.ok ([], [ni]))

let desugar_node_decl (node_id, b, opac, nps, cctds, ctds, nlds, nis, co) =
  let type_lookup = mk_type_lookup cctds ctds nlds in
  let* res = R.seq (List.map (desugar_node_item type_lookup) nis) in
  let decls, nis = List.split res in
  let decls = List.flatten decls in
  let nis = List.flatten nis in
  R.ok (node_id, b, opac, nps, cctds, ctds, decls @ nlds, nis, co)

(** Desugars the [last] operator in a declaration list. *)
let desugar_last decls =
  R.seq (List.map (fun decl -> match decl with
    | A.NodeDecl (s, nd) ->
      let* nd = desugar_node_decl nd in
      R.ok (A.NodeDecl (s, nd))
    | A.FuncDecl (s, nd, attrs) ->
      let* nd = desugar_node_decl nd in
      R.ok (A.FuncDecl (s, nd, attrs))
    | _ -> R.ok decl
  ) decls)
