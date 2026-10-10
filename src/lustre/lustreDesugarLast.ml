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
  | LastUnderRestart of HString.t
  | LastOnInputError of HString.t
  | UnknownIdentifier of HString.t

let error_message = function
  | LastUnderRestart id ->
    "The 'last' operator cannot be used under a restart (found 'last "
    ^ HString.string_of_hstring id ^ "')."
  | MisplacedLastError id ->
    "The 'last' operator can only be used within a frame block (found 'last "
    ^ HString.string_of_hstring id ^ "')."
  | LastOnInputError id ->
    "The 'last' operator cannot be applied to the input '"
    ^ HString.string_of_hstring id ^ "'"
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

(* Fresh local name holding the (shared) frame-initialization value of [x]. The
   [last_local] segment makes it a Kind 2 generated (invisible) local, and the
   leading digit guarantees it cannot clash with user-written identifiers. *)
let mk_fresh_init_name x =
  let name =
    (string_of_int !i) ^ "_" ^ GI.last_local ^ "_init_" ^ (HString.string_of_hstring x)
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
  | FieldProject (pos, e, idx, pk) -> FieldProject (pos, r e, idx, pk)
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
  | ArrayComprehension (pos, bs, e) -> ArrayComprehension (pos, bs, r e)
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
  | Restart (pos, e1, e2) -> Restart (pos, r e1, r e2)
  | RestartEvery _ -> assert false (* only generated by lustreGenNodes *)
  | Pre (pos, e) -> Pre (pos, r e)
  | Arrow (pos, e1, e2) -> Arrow (pos, r e1, r e2)
  | Fby (pos, e1, e2) -> Fby (pos, r e1, r e2)
  | TypeAscription (pos, e, ty) -> TypeAscription (pos, r e, ty)
  | Call (pos, ty_args, id, expr_list) ->
    Call (pos, ty_args, id, List.map r expr_list)
  | AbstractSymConst _ -> assert false (* never produced before lustreDesugarLast runs *)
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
  | A.MatchBlock (pos, e, arms, ty) ->
    A.MatchBlock (pos, replace_last acc e,
                  List.map (fun (p, items) ->
                    (p, List.map (replace_last_ni acc) items)) arms,
                  ty)
  | A.RestartBlock (pos, nis, e) ->
    A.RestartBlock (pos, List.map (replace_last_ni acc) nis, replace_last acc e)
  | A.FrameBlock (pos, vars, nes, nis) ->
    A.FrameBlock (pos, vars, List.map (replace_last_eq acc) nes,
                  List.map (replace_last_ni acc) nis)
  | A.AnnotProperty (pos, name, e, k) ->
    A.AnnotProperty (pos, name, replace_last acc e, replace_last_prop_kind acc k)
  | A.AnnotMain _ | A.Auto _ -> ni

(* {1 Detecting misplaced last operators} *)

(* With [only_under_restart], only a [last] under a restart is reported *)
let rec find_last_expr ?(only_under_restart = false) e =
  let r = find_last_expr ~only_under_restart in
  let rs = find_last_first ~only_under_restart in
  match e with
  | A.Last (pos, x) -> if only_under_restart then None else Some (pos, x)
  | Ident _ | ModeRef _ | Const _
  | EmptyMap _ | EmptySet _ -> None
  | FieldProject (_, e, _, _) | Extract (_, e, _, _)
  | UnaryOp (_, _, e) | ConvOp (_, _, e)
  | AnyOp (_, _, e) | ChooseOp (_, _, e) | Quantifier (_, _, _, e)
  | ArrayComprehension (_, _, e)
  | Pre (_, e) | TypeAscription (_, e, _) -> r e
  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2)
  | ArrayConstr (_, e1, e2) | IndexAccess (_, e1, e2, _)
  | Arrow (_, e1, e2) | Fby (_, e1, e2) -> rs [e1; e2]
  | TernaryOp (_, _, e1, e2, e3) -> rs [e1; e2; e3]
  | RecordExpr (_, _, _, l) -> rs (List.map snd l)
  | GroupExpr (_, _, l) | Call (_, _, _, l) -> rs l
  | StructUpdate (_, e1, _, Some e2) -> rs [e1; e2]
  | StructUpdate (_, e1, _, None) -> r e1
  (* The condition of a restart is not under the restart *)
  | Restart (_, e1, e2) ->
    (match find_last_expr e1 with Some l -> Some l | None -> r e2)
  | RestartEvery _ -> assert false (* only generated by lustreGenNodes *)
  | ADTTerm (_, _, _, l) -> rs l
  | Match (_, e, arms, _) -> rs (e :: List.map snd arms)
  | AbstractSymConst _ -> assert false (* never produced before lustreDesugarLast runs *)
  | ADTTester (_, e, _) -> r e

and find_last_first ?(only_under_restart = false) = function
  | [] -> None
  | e :: es ->
    (match find_last_expr ~only_under_restart e with
     | Some r -> Some r
     | None -> find_last_first ~only_under_restart es)

let find_last_eq ?(only_under_restart = false) = function
  | A.Assert (_, e) | A.Equation (_, _, e) -> find_last_expr ~only_under_restart e

(** Looks for a [last] in a node item, descending into nested if/when/match/
    restart blocks but not frame blocks (which handle [last] themselves). With
    [only_under_restart], only a [last] under a restart is reported. *)
let rec find_last_ni ?(only_under_restart = false) ni =
  let r = find_last_expr ~only_under_restart in
  let rs = find_last_nis ~only_under_restart in
  match ni with
  | A.Body eq -> find_last_eq ~only_under_restart eq
  | A.IfBlock (_, e, nis1, nis2) | A.WhenBlock (_, e, nis1, nis2) ->
    (match r e with
     | Some l -> Some l
     | None -> rs (nis1 @ nis2))
  | A.MatchBlock (_, e, arms, _) ->
    (match r e with
     | Some l -> Some l
     | None -> rs (List.concat_map snd arms))
  (* The condition of a restart is not under the restart *)
  | A.RestartBlock (_, nis, e) ->
    (match find_last_nis nis with
     | Some l -> Some l
     | None -> r e)
  | A.FrameBlock _ -> None
  | A.AnnotProperty (_, _, e, A.Provided e2) ->
    (match r e with Some l -> Some l | None -> r e2)
  | A.AnnotProperty (_, _, e, _) -> r e
  | A.AnnotMain _ | A.Auto _ -> None

and find_last_nis ?(only_under_restart = false) nis =
  List.fold_left
    (fun acc ni -> match acc with
       | Some _ -> acc
       | None -> find_last_ni ~only_under_restart ni)
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

(* The names of the node's inputs. [last] may not be applied to one: see
   [gen_last_defs]. *)
let mk_input_names cctds = List.map (fun (_, id, _, _, _) -> id) cctds

(** Generates, for each recorded last-variable [x], its fresh local declaration
    and defining equation. When [x] is initialized in the frame the definition is
    [init_x -> pre x] (initialized by the frame, then holding the previous value);
    with no initialization it is just [pre x]. *)
let gen_last_defs f_pos type_lookup input_names nes last_vars =
  R.seq (List.map (fun (x, (last_name, pos)) ->
    match List.assoc_opt x type_lookup with
    | None -> mk_error pos (UnknownIdentifier x)
    | Some _ when List.mem x input_names -> mk_error pos (LastOnInputError x)
    | Some ty ->
      let decl = A.NodeVarDecl (f_pos, (f_pos, last_name, ty, A.ClockTrue)) in
      (* Find x's initialization equation in the frame block, if any. *)
      let init_eq = List.find_opt (function
        | A.Equation (_, A.StructDef (_, [A.SingleIdent (_, id)]), _) -> id = x
        | _ -> false) nes
      in
      let eq = match init_eq with
        | Some (A.Equation (_, _, init)) ->
          (* Frame variable with initialization. *)
          let pre_x = A.Pre (f_pos, A.Ident (f_pos, x)) in
          let rhs = A.Arrow (AH.pos_of_expr init, init, pre_x) in
          A.Body (A.Equation (f_pos,
            A.StructDef (f_pos, [A.SingleIdent (f_pos, last_name)]), rhs))
        | _ ->
          (* No frame initialization. *)
          let pre_x = A.Pre (f_pos, A.Ident (f_pos, x)) in
          A.Body (A.Equation (f_pos,
            A.StructDef (f_pos, [A.SingleIdent (f_pos, last_name)]), pre_x))
      in
      R.ok (decl, eq)
  ) last_vars)

(** For each frame variable that is referenced through [last] (i.e. appears in
    [last_vars]) and is initialized in the frame, share the initialization value:
    introduce a fresh local [init_x] defined by [init_x = <init>] and rewrite the
    frame initialization [x = <init>] to [x = init_x]. The generated
    last-definition (see [gen_last_defs]) then also references [init_x] because it
    reads the rewritten frame initialization. Returns the rewritten
    frame initializations together with the new locals and their defining
    equations.

    Sharing guarantees the initialization is evaluated exactly once rather than
    being duplicated into the generated last-definition. This is required for
    correctness whenever the initialization cannot be freely duplicated, e.g. an
    'any'/'choose' operator (each of which desugars, in lustreGenNodes, into a
    call to a fresh internal node named after its source position, so duplicating
    it introduces both an extra nondeterministic choice and a duplicate-name
    error). It is done unconditionally so that any such construct, present or
    future, is handled without special-casing. *)
let share_frame_inits type_lookup last_vars nes =
  let last_names = List.map fst last_vars in
  let shared x = List.mem x last_names && List.mem_assoc x type_lookup in
  let defs = ref [] in
  let nes = List.map (fun ne -> match ne with
    | A.Equation (epos, A.StructDef (spos, [A.SingleIdent (ipos, x)]), init)
      when shared x ->
      let ty = List.assoc x type_lookup in
      let init_name = mk_fresh_init_name x in
      let decl = A.NodeVarDecl (epos, (epos, init_name, ty, A.ClockTrue)) in
      let eq = A.Body (A.Equation (epos,
        A.StructDef (epos, [A.SingleIdent (epos, init_name)]), init))
      in
      defs := !defs @ [(decl, eq)];
      A.Equation (epos, A.StructDef (spos, [A.SingleIdent (ipos, x)]),
                  A.Ident (ipos, init_name))
    | _ -> ne
  ) nes in
  (nes, !defs)

(* {1 Node processing} *)

(** Processes a single (top-level) node item, returning the new local
    declarations, the (possibly several) replacement node items, after
    desugaring any [last] operators. *)
let desugar_node_item type_lookup input_names ni = match ni with
  | A.FrameBlock (pos, vars, nes, nis) ->
    (* The local a [last] is replaced with is defined outside the restart, so it
       would not be restarted *)
    let* () =
      match
        List.find_map (find_last_eq ~only_under_restart:true) nes
        |> (function Some l -> Some l | None -> find_last_nis ~only_under_restart:true nis)
      with
      | Some (pos, x) -> mk_error pos (LastUnderRestart x)
      | None -> R.ok ()
    in
    let acc = ref [] in
    let nes = List.map (replace_last_eq acc) nes in
    let nis = List.map (replace_last_ni acc) nis in
    (* Share frame initializations with the generated last-variables so that the
       initialization is evaluated once rather than duplicated (required for
       non-duplicable initializations such as 'any'/'choose'). *)
    let nes, share_defs = share_frame_inits type_lookup !acc nes in
    let* defs = gen_last_defs pos type_lookup input_names nes !acc in
    let decls = List.map fst share_defs @ List.map fst defs in
    let share_eqs = List.map snd share_defs in
    let last_eqs = List.map snd defs in
    R.ok (decls, share_eqs @ last_eqs @ [A.FrameBlock (pos, vars, nes, nis)])
  | _ ->
    (match find_last_ni ni with
     | Some (pos, x) -> mk_error pos (MisplacedLastError x)
     | None -> R.ok ([], [ni]))

let desugar_node_decl (node_id, b, opac, nps, cctds, ctds, nlds, nis, co) =
  let type_lookup = mk_type_lookup cctds ctds nlds in
  let input_names = mk_input_names cctds in
  let* res = R.seq (List.map (desugar_node_item type_lookup input_names) nis) in
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
