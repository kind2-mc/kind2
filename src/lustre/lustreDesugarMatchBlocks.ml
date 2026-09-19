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

module A = LustreAst
module AH = LustreAstHelpers
module Chk = LustreTypeChecker
module LCME = LustreCheckMatchExpressions

module R = Res

let (let*) = R.(>>=)

type error_kind =
  | MisplacedNodeItemInMatchArm of A.node_item
  | MisplacedMatchBlock of A.node_item
  | ShadowingPatternVariable of HString.t

let error_message = function
  | MisplacedNodeItemInMatchArm ni -> (match ni with
    | A.Body (A.Assert _) -> "Asserts are not allowed inside match blocks."
    | A.AnnotMain _ -> "Main annotations are not allowed inside match blocks."
    | A.AnnotProperty _ -> "Property annotations are not allowed inside match blocks."
    | A.FrameBlock _ -> "Frame blocks are not allowed inside match blocks."
    | A.IfBlock _ -> "If blocks are not allowed inside match blocks."
    | A.Body (A.Equation _) | A.MatchBlock _ | A.WhenBlock _ | A.Auto _ -> assert false
  )
  | MisplacedMatchBlock ni -> (match ni with
    | A.IfBlock _ -> "Match blocks are not allowed inside if blocks."
    | A.Body _ | A.MatchBlock _ | A.WhenBlock _ | A.FrameBlock _
    | A.AnnotMain _ | A.AnnotProperty _ | A.Auto _ -> assert false
  )
  | ShadowingPatternVariable id ->
    "Match block pattern variable '" ^ HString.string_of_hstring id
    ^ "' shadows a variable of the enclosing node."

type error = [
  | `LustreDesugarMatchBlocksError of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreDesugarMatchBlocksError (pos, kind))

(* The underlying datatype of a type, looking through type synonyms and
   refinement types. *)
let rec adt_of_type ctx ty =
  match ty with
  | A.ADT _ -> Some ty
  | A.RefinementType (_, (_, _, inner), _) -> adt_of_type ctx inner
  | _ ->
    (match Chk.expand_type_syn_reftype_history ctx ty with
     | Ok (A.ADT _ as adt) -> Some adt
     | Ok _ | Error _ -> None)

(* The conjunction of constructor testers and the variable -> projection
   substitutions a (possibly nested) pattern imposes on the scrutinee.

   Datatypes are still datatypes at this point, so the surface tester and
   selector forms are emitted; LustreDesugarADTs rewrites them into the record
   encoding for non-recursive datatypes and leaves them alone for recursive
   ones. *)
let rec pattern_constraints pos ctx adt_ty scrut pat =
  match pat with
  (* Type checking has already resolved a 0-arg constructor written without
     parentheses into Pat (_, ctor, []), so a VarPat here is a real binder *)
  | A.VarPat (_, name) -> ([], [(name, scrut)])
  | A.Pat (_, ctor, sub_pats) ->
    let ctors = match adt_ty with
      | A.ADT (_, _, ctors) -> ctors
      | _ -> assert false (* the type checker rejects a non-datatype scrutinee *)
    in
    let fields = match List.assoc_opt ctor ctors with
      | Some fields -> fields
      | None -> assert false (* likewise for an unknown constructor *)
    in
    let tester = A.ADTTester (pos, scrut, ctor) in
    let sub_conds, subs =
      List.fold_left2 (fun (conds, subs) (fname, fty) sub_pat ->
        let proj =
          A.FieldProject (pos, scrut, fname,
                          A.Selector (A.Kind2Generated, adt_ty, ctor))
        in
        match sub_pat with
        | A.VarPat (_, sub_name) -> (conds, subs @ [(sub_name, proj)])
        | A.Pat _ ->
          let sub_adt = match adt_of_type ctx fty with
            | Some adt -> adt
            | None -> assert false (* a constructor pattern needs a datatype field *)
          in
          let c, s = pattern_constraints pos ctx sub_adt proj sub_pat in
          (conds @ c, subs @ s)
      ) ([], []) fields sub_pats
    in
    (tester :: sub_conds, subs)

let conjoin pos = function
  | [] -> None
  | c :: cs -> Some (List.fold_left (fun acc c' -> A.BinaryOp (pos, A.And, acc, c')) c cs)

(* Applies a substitution to every expression a node item holds. Arm bodies are
   desugared before their enclosing arm's substitution is applied, so a binder
   that shadows an outer one has already consumed its own occurrences. *)
let rec apply_subst_in_item subs item =
  let e = AH.apply_subst_in_expr subs in
  let ri = List.map (apply_subst_in_item subs) in
  match item with
  | A.Body (A.Equation (pos, (A.StructDef (_, ss) as lhs), rhs)) ->
    (* The indices of an array definition bind over the right-hand side, so
       they shadow a pattern variable of the same name *)
    let indices = List.concat_map (function
      | A.ArrayDef (_, _, is) -> is
      | A.SingleIdent _ | A.TupleStructItem _ | A.TupleSelection _
      | A.FieldSelection _ | A.ArraySliceStructItem _ -> []) ss
    in
    let subs =
      List.filter (fun (id, _) -> not (List.exists (HString.equal id) indices)) subs
    in
    A.Body (A.Equation (pos, lhs, AH.apply_subst_in_expr subs rhs))
  | A.Body (A.Assert (pos, expr)) -> A.Body (A.Assert (pos, e expr))
  | A.AnnotProperty (pos, n, expr, A.Provided expr2) ->
    A.AnnotProperty (pos, n, e expr, A.Provided (e expr2))
  | A.AnnotProperty (pos, n, expr, ((A.Invariant | A.Reachable _) as k)) ->
    A.AnnotProperty (pos, n, e expr, k)
  | A.IfBlock (pos, cond, l1, l2) -> A.IfBlock (pos, e cond, ri l1, ri l2)
  | A.WhenBlock (pos, cond, l1, l2) -> A.WhenBlock (pos, e cond, ri l1, ri l2)
  | A.MatchBlock (pos, scrut, arms, ty) ->
    A.MatchBlock (pos, e scrut, List.map (fun (p, items) -> (p, ri items)) arms, ty)
  | A.FrameBlock (pos, vars, nes, nis) ->
    let ne = function
      | A.Equation (p, lhs, rhs) -> A.Equation (p, lhs, e rhs)
      | A.Assert (p, expr) -> A.Assert (p, e expr)
    in
    A.FrameBlock (pos, vars, List.map ne nes, ri nis)
  | A.AnnotMain _ | A.Auto _ -> item

(* Only equations and nested match blocks may appear in an arm. If and when
   blocks are rejected here rather than being left to the when-block
   desugaring, which would report them against a when block the user never
   wrote. *)
let check_arm_item item =
  match item with
  | A.Body (A.Equation _) | A.MatchBlock _ | A.WhenBlock _ | A.Auto _ -> R.ok ()
  | A.Body (A.Assert (pos, _))
  | A.AnnotMain (pos, _)
  | A.AnnotProperty (pos, _, _, _)
  | A.IfBlock (pos, _, _, _)
  | A.FrameBlock (pos, _, _, _) -> mk_error pos (MisplacedNodeItemInMatchArm item)

(* The identifiers a pattern variable may not shadow are the
   enclosing node's inputs, outputs and locals. An arm that rebinds one of them
   makes an equation naming it ambiguous. *)
let check_no_shadowing node_vars pat =
  R.seq_ (List.map (fun (id, pos) ->
    if A.SI.mem id node_vars then mk_error pos (ShadowingPatternVariable id)
    else R.ok ())
    (AH.pat_bound_vars_with_pos pat))

(* The enclosing item is the if block a match block would be nested in, if any. A
   match block becomes a when block, which the if-block desugaring rejects;
   reporting it here keeps the message about the match block the user actually
   wrote. Nesting with when blocks needs no such check: match and when blocks
   both become when blocks, and those nest freely. *)
let rec desugar_item ctx node_vars enclosing item =
  match item with
  | A.Body _ | A.AnnotMain _ | A.AnnotProperty _ | A.Auto _ -> R.ok [item]
  | A.IfBlock (pos, cond, l1, l2) ->
    let* l1 = desugar_items ctx node_vars (Some item) l1 in
    let* l2 = desugar_items ctx node_vars (Some item) l2 in
    R.ok [A.IfBlock (pos, cond, l1, l2)]
  | A.WhenBlock (pos, cond, l1, l2) ->
    let* l1 = desugar_items ctx node_vars None l1 in
    let* l2 = desugar_items ctx node_vars None l2 in
    R.ok [A.WhenBlock (pos, cond, l1, l2)]
  | A.FrameBlock (pos, vars, nes, nis) ->
    let* nis = desugar_items ctx node_vars None nis in
    R.ok [A.FrameBlock (pos, vars, nes, nis)]
  | A.MatchBlock (pos, scrut, arms, scrut_ty_opt) ->
    let* () = match enclosing with
      | Some encl -> mk_error pos (MisplacedMatchBlock encl)
      | None -> R.ok ()
    in
    let* () = R.seq_ (List.map (fun (pat, _) -> check_no_shadowing node_vars pat) arms) in
    let* () =
      R.seq_ (List.map (fun (_, items) ->
        R.seq_ (List.map check_arm_item items)) arms)
    in
    (* Desugar the arms' own match blocks first, so that an arm binder
       shadowing an outer one is substituted before the outer binder is *)
    let* arms =
      R.seq (List.map (fun (pat, items) ->
        let* items = desugar_items ctx node_vars None items in
        R.ok (pat, items)) arms)
    in
    let adt_ty = match scrut_ty_opt with
      | Some ty -> ty
      (* The type checker records the scrutinee's datatype in every match block
         it checks, and a node it never reached is never desugared *)
      | None -> assert false
    in
    let exhaustive = LCME.is_exhaustive ctx adt_ty (List.map fst arms) in
    let arm_branch (pat, items) =
      let conds, subs = pattern_constraints pos ctx adt_ty scrut pat in
      (conjoin pos conds, List.map (apply_subst_in_item subs) items)
    in
    let branches = List.map arm_branch arms in
    (* When the arms are exhaustive the last one covers everything the earlier
       ones leave, so it becomes the final else rather than a guarded branch:
       otherwise the when-block desugaring would see an implicit empty branch
       and report every variable as undefined in it. A non-exhaustive block is
       legal only inside a frame block, where the empty else stutters. *)
    let rec chain = function
      | [] -> assert false (* the grammar requires at least one arm *)
      | [(_, items)] when exhaustive -> items
      | [(cond, items)] ->
        let cond = match cond with
          | Some c -> c
          (* A catch-all arm covers everything, so the arms are exhaustive and
             this branch is unreachable *)
          | None -> assert false
        in
        [A.WhenBlock (pos, cond, items, [])]
      | (cond, items) :: rest ->
        let cond = match cond with
          | Some c -> c
          (* Any arm after a catch-all is useless, which LustreCheckMatchExpressions
             rejects *)
          | None -> assert false
        in
        [A.WhenBlock (pos, cond, items, chain rest)]
    in
    R.ok (chain branches)

and desugar_items ctx node_vars enclosing items =
  let* items = R.seq (List.map (desugar_item ctx node_vars enclosing) items) in
  R.ok (List.flatten items)

let vars_of_node inputs outputs locals =
  let ins = List.map (fun (_, id, _, _, _) -> id) inputs in
  let outs = List.map (fun (_, id, _, _) -> id) outputs in
  let locs = List.filter_map (function
    | A.NodeVarDecl (_, (_, id, _, _)) -> Some id
    | A.NodeConstDecl (_, A.FreeConst (_, id, _))
    | A.NodeConstDecl (_, A.UntypedConst (_, id, _))
    | A.NodeConstDecl (_, A.TypedConst (_, id, _, _)) -> Some id)
    locals
  in
  A.SI.of_list (ins @ outs @ locs)

let desugar_node ctx (id, is_extern, opac, params, inputs, outputs, locals, items, contract) =
  let node_vars = vars_of_node inputs outputs locals in
  let* items = desugar_items ctx node_vars None items in
  R.ok (id, is_extern, opac, params, inputs, outputs, locals, items, contract)

let desugar_declaration ctx decl =
  match decl with
  | A.NodeDecl (span, nd) ->
    let* nd = desugar_node ctx nd in
    R.ok (A.NodeDecl (span, nd))
  | A.FuncDecl (span, nd, is_rec) ->
    let* nd = desugar_node ctx nd in
    R.ok (A.FuncDecl (span, nd, is_rec))
  | A.TypeDecl _ | A.ConstDecl _ | A.ContractNodeDecl _ | A.NodeParamInst _ ->
    R.ok decl

let desugar_match_blocks ctx decls =
  R.seq (List.map (desugar_declaration ctx) decls)
