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

(** Replace array comprehensions with fresh local variables.

    An array comprehension [(e foreach i, j)^m^n] in the body of a node or a
    function is replaced with a fresh local variable [x] of type [T^m^n],
    where [T] is the type of [e], defined by the equation [x[i][j] = e]. The
    variable is not mentioned in [e], so the definition is never recursive.
    In a contract, it is replaced with a fresh ghost variable defined
    element-wise in the same way, just before the contract item it is in.

    A comprehension whose body is a comprehension is lowered as a single one
    with the index variables of both. Otherwise, a comprehension is lowered
    after the comprehensions in its body, so that its equation mentions their
    variables. It cannot mention a variable bound around it (by a quantifier,
    an enclosing comprehension or a match arm), since its equation is placed
    in the body of the node. Comprehensions are not supported in types,
    decreases clauses and the ghost constants of a contract; a global or local
    constant defined by a comprehension is replaced with its definition
    beforehand (see [inline_comprehension_constants]).

    This pass must run after type checking, since the types of the
    comprehensions are needed to declare the fresh locals. *)

module R = Res
module A = LustreAst
module AH = LustreAstHelpers
module Chk = LustreTypeChecker
module Ctx = TypeCheckerContext
module GI = GeneratedIdentifiers

let (let*) = R.(>>=)

let seq_map f l = R.seq (List.map f l)

type error_kind =
  | BoundVariableInComprehension of HString.t
  | UnsupportedComprehensionPosition of string
  | ComprehensionConstantIn of HString.t * string

let error_message = function
  | BoundVariableInComprehension v ->
    "An array comprehension cannot mention the variable '"
    ^ HString.string_of_hstring v
    ^ "' bound by an enclosing quantifier, array comprehension or match arm"
  | UnsupportedComprehensionPosition where ->
    "Array comprehensions are not supported in " ^ where
  | ComprehensionConstantIn (c, where) ->
    "The constant '" ^ HString.string_of_hstring c
    ^ "', whose definition contains an array comprehension, cannot be used in "
    ^ where

type error = [
  | `LustreDesugarArrayComprehensionsError of Lib.position * error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
]

let mk_error pos kind =
  Error (`LustreDesugarArrayComprehensionsError (pos, kind))

(** [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

(** The comprehension each fresh local stands for, as written *)
let sources : (HString.t, A.expr) Hashtbl.t = Hashtbl.create 7

let restore e =
  let sigma =
    A.SI.fold (fun x sigma -> match Hashtbl.find_opt sources x with
      | Some src -> (x, src) :: sigma
      | None -> sigma
    ) (AH.vars_without_node_call_ids e) []
  in
  if sigma = [] then e else AH.apply_subst_in_expr sigma e

let mk_fresh_var () =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  HString.concat2 prefix (HString.mk_hstring ("_" ^ GI.array_comprehension))

(** An index variable of the element-wise definition of a ghost variable *)
let mk_fresh_index () =
  i := !i + 1;
  HString.mk_hstring (string_of_int !i ^ "_gidx")

(** The lowering of the comprehensions of a node body or of a contract *)
type lowering = {
  (* The node or contract the comprehensions are in, and its context *)
  scope_id : NodeId.t;
  mutable ctx : Ctx.tc_context;
  (* The comprehensions lowered so far, with their fresh variables *)
  mutable lowered : (A.expr * HString.t) list;
  (* [define p x ty ids extra_ids e] defines the fresh variable [x] of type
     [ty] by the equation [x[ids][extra_ids] = e]: a local variable in a node
     body, a ghost variable in a contract *)
  define :
    Lib.position -> HString.t -> A.lustre_type -> HString.t list ->
    HString.t list -> A.expr -> unit;
}

(** What to do with the comprehensions of an expression: lower them, or
    reject them *)
type mode =
  | Lower of lowering
  | Reject of string

(** Lower the array comprehensions of [e], innermost first. [bound] holds the
    variables bound around [e] in the expression being lowered. *)
let rec lower_expr mode bound e =
  let r = lower_expr mode bound in
  let rl = seq_map r in
  match e with
  | A.Ident _ | ModeRef _ | Const _ | Last _ | AbstractSymConst _
  | EmptyMap (_, None) | EmptySet (_, None) -> R.ok e
  | EmptyMap (_, Some (kt, vt)) ->
    let* () = check_type kt in let* () = check_type vt in R.ok e
  | EmptySet (_, Some ty) -> let* () = check_type ty in R.ok e
  | FieldProject (p, e, i, k) -> let* e = r e in R.ok (A.FieldProject (p, e, i, k))
  | UnaryOp (p, op, e) -> let* e = r e in R.ok (A.UnaryOp (p, op, e))
  | ConvOp (p, op, e) -> let* e = r e in R.ok (A.ConvOp (p, op, e))
  | Extract (p, e, i, j) -> let* e = r e in R.ok (A.Extract (p, e, i, j))
  | Pre (p, e) -> let* e = r e in R.ok (A.Pre (p, e))
  | TypeAscription (p, e, ty) ->
    let* () = check_type ty in let* e = r e in R.ok (A.TypeAscription (p, e, ty))
  | ADTTester (p, e, c) -> let* e = r e in R.ok (A.ADTTester (p, e, c))
  | BinaryOp (p, op, e1, e2) ->
    let* e1 = r e1 in let* e2 = r e2 in R.ok (A.BinaryOp (p, op, e1, e2))
  | CompOp (p, op, e1, e2) ->
    let* e1 = r e1 in let* e2 = r e2 in R.ok (A.CompOp (p, op, e1, e2))
  | ArrayConstr (p, e1, e2) ->
    let* e1 = r e1 in let* e2 = r e2 in R.ok (A.ArrayConstr (p, e1, e2))
  | IndexAccess (p, e1, e2, k) ->
    let* e1 = r e1 in let* e2 = r e2 in R.ok (A.IndexAccess (p, e1, e2, k))
  | Arrow (p, e1, e2) ->
    let* e1 = r e1 in let* e2 = r e2 in R.ok (A.Arrow (p, e1, e2))
  | Fby (p, e1, e2) ->
    let* e1 = r e1 in let* e2 = r e2 in R.ok (A.Fby (p, e1, e2))
  | Restart (p, e1, e2) ->
    let* e1 = r e1 in let* e2 = r e2 in R.ok (A.Restart (p, e1, e2))
  | TernaryOp (p, op, e1, e2, e3) ->
    let* e1 = r e1 in let* e2 = r e2 in let* e3 = r e3 in
    R.ok (A.TernaryOp (p, op, e1, e2, e3))
  | RecordExpr (p, id, tys, flds) ->
    let* () = check_types tys in
    let* flds = seq_map (fun (f, e) -> let* e = r e in R.ok (f, e)) flds in
    R.ok (A.RecordExpr (p, id, tys, flds))
  | GroupExpr (p, k, es) -> let* es = rl es in R.ok (A.GroupExpr (p, k, es))
  | Call (p, tys, id, es) ->
    let* () = check_types tys in let* es = rl es in R.ok (A.Call (p, tys, id, es))
  | ADTTerm (p, tys, c, es) ->
    let* () = check_types tys in let* es = rl es in R.ok (A.ADTTerm (p, tys, c, es))
  | RestartEvery (p, id, es, e) ->
    let* es = rl es in let* e = r e in R.ok (A.RestartEvery (p, id, es, e))
  | StructUpdate (p, e1, idxs, e2) ->
    let* e1 = r e1 in
    let* idxs = seq_map (lower_label_or_index mode bound) idxs in
    let* e2 = match e2 with
      | Some e2 -> let* e2 = r e2 in R.ok (Some e2)
      | None -> R.ok None
    in
    R.ok (A.StructUpdate (p, e1, idxs, e2))
  | AnyOp (p, ((_, id, _) as ti), e) ->
    let* e = lower_expr mode (A.SI.add id bound) e in R.ok (A.AnyOp (p, ti, e))
  | ChooseOp (p, ((_, id, _) as ti), e) ->
    let* e = lower_expr mode (A.SI.add id bound) e in R.ok (A.ChooseOp (p, ti, e))
  | Quantifier (p, q, tis, e) ->
    let* () = check_types (List.map (fun (_, _, ty) -> ty) tis) in
    let bound = List.fold_left (fun acc (_, id, _) -> A.SI.add id acc) bound tis in
    let* e = lower_expr mode bound e in
    R.ok (A.Quantifier (p, q, tis, e))
  | Match (p, e, arms, ty) ->
    let* () = match ty with Some ty -> check_type ty | None -> R.ok () in
    let* e = r e in
    let* arms = seq_map (fun (pat, arm) ->
      let bound = A.SI.union bound (AH.pat_bound_vars pat) in
      let* arm = lower_expr mode bound arm in
      R.ok (pat, arm)
    ) arms in
    R.ok (A.Match (p, e, arms, ty))
  (* A comprehension whose body is a comprehension has the dimensions of both,
     so that the inner body may mention the outer index variables *)
  | ArrayComprehension (p, bs1, ArrayComprehension (_, bs2, body)) as source ->
    let* res = r (A.ArrayComprehension (p, bs1 @ bs2, body)) in
    (* The fresh local stands for the comprehensions as written *)
    (match res with
     | A.Ident (_, x) when Hashtbl.mem sources x -> Hashtbl.replace sources x source
     | _ -> ());
    R.ok res
  | ArrayComprehension (p, bs, body) as source -> (
    match mode with
    | Reject where -> mk_error p (UnsupportedComprehensionPosition where)
    | Lower st ->
      let ids = List.map (fun (_, id, _) -> id) bs in
      let* body = lower_expr mode (A.SI.union bound (A.SI.of_list ids)) body in
      let comp = A.ArrayComprehension (p, bs, body) in
      (* The free variables of the comprehension, whose own index variables
         are bound in it *)
      let* () =
        match
          A.SI.elements (A.SI.inter (AH.vars_without_node_call_ids comp) bound)
        with
        | v :: _ -> mk_error p (BoundVariableInComprehension v)
        | [] -> R.ok ()
      in
      (* An equal comprehension lowered before has the same value, and shares
         its variable, unless it has calls, which may have distinct instances
         with distinct values *)
      let previous =
        if AH.expr_contains_call comp then None
        else
          List.find_opt (fun (c, _) -> AH.syn_expr_equal None c comp = Ok true)
            st.lowered
      in
      match previous with
      | Some (_, x) -> R.ok (A.Ident (p, x))
      | None ->
        (* The context holds the fresh variables of the comprehensions of the
           body, lowered above *)
        let* ty, _, _ = Chk.infer_type_expr st.ctx (Some st.scope_id) comp in
        (* An array definition takes an index for every dimension of the
           array, so the elements of an array type (such as the value of an
           inner comprehension) are defined element-wise with fresh index
           variables *)
        let elem_ty =
          List.fold_left (fun ty _ -> match ty with
            | A.ArrayType (_, (ty, _)) -> ty
            | _ -> assert false (* the type of a comprehension *)
          ) ty bs
        in
        let rec extra_dims ty =
          let* ty = Chk.expand_type_syn_reftype_history st.ctx ty in
          match ty with
          | A.ArrayType (_, (ty, _)) ->
            let* n = extra_dims ty in R.ok (n + 1)
          | _ -> R.ok 0
        in
        let* k = extra_dims elem_ty in
        let extra_ids = List.init k (fun _ -> mk_fresh_var ()) in
        let body =
          List.fold_left (fun e j -> A.IndexAccess (p, e, A.Ident (p, j), A.Array))
            body extra_ids
        in
        (* The fresh variable has the base type of the comprehension, without
           its refinement types (such as the subrange types of the values of
           its body): their constraints are not obligations of the user, and
           the ones of the variables the comprehension is assigned to are
           checked on those variables *)
        let* ty = Chk.expand_type_syn_reftype_history st.ctx ty in
        let x = mk_fresh_var () in
        Hashtbl.replace sources x source;
        st.ctx <- Ctx.add_ty st.ctx x ty;
        st.lowered <- (comp, x) :: st.lowered;
        st.define p x ty ids extra_ids body;
        R.ok (A.Ident (p, x))
  )

(* Comprehensions are not supported in types: the expressions of a type, such
   as the predicate of a refinement type, are not lowered *)
and check_type ty =
  let first a b = match a with Some _ -> a | None -> b in
  let find e =
    match lower_expr (Reject "") A.SI.empty e with
    | Ok _ -> None
    | Error (`LustreDesugarArrayComprehensionsError (pos, _)) -> Some pos
    | Error _ -> None
  in
  match AH.fold_lustre_ty ~into_ty_args:true find None first ty with
  | Some pos -> mk_error pos (UnsupportedComprehensionPosition "types")
  | None -> R.ok ()

and check_types tys = R.seq_ (List.map check_type tys)

and lower_label_or_index mode bound = function
  | A.Label _ as l -> R.ok l
  | Index (p, e, k) -> let* e = lower_expr mode bound e in R.ok (A.Index (p, e, k))
  | MapIndex (p, e) -> let* e = lower_expr mode bound e in R.ok (A.MapIndex (p, e))
  | SetIndex (p, e) -> let* e = lower_expr mode bound e in R.ok (A.SetIndex (p, e))
  | GenericIndex (p, e) ->
    let* e = lower_expr mode bound e in R.ok (A.GenericIndex (p, e))

let lower mode e = lower_expr mode A.SI.empty e

let lower_node_equation mode bound = function
  | A.Assert (p, e) -> let* e = lower_expr mode bound e in R.ok (A.Assert (p, e))
  | A.Equation (p, lhs, e) ->
    let* e = lower_expr mode bound e in R.ok (A.Equation (p, lhs, e))

(** Lower the comprehensions of a node item. [bound] holds the variables bound
    around the item, by the arms of the match blocks it is in. *)
let rec lower_node_item mode bound item =
  let low = lower_expr mode bound in
  match item with
  | A.Body eq -> let* eq = lower_node_equation mode bound eq in R.ok (A.Body eq)
  | IfBlock (p, e, l1, l2) ->
    let* e = low e in
    let* l1 = lower_node_items mode bound l1 in
    let* l2 = lower_node_items mode bound l2 in
    R.ok (A.IfBlock (p, e, l1, l2))
  | WhenBlock (p, e, l1, l2) ->
    let* e = low e in
    let* l1 = lower_node_items mode bound l1 in
    let* l2 = lower_node_items mode bound l2 in
    R.ok (A.WhenBlock (p, e, l1, l2))
  | MatchBlock (p, e, arms, ty) ->
    let* () = match ty with Some ty -> check_type ty | None -> R.ok () in
    let* e = low e in
    let* arms = seq_map (fun (pat, items) ->
      let bound = A.SI.union bound (AH.pat_bound_vars pat) in
      let* items = lower_node_items mode bound items in
      R.ok (pat, items)
    ) arms in
    R.ok (A.MatchBlock (p, e, arms, ty))
  | RestartBlock (p, items, e) ->
    let* items = lower_node_items mode bound items in
    let* e = low e in
    R.ok (A.RestartBlock (p, items, e))
  | FrameBlock (p, vars, nes, nis) ->
    let* nes = seq_map (lower_node_equation mode bound) nes in
    let* nis = lower_node_items mode bound nis in
    R.ok (A.FrameBlock (p, vars, nes, nis))
  | AnnotProperty (p, name, e, kind) ->
    let* e = low e in
    let* kind = match kind with
      | A.Provided c -> let* c = low c in R.ok (A.Provided c)
      | A.Invariant | A.Reachable _ -> R.ok kind
    in
    R.ok (A.AnnotProperty (p, name, e, kind))
  | AnnotMain _ | Auto _ as item -> R.ok item

and lower_node_items mode bound items =
  seq_map (lower_node_item mode bound) items

(** Lower the comprehensions of a contract to fresh ghost variables, each
    defined just before the item it is lowered from *)
let lower_contract ctx contract_id ((p, eqs) as contract) =
  (* The modes are not needed to type the comprehensions, and a mode may
     have the name of an input *)
  let* _, ctx, _ =
    Chk.tc_ctx_of_contract ~ignore_modes:true ctx Ctx.Ghost contract_id contract
  in
  let ghosts = ref [] in
  let define p x ty ids extra_ids body =
    (* The index variables are renamed apart, since the passes that follow
       do not see them bound in the right-hand side of a ghost variable, as
       they do in an array definition of a node *)
    let ids' = List.map (fun _ -> mk_fresh_index ()) ids in
    let body =
      List.fold_left2 (fun e i i' -> AH.substitute_naive i (A.Ident (p, i')) e)
        body ids ids'
    in
    let lhs = A.GhostArrayDef (p, (p, x, ty), ids' @ extra_ids) in
    ghosts := A.GhostVars (p, lhs, body) :: !ghosts
  in
  let mode = Lower { scope_id = contract_id; ctx; lowered = []; define } in
  let low e = lower mode e in
  let reject where e = let* _ = lower (Reject where) e in R.ok () in
  let lower_item = function
    | A.GhostConst (A.FreeConst (_, _, ty)) as eq -> let* () = check_type ty in R.ok eq
    | A.GhostConst (A.UntypedConst (_, _, e)) as eq ->
      let* () = reject "the ghost constants of a contract" e in R.ok eq
    | A.GhostConst (A.TypedConst (_, _, e, ty)) as eq ->
      let* () = check_type ty in
      let* () = reject "the ghost constants of a contract" e in R.ok eq
    | A.GhostVars (p, lhs, e) ->
      let* () = match lhs with
        | A.GhostVarDec (_, tis) -> check_types (List.map (fun (_, _, ty) -> ty) tis)
        | A.GhostArrayDef _ -> R.ok ()
      in
      let* e = low e in R.ok (A.GhostVars (p, lhs, e))
    | A.Assume (p, n, s, e) -> let* e = low e in R.ok (A.Assume (p, n, s, e))
    | A.Guarantee (p, n, s, e) -> let* e = low e in R.ok (A.Guarantee (p, n, s, e))
    | A.Decreases (_, e) as eq -> let* () = reject "decreases clauses" e in R.ok eq
    | A.Mode (p, id, reqs, enss) ->
      let low_item (p, n, e) = let* e = low e in R.ok (p, n, e) in
      let* reqs = seq_map low_item reqs in
      let* enss = seq_map low_item enss in
      R.ok (A.Mode (p, id, reqs, enss))
    | A.ContractCall (p, id, tys, es, outs) ->
      let* es = seq_map low es in R.ok (A.ContractCall (p, id, tys, es, outs))
    | A.AssumptionVars _ as eq -> R.ok eq
  in
  let* eqs =
    seq_map (fun eq ->
      let* eq = lower_item eq in
      let defs = List.rev !ghosts in
      ghosts := [];
      R.ok (defs @ [eq])
    ) eqs
  in
  R.ok (p, List.flatten eqs)

let lower_node ctx (node_id, ext, opac, nps, cctds, ctds, nlds, nis, co) =
  let* () =
    check_types
      (List.map (fun (_, _, ty, _, _) -> ty) cctds @ List.map (fun (_, _, ty, _) -> ty) ctds)
  in
  (* The local constants defined by comprehensions have been inlined (see
     [inline_comprehension_constants]) *)
  let* () =
    R.seq_ (List.map (function
      | A.NodeConstDecl (_, A.UntypedConst _) -> R.ok ()
      | A.NodeConstDecl (_, (A.FreeConst (_, _, ty) | A.TypedConst (_, _, _, ty)))
      | A.NodeVarDecl (_, (_, _, ty, _)) -> check_type ty
    ) nlds)
  in
  (* A contract sees the parameters of the node, but not its locals, which
     may have the names of its ghost variables *)
  let* co = match co with
    | Some c ->
      let contract_ctx = Chk.add_full_node_ctx ctx node_id nps cctds ctds [] in
      let* c = lower_contract contract_ctx node_id c in R.ok (Some c)
    | None -> R.ok None
  in
  let ctx = Chk.add_full_node_ctx ctx node_id nps cctds ctds nlds in
  let decls = ref [] in
  let eqs = ref [] in
  let define p x ty ids extra_ids body =
    let lhs = A.StructDef (p, [A.ArrayDef (p, x, ids @ extra_ids)]) in
    decls := A.NodeVarDecl (p, (p, x, ty, A.ClockTrue)) :: !decls;
    eqs := A.Body (A.Equation (p, lhs, body)) :: !eqs
  in
  let mode = Lower { scope_id = node_id; ctx; lowered = []; define } in
  let* nis = lower_node_items mode A.SI.empty nis in
  R.ok (node_id, ext, opac, nps, cctds, ctds,
        nlds @ List.rev !decls, nis @ List.rev !eqs, co)

(** The declaration with its comprehensions lowered, and [ctx] with the types
    of the ghost variables introduced in a contract node among its exports, as
    they are looked up when the contract is imported *)
let lower_decl ctx = function
  | A.NodeDecl (s, decl) ->
    let* decl = lower_node ctx decl in R.ok (ctx, A.NodeDecl (s, decl))
  | A.FuncDecl (s, decl, attrs) ->
    let* decl = lower_node ctx decl in R.ok (ctx, A.FuncDecl (s, decl, attrs))
  | A.ContractNodeDecl (s, (id, ps, ins, outs, c)) ->
    let* () =
      check_types
        (List.map (fun (_, _, ty, _, _) -> ty) ins @ List.map (fun (_, _, ty, _) -> ty) outs)
    in
    let node_ctx = Chk.add_full_node_ctx ctx id ps ins outs [] in
    let* ((_, eqs) as c) = lower_contract node_ctx id c in
    let ctx =
      match Ctx.lookup_contract_exports ctx id with
      | None -> ctx
      | Some exports ->
        let exports =
          List.fold_left (fun exports eq -> match eq with
            | A.GhostVars (_, A.GhostArrayDef (_, (_, x, ty), _), _) ->
              Ctx.IMap.add x ty exports
            | _ -> exports
          ) exports eqs
        in
        Ctx.add_contract_exports ctx id exports
    in
    R.ok (ctx, A.ContractNodeDecl (s, (id, ps, ins, outs, c)))
  | A.ConstDecl (_, A.UntypedConst (_, _, e)) as decl ->
    let* _ = lower (Reject "constant declarations") e in R.ok (ctx, decl)
  | A.ConstDecl (_, A.TypedConst (_, _, e, ty)) as decl ->
    let* () = check_type ty in
    let* _ = lower (Reject "constant declarations") e in R.ok (ctx, decl)
  | A.ConstDecl (_, A.FreeConst (_, _, ty)) as decl ->
    let* () = check_type ty in R.ok (ctx, decl)
  | A.TypeDecl (_, A.AliasType (_, _, _, ty)) as decl ->
    let* () = check_type ty in R.ok (ctx, decl)
  | A.TypeDecl (_, A.FreeType _) | A.NodeParamInst _ as decl -> R.ok (ctx, decl)

let desugar_array_comprehensions ctx decls =
  let* ctx, decls =
    R.seq_chain (fun (ctx, acc) decl ->
      let* ctx, decl = lower_decl ctx decl in
      R.ok (ctx, decl :: acc)
    ) (ctx, []) decls
  in
  R.ok (ctx, List.rev decls)

(* ********************************************************************** *)
(* Constants defined by comprehensions                                    *)
(* ********************************************************************** *)

let has_comprehension e =
  match lower (Reject "") e with Ok _ -> false | Error _ -> true

(** Split the constant declarations [decls] into those defined by an
    expression that contains a comprehension, possibly through the
    constants of [sigma], and the others. The definitions of the former,
    with the constants of [sigma] replaced, extend [sigma]. *)
let split_constants sigma decl_of decls =
  List.fold_left (fun (sigma, kept) decl ->
    match decl_of decl with
    | Some (id, e) ->
      let e = AH.apply_subst_in_expr sigma e in
      if has_comprehension e then (sigma @ [(id, e)], kept)
      else (sigma, decl :: kept)
    | None -> (sigma, decl :: kept)
  ) (sigma, []) decls
  |> fun (sigma, kept) -> sigma, List.rev kept

let const_def = function
  | A.UntypedConst (_, id, e) | A.TypedConst (_, id, e, _) -> Some (id, e)
  | A.FreeConst _ -> None

(** Fail if the variables [vars] of an item at [pos] include a constant of
    [sigma], which cannot be inlined there *)
let check_mentions_inlined sigma where pos vars =
  match List.find_opt (fun (c, _) -> A.SI.mem c vars) sigma with
  | Some (c, _) -> mk_error pos (ComprehensionConstantIn (c, where))
  | None -> R.ok ()

(** Fail if a type mentions a constant of [sigma] *)
let check_type_mentions_inlined sigma pos ty =
  check_mentions_inlined sigma "a type" pos (AH.vars_of_type ty)

(** [sigma] without the identifiers [ids], which shadow its constants *)
let unshadowed sigma ids =
  List.filter (fun (c, _) -> not (List.exists (HString.equal c) ids)) sigma

let subst_contract sigma (p, eqs) =
  let ghost_ids = List.concat_map (function
    | A.GhostVars (_, A.GhostVarDec (_, tis), _) -> List.map (fun (_, i, _) -> i) tis
    | A.GhostVars (_, A.GhostArrayDef (_, (_, i, _), _), _) -> [i]
    | A.GhostConst (A.FreeConst (_, i, _) | A.UntypedConst (_, i, _)
                   | A.TypedConst (_, i, _, _)) -> [i]
    | A.Mode (_, i, _, _) -> [i]
    | _ -> []
  ) eqs in
  let sigma = unshadowed sigma ghost_ids in
  (* The types of a contract, its ghost constants and its decreases clause
     cannot mention a constant defined by a comprehension, since the
     comprehension would not be supported there *)
  let check_ty p ty = check_type_mentions_inlined sigma p ty in
  let check_expr where p e =
    check_mentions_inlined sigma where p (AH.vars_without_node_call_ids e)
  in
  let ghost_const = "the ghost constants of a contract" in
  let* () =
    R.seq_ (List.map (function
      | A.GhostVars (_, A.GhostVarDec (_, tis), _) ->
        R.seq_ (List.map (fun (p, _, ty) -> check_ty p ty) tis)
      | A.GhostVars (_, A.GhostArrayDef (_, (p, _, ty), _), _) -> check_ty p ty
      | A.GhostConst (A.FreeConst (p, _, ty)) -> check_ty p ty
      | A.GhostConst (A.UntypedConst (p, _, e)) -> check_expr ghost_const p e
      | A.GhostConst (A.TypedConst (p, _, e, ty)) ->
        let* () = check_ty p ty in check_expr ghost_const p e
      | A.Decreases (p, e) -> check_expr "decreases clauses" p e
      | _ -> R.ok ()
    ) eqs)
  in
  let s = AH.apply_subst_in_expr sigma in
  let s_const = function
    | A.FreeConst _ as c -> c
    | A.UntypedConst (p, i, e) -> A.UntypedConst (p, i, s e)
    | A.TypedConst (p, i, e, ty) -> A.TypedConst (p, i, s e, ty)
  in
  R.ok (p, List.map (function
    | A.GhostConst c -> A.GhostConst (s_const c)
    | A.GhostVars (p, lhs, e) -> A.GhostVars (p, lhs, s e)
    | A.Assume (p, n, b, e) -> A.Assume (p, n, b, s e)
    | A.Guarantee (p, n, b, e) -> A.Guarantee (p, n, b, s e)
    | A.Decreases (p, e) -> A.Decreases (p, s e)
    | A.Mode (p, i, reqs, enss) ->
      let si (p, n, e) = (p, n, s e) in
      A.Mode (p, i, List.map si reqs, List.map si enss)
    | A.ContractCall (p, i, tys, es, outs) -> A.ContractCall (p, i, tys, List.map s es, outs)
    | A.AssumptionVars _ as eq -> eq
  ) eqs)

let subst_node sigma (node_id, ext, opac, nps, cctds, ctds, nlds, nis, co) =
  let params =
    List.map (fun (_, i, _, _, _) -> i) cctds @ List.map (fun (_, i, _, _) -> i) ctds
  in
  let sigma = unshadowed sigma params in
  (* The local variables shadow the constants, and the local constants
     defined by comprehensions are replaced as the global ones *)
  let local_vars = List.filter_map (function
    | A.NodeVarDecl (_, (_, i, _, _)) -> Some i
    | A.NodeConstDecl _ -> None) nlds
  in
  let sigma = unshadowed sigma local_vars in
  let sigma, nlds =
    split_constants sigma
      (function A.NodeConstDecl (_, c) -> const_def c | A.NodeVarDecl _ -> None)
      nlds
  in
  let types =
    List.map (fun (p, _, ty, _, _) -> (p, ty)) cctds
    @ List.map (fun (p, _, ty, _) -> (p, ty)) ctds
    @ List.filter_map (function
      | A.NodeVarDecl (p, (_, _, ty, _)) -> Some (p, ty)
      | A.NodeConstDecl (p, (A.FreeConst (_, _, ty) | A.TypedConst (_, _, _, ty))) -> Some (p, ty)
      | A.NodeConstDecl (_, A.UntypedConst _) -> None) nlds
  in
  let* () =
    R.seq_ (List.map (fun (p, ty) -> check_type_mentions_inlined sigma p ty) types)
  in
  let nlds = List.map (function
    | A.NodeConstDecl (p, A.UntypedConst (p2, i, e)) ->
      A.NodeConstDecl (p, A.UntypedConst (p2, i, AH.apply_subst_in_expr sigma e))
    | A.NodeConstDecl (p, A.TypedConst (p2, i, e, ty)) ->
      A.NodeConstDecl (p, A.TypedConst (p2, i, AH.apply_subst_in_expr sigma e, ty))
    | d -> d) nlds
  in
  let nis = List.map (AH.apply_subst_in_node_item sigma) nis in
  let* co = match co with
    | Some c -> let* c = subst_contract sigma c in R.ok (Some c)
    | None -> R.ok None
  in
  R.ok (node_id, ext, opac, nps, cctds, ctds, nlds, nis, co)

let inline_comprehension_constants consts decls =
  let sigma, consts =
    split_constants []
      (function A.ConstDecl (_, c) -> const_def c | _ -> None)
      consts
  in
  let* () =
    R.seq_ (List.map (function
      | A.ConstDecl (s, (A.FreeConst (_, _, ty) | A.TypedConst (_, _, _, ty))) ->
        check_type_mentions_inlined sigma s.A.start_pos ty
      | A.TypeDecl (s, A.AliasType (_, _, _, ty)) ->
        check_type_mentions_inlined sigma s.A.start_pos ty
      | _ -> R.ok ()
    ) consts)
  in
  let* decls =
    seq_map (function
      | A.NodeDecl (s, d) -> let* d = subst_node sigma d in R.ok (A.NodeDecl (s, d))
      | A.FuncDecl (s, d, a) -> let* d = subst_node sigma d in R.ok (A.FuncDecl (s, d, a))
      | A.ContractNodeDecl (s, (id, ps, ins, outs, c)) ->
        let params =
          List.map (fun (_, i, _, _, _) -> i) ins @ List.map (fun (_, i, _, _) -> i) outs
        in
        let* () =
          R.seq_ (List.map (fun (p, ty) -> check_type_mentions_inlined sigma p ty)
            (List.map (fun (p, _, ty, _, _) -> (p, ty)) ins
             @ List.map (fun (p, _, ty, _) -> (p, ty)) outs))
        in
        let* c = subst_contract (unshadowed sigma params) c in
        R.ok (A.ContractNodeDecl (s, (id, ps, ins, outs, c)))
      | d -> R.ok d
    ) decls
  in
  R.ok (consts, decls)
