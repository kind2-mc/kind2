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

    A comprehension whose body is a comprehension is lowered as a single one
    with the index variables of both. Otherwise, a comprehension is lowered
    after the comprehensions in its body, so that its equation mentions their
    variables. It cannot mention a variable bound around it (by a quantifier,
    an enclosing comprehension or a match arm), since its equation is placed
    in the body of the node. Comprehensions are not supported in contracts and
    in constant declarations.

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

let error_message = function
  | BoundVariableInComprehension v ->
    "An array comprehension cannot mention the variable '"
    ^ HString.string_of_hstring v
    ^ "' bound by an enclosing quantifier, array comprehension or match arm"
  | UnsupportedComprehensionPosition where ->
    "Array comprehensions are not supported in " ^ where

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

(** What to do with the comprehensions of a node or a contract: lower them,
    accumulating the declarations and equations of their fresh locals, or the
    definitions of their fresh ghost variables, or reject them *)
type mode =
  | Lower of {
      node_id : NodeId.t;
      mutable ctx : Ctx.tc_context;
      mutable decls : A.node_local_decl list;
      mutable eqs : A.node_item list;
    }
  | LowerContract of {
      contract_id : NodeId.t;
      mutable contract_ctx : Ctx.tc_context;
      mutable ghosts : A.contract_node_equation list;
    }
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
    | Lower { node_id; ctx; _ } | LowerContract { contract_id = node_id; contract_ctx = ctx; _ } ->
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
      let* ty, _, _ = Chk.infer_type_expr ctx (Some node_id) comp in
      (* An array definition takes an index for every dimension of the array,
         so the elements of an array type (such as the value of an inner
         comprehension) are defined element-wise with fresh index variables *)
      let elem_ty =
        List.fold_left (fun ty _ -> match ty with
          | A.ArrayType (_, (ty, _)) -> ty
          | _ -> assert false (* the type of a comprehension *)
        ) ty bs
      in
      let rec extra_dims ty =
        let* ty = Chk.expand_type_syn_reftype_history ctx ty in
        match ty with
        | A.ArrayType (_, (ty, _)) ->
          let* n = extra_dims ty in R.ok (n + 1)
        | _ -> R.ok 0
      in
      let* k = extra_dims elem_ty in
      let extra_ids = List.init k (fun _ -> mk_fresh_var ()) in
      let index body ids =
        List.fold_left (fun e j -> A.IndexAccess (p, e, A.Ident (p, j), A.Array))
          body ids
      in
      let x = mk_fresh_var () in
      Hashtbl.replace sources x source;
      (match mode with
       | Lower st ->
         let lhs = A.StructDef (p, [A.ArrayDef (p, x, ids @ extra_ids)]) in
         st.ctx <- Ctx.add_ty st.ctx x ty;
         st.decls <- A.NodeVarDecl (p, (p, x, ty, A.ClockTrue)) :: st.decls;
         st.eqs <- A.Body (A.Equation (p, lhs, index body extra_ids)) :: st.eqs
       | LowerContract st ->
         (* The index variables are renamed apart, since the passes that
            follow do not see them bound in the right-hand side of a ghost
            variable, as they do in an array definition of a node *)
         let ids' = List.map (fun _ -> mk_fresh_index ()) ids in
         let body =
           List.fold_left2 (fun e i i' -> AH.substitute_naive i (A.Ident (p, i')) e)
             body ids ids'
         in
         let lhs = A.GhostArrayDef (p, (p, x, ty), ids' @ extra_ids) in
         st.contract_ctx <- Ctx.add_ty st.contract_ctx x ty;
         st.ghosts <- A.GhostVars (p, lhs, index body extra_ids) :: st.ghosts
       | Reject _ -> assert false);
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

(** The types of the ghost variables and constants of a contract, added to
    [ctx] so that the comprehensions that mention them can be typed *)
let add_ghost_types ctx contract_id eqs =
  List.fold_left (fun ctx eq -> match eq with
    | A.GhostVars (_, A.GhostVarDec (_, tis), _) ->
      List.fold_left (fun ctx (_, id, ty) -> Ctx.add_ty ctx id ty) ctx tis
    | A.GhostConst (A.FreeConst (_, id, ty) | A.TypedConst (_, id, _, ty)) ->
      Ctx.add_ty ctx id ty
    | A.GhostConst (A.UntypedConst (_, id, e)) -> (
      match Chk.infer_type_expr ctx (Some contract_id) e with
      | Ok (ty, _, _) -> Ctx.add_ty ctx id ty
      | Error _ -> ctx)
    | _ -> ctx
  ) ctx eqs

(** Lower the comprehensions of a contract to fresh ghost variables, each
    defined just before the item it is lowered from *)
let lower_contract ctx contract_id (p, eqs) =
  let contract_ctx = add_ghost_types ctx contract_id eqs in
  let st = LowerContract { contract_id; contract_ctx; ghosts = [] } in
  let low e = lower st e in
  let reject where e = let* _ = lower (Reject where) e in R.ok () in
  let lower_item = function
    | A.GhostConst (A.FreeConst (_, _, ty)) as eq -> let* () = check_type ty in R.ok eq
    | A.GhostConst (A.UntypedConst (_, _, e)) as eq ->
      let* () = reject "constant declarations" e in R.ok eq
    | A.GhostConst (A.TypedConst (_, _, e, ty)) as eq ->
      let* () = check_type ty in
      let* () = reject "constant declarations" e in R.ok eq
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
      match st with
      | LowerContract st ->
        let ghosts = List.rev st.ghosts in
        st.ghosts <- [];
        R.ok (ghosts @ [eq])
      | Lower _ | Reject _ -> assert false
    ) eqs
  in
  R.ok (p, List.flatten eqs)

let lower_node ctx (node_id, ext, opac, nps, cctds, ctds, nlds, nis, co) =
  let* () =
    check_types
      (List.map (fun (_, _, ty, _, _) -> ty) cctds @ List.map (fun (_, _, ty, _) -> ty) ctds)
  in
  let* () =
    R.seq_ (List.map (function
      | A.NodeConstDecl (_, A.UntypedConst (_, _, e)) ->
        let* _ = lower (Reject "constant declarations") e in R.ok ()
      | A.NodeConstDecl (_, A.TypedConst (_, _, e, ty)) ->
        let* () = check_type ty in
        let* _ = lower (Reject "constant declarations") e in R.ok ()
      | A.NodeConstDecl (_, A.FreeConst (_, _, ty)) | A.NodeVarDecl (_, (_, _, ty, _)) ->
        check_type ty
    ) nlds)
  in
  let ctx = Chk.add_full_node_ctx ctx node_id nps cctds ctds nlds in
  let* co = match co with
    | Some c -> let* c = lower_contract ctx node_id c in R.ok (Some c)
    | None -> R.ok None
  in
  let st = Lower { node_id; ctx; decls = []; eqs = [] } in
  let* nis = lower_node_items st A.SI.empty nis in
  match st with
  | Lower { decls; eqs; _ } ->
    R.ok (node_id, ext, opac, nps, cctds, ctds,
          nlds @ List.rev decls, nis @ List.rev eqs, co)
  | LowerContract _ | Reject _ -> assert false

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
