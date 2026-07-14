(* This file is part of the Kind 2 model checker.

   Copyright (c) 2023 by the Board of Trustees of the University of Iowa

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
module GI = GeneratedIdentifiers
module NI = NodeId

open A

let i = ref 0
let mk_fresh_dummy_index () =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  HString.concat2 prefix (HString.mk_hstring "_index")

type error_kind =
  | ADTBoundVariable

let error_message = function
  | ADTBoundVariable ->
    "Refinement types with a datatype as the bound variable type are not currently supported"

let (let*) = Result.bind

(* currently unused *)
(*let mk_error pos kind = Error (`LustreFlattenRefinementTypesError (pos, kind))*)

let rec flatten_ref_type ctx ty = match ty with
  | A.UserType (pos, ty_args, str) ->
    let ty = TypeCheckerContext.lookup_ty_syn ctx str ty_args in
    (match ty with
    | Some (A.ADT _) -> Ok (A.UserType (pos, ty_args, str))
    | Some ty -> flatten_ref_type ctx ty
    | None -> Ok (A.UserType (pos, ty_args, str)))
  | RecordType (pos, id, tis) ->
    let* tis = Res.seq (List.map (fun (p, id, ty) ->
      let* ty = flatten_ref_type ctx ty in Ok (p, id, ty)
    ) tis) in
    Ok (A.RecordType (pos, id, tis))
  | Set (pos, ty) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (A.Set (pos, ty))
  | Map (pos, ty1, ty2) ->
    let* ty1 = flatten_ref_type ctx ty1 in
    let* ty2 = flatten_ref_type ctx ty2 in
    Ok (A.Map (pos, ty1, ty2))
  | TupleType (pos, tys) | GroupType (pos, tys) ->
    let* tys = Res.seq (List.map (flatten_ref_type ctx) tys) in
    Ok (A.TupleType (pos, tys))
  | ArrayType (pos, (ty, expr)) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (A.ArrayType (pos, (ty, expr)))
  | RefinementType (pos, (pos2, id, ty), expr) ->
    let* ty = flatten_ref_type ctx ty in
    let rec chase_refinements ty = match ty with
    | A.RefinementType (_, (_, id2, ty2), expr2) ->
      let cons = chase_refinements ty2 in
      (AH.substitute_naive id2 (Ident(pos, id)) expr2) :: cons
    | RecordType (_, _, tis) ->
      List.map (fun (_, id2, ty) -> 
        let exprs = chase_refinements ty in 
        List.map (AH.substitute_naive id (A.FieldProject(pos, Ident(pos, id), id2, None))) exprs
      ) tis |> List.flatten
    | TupleType (pos, tys) | GroupType (pos, tys) -> 
      List.mapi (fun i ty ->
        let exprs = chase_refinements ty in
        let i = i |> string_of_int |> HString.mk_hstring in
        List.map (AH.substitute_naive id (A.IndexAccess (pos, Ident(pos, id), A.Const (pos, A.Num i), A.Tuple))) exprs
      ) tys |> List.flatten
    | Set (pos, ty) ->
      let dummy_index = mk_fresh_dummy_index () in
      let exprs = chase_refinements ty in
      List.map (fun expr ->
        let idx = A.Ident(pos, dummy_index) in
        let expr = AH.substitute_naive id idx expr in
        let expr =
          A.BinaryOp(pos, A.Impl, A.BinaryOp(pos, In Set, Ident(pos, dummy_index), Ident(pos, id)), expr)
        in
        let ty = LustreTypeChecker.expand_type_syn_reftype_history ctx ty |> Result.get_ok in 
        A.Quantifier(pos, Forall, [pos, dummy_index, ty], expr)
      ) exprs
    | Map (pos, ty1, ty2) ->
      let dummy_index = mk_fresh_dummy_index () in
      let exprs1 = chase_refinements ty1 in
      let exprs1 = List.map (fun expr ->
        let idx = A.Ident(pos, dummy_index) in
        let expr = AH.substitute_naive id idx expr in
        let expr =
          A.BinaryOp(pos, A.Impl, A.BinaryOp(pos, In Map, Ident(pos, dummy_index), Ident(pos, id)), expr)
        in
        let ty1 = LustreTypeChecker.expand_type_syn_reftype_history ctx ty1 |> Result.get_ok in 
        A.Quantifier(pos, Forall, [pos, dummy_index, ty1], expr)
      ) exprs1 in 
      let exprs2 = chase_refinements ty2 in
      let exprs2 = List.map (fun expr ->
        let idx =
          A.IndexAccess(pos, Ident(pos, id), Ident(pos, dummy_index), Map)
        in
        let expr = AH.substitute_naive id idx expr in
        let expr =
          A.BinaryOp(pos, A.Impl, A.BinaryOp(pos, In Map, Ident(pos, dummy_index), Ident(pos, id)), expr)
        in
        A.Quantifier(pos, Forall, [pos, dummy_index, ty1], expr)
      ) exprs2 in 
      exprs1 @ exprs2
    | ArrayType (pos, (ty, len)) ->
      let dummy_index = mk_fresh_dummy_index () in
      let exprs = chase_refinements ty in
      List.map (fun expr ->
        let idx =
          A.IndexAccess(pos, Ident(pos, id), Ident(pos, dummy_index), Array)
        in
        let expr = AH.substitute_naive id idx expr in
        let bound1 = 
          A.CompOp(pos, Lte, A.Const(pos, Num (HString.mk_hstring "0")), A.Ident(pos, dummy_index)) 
        in 
        let bound2 = A.CompOp(pos, Lt, A.Ident(pos, dummy_index), len) in
        let expr = A.BinaryOp(pos, Impl, A.BinaryOp(pos, And, bound1, bound2), expr) in
        A.Quantifier(pos, Forall, [pos, dummy_index, A.Int pos], expr)
      ) exprs
    | Int _ | Bool _ | Real _ | AbstractType _ | EnumType _ 
    | History _ | TArr _ | UserType _ | SBitVector _ | UBitVector _ -> []
    | ADT _ -> assert false (* desugared in lustreDesugarADTs *)
    in
    let constraints = chase_refinements ty in 
    let expr = List.fold_left (fun acc expr ->
      A.BinaryOp(pos, And, acc, expr)
    ) expr constraints in
    (match LustreTypeChecker.expand_type_syn_reftype_history ctx ty with
      | Ok ty -> Ok (A.RefinementType (pos, (pos2, id, ty), expr))
      | _ -> assert false)
  | Int _ | Bool _ | Real _ | AbstractType _ | EnumType _ 
  | History _ | TArr _ | SBitVector _ | UBitVector _ -> Ok ty
  | ADT _ -> (*!! TODO *) Ok ty

let flatten_ref_types_local_decl ctx = function 
  | A.NodeConstDecl (pos, FreeConst (pos2, id, ty)) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (A.NodeConstDecl (pos, FreeConst (pos2, id, ty)))
  | A.NodeConstDecl (pos, TypedConst (pos2, id, expr, ty)) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (A.NodeConstDecl (pos, TypedConst (pos2, id, expr, ty)))
  | NodeVarDecl (pos, (pos2, id, ty, cl)) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (NodeVarDecl (pos, (pos2, id, ty, cl)))
  | decl -> Ok decl


let rec flatten_ref_types_expr: TypeCheckerContext.tc_context -> A.expr -> (A.expr, _) result =
  fun ctx e ->
  let rc e = flatten_ref_types_expr ctx e in
  match e with
  (* Expressions with types *)
  | Quantifier (p, q, tis, e) ->
    let* tis = Res.seq (List.map (fun (p, id, ty) ->
      let* ty = flatten_ref_type ctx ty in Ok (p, id, ty)
    ) tis) in
    let* e = rc e in
    Ok (Quantifier (p, q, tis, e))
  | EmptySet (p, Some ty) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (EmptySet (p, Some ty))
  | EmptyMap (p, Some (kt, vt)) ->
    let* kt = flatten_ref_type ctx kt in
    let* vt = flatten_ref_type ctx vt in
    Ok (EmptyMap (p, Some (kt, vt)))
  (* Everything else *)
  | Ident _ | Last _ | EmptyMap (_, None) | EmptySet (_, None)
  | ModeRef _ as e -> Ok e
  | FieldProject (p, e, i, ty_opt) -> 
    let* e = rc e in
    Ok (FieldProject (p, e, i, ty_opt))
  | Const _ as e -> Ok e
  | UnaryOp (p, op, e) -> 
    let* e = rc e in
    Ok (UnaryOp (p, op, e))
  | BinaryOp (p, op, e1, e2) -> 
    let* e1 = rc e1 in
    let* e2 = rc e2 in
    Ok (BinaryOp (p, op, e1, e2))
  | TernaryOp (p, op, e1, e2, e3) -> 
    let* e1 = rc e1 in
    let* e2 = rc e2 in
    let* e3 = rc e3 in
    Ok (TernaryOp (p, op, e1, e2, e3))
  | ConvOp  (p, op, e) -> 
    let* e = rc e in
    Ok (ConvOp (p, op, e))
  | CompOp (p, op, e1, e2) -> 
    let* e1 = rc e1 in
    let* e2 = rc e2 in
    Ok (CompOp (p, op, e1, e2))
  | Extract (p, e, idx1, idx2) -> 
    let* e = rc e in
    Ok (Extract (p, e, idx1, idx2))
  | AnyOp _ -> assert false (* desugared in lustreDesugarAnyChooseOps *)
  | ChooseOp _ -> assert false (* desugared in lustreDesugarAnyChooseOps *)
  | RecordExpr (p, i, ps, flds) ->
    let* ps = Res.seq (List.map (flatten_ref_type ctx) ps) in
    let* flds = Res.seq (List.map (fun (f, e) -> let* e = rc e in Ok (f, e)) flds) in
    Ok (RecordExpr (p, i, ps, flds))
  | GroupExpr (p, g, es) ->
    let* es = Res.seq (List.map rc es) in Ok (GroupExpr (p, g, es))
  | StructUpdate (p, e1, i, Some e2) ->
    let* e1 = rc e1 in let* e2 = rc e2 in Ok (StructUpdate (p, e1, i, Some e2))
  | StructUpdate (p, e1, i, None) ->
    let* e1 = rc e1 in Ok (StructUpdate (p, e1, i, None))
  | ArrayConstr (p, e1, e2) ->
    let* e1 = rc e1 in let* e2 = rc e2 in Ok (ArrayConstr (p, e1, e2))
  | IndexAccess (p, e1, e2, k) ->
    let* e1 = rc e1 in let* e2 = rc e2 in Ok (IndexAccess (p, e1, e2, k))
  | When (p, e, c) ->
    let* e = rc e in Ok (When (p, e, c))
  | Condact (p, e1, e2, i, es1, es2) ->
    let* e1 = rc e1 in let* e2 = rc e2 in
    let* es1 = Res.seq (List.map rc es1) in let* es2 = Res.seq (List.map rc es2) in
    Ok (Condact (p, e1, e2, i, es1, es2))
  | Activate (p, i, e1, e2, es) ->
    let* e1 = rc e1 in let* e2 = rc e2 in
    let* es = Res.seq (List.map rc es) in
    Ok (Activate (p, i, e1, e2, es))
  | Merge (p, i, es) ->
    let* es = Res.seq (List.map (fun (i, e) -> let* e = rc e in Ok (i, e)) es) in
    Ok (Merge (p, i, es))
  | RestartEvery (p, i, es, e) ->
    let* es = Res.seq (List.map rc es) in let* e = rc e in
    Ok (RestartEvery (p, i, es, e))
  | Pre (p, e) ->
    let* e = rc e in Ok (Pre (p, e))
  | Arrow (p, e1, e2) ->
    let* e1 = rc e1 in let* e2 = rc e2 in Ok (Arrow (p, e1, e2))
  | TypeAscription (p, e, ty) ->
    let* e = rc e in let* ty = flatten_ref_type ctx ty in
    Ok (TypeAscription (p, e, ty))
  | Call (p, ty_args, i, es) ->
    let* es = Res.seq (List.map rc es) in Ok (Call (p, ty_args, i, es))
  | Match (p, e, arms, ty_opt) ->
    let* e = rc e in
    let* arms = Res.seq (List.map (fun (pat, arm_e) -> let* e = rc arm_e in Ok (pat, e)) arms) in
    Ok (Match (p, e, arms, ty_opt))
  | ADTTerm (p, ty_args, ctor, args) ->
    let* ty_args = Res.seq (List.map (flatten_ref_type ctx) ty_args) in
    let* args = Res.seq (List.map rc args) in Ok (ADTTerm (p, ty_args, ctor, args))
  | ADTTester _ -> assert false

let flatten_ref_types_item ctx item =
  match item with
  | A.AnnotProperty (p, id, expr, k) ->
    let* expr = flatten_ref_types_expr ctx expr in
    Ok (A.AnnotProperty (p, id, expr, k))
  | Body _ | FrameBlock _ | IfBlock _ | WhenBlock _ | AnnotMain _ | Auto _ -> Ok item

let flatten_ref_types_const_decl ctx decl =
  match decl with
  | A.FreeConst (pos, id, ty) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (A.FreeConst (pos, id, ty))
  | TypedConst (pos, id, expr, ty) ->
    let* ty = flatten_ref_type ctx ty in
    Ok (TypedConst (pos, id, expr, ty))
  | UntypedConst _ -> Ok decl

let flatten_ref_types_contract_eq ctx eq =
  match eq with
  | A.GhostConst cd ->
    let* cd = flatten_ref_types_const_decl ctx cd in
    Ok (A.GhostConst cd)
  | A.GhostVars (p1, GhostVarDec (p2, tids), expr) ->
    let* tids = Res.seq (List.map (fun (p, id, ty) ->
      let* ty = flatten_ref_type ctx ty in Ok (p, id, ty)
    ) tids) in
    Ok (A.GhostVars (p1, GhostVarDec (p2, tids), expr))
  | A.Assume (p, id, s, expr) ->
    let* expr = flatten_ref_types_expr ctx expr in
    Ok (A.Assume (p, id, s, expr))
  | A.Guarantee (p, id, s, expr) ->
    let* expr = flatten_ref_types_expr ctx expr in
    Ok (A.Guarantee (p, id, s, expr))
  | A.Decreases (p, expr) ->
    let* expr = flatten_ref_types_expr ctx expr in
    Ok (A.Decreases (p, expr))
  | A.Mode (p, id, requires, ensures) ->
    let* requires = Res.seq (List.map (fun (p, id, expr) ->
      let* expr = flatten_ref_types_expr ctx expr in Ok (p, id, expr)
    ) requires) in
    let* ensures = Res.seq (List.map (fun (p, id, expr) ->
      let* expr = flatten_ref_types_expr ctx expr in Ok (p, id, expr)
    ) ensures) in
    Ok (A.Mode (p, id, requires, ensures))
  | A.ContractCall (pos, id, ps, args, outputs) ->
    let* ps = Res.seq (List.map (flatten_ref_type ctx) ps) in
    let* args = Res.seq (List.map (flatten_ref_types_expr ctx) args) in
    Ok (A.ContractCall (pos, id, ps, args, outputs))
  | AssumptionVars _ -> Ok eq

let flatten_ref_types_contract ctx (p, contract_eqs) =
  let* contract_eqs = Res.seq (List.map (flatten_ref_types_contract_eq ctx) contract_eqs) in
  Ok (p, contract_eqs)

let flatten_ref_types_contract_opt ctx = function
  | Some c ->
    let* c = flatten_ref_types_contract ctx c in Ok (Some c)
  | None -> Ok None

let flatten_ref_types ctx (gids : GI.t NI.Map.t) decls =
  let flatten_node_decl_ctx ctx params =
    List.fold_left (fun acc p ->
      TypeCheckerContext.add_ty_syn acc p (A.AbstractType (Lib.dummy_pos, p))
    ) ctx params
  in
  let flatten_inputs ctx ips =
    Res.seq (List.map (fun (pos, id, ty, cl, b) ->
      let* ty = flatten_ref_type ctx ty in Ok (pos, id, ty, cl, b)
    ) ips)
  in
  let flatten_outputs ctx ops =
    Res.seq (List.map (fun (pos, id, ty, cl) ->
      let* ty = flatten_ref_type ctx ty in Ok (pos, id, ty, cl)
    ) ops)
  in
  let* decls = Res.seq (List.map (fun decl -> match decl with
    | A.TypeDecl (pos, AliasType (pos2, id, ps, ty)) ->
      let* ty = flatten_ref_type ctx ty in
      Ok (A.TypeDecl (pos, AliasType (pos2, id, ps, ty)))
    | NodeDecl (pos, (id, imported, opac, params, ips, ops, locals, items, contract)) ->
      let ctx = flatten_node_decl_ctx ctx params in
      let* ips = flatten_inputs ctx ips in
      let* ops = flatten_outputs ctx ops in
      let* locals = Res.seq (List.map (flatten_ref_types_local_decl ctx) locals) in
      let* items = Res.seq (List.map (flatten_ref_types_item ctx) items) in
      let* contract = flatten_ref_types_contract_opt ctx contract in
      Ok (NodeDecl (pos, (id, imported, opac, params, ips, ops, locals, items, contract)))
    | FuncDecl (pos, (id, imported, opac, params, ips, ops, locals, items, contract), is_rec) ->
      let ctx = flatten_node_decl_ctx ctx params in
      let* ips = flatten_inputs ctx ips in
      let* ops = flatten_outputs ctx ops in
      let* locals = Res.seq (List.map (flatten_ref_types_local_decl ctx) locals) in
      let* items = Res.seq (List.map (flatten_ref_types_item ctx) items) in
      let* contract = flatten_ref_types_contract_opt ctx contract in
      Ok (FuncDecl (pos, (id, imported, opac, params, ips, ops, locals, items, contract), is_rec))
    | NodeParamInst (pos, (id1, id2, tys)) ->
      let* tys = Res.seq (List.map (flatten_ref_type ctx) tys) in
      Ok (NodeParamInst (pos, (id1, id2, tys)))
    | ContractNodeDecl (pos, (id, params, ips, ops, contract)) ->
      let* ips = flatten_inputs ctx ips in
      let* ops = flatten_outputs ctx ops in
      let* contract = flatten_ref_types_contract ctx contract in
      Ok (ContractNodeDecl (pos, (id, params, ips, ops, contract)))
    | ConstDecl (pos, cd) ->
      let* cd = flatten_ref_types_const_decl ctx cd in
      Ok (ConstDecl (pos, cd))
    | A.TypeDecl (_, FreeType _) -> Ok decl
  ) decls) in
  let* gids = Res.seq_chain (fun acc (k, gids) ->
    let* ib_oracles = Res.seq (List.map (fun (id, ty) ->
      let* ty = flatten_ref_type ctx ty in Ok (id, ty)
    ) gids.GI.ib_oracles) in
    let* locals =
      let bindings = GI.StringMap.bindings gids.GI.locals in
      let* bindings = Res.seq (List.map (fun (id, ty) ->
        let* ty = flatten_ref_type ctx ty in Ok (id, ty)
      ) bindings) in
      Ok (List.fold_left (fun m (k, v) -> GI.StringMap.add k v m) GI.StringMap.empty bindings)
    in
    Ok (NI.Map.add k { gids with GI.ib_oracles; GI.locals } acc)
  ) NI.Map.empty (NI.Map.bindings gids) in
  Ok (decls, gids)
