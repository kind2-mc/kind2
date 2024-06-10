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
module AN = LustreAstNormalizer

let rec flatten_ref_type ctx ty = match ty with
  | A.UserType (pos, str) -> 
    let ty = TypeCheckerContext.lookup_ty_syn ctx str in 
    (match ty with 
    | Some ty -> flatten_ref_type ctx ty
    | None -> A.UserType (pos, str))
  | RecordType (pos, id, tis) -> 
    let tis = List.map (fun (pos, id, ty) -> pos, id, flatten_ref_type ctx ty) tis in 
    RecordType (pos, id, tis)
  | TupleType (pos, tys) | GroupType (pos, tys) -> 
    let tys = List.map (flatten_ref_type ctx) tys in 
    TupleType (pos, tys)
  | ArrayType (pos, (ty, expr)) -> 
    let ty = flatten_ref_type ctx ty in 
    ArrayType (pos, (ty, expr))
  | RefinementType (pos, (pos2, id, ty), expr) -> 
    let ty = flatten_ref_type ctx ty in
    let rec chase_refinements ty = match ty with 
    | A.RefinementType (_, (_, id2, ty2), expr2) -> 
      let cons = chase_refinements ty2 in
      (AH.substitute_naive id2 (Ident(pos, id)) expr2) :: cons
    | RecordType (_, _, tis) ->
      List.map (fun (_, id2, ty) -> 
        let exprs = chase_refinements ty in 
        List.map (AH.substitute_naive id (A.RecordProject(pos, Ident(pos, id), id2))) exprs
      ) tis |> List.flatten
    | TupleType (pos, tys) | GroupType (pos, tys) -> 
      List.mapi (fun i ty ->
        let exprs = chase_refinements ty in
        List.map (AH.substitute_naive id (A.TupleProject(pos, Ident(pos, id), i))) exprs
      ) tys |> List.flatten
    | ArrayType (pos, (ty, len)) -> 
      let dummy_index = AN.mk_fresh_dummy_index () in
      let exprs = chase_refinements ty in
      List.map (fun expr -> 
        let expr = AH.substitute_naive id (A.ArrayIndex(pos, Ident(pos, id), Ident(pos, dummy_index))) expr in
        let bound1 = 
          A.CompOp(pos, Lte, A.Const(pos, Num (HString.mk_hstring "0")), A.Ident(pos, dummy_index)) 
        in 
        let bound2 = A.CompOp(pos, Lt, A.Ident(pos, dummy_index), len) in
        let expr = A.BinaryOp(pos, Impl, A.BinaryOp(pos, And, bound1, bound2), expr) in
        A.Quantifier(pos, Forall, [pos, dummy_index, A.Int pos], expr)
      ) exprs
    | Int _ | Int64 _ | Int32 _ | Int16 _ | Int8 _ | UInt64 _ | UInt32 _ | UInt16 _ | UInt8 _ 
    | Bool _ | TVar _ | IntRange _ | Real _ | AbstractType _ | EnumType _ 
    | History _ | TArr _ | UserType _ -> []
    in
    let constraints = chase_refinements ty in 
    let expr = List.fold_left (fun acc expr ->
      A.BinaryOp(pos, And, acc, expr)
    ) expr constraints in
    (match LustreTypeChecker.expand_type_syn_reftype_history ctx ty with 
      | Ok (ty) -> RefinementType (pos, (pos2, id, ty), expr)
      | _ -> assert false)
  | Int _ | Int64 _ | Int32 _ | Int16 _ | Int8 _ | UInt64 _ | UInt32 _ | UInt16 _ | UInt8 _ | Bool _  
  | TVar _ | IntRange _ | Real _ | AbstractType _ | EnumType _ | History _ | TArr _ -> ty

let flatten_ref_types_local_decl ctx = function 
  | A.NodeConstDecl (pos, FreeConst (pos2, id, ty)) ->
    A.NodeConstDecl (pos, FreeConst (pos2, id, flatten_ref_type ctx ty))
  | A.NodeConstDecl (pos, TypedConst (pos2, id, expr, ty)) ->
    A.NodeConstDecl (pos, TypedConst (pos2, id, expr, flatten_ref_type ctx ty)) 
  | NodeVarDecl (pos, (pos2, id, ty, cl)) -> 
    NodeVarDecl (pos, (pos2, id, flatten_ref_type ctx ty, cl))
  | decl -> decl 


let rec flatten_ref_types_expr: TypeCheckerContext.tc_context -> A.expr -> A.expr = 
  fun ctx e -> 
  let rec_call = flatten_ref_types_expr ctx in  
  match e with
  (* Quantified expressions *)
  | Quantifier (p, q, tis, e) ->
    let tis = List.map (fun (p, id, ty) -> p, id, flatten_ref_type ctx ty) tis in
    Quantifier (p, q, tis, rec_call e)
  (* Everything else *)
  | Ident _ 
  | ModeRef _ as e -> e 
  | RecordProject (p, e, i) -> RecordProject (p, rec_call e, i)  
  | TupleProject (p, e, i) -> TupleProject (p, rec_call e, i)
  | Const _ as e -> e
  | UnaryOp (p, op, e) -> UnaryOp (p, op, rec_call e)
  | BinaryOp (p, op, e1, e2) -> BinaryOp (p, op, rec_call e1, rec_call e2) 
  | TernaryOp (p, op, e1, e2, e3) -> TernaryOp (p, op, rec_call e1, rec_call e2, rec_call e3)
  | ConvOp  (p, op, e) -> ConvOp (p, op, rec_call e)
  | CompOp (p, op, e1, e2) -> CompOp (p, op, rec_call e1, rec_call e2)
  | AnyOp _ -> assert false (* desugared in lustreDesugarAnyOps *)
  | RecordExpr (p, i, flds) -> RecordExpr (p, i, (List.map (fun (f, e) -> (f, rec_call e)) flds))
  | GroupExpr (p, g, es) -> GroupExpr (p, g, List.map rec_call es)
  | StructUpdate (p, e1, i, e2) -> StructUpdate (p, rec_call e1, i, rec_call e2) 
  | ArrayConstr (p, e1, e2) -> ArrayConstr (p, rec_call e1, rec_call e2) 
  | ArrayIndex (p, e1, e2) -> ArrayIndex (p, rec_call e1, rec_call e2)
  | When (p, e, c) -> When (p, rec_call e, c) 
  | Condact (p, e1, e2, i, es1, es2) ->
    Condact (p, rec_call e1
              , rec_call e2
              , i
              , List.map rec_call es1
              , List.map rec_call es2)
  | Activate (p, i, e1, e2, es) ->
    Activate(p, i
              , rec_call e1
              , rec_call e2
              , List.map rec_call es)
  | Merge (p, i, es) ->
    Merge (p, i, List.map (fun (i, e) -> i, rec_call e) es)
  | RestartEvery (p, i, es, e) ->
    RestartEvery (p, i, List.map rec_call es, rec_call e)
  | Pre (p, e) -> Pre(p, rec_call e)
  | Arrow (p, e1, e2) ->  Arrow (p, rec_call e1, rec_call e2)
  | Call (p, ps, i, es) -> Call (p, ps, i, List.map rec_call es) 

let flatten_ref_types_item ctx item = 
  match item with 
  | A.AnnotProperty (p, id, expr, k) -> A.AnnotProperty (p, id, flatten_ref_types_expr ctx expr, k)
  | Body _ | FrameBlock _ | IfBlock _ | AnnotMain _ -> item

let flatten_ref_types ctx sorted_node_contract_decls = 
  List.map (fun decl -> match decl with
    | A.TypeDecl (pos, AliasType (pos2, id, ty)) -> 
      A.TypeDecl (pos, AliasType (pos2, id, flatten_ref_type ctx ty))
    | NodeDecl (pos, (id, imported, params, ips, ops, locals, items, contract)) -> 
      let ips = List.map (fun (pos, id, ty, cl, b) -> 
        (pos, id, flatten_ref_type ctx ty, cl, b)
      ) ips in
      let ops = List.map (fun (pos, id, ty, cl) -> 
        (pos, id, flatten_ref_type ctx ty, cl)
      ) ops in
      let locals = List.map (flatten_ref_types_local_decl ctx) locals in
      let items = List.map (flatten_ref_types_item ctx) items in
      NodeDecl (pos, (id, imported, params, ips, ops, locals, items, contract))
    | FuncDecl (pos, (id, imported, params, ips, ops, locals, items, contract)) -> 
      let ips = List.map (fun (pos, id, ty, cl, b) -> 
        (pos, id, flatten_ref_type ctx ty, cl, b)
      ) ips in
      let ops = List.map (fun (pos, id, ty, cl) -> 
        (pos, id, flatten_ref_type ctx ty, cl)
      ) ops in
      let locals = List.map (flatten_ref_types_local_decl ctx) locals in
      let items = List.map (flatten_ref_types_item ctx) items in
      FuncDecl (pos, (id, imported, params, ips, ops, locals, items, contract))
    | NodeParamInst (pos, (id1, id2, tys)) -> 
      let tys = List.map (flatten_ref_type ctx) tys in 
      NodeParamInst (pos, (id1, id2, tys))
    | ContractNodeDecl (pos, (id, params, ips, ops, contract)) -> 
      let ips = List.map (fun (pos, id, ty, cl, b) -> 
        (pos, id, flatten_ref_type ctx ty, cl, b)
      ) ips in
      let ops = List.map (fun (pos, id, ty, cl) -> 
        (pos, id, flatten_ref_type ctx ty, cl)
      ) ops in
      ContractNodeDecl (pos, (id, params, ips, ops, contract))
    | ConstDecl (pos, (FreeConst (pos2, id, ty))) -> 
      let ty = flatten_ref_type ctx ty in 
      ConstDecl (pos, (FreeConst (pos2, id, ty)))
    | ConstDecl (pos, (TypedConst (pos2, id, expr, ty))) -> 
      let ty = flatten_ref_type ctx ty in 
      ConstDecl (pos, (TypedConst (pos2, id, expr, ty))) 
    | A.TypeDecl (_, FreeType _) 
    | ConstDecl (_, (UntypedConst _))  -> decl
    
  ) sorted_node_contract_decls
