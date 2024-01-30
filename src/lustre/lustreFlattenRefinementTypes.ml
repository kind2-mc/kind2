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
      | History _ | TArr _ | UserType _  ->[]
    in
    let constraints = chase_refinements ty in 
    let expr = List.fold_left (fun acc expr ->
      A.BinaryOp(pos, And, acc, expr)
    ) expr constraints in
    RefinementType (pos, (pos2, id, ty), expr)
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
      NodeDecl (pos, (id, imported, params, ips, ops, locals, items, contract))
    | FuncDecl (pos, (id, imported, params, ips, ops, locals, items, contract)) -> 
      let ips = List.map (fun (pos, id, ty, cl, b) -> 
        (pos, id, flatten_ref_type ctx ty, cl, b)
      ) ips in
      let ops = List.map (fun (pos, id, ty, cl) -> 
        (pos, id, flatten_ref_type ctx ty, cl)
      ) ops in
      let locals = List.map (flatten_ref_types_local_decl ctx) locals in
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
