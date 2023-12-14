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

let rec flatten_ref_type ctx = function
  | A.UserType (_, str) as ty -> 
    let ty2 = TypeCheckerContext.lookup_ty_syn ctx str in 
    (match ty2 with 
    | Some ty2 -> flatten_ref_type ctx ty2
    | None -> ty)
  | RefinementType (pos, (pos2, id, ty2), expr, expr_opt) as ty -> 
    let ty2 = flatten_ref_type ctx ty2 in
    (match ty2 with 
      | A.RefinementType (_, (_, id2, ty3), expr2, expr_opt2) -> 
        print_endline "Got here";
        let expr2 = AH.substitute_naive id2 (Ident(pos, id)) expr2 in
        RefinementType (pos, (pos2, id, ty3), BinaryOp(pos, And, expr, expr2), expr_opt) 
      | _ -> ty)
  | ty -> ty

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
    | A.TypeDecl (_, FreeType _) 
    (*!! Finish cases *)
    | ConstDecl _
    | ContractNodeDecl _
    | NodeParamInst _ -> decl
  ) sorted_node_contract_decls
