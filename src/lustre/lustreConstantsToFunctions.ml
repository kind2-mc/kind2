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


module R = Res
module A = LustreAst
module AH = LustreAstHelpers
module NI = NodeId
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

let (let*) = R.(>>=)

type error_kind = 
  | GenCallInArrayLength of HString.t 

let error_message error = match error with
  | GenCallInArrayLength id -> 
    Format.asprintf "Constant %a is unsupported in array length"
      HString.pp_print_hstring id

type error = [
  | `LustreConstantsToFunctionsError of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreConstantsToFunctionsError (pos, kind))

let is_array_type_containing_id new_func_id ty = match ty with 
  | A.ArrayType (_, (_, expr)) -> AH.expr_contains_id new_func_id expr
  | _ -> false

(* Convert constants to calls in a type, but error if generating a call in an array length *)
let ty_constants_to_calls_safe new_func_ids ty = 
  match List.find_opt (fun id -> (AH.contains_subtype_satisfying (is_array_type_containing_id id) ty)) new_func_ids with 
  | Some func_id -> 
    mk_error (AH.pos_of_type ty) (GenCallInArrayLength func_id)   
  | None -> 
    Ok (AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty)

let const_decl_constants_to_calls new_func_ids const_decl = match const_decl with
| A.FreeConst (pos, id, ty) -> 
  let* ty = ty_constants_to_calls_safe new_func_ids ty in 
  R.ok (A.FreeConst (pos, id, ty))
| A.TypedConst (pos, id, expr, ty) -> 
  let expr = AH.constants_to_calls new_func_ids expr in 
  let* ty = ty_constants_to_calls_safe new_func_ids ty in 
  R.ok (A.TypedConst (pos, id, expr, ty))
| A.UntypedConst (pos, id, expr) -> 
  let expr = AH.constants_to_calls new_func_ids expr in 
  R.ok (A.UntypedConst (pos, id, expr))

let contract_constants_to_calls new_func_ids (p, ceqs) = 
  let* ceqs = R.seq (List.map (fun ceq -> match ceq with 
  | A.GhostConst const_decl -> 
    let* const_decl = const_decl_constants_to_calls new_func_ids const_decl in
    R.ok (A.GhostConst (const_decl))
  | GhostVars (p, (GhostVarDec (p2, tis)), rhs) -> 
    let* tis = R.seq (List.map (fun (p, id, ty) -> 
      let* ty = ty_constants_to_calls_safe new_func_ids ty in
      R.ok (p, id, ty)
    ) tis) in 
    let rhs = AH.constants_to_calls new_func_ids rhs in 
    R.ok (A.GhostVars (p, (GhostVarDec (p2, tis)), rhs))
  | Assume (p, id, b, e) -> 
    R.ok (A.Assume (p, id, b, AH.constants_to_calls new_func_ids e))
  | Guarantee (p, id, b, e) -> 
    R.ok (A.Guarantee (p, id, b, AH.constants_to_calls new_func_ids e))
  | Decreases (p, e) -> 
    R.ok (A.Decreases (p, AH.constants_to_calls new_func_ids e))
  | Mode (p, id, reqs, enss) -> 
    let reqs = List.map (fun (p, id, e) -> p, id, AH.constants_to_calls new_func_ids e) reqs in 
    let enss = List.map (fun (p, id, e) -> p, id, AH.constants_to_calls new_func_ids e) enss in 
    R.ok (A.Mode (p, id, reqs, enss))
  | ContractCall (p, id, tys, es, ops) -> 
    let* tys = R.seq (List.map (ty_constants_to_calls_safe new_func_ids) tys) in 
    let es = List.map (AH.constants_to_calls new_func_ids) es in 
    R.ok (A.ContractCall (p, id, tys, es, ops))
  | AssumptionVars _ -> R.ok ceq 
  ) ceqs) in 
  R.ok (p, ceqs)

let rec ni_constants_to_calls new_func_ids ni = match ni with 
| A.Body (A.Assert (p, e)) ->
  A.Body (A.Assert (p, AH.constants_to_calls new_func_ids e))
| A.Body (A.Equation (p, lhs, e))  -> 
  A.Body (A.Equation (p, lhs, AH.constants_to_calls new_func_ids e))
| A.IfBlock (p, e, nis1, nis2) -> 
  let e = AH.constants_to_calls new_func_ids e in 
  let nis1 = List.map (ni_constants_to_calls new_func_ids) nis1 in 
  let nis2 = List.map (ni_constants_to_calls new_func_ids) nis2 in 
  A.IfBlock (p, e, nis1, nis2)
| A.WhenBlock (p, e, nis1, nis2) ->
  let e = AH.constants_to_calls new_func_ids e in
  let nis1 = List.map (ni_constants_to_calls new_func_ids) nis1 in
  let nis2 = List.map (ni_constants_to_calls new_func_ids) nis2 in
  A.WhenBlock (p, e, nis1, nis2)
| A.FrameBlock (p, vars, eqs, nis) -> 
  let eqs = List.map (fun eq -> match eq with 
  | A.Assert _ -> assert false 
  | A.Equation (p, lhs, e) -> A.Equation (p, lhs, AH.constants_to_calls new_func_ids e)
  ) eqs in 
  let nis = List.map (ni_constants_to_calls new_func_ids) nis in 
  A.FrameBlock (p, vars, eqs, nis)
| A.AnnotMain _ -> ni
| A.AnnotProperty (p, id, e, k) -> 
  A.AnnotProperty (p, id, AH.constants_to_calls new_func_ids e, k)

let node_decl_constants_to_calls new_func_ids (ni, imp, opac, ps, ips, ops, locals, nis, c) = 
  let* ips = R.seq (List.map (fun (p, id, ty, c, b) -> 
    let* ty = ty_constants_to_calls_safe new_func_ids ty in 
    R.ok (p, id, ty, c, b)
  ) ips) in 
  let* ops = R.seq (List.map (fun (p, id, ty, c) -> 
    let* ty = ty_constants_to_calls_safe new_func_ids ty in 
    R.ok (p, id, ty, c)
  ) ops) in 
  let* locals = R.seq (List.map (fun local -> match local with 
  | A.NodeConstDecl (p, const_decl) -> 
    let* const_decl = const_decl_constants_to_calls new_func_ids const_decl in
    R.ok (A.NodeConstDecl (p, const_decl))
  | A.NodeVarDecl (p, (p2, id, ty, c)) -> 
    let* ty = ty_constants_to_calls_safe new_func_ids ty in 
    R.ok (A.NodeVarDecl (p, (p2, id, ty, c)))
  ) locals) in
  let nis = List.map (ni_constants_to_calls new_func_ids) nis in
  let* c =  
    match c with
    | None -> Ok None
    | Some c' ->
      let* c'' = contract_constants_to_calls new_func_ids c' in
      R.ok (Some c'')
  in
  R.ok ((ni, imp, opac, ps, ips, ops, locals, nis, c))

let decl_constants_to_calls new_func_ids decl = match decl with 
| A.NodeDecl (s, node_decl) -> 
  let* node_decl = node_decl_constants_to_calls new_func_ids node_decl in
  R.ok (A.NodeDecl (s, node_decl))
| A.FuncDecl (s, node_decl, is_rec) -> 
  let* node_decl = node_decl_constants_to_calls new_func_ids node_decl in
  R.ok (A.FuncDecl (s, node_decl, is_rec))
| A.ContractNodeDecl (p, (id, ps, ips, ops, c)) -> 
  let* ips = R.seq (List.map (fun (p, id, ty, c, b) -> 
    let* ty = ty_constants_to_calls_safe new_func_ids ty in 
    R.ok (p, id, ty, c, b)
  ) ips) in 
  let* ops = R.seq (List.map (fun (p, id, ty, c) -> 
    let* ty = ty_constants_to_calls_safe new_func_ids ty in 
    R.ok (p, id, ty, c)
  ) ops) in 
  let* c = contract_constants_to_calls new_func_ids c in 
  R.ok (A.ContractNodeDecl (p, (id, ps, ips, ops, c)))
| A.TypeDecl (s, AliasType (p, id, ps, ty)) -> 
  let* ty = ty_constants_to_calls_safe new_func_ids ty in 
  R.ok (A.TypeDecl (s, AliasType (p, id, ps, ty)))
| A.TypeDecl (_, FreeType _) -> R.ok decl 
| A.ConstDecl (s, const_decl) -> 
  let* const_decl = const_decl_constants_to_calls new_func_ids const_decl in
  R.ok (A.ConstDecl (s, const_decl))
| A.NodeParamInst _ -> assert false

(* Across all decls, convert identifiers present in `new_func_ids` to calls with no args *)
let constants_to_calls new_func_ids decls = 
  R.seq (List.map (decl_constants_to_calls new_func_ids) decls)

(* Returns true iff the type contains some expression that would induce generated 
   identifiers. In this context, the only way to induce generated identifiers 
   is from set binary operations (union/intersection) *)
let rec ty_contains_gids ctx ni ty = 
  let r = ty_contains_gids ctx ni in
  match ty with  
  | A.RefinementType (_, (_, id, ty), e) ->
    let ctx = Ctx.add_ty ctx id ty in
    (r ty) || (Chk.expr_contains_set_binop ctx ni e)
  | A.ArrayType (_, (ty, e)) -> 
    (r ty) || (Chk.expr_contains_set_binop ctx ni e) 
  | A.History (_, id) -> (
    match Ctx.lookup_ty ctx id with 
    | None -> false 
    | Some ty -> r ty
  )
  | A.TupleType (_, tys)  
  | A.GroupType (_, tys) -> 
    List.fold_left (||) false (List.map r tys)
  | A.RecordType (_, _, tis) -> 
    let tys = List.map (fun (_, _, ty) -> ty) tis in 
    List.fold_left (||) false (List.map r tys)
  | A.Set (_, ty) -> r ty
  | A.Map (_, ty1, ty2)
  | A.TArr (_, ty1, ty2) ->
    (r ty1) || (r ty2)
  | A.AbstractType _ | A.EnumType _  
  | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _ 
  | A.UserType _ -> false 

(* Convert free constants to imported functions without args if there are (will be) associated 
   generated identifiers *)
let gen_const_functions ctx decls = 
  let decls, new_func_ids, ctx = 
    List.fold_left (fun (acc_decls, acc_new_func_ids, acc_ctx) decl -> match decl with 
    | A.ConstDecl (s, A.FreeConst (_, id, ty)) -> 
      let ctx = Ctx.add_ty ctx id ty in
      let contains_gids = ty_contains_gids ctx None ty in
      if contains_gids || List.mem `CONTRACTCK (Flags.enabled ()) then
        (* Generate a function for free constants when the type includes generated identifiers,
           and for realizability checking of free constants. *)
        let p = s.start_pos in
        let node_type = NI.FreeConstant in
        let node_id = NI.mk_node_id ~node_type id in
        let ops = [s.start_pos, id, ty, A.ClockTrue] in
        let func_ty = A.TArr (p, GroupType (p, []), ty) in 
        let acc_ctx = Ctx.remove_const acc_ctx id in
        let acc_ctx = Ctx.add_ty_node acc_ctx node_id func_ty true in 
        let acc_ctx = Ctx.add_node_param_attr acc_ctx node_id [] in
        let acc_decls =
          acc_decls @ [A.FuncDecl (s, (node_id, true, Default, [], [], ops, [], [], None), { is_lemma = false; is_rec = false })]
        in
        let acc_decls, acc_new_func_ids =
          (* If type does not contain generated identifiers, and we are only generating
             an imported function for realizability checking, then we don't need to
             convert references to this constant to calls, so we keep original declaration,
             and we don't include the id in new_func_ids *)
          if not contains_gids then
            acc_decls @ [decl], acc_new_func_ids
          else
            acc_decls, id :: acc_new_func_ids
        in
        acc_decls, acc_new_func_ids, acc_ctx
      else 
        acc_decls @ [decl], acc_new_func_ids, acc_ctx
    | A.ConstDecl (s, A.TypedConst (_, id, e, ty)) -> 
      if Ctx.type_contains_ref ctx ty then 
        let p = s.start_pos in
        let node_type = NI.DefinedConstant in 
        let node_id = NI.mk_node_id ~node_type id in
        let ops = [s.start_pos, id, ty, A.ClockTrue] in
        let nis = [A.Body (A.Equation (p, A.StructDef (p, [A.SingleIdent (p, id)]), e))] in 
        let func_ty = A.TArr (p, GroupType (p, []), ty) in 
        let acc_ctx = Ctx.remove_const acc_ctx id in
        let acc_ctx = Ctx.add_ty_node acc_ctx node_id func_ty true in 
        let acc_ctx = Ctx.add_node_param_attr acc_ctx node_id [] in
        let func_decl1 =
          A.FuncDecl (s, (node_id, false, Transparent, [], [], ops, [], nis, None), { is_lemma = false; is_rec = false })
        in
        (if List.mem `CONTRACTCK (Flags.enabled ()) then
          let func_decl2 =
            let node_id = NI.mk_node_id ~node_type:NI.FreeConstant id in
            A.FuncDecl (s, (node_id, true, Default, [], [], ops, [], [], None), { is_lemma = false; is_rec = false })
          in
          acc_decls @ [func_decl1; func_decl2]
        else
          acc_decls @ [func_decl1]),
        (* Constants with definitions don't appear in `new_func_ids` because their 
           references don't need to be converted to calls (these constants are inlined) *)
        acc_new_func_ids,
        acc_ctx
      else 
        acc_decls @ [decl], acc_new_func_ids, acc_ctx
    | A.ConstDecl (_, A.UntypedConst _) 
    | A.NodeDecl _ 
    | A.FuncDecl _ 
    | A.ContractNodeDecl _
    | A.TypeDecl _ 
    | A.NodeParamInst _ -> acc_decls @ [decl], acc_new_func_ids, acc_ctx
    ) ([], [], ctx) decls  
  in 
  decls, new_func_ids, ctx
