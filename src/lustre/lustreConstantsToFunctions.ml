module A = LustreAst
module AH = LustreAstHelpers
module NI = NodeId
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

let const_decl_constants_to_calls new_func_ids const_decl = match const_decl with
| A.FreeConst (pos, id, ty) -> 
  let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
  A.FreeConst (pos, id, ty)
| A.TypedConst (pos, id, expr, ty) -> 
  let expr = AH.constants_to_calls new_func_ids expr in 
  let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
  A.TypedConst (pos, id, expr, ty)
| A.UntypedConst (pos, id, expr) -> 
  let expr = AH.constants_to_calls new_func_ids expr in 
  A.UntypedConst (pos, id, expr)

let contract_constants_to_calls new_func_ids (p, ceqs) = 
  let ceqs = List.map (fun ceq -> match ceq with 
  | A.GhostConst const_decl -> 
    A.GhostConst (const_decl_constants_to_calls new_func_ids const_decl)
  | GhostVars (p, (GhostVarDec (p2, tis)), rhs) -> 
    let tis = List.map (fun (p, id, ty) -> 
      p, id, AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty 
    ) tis in 
    let rhs = AH.constants_to_calls new_func_ids rhs in 
    GhostVars (p, (GhostVarDec (p2, tis)), rhs)
  | Assume (p, id, b, e) -> 
    Assume (p, id, b, AH.constants_to_calls new_func_ids e)
  | Guarantee (p, id, b, e) -> 
    Guarantee (p, id, b, AH.constants_to_calls new_func_ids e)
  | Mode (p, id, reqs, enss) -> 
    let reqs = List.map (fun (p, id, e) -> p, id, AH.constants_to_calls new_func_ids e) reqs in 
    let enss = List.map (fun (p, id, e) -> p, id, AH.constants_to_calls new_func_ids e) enss in 
    Mode (p, id, reqs, enss)
  | ContractCall (p, id, tys, es, ops) -> 
    let tys = List.map (AH.map_lustre_ty (AH.constants_to_calls new_func_ids)) tys in 
    let es = List.map (AH.constants_to_calls new_func_ids) es in 
    ContractCall (p, id, tys, es, ops)
  | AssumptionVars _ -> ceq 
  ) ceqs in 
  p, ceqs

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

let node_decl_constants_to_calls new_func_ids (ni, gen, imp, opac, ps, ips, ops, locals, nis, c) = 
  let ips = List.map (fun (p, id, ty, c, b) -> 
    let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
    p, id, ty, c, b
  ) ips in 
  let ops = List.map (fun (p, id, ty, c) -> 
    let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
    p, id, ty, c
  ) ops in 
  let locals = List.map (fun local -> match local with 
  | A.NodeConstDecl (p, const_decl) -> 
    A.NodeConstDecl (p, const_decl_constants_to_calls new_func_ids const_decl)
  | A.NodeVarDecl (p, (p2, id, ty, c)) -> 
    let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
    A.NodeVarDecl (p, (p2, id, ty, c))
  ) locals in
  let nis = List.map (ni_constants_to_calls new_func_ids) nis in
  let c = Option.map (contract_constants_to_calls new_func_ids) c in
  (ni, gen, imp, opac, ps, ips, ops, locals, nis, c)

let decl_constants_to_calls new_func_ids decl = match decl with 
| A.NodeDecl (s, node_decl) -> 
  A.NodeDecl (s, node_decl_constants_to_calls new_func_ids node_decl)
| A.FuncDecl (s, node_decl) -> 
  A.FuncDecl (s, node_decl_constants_to_calls new_func_ids node_decl) 
| A.ContractNodeDecl (p, (id, ps, ips, ops, c)) -> 
  let ips = List.map (fun (p, id, ty, c, b) -> 
    let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
    p, id, ty, c, b
  ) ips in 
  let ops = List.map (fun (p, id, ty, c) -> 
    let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
    p, id, ty, c
  ) ops in 
  let c = contract_constants_to_calls new_func_ids c in 
  A.ContractNodeDecl (p, (id, ps, ips, ops, c)) 
| A.TypeDecl (s, AliasType (p, id, ps, ty)) -> 
  let ty = AH.map_lustre_ty (AH.constants_to_calls new_func_ids) ty in 
  A.TypeDecl (s, AliasType (p, id, ps, ty)) 
| A.TypeDecl (_, FreeType _) -> decl 
| A.ConstDecl (s, const_decl) -> 
  A.ConstDecl (s, const_decl_constants_to_calls new_func_ids const_decl)
| A.NodeParamInst _ -> assert false

let constants_to_calls new_func_ids decls = 
  List.map (decl_constants_to_calls new_func_ids) decls

let ty_contains_gids ctx ni ty =
  AH.fold_lustre_ty (Chk.expr_contains_set_binop ctx ni) false (||) ty

let gen_functions ctx decls = 
  let decls, new_func_ids, ctx = 
    List.fold_left (fun (acc_decls, acc_new_func_ids, acc_ctx) decl -> match decl with 
    | A.ConstDecl (s, A.FreeConst (_, id, ty)) -> 
      let ctx = Ctx.add_ty ctx id ty in
      if ty_contains_gids ctx None ty then 
        (* Only generate a function if necessary (we need it to handle generated identifiers *)
        let p = s.start_pos in
        let node_id = NI.mk_node_id id in
        let ops = [s.start_pos, id, ty, A.ClockTrue] in
        let func_ty = A.TArr (p, GroupType (p, []), ty) in 
        let acc_ctx = Ctx.remove_const acc_ctx id in
        let acc_ctx = Ctx.add_ty_node acc_ctx node_id func_ty in 
        let acc_ctx = Ctx.add_node_param_attr acc_ctx node_id [] in
        acc_decls @ [A.FuncDecl (s, (node_id, true, true, Default, [], [], ops, [], [], None))],
        id :: acc_new_func_ids, 
        acc_ctx
      else 
        acc_decls @ [decl], acc_new_func_ids, acc_ctx
    | A.ConstDecl (_, A.UntypedConst _) 
    | A.ConstDecl (_, A.TypedConst _) 
    | A.NodeDecl _ 
    | A.FuncDecl _ 
    | A.ContractNodeDecl _
    | A.TypeDecl _ 
    | A.NodeParamInst _ -> acc_decls @ [decl], acc_new_func_ids, acc_ctx
    ) ([], [], ctx) decls  
  in 
  decls, new_func_ids, ctx
