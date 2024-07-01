module A = LustreAst
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module GI = GeneratedIdentifiers
module LH = LustreAstHelpers

let build_node_fun_ty
= fun pos args rets ->
  let ops = List.map snd (List.map LH.extract_op_ty rets) in
  let ips = List.map snd (List.map LH.extract_ip_ty args) in
  let ret_ty = if List.length ops = 1 then List.hd ops else A.GroupType (pos, ops) in
  let arg_ty = if List.length ips = 1 then List.hd ips else A.GroupType (pos, ips) in
  A.TArr (pos, arg_ty, ret_ty)

(* Given a context, a map of node names to existing polymorphic instantiations, a (polymorphic) node to call,
   and type arguments, return the associated generated polymorphic node name, a new declaration for the 
   polymorphic node instantiation (if it hasn't already been created), and the updated map of 
   node names to polymorphic instantiations *)
let gen_poly_decl: Ctx.tc_context -> (A.declaration * A.lustre_type list list) HString.HStringMap.t ->
                   HString.t -> A.lustre_type list -> Ctx.tc_context * HString.t *  A.declaration option * (A.declaration * A.lustre_type list list) HString.HStringMap.t 
= fun ctx node_decls_map nname ty_args ->
  (* Check for pre-existing instantiation of the node before compiling a new one *)
  let decl, tyss = GI.StringMap.find nname node_decls_map in 
  let find_decl tys = 
    (List.length tys = List.length ty_args) &&
    (List.for_all2 (fun ty p -> match Chk.eq_lustre_type ctx ty p with 
    | Ok true -> true
    | _ -> false
    ) tys ty_args) 
  in
  match Lib.find_opt_index find_decl tyss with 
  (* This polymorphic instantiation already exists *)
  | Some i -> 
    let prefix =  LustreGenRefTypeImpNodes.poly_gen_node_tag ^ (string_of_int i) ^ "_" in
    let pnname = HString.concat2 (HString.mk_hstring prefix) nname in
    ctx, pnname, None, node_decls_map   
  (* Creating new polymorphic instantiation *) 
  | None ->
    let span, is_function, is_contract, ext, ps, ips, ops, locs, nis, c = 
      match GI.StringMap.find nname node_decls_map with
      | (A.FuncDecl (span, (_, ext, ps, ips, ops, locs, nis, c)), _) -> 
        span, true, false, ext, ps, ips, ops, locs, nis, c 
      | (A.NodeDecl (span, (_, ext, ps, ips, ops, locs, nis, c)), _) -> 
        span, false, false, ext, ps, ips, ops, locs, nis, c
      | (A.ContractNodeDecl (span, (_, ps, ips, ops, c)), _) -> 
        span, false, true, false, ps, ips, ops, [], [], Some c
      | _ -> assert false
    in
    let nis = List.filter (fun ni -> match ni with 
    | A.AnnotMain _ -> false 
    | _ -> true
    ) nis in
    let ips = List.map (fun (pos, id, ty, cl, const) -> 
      let ty = Chk.instantiate_type_variables ctx pos nname ty ty_args in
      match ty with 
      | Ok ty -> (pos, id, ty, cl, const)
      | Error _ -> assert false
    ) ips in 
    let ops = List.map (fun (pos, id, ty, cl) -> 
      let ty = Chk.instantiate_type_variables ctx pos nname ty ty_args in
      match ty with 
      | Ok ty -> (pos, id, ty, cl)
      | Error _ -> assert false
    )  ops in
    (* Replace type variables that are instantiated with other type variables *)
    let ps = List.map (fun p -> 
      let ty = Chk.instantiate_type_variables ctx span.start_pos nname (A.UserType (span.start_pos, p)) ty_args in
      match ty with 
      | Ok ty -> 
        (match ty with 
        | UserType (_, id) -> id 
        | _ -> p
        )
      | Error _ -> assert false
    )  ps in

    (* Create fresh identifier for instantiated polymorphic node *)
    let prefix =  LustreGenRefTypeImpNodes.poly_gen_node_tag ^ (List.length tyss |> string_of_int) ^ "_" in
    let pnname = HString.concat2 (HString.mk_hstring prefix) nname in
    (* Remember new instantiation *)
    let node_decls_map = GI.StringMap.add nname (decl, tyss @ [ty_args]) node_decls_map in
    let ctx, called_decl = 
      if is_function then 
        let ctx = Ctx.add_ty_vars_node ctx pnname ps in
        let ctx = Ctx.add_node_param_attr ctx pnname ips in
        let node_ty = build_node_fun_ty span.start_pos ips ops in
        Ctx.add_ty_node ctx pnname node_ty, 
        A.FuncDecl (span, (pnname, ext, ps, ips, ops, locs, nis, c))
      else if is_contract then 
        let c = Option.get c in
        let ctx = Ctx.add_ty_vars_contract ctx pnname ps in
        let ctx = match Chk.extract_exports pnname ctx c with 
        | Ok ctx -> ctx 
        | Error _ -> assert false 
        in
        ctx, 
        ContractNodeDecl (span, (pnname, ps, ips, ops, c))
      else     
        let ctx = Ctx.add_ty_vars_node ctx pnname ps in
        let ctx = Ctx.add_node_param_attr ctx pnname ips in
        let node_ty = build_node_fun_ty span.start_pos ips ops in
        Ctx.add_ty_node ctx pnname node_ty, 
        NodeDecl (span, (pnname, ext, ps, ips, ops, locs, nis, c))
    in
    ctx, pnname, Some called_decl, node_decls_map                     

let rec gen_poly_decls_ty: Ctx.tc_context -> (A.declaration * A.lustre_type list list) HString.HStringMap.t ->
                           A.lustre_type -> Ctx.tc_context * A.lustre_type * A.declaration list * (A.declaration * A.lustre_type list list) HString.HStringMap.t
= fun ctx node_decls_map ty -> match ty with
  | A.TupleType (p, tys) -> 
    let ctx, tys, decls, node_decls_map = List.fold_left (fun (ctx, acc_tys, acc_decls, acc_node_decls_map) ty -> 
      let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      ctx, acc_tys @ [ty], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) tys in 
    ctx, TupleType (p, tys), decls, node_decls_map
  | GroupType (p, tys) -> 
    let ctx, tys, decls, node_decls_map = List.fold_left (fun (ctx, acc_tys, acc_decls, acc_node_decls_map) ty -> 
      let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      ctx, acc_tys @ [ty], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) tys in 
    ctx, GroupType (p, tys), decls, node_decls_map
  | RecordType (p, id, tis) -> 
    let ctx, tis, decls, node_decls_map = List.fold_left (fun (ctx, acc_tys, acc_decls, acc_node_decls_map) (p, id, ty) -> 
      let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      ctx, acc_tys @ [(p, id, ty)], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) tis in 
    ctx, RecordType (p, id, tis), decls, node_decls_map
  | ArrayType (p, (ty, expr)) -> 
    let ctx, ty, decls1, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    let ctx, expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    ctx, ArrayType (p, (ty, expr)), decls1 @ decls2, node_decls_map
  | TArr (p, ty1, ty2) -> 
    let ctx, ty1, decls1, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty1 in 
    let ctx, ty2, decls2, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty2 in 
    ctx, TArr (p, ty1, ty2), decls1 @ decls2, node_decls_map
  | RefinementType (p, (p2, id, ty), expr) -> 
    let ctx, ty, decls1, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    let ctx, expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    ctx, RefinementType (p, (p2, id, ty), expr), decls1 @ decls2, node_decls_map
  | Bool _ | Int _ | UInt8 _ | UInt16 _ | UInt32 _ | UInt64  _ | Int8 _ | Int16 _
  | Int32 _ | Int64 _ | IntRange _ | Real _ | UserType _ | TypeVariable _ 
  | AbstractType _ | EnumType _ | History _ -> ctx, ty, [], node_decls_map

and gen_poly_decls_expr: Ctx.tc_context -> (A.declaration * A.lustre_type list list) HString.HStringMap.t ->
                             A.expr -> Ctx.tc_context * A.expr *  A.declaration list * (A.declaration * A.lustre_type list list) HString.HStringMap.t
= fun ctx node_decls_map expr -> 
  let rec_call = gen_poly_decls_expr ctx node_decls_map in
  match expr with 
  | A.Call (pos, ty :: tys, nname, exprs) -> (
    let ctx, exprs, decls, node_decls_map = List.fold_left (fun (ctx, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) exprs in 
    match gen_poly_decl ctx node_decls_map nname (ty :: tys) with 
    | ctx, pnname, Some decl, node_decls_map -> 
      ctx, A.Call (pos, ty :: tys, pnname, exprs), decl :: decls, node_decls_map
    | ctx, pnname, None, node_decls_map -> 
      ctx, Call (pos, ty :: tys, pnname, exprs), decls, node_decls_map
    )
  | Ident _ 
  | Call _ 
  | Const _
  | ModeRef _ -> ctx, expr, [], node_decls_map
  | RecordProject (p, expr, id) -> 
    let ctx, expr, decls, node_decls_map = rec_call expr in 
    ctx, RecordProject (p, expr, id), decls, node_decls_map
  | TupleProject (p, expr, i) -> 
    let ctx, expr, decls, node_decls_map = rec_call expr in 
    ctx, TupleProject (p, expr, i), decls, node_decls_map
  | ConvOp (p, op, expr) -> 
    let ctx, expr, decls, node_decls_map = rec_call expr in 
    ctx, ConvOp (p, op, expr), decls, node_decls_map
  | When (p, expr, cl) -> 
    let ctx, expr, decls, node_decls_map = rec_call expr in 
    ctx, When (p, expr, cl), decls, node_decls_map
  | Pre (p, expr) -> 
    let ctx, expr, decls, node_decls_map = rec_call expr in 
    ctx, Pre (p, expr), decls, node_decls_map
  | UnaryOp (p, op, expr) -> 
    let ctx, expr, decls, node_decls_map = rec_call expr in 
    ctx, UnaryOp (p, op, expr), decls, node_decls_map
  | BinaryOp (p, op, expr1, expr2) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ctx, BinaryOp (p, op, expr1, expr2), decls1 @ decls2, node_decls_map 
  | CompOp (p, op, expr1, expr2) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ctx, CompOp (p, op, expr1, expr2), decls1 @ decls2, node_decls_map 
  | ArrayConstr (p, expr1, expr2) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ctx, ArrayConstr (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | Arrow (p, expr1, expr2) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ctx, Arrow (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | StructUpdate (p, expr1, lois, expr2) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ctx, StructUpdate (p, expr1, lois, expr2), decls1 @ decls2, node_decls_map 
  | ArrayIndex (p, expr1, expr2) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ctx, ArrayIndex (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | TernaryOp (p, op, expr1, expr2, expr3) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let ctx, expr3, decls3, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr3 in
    ctx, TernaryOp (p, op, expr1, expr2, expr3), decls1 @ decls2 @ decls3, node_decls_map
  | AnyOp (p, (p2, id, ty), expr1, Some expr2) -> 
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let ctx, ty, decls3, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    ctx, AnyOp (p, (p2, id, ty), expr1, Some expr2), decls1 @ decls2 @ decls3, node_decls_map
  | AnyOp (p, (p2, id, ty), expr, None) ->
    let ctx, expr, decls1, node_decls_map = rec_call expr in 
    let ctx, ty, decls2, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    ctx, AnyOp (p, (p2, id, ty), expr, None), decls1 @ decls2, node_decls_map
  | Quantifier (p, q, tis, expr) -> 
    let ctx, expr, decls1, node_decls_map = rec_call expr in 
    let ctx, tis, decls2, node_decls_map = List.fold_left (fun (ctx, acc_tis, acc_decls, acc_node_decls_map) (p, id, ty) -> 
      let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      ctx, acc_tis @ [p, id, ty], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls1, node_decls_map) tis in 
    ctx, Quantifier (p, q, tis, expr), decls1 @ decls2, node_decls_map
  | Merge (p, id, id_exprs) ->
    let ctx, id_exprs, decls, node_decls_map = List.fold_left (fun (ctx, acc_id_exprs, acc_decls, acc_node_decls_map) (id, expr) -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_id_exprs @ [id, expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) id_exprs in 
    ctx, Merge (p, id, id_exprs), decls, node_decls_map
  | RecordExpr (p, id, id_exprs) ->
    let ctx, id_exprs, decls, node_decls_map = List.fold_left (fun (ctx, acc_id_exprs, acc_decls, acc_node_decls_map) (id, expr) -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_id_exprs @ [id, expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) id_exprs in 
    ctx, RecordExpr (p, id, id_exprs), decls, node_decls_map
  | GroupExpr (p, ge, exprs) ->
    let ctx, exprs, decls, node_decls_map = List.fold_left (fun (ctx, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) exprs in 
    ctx, GroupExpr (p, ge, exprs), decls, node_decls_map
  | Condact (p, expr1, expr2, id, exprs1, exprs2) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let ctx, exprs1, decls, node_decls_map = List.fold_left (fun (ctx, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls1 @ decls2, node_decls_map) exprs1 in 
    let ctx, exprs2, decls, node_decls_map = List.fold_left (fun (ctx, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) exprs2 in 
    ctx, Condact (p, expr1, expr2, id, exprs1, exprs2), decls, node_decls_map
  | Activate (p, id, expr1, expr2, exprs) ->
    let ctx, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let ctx, exprs, decls, node_decls_map = List.fold_left (fun (ctx, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls1 @ decls2, node_decls_map) exprs in 
    ctx, Activate (p, id, expr1, expr2, exprs), decls, node_decls_map
  | RestartEvery (p, id, exprs, expr) ->
    let ctx, expr, decls, node_decls_map = rec_call expr in 
    let ctx, exprs, decls, node_decls_map = List.fold_left (fun (ctx, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      ctx, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) exprs in 
    ctx, RestartEvery (p, id, exprs, expr), decls, node_decls_map


let gen_poly_decls_ip
= fun ctx node_decls_map (p, id, ty, cl, is_const) -> 
  let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  ctx, (p, id, ty, cl, is_const), decls, node_decls_map

let gen_poly_decls_op
= fun ctx node_decls_map (p, id, ty, cl) -> 
  let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  ctx, (p, id, ty, cl), decls, node_decls_map

let gen_poly_decls_loc
= fun ctx node_decls_map loc -> match loc with 
| A.NodeConstDecl (p, FreeConst (p2, id, ty)) -> 
  let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in
  ctx, A.NodeConstDecl (p, FreeConst (p2, id, ty)), decls, node_decls_map
| A.NodeConstDecl (p, UntypedConst (p2, id, expr)) -> 
  let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in
  ctx, A.NodeConstDecl (p, UntypedConst (p2, id, expr)), decls, node_decls_map
| A.NodeConstDecl (p, TypedConst (p2, id, expr, ty)) -> 
  let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  let ctx, expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  ctx, A.NodeConstDecl (p, TypedConst (p2, id, expr, ty)), decls @ decls2, node_decls_map
| NodeVarDecl (p, var_decl) -> 
  let ctx, var_decl, decls, node_decls_map = gen_poly_decls_op ctx node_decls_map var_decl in 
  ctx, NodeVarDecl (p, var_decl), decls, node_decls_map

let rec gen_poly_decls_ni
= fun ctx node_decls_map ni -> match ni with 
  | A.Body (Equation (p, lhs, expr)) -> 
    let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    ctx, A.Body (Equation (p, lhs, expr)), decls, node_decls_map
  | Body (Assert (p, expr)) -> 
    let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    ctx, Body (Assert (p, expr)), decls, node_decls_map
  | IfBlock (p, expr, nis1, nis2) -> 
    let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    let ctx, nis1, decls, node_decls_map = List.fold_left (fun (ctx, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      ctx, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) nis1 in 
    let ctx, nis2, decls, node_decls_map = List.fold_left (fun (ctx, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      ctx, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) nis2 in 
    ctx, IfBlock (p, expr, nis1, nis2), decls, node_decls_map
  | FrameBlock (p, vars, nes, nis) -> 
    let ctx, nis, decls, node_decls_map = List.fold_left (fun (ctx, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      ctx, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, [], [], node_decls_map) nis in 
    let ctx, nes, decls, node_decls_map = List.fold_left (fun (ctx, acc_nes, acc_decls, acc_node_decls_map) ne -> 
      let ctx, ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map (A.Body ne) in 
      let ne = match ni with | Body ne -> ne | _ -> assert false in
      ctx, acc_nes @ [ne], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) nes in  
    ctx, FrameBlock (p, vars, nes, nis), decls, node_decls_map
  | AnnotProperty (p, n, expr, k) -> 
    let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    ctx, AnnotProperty (p, n, expr, k), decls, node_decls_map
  | AnnotMain _ -> ctx, ni, [], node_decls_map

let gen_poly_decls_ci
= fun ctx node_decls_map ci -> match ci with 
| A.ContractCall (p, cname, ty :: tys, ips, ops) -> (
  match gen_poly_decl ctx node_decls_map cname (ty :: tys) with 
  | ctx, pcname, Some decl, node_decls_map -> 
    ctx, A.ContractCall (p, pcname, ty :: tys, ips, ops), [decl], node_decls_map
  | ctx, pcname, None, node_decls_map -> 
    ctx, A.ContractCall (p, pcname, ty :: tys, ips, ops), [], node_decls_map
  )
| A.ContractCall (_, _, [], _, _) -> ctx, ci, [], node_decls_map
| Assume (p, id, b, expr) -> 
  let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  ctx, Assume (p, id, b, expr), decls, node_decls_map 
| Guarantee (p, id, b, expr) -> 
  let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  ctx, Guarantee (p, id, b, expr), decls, node_decls_map 
| GhostConst (FreeConst (p, id, ty)) -> 
  let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  ctx, GhostConst (FreeConst (p, id, ty)), decls, node_decls_map
| GhostConst (UntypedConst (p, id, expr)) -> 
  let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in
  ctx, GhostConst (UntypedConst (p, id, expr)), decls, node_decls_map
| GhostConst (TypedConst (p, id, expr, ty)) -> 
  let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  let ctx, expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  ctx, GhostConst (TypedConst (p, id, expr, ty)), decls @ decls2, node_decls_map
| GhostVars (p, GhostVarDec (p2, tis), expr) -> 
  let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  let ctx, tis, decls, node_decls_map = List.fold_left (fun (ctx, acc_tis, acc_decls, acc_node_decls_map) (p, id, ty) -> 
    let ctx, ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
    ctx, acc_tis @ [p, id, ty], decls @ acc_decls, node_decls_map
  ) (ctx, [], decls, node_decls_map) tis in 
  ctx, GhostVars (p, GhostVarDec (p2, tis), expr), decls, node_decls_map
| Mode (p, id, creqs, cens) -> 
  let ctx, creqs, decls, node_decls_map = List.fold_left (fun (ctx, acc_creqs, acc_decls, acc_node_decls_map) (p, id, expr) -> 
    let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
    ctx, acc_creqs @ [p, id, expr], decls @ acc_decls, node_decls_map
  ) (ctx, [], [], node_decls_map) creqs in 
  let ctx, cens, decls, node_decls_map = List.fold_left (fun (ctx, acc_cens, acc_decls, acc_node_decls_map) (p, id, expr) -> 
    let ctx, expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
    ctx, acc_cens @ [p, id, expr], decls @ acc_decls, node_decls_map
  ) (ctx, [], decls, node_decls_map) cens in 
  ctx, Mode (p, id, creqs, cens), decls, node_decls_map
| AssumptionVars _ -> ctx, ci, [], node_decls_map

let instantiate_polymorphic_calls: Ctx.tc_context -> A.declaration list -> Ctx.tc_context * A.declaration list 
= fun ctx decls -> 
  (* Initialize node_decls_map (a map from a node name to its declaration and the list of its polymorphic instantiations 
     created so far) *)
  let node_decls_map = List.fold_left (fun acc decl -> match decl with 
  | (A.NodeDecl (_, (id, _, _, _, _, _, _, _)) as decl)
  | (FuncDecl (_, (id, _, _, _, _, _, _, _)) as decl)  
  | (ContractNodeDecl (_, (id, _, _, _, _)) as decl) -> 
    GI.StringMap.add id (decl, []) acc
  | TypeDecl _ | ConstDecl _ | NodeParamInst _ -> acc
  ) GI.StringMap.empty decls 
  in

  let ctx, decls, _ = List.fold_left (fun (ctx, acc_decls, acc_node_decls_map) decl -> match decl with
  | A.FuncDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) -> 
    let ctx, ips, decls, node_decls_map = List.fold_left (fun (ctx, acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ctx, ip, decls, node_decls_map = gen_poly_decls_ip ctx acc_node_decls_map ip in 
      ctx, acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) (ctx, [], acc_decls, acc_node_decls_map) ips in 
    let ctx, ops, decls, node_decls_map = List.fold_left (fun (ctx, acc_ops, acc_decls, acc_node_decls_map) op -> 
      let ctx, op, decls, node_decls_map = gen_poly_decls_op ctx acc_node_decls_map op in 
      ctx, acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) ops in
    let ctx, locs, decls, node_decls_map = List.fold_left (fun (ctx, acc_locs, acc_decls, acc_node_decls_map) loc -> 
      let ctx, loc, decls, node_decls_map = gen_poly_decls_loc ctx acc_node_decls_map loc in 
      ctx, acc_locs @ [loc], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) locs in
    let ctx, nis, decls, node_decls_map = List.fold_left (fun (ctx, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      ctx, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) nis in (
    match c with 
      | None -> 
        let decl =  A.FuncDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) in
        ctx, decl :: decls, node_decls_map
      | Some (p3, c) ->
        let ctx, c, decls, node_decls_map = List.fold_left (fun (ctx, acc_cis, acc_decls, acc_node_decls_map) ip -> 
          let ctx, ci, decls, node_decls_map = gen_poly_decls_ci ctx acc_node_decls_map ip in 
          ctx, acc_cis @ [ci], decls @ acc_decls, node_decls_map
        ) (ctx, [], decls, node_decls_map) c in 
        let decl = A.FuncDecl (p, (p2, ext, ps, ips, ops, locs, nis, Some (p3, c))) in
        ctx, decl :: decls, node_decls_map
    )
  | NodeDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) -> 
    let ctx, ips, decls, node_decls_map = List.fold_left (fun (ctx, acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ctx, ip, decls, node_decls_map = gen_poly_decls_ip ctx acc_node_decls_map ip in 
      ctx, acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) (ctx, [], acc_decls, acc_node_decls_map) ips in 
    let ctx, ops, decls, node_decls_map = List.fold_left (fun (ctx, acc_ops, acc_decls, acc_node_decls_map) op -> 
      let ctx, op, decls, node_decls_map = gen_poly_decls_op ctx acc_node_decls_map op in 
      ctx, acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) ops in
    let ctx, locs, decls, node_decls_map = List.fold_left (fun (ctx, acc_locs, acc_decls, acc_node_decls_map) loc -> 
      let ctx, loc, decls, node_decls_map = gen_poly_decls_loc ctx acc_node_decls_map loc in 
      ctx, acc_locs @ [loc], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) locs in
    let ctx, nis, decls, node_decls_map = List.fold_left (fun (ctx, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      ctx, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) nis in (
    match c with 
      | None -> 
        let decl =  A.NodeDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) in
        ctx, decl :: decls, node_decls_map
      | Some (p3, c) ->
        let ctx, c, decls, node_decls_map = List.fold_left (fun (ctx, acc_cis, acc_decls, acc_node_decls_map) ip -> 
          let ctx, ci, decls, node_decls_map = gen_poly_decls_ci ctx acc_node_decls_map ip in 
          ctx, acc_cis @ [ci], decls @ acc_decls, node_decls_map
        ) (ctx, [], decls, node_decls_map) c in 
        let decl = A.NodeDecl (p, (p2, ext, ps, ips, ops, locs, nis, Some (p3, c))) in
        ctx, decl :: decls, node_decls_map
    )
  | ContractNodeDecl (p, (cname, ps, ips, ops, (p3, c))) -> 
    let ctx, ips, decls, node_decls_map = List.fold_left (fun (ctx, acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ctx, ip, decls, node_decls_map = gen_poly_decls_ip ctx acc_node_decls_map ip in 
      ctx, acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) (ctx, [], acc_decls, acc_node_decls_map) ips in 
    let ctx, ops, decls, node_decls_map = List.fold_left (fun (ctx, acc_ops, acc_decls, acc_node_decls_map) op -> 
      let ctx, op, decls, node_decls_map = gen_poly_decls_op ctx acc_node_decls_map op in 
      ctx, acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) ops in
    let ctx, c, decls, node_decls_map = List.fold_left (fun (ctx, acc_cis, acc_decls, acc_node_decls_map) ip -> 
      let ctx, ci, decls, node_decls_map = gen_poly_decls_ci ctx acc_node_decls_map ip in 
      ctx, acc_cis @ [ci], decls @ acc_decls, node_decls_map
    ) (ctx, [], decls, node_decls_map) c in 
    let decl = A.ContractNodeDecl (p, (cname, ps, ips, ops, (p3, c))) in
    ctx, decl :: decls, node_decls_map
  | TypeDecl _ 
  | ConstDecl _ 
  | NodeParamInst _ -> ctx, decl :: acc_decls, node_decls_map
  ) (ctx, [], node_decls_map) decls in
  ctx, List.rev decls