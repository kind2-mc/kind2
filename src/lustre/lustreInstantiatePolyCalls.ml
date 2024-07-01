module A = LustreAst
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module GI = GeneratedIdentifiers

(* Given a context, a map of node names to existing polymorphic instantiations, a (polymorphic) node to call,
   and type arguments, return the associated generated polymorphic node name, a new declaration for the 
   polymorphic node instantiation (if it hasn't already been created), and the updated map of 
   node names to polymorphic instantiations *)
let gen_poly_decl: Ctx.tc_context -> (A.declaration * A.lustre_type list list) HString.HStringMap.t ->
                   HString.t -> A.lustre_type list -> HString.t *  A.declaration option * (A.declaration * A.lustre_type list list) HString.HStringMap.t 
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
    pnname, None, node_decls_map   
  (* Creating new polymorphic instantiation *) 
  | None ->
    let span, is_function, is_contract, ext, ips, ops, locs, nis, c = 
      match GI.StringMap.find nname node_decls_map with
      | (A.FuncDecl (span, (_, ext, _, ips, ops, locs, nis, c)), _) -> 
        span, true, false, ext, ips, ops, locs, nis, c 
      | (A.NodeDecl (span, (_, ext, _, ips, ops, locs, nis, c)), _) -> 
        span, false, false, ext, ips, ops, locs, nis, c
      | (A.ContractNodeDecl (span, (_, _, ips, ops, c)), _) -> 
        span, false, true, false, ips, ops, [], [], Some c
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
    let ps = List.filter (fun ty -> match ty with 
    | A.UserType (_, id) -> (
      not (Ctx.member_ty_syn ctx id || Ctx.member_val ctx id)
    )
    | _ -> false 
    ) ty_args in 
    let ps = List.map (fun ty -> match ty with | A.UserType (_, id) -> id | _ -> assert false) ps in
    (* Create fresh identifier for instantiated polymorphic node *)
    let prefix =  LustreGenRefTypeImpNodes.poly_gen_node_tag ^ (List.length tyss |> string_of_int) ^ "_" in
    let pnname = HString.concat2 (HString.mk_hstring prefix) nname in
    (* Remember new instantiation *)
    let node_decls_map = GI.StringMap.add nname (decl, tyss @ [ty_args]) node_decls_map in
    let called_decl = 
      if is_function then 
        A.FuncDecl (span, (pnname, ext, ps, ips, ops, locs, nis, c))
      else if is_contract then 
        ContractNodeDecl (span, (pnname, ps, ips, ops, Option.get c))
      else      
        NodeDecl (span, (pnname, ext, ps, ips, ops, locs, nis, c))
    in
    pnname, Some called_decl, node_decls_map                     

let rec gen_poly_decls_ty: Ctx.tc_context -> (A.declaration * A.lustre_type list list) HString.HStringMap.t ->
                           A.lustre_type -> A.lustre_type * A.declaration list * (A.declaration * A.lustre_type list list) HString.HStringMap.t
= fun ctx node_decls_map ty -> match ty with
  | A.TupleType (p, tys) -> 
    let tys, decls, node_decls_map = List.fold_left (fun (acc_tys, acc_decls, acc_node_decls_map) ty -> 
      let ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      acc_tys @ [ty], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) tys in 
    TupleType (p, tys), decls, node_decls_map
  | GroupType (p, tys) -> 
    let tys, decls, node_decls_map = List.fold_left (fun (acc_tys, acc_decls, acc_node_decls_map) ty -> 
      let ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      acc_tys @ [ty], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) tys in 
    GroupType (p, tys), decls, node_decls_map
  | RecordType (p, id, tis) -> 
    let tis, decls, node_decls_map = List.fold_left (fun (acc_tys, acc_decls, acc_node_decls_map) (p, id, ty) -> 
      let ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      acc_tys @ [(p, id, ty)], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) tis in 
    RecordType (p, id, tis), decls, node_decls_map
  | ArrayType (p, (ty, expr)) -> 
    let ty, decls1, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    let expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    ArrayType (p, (ty, expr)), decls1 @ decls2, node_decls_map
  | TArr (p, ty1, ty2) -> 
    let ty1, decls1, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty1 in 
    let ty2, decls2, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty2 in 
    TArr (p, ty1, ty2), decls1 @ decls2, node_decls_map
  | RefinementType (p, (p2, id, ty), expr) -> 
    let ty, decls1, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    let expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    RefinementType (p, (p2, id, ty), expr), decls1 @ decls2, node_decls_map
  | TVar _ | Bool _ | Int _ | UInt8 _ | UInt16 _ | UInt32 _ | UInt64  _ | Int8 _ | Int16 _
  | Int32 _ | Int64 _ | IntRange _ | Real _ | UserType _ | TypeVariable _ 
  | AbstractType _ | EnumType _ | History _ -> ty, [], node_decls_map

and gen_poly_decls_expr: Ctx.tc_context -> (A.declaration * A.lustre_type list list) HString.HStringMap.t ->
                             A.expr -> A.expr *  A.declaration list * (A.declaration * A.lustre_type list list) HString.HStringMap.t
= fun ctx node_decls_map expr -> 
  let rec_call = gen_poly_decls_expr ctx node_decls_map in
  match expr with 
  | A.Call (pos, ty :: tys, nname, exprs) -> (
    let exprs, decls, node_decls_map = List.fold_left (fun (acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) exprs in 
    match gen_poly_decl ctx node_decls_map nname (ty :: tys) with 
    | pnname, Some decl, node_decls_map -> 
      A.Call (pos, ty :: tys, pnname, exprs), decl :: decls, node_decls_map
    | pnname, None, node_decls_map -> 
      Call (pos, ty :: tys, pnname, exprs), decls, node_decls_map
    )
  | Ident _ 
  | Call _ 
  | Const _
  | ModeRef _ -> expr, [], node_decls_map
  | RecordProject (p, expr, id) -> 
    let expr, decls, node_decls_map = rec_call expr in 
    RecordProject (p, expr, id), decls, node_decls_map
  | TupleProject (p, expr, i) -> 
    let expr, decls, node_decls_map = rec_call expr in 
    TupleProject (p, expr, i), decls, node_decls_map
  | ConvOp (p, op, expr) -> 
    let expr, decls, node_decls_map = rec_call expr in 
    ConvOp (p, op, expr), decls, node_decls_map
  | When (p, expr, cl) -> 
    let expr, decls, node_decls_map = rec_call expr in 
    When (p, expr, cl), decls, node_decls_map
  | Pre (p, expr) -> 
    let expr, decls, node_decls_map = rec_call expr in 
    Pre (p, expr), decls, node_decls_map
  | UnaryOp (p, op, expr) -> 
    let expr, decls, node_decls_map = rec_call expr in 
    UnaryOp (p, op, expr), decls, node_decls_map
  | BinaryOp (p, op, expr1, expr2) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    BinaryOp (p, op, expr1, expr2), decls1 @ decls2, node_decls_map 
  | CompOp (p, op, expr1, expr2) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    CompOp (p, op, expr1, expr2), decls1 @ decls2, node_decls_map 
  | ArrayConstr (p, expr1, expr2) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ArrayConstr (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | Arrow (p, expr1, expr2) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    Arrow (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | StructUpdate (p, expr1, lois, expr2) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    StructUpdate (p, expr1, lois, expr2), decls1 @ decls2, node_decls_map 
  | ArrayIndex (p, expr1, expr2) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    ArrayIndex (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | TernaryOp (p, op, expr1, expr2, expr3) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let expr3, decls3, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr3 in
    TernaryOp (p, op, expr1, expr2, expr3), decls1 @ decls2 @ decls3, node_decls_map
  | AnyOp (p, (p2, id, ty), expr1, Some expr2) -> 
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let ty, decls3, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    AnyOp (p, (p2, id, ty), expr1, Some expr2), decls1 @ decls2 @ decls3, node_decls_map
  | AnyOp (p, (p2, id, ty), expr, None) ->
    let expr, decls1, node_decls_map = rec_call expr in 
    let ty, decls2, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
    AnyOp (p, (p2, id, ty), expr, None), decls1 @ decls2, node_decls_map
  | Quantifier (p, q, tis, expr) -> 
    let expr, decls1, node_decls_map = rec_call expr in 
    let tis, decls2, node_decls_map = List.fold_left (fun (acc_tis, acc_decls, acc_node_decls_map) (p, id, ty) -> 
      let ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
      acc_tis @ [p, id, ty], decls @ acc_decls, node_decls_map
    ) ([], decls1, node_decls_map) tis in 
    Quantifier (p, q, tis, expr), decls1 @ decls2, node_decls_map
  | Merge (p, id, id_exprs) ->
    let id_exprs, decls, node_decls_map = List.fold_left (fun (acc_id_exprs, acc_decls, acc_node_decls_map) (id, expr) -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_id_exprs @ [id, expr], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) id_exprs in 
    Merge (p, id, id_exprs), decls, node_decls_map
  | RecordExpr (p, id, id_exprs) ->
    let id_exprs, decls, node_decls_map = List.fold_left (fun (acc_id_exprs, acc_decls, acc_node_decls_map) (id, expr) -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_id_exprs @ [id, expr], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) id_exprs in 
    RecordExpr (p, id, id_exprs), decls, node_decls_map
  | GroupExpr (p, ge, exprs) ->
    let exprs, decls, node_decls_map = List.fold_left (fun (acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) exprs in 
    GroupExpr (p, ge, exprs), decls, node_decls_map
  | Condact (p, expr1, expr2, id, exprs1, exprs2) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let exprs1, decls, node_decls_map = List.fold_left (fun (acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) ([], decls1 @ decls2, node_decls_map) exprs1 in 
    let exprs2, decls, node_decls_map = List.fold_left (fun (acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) exprs2 in 
    Condact (p, expr1, expr2, id, exprs1, exprs2), decls, node_decls_map
  | Activate (p, id, expr1, expr2, exprs) ->
    let expr1, decls1, node_decls_map = rec_call expr1 in 
    let expr2, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr2 in 
    let exprs, decls, node_decls_map = List.fold_left (fun (acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) ([], decls1 @ decls2, node_decls_map) exprs in 
    Activate (p, id, expr1, expr2, exprs), decls, node_decls_map
  | RestartEvery (p, id, exprs, expr) ->
    let expr, decls, node_decls_map = rec_call expr in 
    let exprs, decls, node_decls_map = List.fold_left (fun (acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
      acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) exprs in 
    RestartEvery (p, id, exprs, expr), decls, node_decls_map


let gen_poly_decls_ip
= fun ctx node_decls_map (p, id, ty, cl, is_const) -> 
  let ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  (p, id, ty, cl, is_const), decls, node_decls_map

let gen_poly_decls_op
= fun ctx node_decls_map (p, id, ty, cl) -> 
  let ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  (p, id, ty, cl), decls, node_decls_map

let gen_poly_decls_loc
= fun ctx node_decls_map loc -> match loc with 
| A.NodeConstDecl (p, FreeConst (p2, id, ty)) -> 
  let ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in
  A.NodeConstDecl (p, FreeConst (p2, id, ty)), decls, node_decls_map
| A.NodeConstDecl (p, UntypedConst (p2, id, expr)) -> 
  let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in
  A.NodeConstDecl (p, UntypedConst (p2, id, expr)), decls, node_decls_map
| A.NodeConstDecl (p, TypedConst (p2, id, expr, ty)) -> 
  let ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  let expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  A.NodeConstDecl (p, TypedConst (p2, id, expr, ty)), decls @ decls2, node_decls_map
| NodeVarDecl (p, var_decl) -> 
  let var_decl, decls, node_decls_map = gen_poly_decls_op ctx node_decls_map var_decl in 
  NodeVarDecl (p, var_decl), decls, node_decls_map

let rec gen_poly_decls_ni
= fun ctx node_decls_map ni -> match ni with 
  | A.Body (Equation (p, lhs, expr)) -> 
    let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    A.Body (Equation (p, lhs, expr)), decls, node_decls_map
  | Body (Assert (p, expr)) -> 
    let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    Body (Assert (p, expr)), decls, node_decls_map
  | IfBlock (p, expr, nis1, nis2) -> 
    let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    let nis1, decls, node_decls_map = List.fold_left (fun (acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) nis1 in 
    let nis2, decls, node_decls_map = List.fold_left (fun (acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) nis2 in 
    IfBlock (p, expr, nis1, nis2), decls, node_decls_map
  | FrameBlock (p, vars, nes, nis) -> 
    let nis, decls, node_decls_map = List.fold_left (fun (acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) ([], [], node_decls_map) nis in 
    let nes, decls, node_decls_map = List.fold_left (fun (acc_nes, acc_decls, acc_node_decls_map) ne -> 
      let ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map (A.Body ne) in 
      let ne = match ni with | Body ne -> ne | _ -> assert false in
      acc_nes @ [ne], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) nes in  
    FrameBlock (p, vars, nes, nis), decls, node_decls_map
  | AnnotProperty (p, n, expr, k) -> 
    let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
    AnnotProperty (p, n, expr, k), decls, node_decls_map
  | AnnotMain _ -> ni ,[], node_decls_map

let gen_poly_decls_ci
= fun ctx node_decls_map ci -> match ci with 
| A.ContractCall (p, cname, ty :: tys, ips, ops) -> (
  match gen_poly_decl ctx node_decls_map cname (ty :: tys) with 
  | pcname, Some decl, node_decls_map -> 
    A.ContractCall (p, pcname, ty :: tys, ips, ops), [decl], node_decls_map
  | pcname, None, node_decls_map -> 
    A.ContractCall (p, pcname, ty :: tys, ips, ops), [], node_decls_map
  )
| A.ContractCall (_, _, [], _, _) -> ci, [], node_decls_map
| Assume (p, id, b, expr) -> 
  let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  Assume (p, id, b, expr), decls, node_decls_map 
| Guarantee (p, id, b, expr) -> 
  let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  Guarantee (p, id, b, expr), decls, node_decls_map 
| GhostConst (FreeConst (p, id, ty)) -> 
  let ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  GhostConst (FreeConst (p, id, ty)), decls, node_decls_map
| GhostConst (UntypedConst (p, id, expr)) -> 
  let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in
  GhostConst (UntypedConst (p, id, expr)), decls, node_decls_map
| GhostConst (TypedConst (p, id, expr, ty)) -> 
  let ty, decls, node_decls_map = gen_poly_decls_ty ctx node_decls_map ty in 
  let expr, decls2, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  GhostConst (TypedConst (p, id, expr, ty)), decls @ decls2, node_decls_map
| GhostVars (p, GhostVarDec (p2, tis), expr) -> 
  let expr, decls, node_decls_map = gen_poly_decls_expr ctx node_decls_map expr in 
  let tis, decls, node_decls_map = List.fold_left (fun (acc_tis, acc_decls, acc_node_decls_map) (p, id, ty) -> 
    let ty, decls, node_decls_map = gen_poly_decls_ty ctx acc_node_decls_map ty in 
    acc_tis @ [p, id, ty], decls @ acc_decls, node_decls_map
  ) ([], decls, node_decls_map) tis in 
  GhostVars (p, GhostVarDec (p2, tis), expr), decls, node_decls_map
| Mode (p, id, creqs, cens) -> 
  let creqs, decls, node_decls_map = List.fold_left (fun (acc_creqs, acc_decls, acc_node_decls_map) (p, id, expr) -> 
    let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
    acc_creqs @ [p, id, expr], decls @ acc_decls, node_decls_map
  ) ([], [], node_decls_map) creqs in 
  let cens, decls, node_decls_map = List.fold_left (fun (acc_cens, acc_decls, acc_node_decls_map) (p, id, expr) -> 
    let expr, decls, node_decls_map = gen_poly_decls_expr ctx acc_node_decls_map expr in 
    acc_cens @ [p, id, expr], decls @ acc_decls, node_decls_map
  ) ([], decls, node_decls_map) cens in 
  Mode (p, id, creqs, cens), decls, node_decls_map
| AssumptionVars _ -> ci, [], node_decls_map

let instantiate_polymorphic_calls: Ctx.tc_context -> A.declaration list -> A.declaration list 
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

  let decls, _ = List.fold_left (fun (acc_decls, acc_node_decls_map) decl -> match decl with
  | A.FuncDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) -> 
    let ips, decls, node_decls_map = List.fold_left (fun (acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ip, decls, node_decls_map = gen_poly_decls_ip ctx acc_node_decls_map ip in 
      acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) ([], acc_decls, acc_node_decls_map) ips in 
    let ops, decls, node_decls_map = List.fold_left (fun (acc_ops, acc_decls, acc_node_decls_map) op -> 
      let op, decls, node_decls_map = gen_poly_decls_op ctx acc_node_decls_map op in 
      acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) ops in
    let locs, decls, node_decls_map = List.fold_left (fun (acc_locs, acc_decls, acc_node_decls_map) loc -> 
      let loc, decls, node_decls_map = gen_poly_decls_loc ctx acc_node_decls_map loc in 
      acc_locs @ [loc], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) locs in
    let nis, decls, node_decls_map = List.fold_left (fun (acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) nis in (
    match c with 
      | None -> 
        let decl =  A.FuncDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) in
        decl :: decls, node_decls_map
      | Some (p3, c) ->
        let c, decls, node_decls_map = List.fold_left (fun (acc_cis, acc_decls, acc_node_decls_map) ip -> 
          let ci, decls, node_decls_map = gen_poly_decls_ci ctx acc_node_decls_map ip in 
          acc_cis @ [ci], decls @ acc_decls, node_decls_map
        ) ([], decls, node_decls_map) c in 
        let decl = A.FuncDecl (p, (p2, ext, ps, ips, ops, locs, nis, Some (p3, c))) in
        decl :: decls, node_decls_map
    )
  | NodeDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) -> 
    let ips, decls, node_decls_map = List.fold_left (fun (acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ip, decls, node_decls_map = gen_poly_decls_ip ctx acc_node_decls_map ip in 
      acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) ([], acc_decls, acc_node_decls_map) ips in 
    let ops, decls, node_decls_map = List.fold_left (fun (acc_ops, acc_decls, acc_node_decls_map) op -> 
      let op, decls, node_decls_map = gen_poly_decls_op ctx acc_node_decls_map op in 
      acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) ops in
    let locs, decls, node_decls_map = List.fold_left (fun (acc_locs, acc_decls, acc_node_decls_map) loc -> 
      let loc, decls, node_decls_map = gen_poly_decls_loc ctx acc_node_decls_map loc in 
      acc_locs @ [loc], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) locs in
    let nis, decls, node_decls_map = List.fold_left (fun (acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ni, decls, node_decls_map = gen_poly_decls_ni ctx acc_node_decls_map ni in 
      acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) nis in (
    match c with 
      | None -> 
        let decl =  A.NodeDecl (p, (p2, ext, ps, ips, ops, locs, nis, c)) in
        decl :: decls, node_decls_map
      | Some (p3, c) ->
        let c, decls, node_decls_map = List.fold_left (fun (acc_cis, acc_decls, acc_node_decls_map) ip -> 
          let ci, decls, node_decls_map = gen_poly_decls_ci ctx acc_node_decls_map ip in 
          acc_cis @ [ci], decls @ acc_decls, node_decls_map
        ) ([], decls, node_decls_map) c in 
        let decl = A.NodeDecl (p, (p2, ext, ps, ips, ops, locs, nis, Some (p3, c))) in
        decl :: decls, node_decls_map
    )
  | ContractNodeDecl (p, (cname, ps, ips, ops, (p3, c))) -> 
    let ips, decls, node_decls_map = List.fold_left (fun (acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ip, decls, node_decls_map = gen_poly_decls_ip ctx acc_node_decls_map ip in 
      acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) ([], acc_decls, acc_node_decls_map) ips in 
    let ops, decls, node_decls_map = List.fold_left (fun (acc_ops, acc_decls, acc_node_decls_map) op -> 
      let op, decls, node_decls_map = gen_poly_decls_op ctx acc_node_decls_map op in 
      acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) ops in
    let c, decls, node_decls_map = List.fold_left (fun (acc_cis, acc_decls, acc_node_decls_map) ip -> 
      let ci, decls, node_decls_map = gen_poly_decls_ci ctx acc_node_decls_map ip in 
      acc_cis @ [ci], decls @ acc_decls, node_decls_map
    ) ([], decls, node_decls_map) c in 
    let decl = A.ContractNodeDecl (p, (cname, ps, ips, ops, (p3, c))) in
    decl :: decls, node_decls_map
  | TypeDecl _ 
  | ConstDecl _ 
  | NodeParamInst _ -> decl :: acc_decls, node_decls_map
  ) ([], node_decls_map) decls in
  List.rev decls