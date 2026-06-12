module A = LustreAst
module AH = LustreAstHelpers
module NI = NodeId
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module LH = LustreAstHelpers
module GI = GeneratedIdentifiers

let unwrap res = match res with 
| Ok res -> res 
| Error _ -> assert false

(* True iff `gen_id` is a monomorphization of `base_id` *)
let is_base_of gen_id base_id =
  HString.equal (NI.get_name base_id) (NI.get_name gen_id)
  && NI.get_monomorphization base_id = []

(* Merge declarations: insert each monomorphization immediately after the polymorphic version *)
let merge_decls decls gen_decls =
  let decls_with_idx = List.mapi (fun i d -> (i, d)) decls in
  let find_base_index gen_decl =
    let gen_id = match AH.node_id_of_decl gen_decl with Some id -> id | None -> assert false in
    match List.find_opt (fun (_, d) ->
      match AH.node_id_of_decl d with
      | None -> false
      | Some base_id -> is_base_of gen_id base_id
    ) decls_with_idx with
    | Some (i, _) -> i
    | None -> assert false
  in
  let with_base_index = List.map (fun g -> (find_base_index g, g)) gen_decls in
  let same_index_decls i = List.filter (fun (j, _) -> j = i) with_base_index |> List.map snd in
  List.concat (List.mapi (fun i decl -> decl :: same_index_decls i) decls)

let instantiate_type_variables_ni 
= fun ctx node_id ty_args ni  -> match ni with 
| A.Body (Equation (pos, lhs, expr)) ->
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in 
  A.Body (Equation (pos, lhs, expr))
| Body (Assert (pos, expr)) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in 
  A.Body (Assert (pos, expr))
| AnnotProperty (pos, name, expr, k) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in 
  AnnotProperty (pos, name, expr, k)
| AnnotMain _ -> ni
| IfBlock _ 
| WhenBlock _
| FrameBlock _ -> assert false

let instantiate_type_variables_loc 
= fun ctx node_id ty_args loc -> match loc with 
| A.NodeConstDecl (p, FreeConst (p2, id, ty)) -> 
  let ty = Chk.instantiate_type_variables ctx p node_id ty ty_args |> unwrap in
  A.NodeConstDecl (p, FreeConst (p2, id, ty))
| A.NodeConstDecl (p, TypedConst (p2, id, expr, ty)) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  let ty = Chk.instantiate_type_variables ctx p node_id ty ty_args |> unwrap in
  A.NodeConstDecl (p, TypedConst (p2, id, expr, ty))
| A.NodeConstDecl (p, UntypedConst (p2, id, expr)) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  A.NodeConstDecl (p, UntypedConst (p2, id, expr))
| NodeVarDecl (p, (p2, id, ty, cl)) -> 
  let ty = Chk.instantiate_type_variables ctx p node_id ty ty_args |> unwrap in
  NodeVarDecl (p, (p2, id, ty, cl))

let instantiate_type_variables_ci
= fun ctx node_id ty_args ci -> match ci with 
| A.GhostConst FreeConst (p, id, ty) -> 
  let ty = Chk.instantiate_type_variables ctx p node_id ty ty_args |> unwrap in
  A.GhostConst (FreeConst (p, id, ty))
| A.GhostConst TypedConst (p, id, expr, ty) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  let ty = Chk.instantiate_type_variables ctx p node_id ty ty_args |> unwrap in
  A.GhostConst (TypedConst (p, id, expr, ty))
| A.GhostConst UntypedConst (p, id, expr) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  A.GhostConst (UntypedConst (p, id, expr))
| GhostVars (p, lhs, expr) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  GhostVars (p, lhs, expr)
| Assume (p, name, b, expr) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  Assume (p, name, b, expr)
| Guarantee (p, name, b, expr) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  Guarantee (p, name, b, expr)
| Decreases (p, expr) -> 
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in  
  Decreases (p, expr)
| Mode (p, id, reqs, enss) -> 
  let reqs = List.map (fun (p, id, expr) -> 
    let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in 
    p, id, expr
  ) reqs in 
  let enss = List.map (fun (p, id, expr) -> 
    let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in 
    p, id, expr
  ) enss in 
  Mode (p, id, reqs, enss)
| AssumptionVars _ -> ci
| ContractCall (p, id, ty_args, exprs, ids) -> 
  let exprs = List.map (fun expr -> 
    Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap
  ) exprs in 
  let ty_args = List.map (fun ty_arg -> 
    Chk.instantiate_type_variables ctx p node_id ty_arg ty_args |> unwrap
  ) ty_args in
  ContractCall (p, id, ty_args, exprs, ids)

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
let rec gen_poly_decl: Ctx.tc_context -> GI.t NI.Map.t -> NI.t option -> (A.declaration * A.lustre_type list list) NI.Map.t ->
                   NI.t -> A.lustre_type list -> Ctx.tc_context * GI.t NI.Map.t * NI.t *  A.declaration list * (A.declaration * A.lustre_type list list) NI.Map.t 
= fun ctx gids caller_nname node_decls_map node_id ty_args ->
  (* Get node_id fields *)
  let node_type = NI.get_node_type node_id in 
  let name = NI.get_name node_id in
  let monomorphization = NI.get_monomorphization node_id in
  let user_name = Format.asprintf
    "%a<%a>"
    HString.pp_print_hstring name
    (Lib.pp_print_list A.pp_print_lustre_type ";") ty_args |> HString.mk_hstring
  in
  (* Check for pre-existing instantiation of the node before compiling a new one *)
  let decl, tyss = NI.Map.find node_id node_decls_map in 
  let find_decl tys = 
    (List.length tys = List.length ty_args) &&
    (* eq_lustre_type only considers base types, so for now we conservatively do not reuse polymorphic 
       instantiations with refinement types *)
    (List.for_all2 (fun ty p -> 
      match Ctx.type_contains_ref ctx ty, 
            Ctx.type_contains_ref ctx p, 
            Chk.eq_lustre_type ctx ty p with 
    | false, false, Ok true -> true
    | _ -> false
    ) tys ty_args) 
  in
  match Lib.find_opt_index find_decl tyss with 
  (* This polymorphic instantiation already exists *)
  | Some j -> 
    let pnname = NI.mk_node_id ~node_type ~monomorphization:(monomorphization @ [j]) ~user_name name in
    ctx, gids, pnname, [], node_decls_map   
  (* Creating new polymorphic instantiation *) 
  | None ->
    let span, is_function, func_attrs, is_contract, ext, opac, ips, ops, locs, nis, c =
      match NI.Map.find node_id node_decls_map with
      | (A.FuncDecl (span, (_, ext, opac, _, ips, ops, locs, nis, c), func_attrs), _) ->
        span, true, func_attrs, false, ext, opac, ips, ops, locs, nis, c
      | (A.NodeDecl (span, (_, ext, opac, __FUNCTION__, ips, ops, locs, nis, c)), _) ->
        span, false, {is_lemma = false; is_rec = false}, false, ext, opac, ips, ops, locs, nis, c
      | (A.ContractNodeDecl (span, (_, _, ips, ops, c)), _) ->
        span, false, {is_lemma = false; is_rec = false}, true, false, A.Default, ips, ops, [], [], Some c
      | _ -> assert false
    in
    let nis = List.filter (fun ni -> match ni with 
    | A.AnnotMain _ -> false 
    | _ -> true
    ) nis in
    (* Instantiate type variables *)
    let nis = List.map (instantiate_type_variables_ni ctx node_id ty_args) nis in
    let locs = List.map (instantiate_type_variables_loc ctx node_id ty_args) locs in
    let c = match c with 
    | Some (pos, cis) -> 
      Some (pos, (List.map (instantiate_type_variables_ci ctx node_id ty_args) cis))
    | None -> c 
    in
    let ips = List.map (fun (pos, id, ty, cl, const) ->
      let ty = Chk.instantiate_type_variables ctx pos node_id ty ty_args in
      match ty with 
      | Ok ty -> (pos, id, ty, cl, const)
      | Error _ -> assert false
    ) ips in 
    let ops = List.map (fun (pos, id, ty, cl) -> 
      let ty = Chk.instantiate_type_variables ctx pos node_id ty ty_args in
      match ty with 
      | Ok ty -> (pos, id, ty, cl)
      | Error _ -> assert false
    )  ops in
    (* Pass forward type variables passed from caller to callee *)
    let ps =
      match caller_nname with
      | None -> []
      | Some caller_nname ->
        let ty_vars = List.map (Ctx.ty_vars_of_type ctx caller_nname) ty_args in
        List.fold_left Ctx.SI.union Ctx.SI.empty ty_vars |> Ctx.SI.elements
    in
    (* Create fresh identifier for instantiated polymorphic node *)
    let pnname = NI.mk_node_id ~node_type ~monomorphization:(monomorphization @ [List.length tyss]) ~user_name name in
    (* Remember new instantiation *)
    let node_decls_map = NI.Map.add node_id (decl, tyss @ [ty_args]) node_decls_map in
    let ctx, called_decl = 
      if is_function then 
        let ctx = Ctx.add_ty_vars_node ctx pnname ps in
        let ctx = Ctx.add_node_param_attr ctx pnname ips in 
        let node_ty = build_node_fun_ty span.start_pos ips ops in
        Ctx.add_ty_vars_node (Ctx.add_ty_node ctx pnname node_ty true) pnname ps, 
        A.FuncDecl (span, (pnname, ext, opac, ps, ips, ops, locs, nis, c), func_attrs)
      else if is_contract then 
        let c = Option.get c in
        let ctx = Ctx.add_ty_vars_contract ctx pnname ps in
        let ctx, _ = match Chk.extract_exports pnname ctx c with 
        | Ok ctx -> ctx 
        | Error _ -> assert false 
        in
        Ctx.add_ty_vars_contract ctx pnname ps, 
        ContractNodeDecl (span, (pnname, ps, ips, ops, c))
      else     
        let ctx = Ctx.add_ty_vars_node ctx pnname ps in
        let ctx = Ctx.add_node_param_attr ctx pnname ips in
        let node_ty = build_node_fun_ty span.start_pos ips ops in
        Ctx.add_ty_vars_node (Ctx.add_ty_node ctx pnname node_ty false) pnname ps, 
        NodeDecl (span, (pnname, ext, opac, ps, ips, ops, locs, nis, c))
    in

    (* If the monomorphization still has parameters, it could be monomorphized again *)
    let node_decls_map = 
      if List.length ps > 0 then 
        NI.Map.add pnname (called_decl, []) node_decls_map 
      else 
        node_decls_map 
    in

    let ctx, gids, decls, node_decls_map = match NI.Map.find_opt node_id gids with
    | None -> 
      ctx, gids, [], node_decls_map 
    | Some polymorphic_gids -> 

      (* Create monomorphization of gids for this new generated declaration *)
      let glocals = GI.StringMap.map (fun ty -> 
        Chk.instantiate_type_variables ctx Lib.dummy_pos node_id ty ty_args |> unwrap 
      ) polymorphic_gids.locals in 
      let ib_oracles = List.map (fun (id, ty) -> 
        let ty = Chk.instantiate_type_variables ctx Lib.dummy_pos node_id ty ty_args |> unwrap in 
        (id, ty)
      ) polymorphic_gids.ib_oracles in
      let geqs = List.map (fun (q_vars, sc, lhs, expr, source) -> 
        let q_vars = List.map (fun (pos, id, ty) -> 
          let ty = Chk.instantiate_type_variables ctx pos node_id ty ty_args |> unwrap in 
          pos, id, ty
        ) q_vars in 
        let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in
        (q_vars, sc, lhs, expr, source)
      ) polymorphic_gids.equations in

      (* Recursively create new polymorphic instantiations, e.g. if the gids contain call M<int> *)
      let monomorphized_gids = { polymorphic_gids with locals = glocals; equations = geqs; ib_oracles = ib_oracles; } in
      gen_poly_decls_gids ctx monomorphized_gids gids pnname node_decls_map
    in

    (* Recursively create new instantiations (this node could use the given polymorphic 
    instantiation to call another polymorphic node *)
    let ctx, gids, decls, gen_decls, node_decls_map = gen_poly_decls_decls ctx gids node_decls_map (decls @ [called_decl]) in
    ctx, gids, pnname, decls @ gen_decls, node_decls_map                     

and gen_poly_decls_ty: Ctx.tc_context -> GI.t NI.Map.t -> NI.t option -> (A.declaration * A.lustre_type list list) NI.Map.t ->
                           A.lustre_type -> Ctx.tc_context * GI.t NI.Map.t * A.lustre_type * A.declaration list * (A.declaration * A.lustre_type list list) NI.Map.t
= fun ctx gids node_id node_decls_map ty -> match ty with
  | A.TupleType (p, tys) -> 
    let ctx, gids, tys, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_tys, acc_decls, acc_node_decls_map) ty -> 
      let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id acc_node_decls_map ty in 
      ctx, gids, acc_tys @ [ty], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) tys in 
    ctx, gids, TupleType (p, tys), decls, node_decls_map
  | GroupType (p, tys) -> 
    let ctx, gids, tys, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_tys, acc_decls, acc_node_decls_map) ty -> 
      let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id acc_node_decls_map ty in 
      ctx, gids, acc_tys @ [ty], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) tys in 
    ctx, gids, GroupType (p, tys), decls, node_decls_map
  | RecordType (p, id, tis) -> 
    let ctx, gids, tis, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_tys, acc_decls, acc_node_decls_map) (p, id, ty) -> 
      let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id acc_node_decls_map ty in 
      ctx, gids, acc_tys @ [(p, id, ty)], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) tis in 
    ctx, gids, RecordType (p, id, tis), decls, node_decls_map
  | ArrayType (p, (ty, expr)) -> 
    let ctx, gids, ty, decls1, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
    let ctx, gids, expr, decls2, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
    ctx, gids, ArrayType (p, (ty, expr)), decls1 @ decls2, node_decls_map
  | TArr (p, ty1, ty2) -> 
    let ctx, gids, ty1, decls1, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty1 in 
    let ctx, gids, ty2, decls2, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty2 in 
    ctx, gids, TArr (p, ty1, ty2), decls1 @ decls2, node_decls_map
  | Map (p, ty1, ty2) -> 
    let ctx, gids, ty1, decls1, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty1 in 
    let ctx, gids, ty2, decls2, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty2 in 
    ctx, gids, Map (p, ty1, ty2), decls1 @ decls2, node_decls_map
  | Set (p, ty) -> 
    let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
    ctx, gids, Set (p, ty), decls, node_decls_map
  | RefinementType (p, (p2, id, ty), expr) -> 
    let ctx, gids, ty, decls1, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
    let ctx, gids, expr, decls2, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
    ctx, gids, RefinementType (p, (p2, id, ty), expr), decls1 @ decls2, node_decls_map
  | Bool _ | Int _ | Real _ | UserType _
  | AbstractType _ | EnumType _ | History _ | SBitVector _ | UBitVector _ -> ctx, gids, ty, [], node_decls_map

and gen_poly_decls_gids ctx gids gids_map node_id node_decls_map = 
  let ctx, gids_map, decls, glocals, node_decls_map = GI.StringMap.fold (fun id ty (ctx, gids_map, acc_decls, acc_glocals, acc_node_decls_map) -> 
    let ctx, gids_map, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids_map (Some node_id) acc_node_decls_map ty in 
    ctx, gids_map, decls @ acc_decls, GI.StringMap.add id ty acc_glocals, node_decls_map
  ) gids.GI.locals (ctx, gids_map, [], GI.StringMap.empty, node_decls_map) in
  let ctx, gids_map, decls, ib_oracles, node_decls_map = List.fold_left (fun (ctx, gids_map, acc_decls, acc_ib_oracles, acc_node_decls_map) (id, ty) -> 
    let ctx, gids_map, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids_map (Some node_id) acc_node_decls_map ty in 
    ctx, gids_map, decls @ acc_decls, (id, ty) :: acc_ib_oracles, node_decls_map
  ) (ctx, gids_map, decls, [], node_decls_map) gids.GI.ib_oracles in 
  let ctx, gids_map, decls, geqs, node_decls_map = List.fold_left (fun (ctx, gids_map, acc_decls, acc_geqs, acc_node_decls_map) (q_vars, sc, lhs, expr, source) -> 
    let ctx, gids_map, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids_map (Some node_id) acc_node_decls_map expr in 
    ctx, gids_map, decls @ acc_decls, (q_vars, sc, lhs, expr, source) :: acc_geqs, node_decls_map
  ) (ctx, gids_map, decls, [], node_decls_map) gids.GI.equations in 

  let gids = { gids with 
    locals = glocals; 
    ib_oracles = ib_oracles; 
    equations = geqs 
  } in
  let gids_map = NI.Map.add node_id gids gids_map in

  ctx, gids_map, decls, node_decls_map

and gen_poly_decls_loi
= fun ctx gids caller_nname node_decls_map loi ->
  let re e =
    let ctx, gids, e, decls, ndm = gen_poly_decls_expr ctx gids caller_nname node_decls_map e in
    ctx, gids, e, decls, ndm
  in
  match loi with
  | A.Label _ -> ctx, gids, loi, [], node_decls_map
  | A.Index (p, e) ->
    let ctx, gids, e, decls, ndm = re e in
    ctx, gids, A.Index (p, e), decls, ndm
  | A.MapIndex (p, e) ->
    let ctx, gids, e, decls, ndm = re e in
    ctx, gids, A.MapIndex (p, e), decls, ndm
  | A.SetIndex (p, e) ->
    let ctx, gids, e, decls, ndm = re e in
    ctx, gids, A.SetIndex (p, e), decls, ndm
  | A.GenericIndex (p, e) ->
    let ctx, gids, e, decls, ndm = re e in
    ctx, gids, A.GenericIndex (p, e), decls, ndm

and gen_poly_decls_expr: Ctx.tc_context -> GI.t NI.Map.t -> NI.t option -> (A.declaration * A.lustre_type list list) NI.Map.t ->
                             A.expr -> Ctx.tc_context * GI.t NI.Map.t * A.expr *  A.declaration list * (A.declaration * A.lustre_type list list) NI.Map.t
= fun ctx gids caller_nname node_decls_map expr -> 
  let rec_call = gen_poly_decls_expr ctx gids caller_nname node_decls_map in
  match expr with 
  | A.Call (pos, ty :: tys, node_id, exprs) ->
    let ctx, gids, exprs, decls1, node_decls_map = List.fold_left (fun (ctx, gids, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) exprs in 
    let ctx, gids, pnname, decls2, node_decls_map  = gen_poly_decl ctx gids caller_nname node_decls_map node_id (ty :: tys) in

    let ty_args =
      match caller_nname with
      | None -> []
      | Some caller_nname ->
        let ty_vars = List.map (Ctx.ty_vars_of_type ctx caller_nname) (ty :: tys) in
        List.fold_left Ctx.SI.union Ctx.SI.empty ty_vars
        |> Ctx.SI.elements
        |> List.map (fun ty_var -> A.UserType (pos, [], ty_var))
    in
    ctx, gids, Call (pos, ty_args, pnname, exprs), decls2 @ decls1, node_decls_map
  | Call (pos, [], node_id, exprs) ->
    let ctx, gids, exprs, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) exprs in 
    ctx, gids, Call (pos, [], node_id, exprs), decls, node_decls_map
  | Ident _ | EmptyMap (_, None) | EmptySet (_, None)
  | Const _
  | ModeRef _ -> ctx, gids, expr, [], node_decls_map
  | RecordProject (p, expr, id) -> 
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in 
    ctx, gids, RecordProject (p, expr, id), decls, node_decls_map
  | ConvOp (p, op, expr) -> 
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in 
    ctx, gids, ConvOp (p, op, expr), decls, node_decls_map
  | When (p, expr, cl) -> 
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in 
    ctx, gids, When (p, expr, cl), decls, node_decls_map
  | Pre (p, expr) -> 
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in 
    ctx, gids, Pre (p, expr), decls, node_decls_map
  | UnaryOp (p, op, expr) -> 
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in 
    ctx, gids, UnaryOp (p, op, expr), decls, node_decls_map
  | Extract (p, expr, ub, lb) -> 
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in 
    ctx, gids, Extract (p, expr, ub, lb), decls, node_decls_map
  | BinaryOp (p, op, expr1, expr2) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    ctx, gids, BinaryOp (p, op, expr1, expr2), decls1 @ decls2, node_decls_map 
  | CompOp (p, op, expr1, expr2) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    ctx, gids, CompOp (p, op, expr1, expr2), decls1 @ decls2, node_decls_map 
  | ArrayConstr (p, expr1, expr2) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    ctx, gids, ArrayConstr (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | Arrow (p, expr1, expr2) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    ctx, gids, Arrow (p, expr1, expr2), decls1 @ decls2, node_decls_map 
  | TypeAscription (p, expr, ty) ->
    let ctx, gids, expr, decls1, node_decls_map = rec_call expr in
    let ctx, gids, ty, decls2, node_decls_map = gen_poly_decls_ty ctx gids caller_nname node_decls_map ty in 
    ctx, gids, TypeAscription (p, expr, ty), decls1 @ decls2, node_decls_map
  | StructUpdate (p, expr1, lois, Some expr2) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in
    let ctx, gids, lois, decls3, node_decls_map = List.fold_left (fun (ctx, gids, acc_lois, acc_decls, acc_ndm) loi ->
      let ctx, gids, loi, decls, ndm = gen_poly_decls_loi ctx gids caller_nname acc_ndm loi in
      ctx, gids, acc_lois @ [loi], acc_decls @ decls, ndm
    ) (ctx, gids, [], [], node_decls_map) lois in
    ctx, gids, StructUpdate (p, expr1, lois, Some expr2), decls1 @ decls2 @ decls3, node_decls_map
  | StructUpdate (p, expr1, lois, None) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in
    let ctx, gids, lois, decls2, node_decls_map = List.fold_left (fun (ctx, gids, acc_lois, acc_decls, acc_ndm) loi ->
      let ctx, gids, loi, decls, ndm = gen_poly_decls_loi ctx gids caller_nname acc_ndm loi in
      ctx, gids, acc_lois @ [loi], acc_decls @ decls, ndm
    ) (ctx, gids, [], [], node_decls_map) lois in
    ctx, gids, StructUpdate (p, expr1, lois, None), decls1 @ decls2, node_decls_map
  | IndexAccess (p, expr1, expr2, kind) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    ctx, gids, IndexAccess (p, expr1, expr2, kind), decls1 @ decls2, node_decls_map 
  | TernaryOp (p, op, expr1, expr2, expr3) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    let ctx, gids, expr3, decls3, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr3 in
    ctx, gids, TernaryOp (p, op, expr1, expr2, expr3), decls1 @ decls2 @ decls3, node_decls_map
  | AnyOp (p, (p2, id, ty), expr) ->
    let ctx, gids, expr, decls1, node_decls_map = rec_call expr in 
    let ctx, gids, ty, decls2, node_decls_map = gen_poly_decls_ty ctx gids caller_nname node_decls_map ty in 
    ctx, gids, AnyOp (p, (p2, id, ty), expr), decls1 @ decls2, node_decls_map
  | ChooseOp (p, (p2, id, ty), expr) ->
    let ctx, gids, expr, decls1, node_decls_map = rec_call expr in 
    let ctx, gids, ty, decls2, node_decls_map = gen_poly_decls_ty ctx gids caller_nname node_decls_map ty in 
    ctx, gids, ChooseOp (p, (p2, id, ty), expr), decls1 @ decls2, node_decls_map
  | EmptySet (p, Some ty) ->
    let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids caller_nname node_decls_map ty in 
    ctx, gids, EmptySet (p, Some ty), decls, node_decls_map
  | EmptyMap (p, Some (kt, vt)) ->
    let ctx, gids, kt, decls1, node_decls_map = gen_poly_decls_ty ctx gids caller_nname node_decls_map kt in 
    let ctx, gids, vt, decls2, node_decls_map = gen_poly_decls_ty ctx gids caller_nname node_decls_map vt in 
    ctx, gids, EmptyMap (p, Some (kt, vt)), decls1 @ decls2, node_decls_map
  | Quantifier (p, q, tis, expr) -> 
    let ctx, gids, expr, decls1, node_decls_map = rec_call expr in 
    let ctx, gids, tis, decls2, node_decls_map = List.fold_left (fun (ctx, gids, acc_tis, acc_decls, acc_node_decls_map) (p, id, ty) -> 
      let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids caller_nname acc_node_decls_map ty in 
      ctx, gids, acc_tis @ [p, id, ty], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) tis in 
    ctx, gids, Quantifier (p, q, tis, expr), decls1 @ decls2, node_decls_map
  | Merge (p, id, id_exprs) ->
    let ctx, gids, id_exprs, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_id_exprs, acc_decls, acc_node_decls_map) (id, expr) -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_id_exprs @ [id, expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) id_exprs in 
    ctx, gids, Merge (p, id, id_exprs), decls, node_decls_map
  | RecordExpr (p, id, ps, id_exprs) ->
    let ctx, gids, id_exprs, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_id_exprs, acc_decls, acc_node_decls_map) (id, expr) -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_id_exprs @ [id, expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) id_exprs in 
    ctx, gids, RecordExpr (p, id, ps, id_exprs), decls, node_decls_map
  | GroupExpr (p, ge, exprs) ->
    let ctx, gids, exprs, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) exprs in 
    ctx, gids, GroupExpr (p, ge, exprs), decls, node_decls_map
  | Condact (p, expr1, expr2, id, exprs1, exprs2) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    let ctx, gids, exprs1, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls1 @ decls2, node_decls_map) exprs1 in 
    let ctx, gids, exprs2, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls, node_decls_map) exprs2 in 
    ctx, gids, Condact (p, expr1, expr2, id, exprs1, exprs2), decls, node_decls_map
  | Activate (p, id, expr1, expr2, exprs) ->
    let ctx, gids, expr1, decls1, node_decls_map = rec_call expr1 in 
    let ctx, gids, expr2, decls2, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map expr2 in 
    let ctx, gids, exprs, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls1 @ decls2, node_decls_map) exprs in 
    ctx, gids, Activate (p, id, expr1, expr2, exprs), decls, node_decls_map
  | RestartEvery (p, id, exprs, expr) ->
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in 
    let ctx, gids, exprs, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_exprs, acc_decls, acc_node_decls_map) expr -> 
      let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map expr in 
      ctx, gids, acc_exprs @ [expr], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls, node_decls_map) exprs in 
    ctx, gids, RestartEvery (p, id, exprs, expr), decls, node_decls_map

and gen_poly_decls_ni
= fun ctx gids node_id node_decls_map ni -> match ni with 
  | A.Body (Equation (p, lhs, expr)) -> 
    let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
    ctx, gids, A.Body (Equation (p, lhs, expr)), decls, node_decls_map
  | Body (Assert (p, expr)) -> 
    let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
    ctx, gids, Body (Assert (p, expr)), decls, node_decls_map
  | IfBlock (p, expr, nis1, nis2) -> 
    let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
    let ctx, gids, nis1, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids node_id acc_node_decls_map ni in 
      ctx, gids, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls, node_decls_map) nis1 in 
    let ctx, gids, nis2, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids node_id acc_node_decls_map ni in 
      ctx, gids, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls, node_decls_map) nis2 in 
    ctx, gids, IfBlock (p, expr, nis1, nis2), decls, node_decls_map
  | WhenBlock (p, expr, nis1, nis2) ->
    let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in
    let ctx, gids, nis1, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nis, acc_decls, acc_node_decls_map) ni ->
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids node_id acc_node_decls_map ni in
      ctx, gids, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls, node_decls_map) nis1 in
    let ctx, gids, nis2, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nis, acc_decls, acc_node_decls_map) ni ->
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids node_id acc_node_decls_map ni in
      ctx, gids, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls, node_decls_map) nis2 in
    ctx, gids, WhenBlock (p, expr, nis1, nis2), decls, node_decls_map
  | FrameBlock (p, vars, nes, nis) -> 
    let ctx, gids, nis, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids node_id acc_node_decls_map ni in 
      ctx, gids, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) nis in 
    let ctx, gids, nes, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nes, acc_decls, acc_node_decls_map) ne -> 
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids node_id acc_node_decls_map (A.Body ne) in 
      let ne = match ni with | Body ne -> ne | _ -> assert false in
      ctx, gids, acc_nes @ [ne], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls, node_decls_map) nes in  
    ctx, gids, FrameBlock (p, vars, nes, nis), decls, node_decls_map
  | AnnotProperty (p, n, expr, k) -> 
    let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
    ctx, gids, AnnotProperty (p, n, expr, k), decls, node_decls_map
  | AnnotMain _ -> ctx, gids, ni, [], node_decls_map

and gen_poly_decls_op
= fun ctx gids node_id node_decls_map (p, id, ty, cl) -> 
  let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
  ctx, gids, (p, id, ty, cl), decls, node_decls_map

and gen_poly_decls_loc
= fun ctx gids node_id node_decls_map loc -> match loc with 
| A.NodeConstDecl (p, FreeConst (p2, id, ty)) -> 
  let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in
  ctx, gids, A.NodeConstDecl (p, FreeConst (p2, id, ty)), decls, node_decls_map
| A.NodeConstDecl (p, UntypedConst (p2, id, expr)) -> 
  let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in
  ctx, gids, A.NodeConstDecl (p, UntypedConst (p2, id, expr)), decls, node_decls_map
| A.NodeConstDecl (p, TypedConst (p2, id, expr, ty)) -> 
  let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
  let ctx, gids, expr, decls2, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
  ctx, gids, A.NodeConstDecl (p, TypedConst (p2, id, expr, ty)), decls @ decls2, node_decls_map
| NodeVarDecl (p, var_decl) -> 
  let ctx, gids, var_decl, decls, node_decls_map = gen_poly_decls_op ctx gids node_id node_decls_map var_decl in 
  ctx, gids, NodeVarDecl (p, var_decl), decls, node_decls_map

and gen_poly_decls_ip
= fun ctx gids node_id node_decls_map (p, id, ty, cl, is_const) -> 
  let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
  ctx, gids, (p, id, ty, cl, is_const), decls, node_decls_map

and gen_poly_decls_ci
= fun ctx gids node_id node_decls_map ci -> match ci with 
| A.ContractCall (p, cname, ty_arg :: ty_args, ips, ops) -> 
  let ctx, gids, pcname, decls, node_decls_map = gen_poly_decl ctx gids node_id node_decls_map cname (ty_arg :: ty_args) in 
  ctx, gids, A.ContractCall (p, pcname, ty_arg :: ty_args, ips, ops), decls, node_decls_map
| A.ContractCall (_, _, [], _, _) -> ctx, gids, ci, [], node_decls_map
| Assume (p, id, b, expr) -> 
  let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
  ctx, gids, Assume (p, id, b, expr), decls, node_decls_map 
| Guarantee (p, id, b, expr) -> 
  let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
  ctx, gids, Guarantee (p, id, b, expr), decls, node_decls_map 
| Decreases (p, expr) -> 
  let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
  ctx, gids, Decreases (p, expr), decls, node_decls_map
| GhostConst (FreeConst (p, id, ty)) -> 
  let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
  ctx, gids, GhostConst (FreeConst (p, id, ty)), decls, node_decls_map
| GhostConst (UntypedConst (p, id, expr)) -> 
  let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in
  ctx, gids, GhostConst (UntypedConst (p, id, expr)), decls, node_decls_map
| GhostConst (TypedConst (p, id, expr, ty)) -> 
  let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id node_decls_map ty in 
  let ctx, gids, expr, decls2, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
  ctx, gids, GhostConst (TypedConst (p, id, expr, ty)), decls @ decls2, node_decls_map
| GhostVars (p, GhostVarDec (p2, tis), expr) -> 
  let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id node_decls_map expr in 
  let ctx, gids, tis, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_tis, acc_decls, acc_node_decls_map) (p, id, ty) -> 
    let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id acc_node_decls_map ty in 
    ctx, gids, acc_tis @ [p, id, ty], decls @ acc_decls, node_decls_map
  ) (ctx, gids, [], decls, node_decls_map) tis in 
  ctx, gids, GhostVars (p, GhostVarDec (p2, tis), expr), decls, node_decls_map
| Mode (p, id, creqs, cens) -> 
  let ctx, gids, creqs, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_creqs, acc_decls, acc_node_decls_map) (p, id, expr) -> 
    let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id acc_node_decls_map expr in 
    ctx, gids, acc_creqs @ [p, id, expr], decls @ acc_decls, node_decls_map
  ) (ctx, gids, [], [], node_decls_map) creqs in 
  let ctx, gids, cens, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_cens, acc_decls, acc_node_decls_map) (p, id, expr) -> 
    let ctx, gids, expr, decls, node_decls_map = gen_poly_decls_expr ctx gids node_id acc_node_decls_map expr in 
    ctx, gids, acc_cens @ [p, id, expr], decls @ acc_decls, node_decls_map
  ) (ctx, gids, [], decls, node_decls_map) cens in 
  ctx, gids, Mode (p, id, creqs, cens), decls, node_decls_map
| AssumptionVars _ -> ctx, gids, ci, [], node_decls_map

and gen_poly_decls_decls
= fun ctx gids node_decls_map decls ->
  let ctx, gids, decls, gen_decls, node_decls_map =
  List.fold_left (fun (ctx, gids, acc_decls, acc_gen_decls, acc_node_decls_map) decl -> match decl with
  | A.FuncDecl (p, (node_id, ext, opac, ps, ips, ops, locs, nis, c), is_rec) ->
    let ctx = Chk.add_ty_params_node_ctx ctx node_id ps in
    let ctx, gids, gen_decls, acc_node_decls_map = match NI.Map.find_opt node_id gids with  
    | Some node_gids -> 
      let ctx, gids, decls, node_decls_map = gen_poly_decls_gids ctx node_gids gids node_id acc_node_decls_map in 
      ctx, gids, decls, node_decls_map
    | None -> ctx, gids, [], acc_node_decls_map
    in 
    let ctx, gids, ips, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ctx, gids, ip, decls, node_decls_map = gen_poly_decls_ip ctx gids (Some node_id) acc_node_decls_map ip in 
      ctx, gids, acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, acc_node_decls_map) ips in 
    let ctx, gids, ops, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_ops, acc_decls, acc_node_decls_map) op -> 
      let ctx, gids, op, decls, node_decls_map = gen_poly_decls_op ctx gids (Some node_id) acc_node_decls_map op in 
      ctx, gids, acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) ops in
    let ctx, gids, locs, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_locs, acc_decls, acc_node_decls_map) loc -> 
      let ctx, gids, loc, decls, node_decls_map = gen_poly_decls_loc ctx gids (Some node_id) acc_node_decls_map loc in 
      ctx, gids, acc_locs @ [loc], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) locs in
    let ctx, gids, nis, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids (Some node_id) acc_node_decls_map ni in 
      ctx, gids, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) nis in (
    match c with 
    | None -> 
      let decl =  A.FuncDecl (p, (node_id, ext, opac, ps, ips, ops, locs, nis, c), is_rec) in
      ctx, gids, decl :: acc_decls, gen_decls @ acc_gen_decls, node_decls_map
    | Some (p3, c) ->
      let ctx, gids, c, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_cis, acc_decls, acc_node_decls_map) ip -> 
        let ctx, gids, ci, decls, node_decls_map = gen_poly_decls_ci ctx gids (Some node_id) acc_node_decls_map ip in 
        ctx, gids, acc_cis @ [ci], decls @ acc_decls, node_decls_map
      ) (ctx, gids, [], gen_decls, node_decls_map) c in 
      let decl = A.FuncDecl (p, (node_id, ext, opac, ps, ips, ops, locs, nis, Some (p3, c)), is_rec) in
      ctx, gids, decl :: acc_decls, gen_decls @ acc_gen_decls, node_decls_map
    )
  | NodeDecl (p, (node_id, ext, opac, ps, ips, ops, locs, nis, c)) ->
    let ctx = Chk.add_ty_params_node_ctx ctx node_id ps in
    let ctx, gids, gen_decls, acc_node_decls_map = match NI.Map.find_opt node_id gids with  
    | Some node_gids -> 
      let ctx, gids, decls, node_decls_map = gen_poly_decls_gids ctx node_gids gids node_id acc_node_decls_map in 
      ctx, gids, decls, node_decls_map
    | None -> ctx, gids, [], acc_node_decls_map
    in 
    let ctx, gids, ips, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ctx, gids, ip, decls, node_decls_map = gen_poly_decls_ip ctx gids (Some node_id) acc_node_decls_map ip in 
      ctx, gids, acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, acc_node_decls_map) ips in 
    let ctx, gids, ops, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_ops, acc_decls, acc_node_decls_map) op -> 
      let ctx, gids, op, decls, node_decls_map = gen_poly_decls_op ctx gids (Some node_id) acc_node_decls_map op in 
      ctx, gids, acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) ops in
    let ctx, gids, locs, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_locs, acc_decls, acc_node_decls_map) loc -> 
      let ctx, gids, loc, decls, node_decls_map = gen_poly_decls_loc ctx gids (Some node_id) acc_node_decls_map loc in 
      ctx, gids, acc_locs @ [loc], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) locs in
    let ctx, gids, nis, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_nis, acc_decls, acc_node_decls_map) ni -> 
      let ctx, gids, ni, decls, node_decls_map = gen_poly_decls_ni ctx gids (Some node_id) acc_node_decls_map ni in 
      ctx, gids, acc_nis @ [ni], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) nis in (
    match c with 
      | None -> 
        let decl =  A.NodeDecl (p, (node_id, ext, opac, ps, ips, ops, locs, nis, c)) in
        ctx, gids, decl :: acc_decls, gen_decls @ acc_gen_decls, node_decls_map
      | Some (p3, c) ->
        let ctx, gids, c, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_cis, acc_decls, acc_node_decls_map) ip -> 
          let ctx, gids, ci, decls, node_decls_map = gen_poly_decls_ci ctx gids (Some node_id) acc_node_decls_map ip in 
          ctx, gids, acc_cis @ [ci], decls @ acc_decls, node_decls_map
        ) (ctx, gids, [], gen_decls, node_decls_map) c in 
        let decl = A.NodeDecl (p, (node_id, ext, opac, ps, ips, ops, locs, nis, Some (p3, c))) in
        ctx, gids, decl :: acc_decls, gen_decls @ acc_gen_decls, node_decls_map
    )
  | ContractNodeDecl (p, (cname, ps, ips, ops, (p3, c))) ->
    let ctx = Chk.add_ty_params_node_ctx ctx cname ps in
    let ctx, gids, gen_decls, acc_node_decls_map = match NI.Map.find_opt cname gids with  
    | Some node_gids -> 
      let ctx, gids, decls, node_decls_map = gen_poly_decls_gids ctx node_gids gids cname acc_node_decls_map in 
      ctx, gids, decls, node_decls_map
    | None -> ctx, gids, [], acc_node_decls_map
    in 
    let ctx, gids, ips, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_ips, acc_decls, acc_node_decls_map) ip -> 
      let ctx, gids, ip, decls, node_decls_map = gen_poly_decls_ip ctx gids (Some cname) acc_node_decls_map ip in 
      ctx, gids, acc_ips @ [ip], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, acc_node_decls_map) ips in 
    let ctx, gids, ops, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_ops, acc_decls, acc_node_decls_map) op -> 
      let ctx, gids, op, decls, node_decls_map = gen_poly_decls_op ctx gids (Some cname) acc_node_decls_map op in 
      ctx, gids, acc_ops @ [op], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) ops in
    let ctx, gids, c, gen_decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_cis, acc_decls, acc_node_decls_map) ip -> 
      let ctx, gids, ci, decls, node_decls_map = gen_poly_decls_ci ctx gids (Some cname) acc_node_decls_map ip in 
      ctx, gids, acc_cis @ [ci], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], gen_decls, node_decls_map) c in 
    let decl = A.ContractNodeDecl (p, (cname, ps, ips, ops, (p3, c))) in
    ctx, gids, decl :: acc_decls, gen_decls @ acc_gen_decls, node_decls_map
  | TypeDecl _ 
  | ConstDecl _ 
  | NodeParamInst _ -> ctx, gids, decl :: acc_decls, acc_gen_decls, acc_node_decls_map
  ) (ctx, gids, [], [], node_decls_map) decls in
  let decls = List.rev decls in
  ctx, gids, decls, gen_decls, node_decls_map 

let instantiate_polymorphic_nodes: Ctx.tc_context -> GI.t NI.Map.t -> A.declaration list -> Ctx.tc_context * GI.t NI.Map.t  * A.declaration list 
= fun ctx gids decls -> 
  (* Initialize node_decls_map (a map from a node name to its declaration and the list of its polymorphic instantiations 
     created so far) *)
  let node_decls_map = List.fold_left (fun acc decl -> match decl with 
  | (A.NodeDecl (_, (id, _, _, _, _, _, _, _, _)) as decl)
  | (FuncDecl (_, (id, _, _, _, _, _, _, _, _), _) as decl)
  | (ContractNodeDecl (_, (id, _, _, _, _)) as decl) -> NI.Map.add id (decl, []) acc
  | TypeDecl _ | ConstDecl _ | NodeParamInst _ -> acc
  ) NI.Map.empty decls 
  in

  let ctx, gids, decls, gen_decls, _ = gen_poly_decls_decls ctx gids node_decls_map decls in
  let merged_decls = merge_decls decls gen_decls in
  ctx, gids, merged_decls
