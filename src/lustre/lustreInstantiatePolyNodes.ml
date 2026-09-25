module A = LustreAst
module AH = LustreAstHelpers
module NI = NodeId
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module LH = LustreAstHelpers
module GI = GeneratedIdentifiers
module R = Res

let (let*) = R.(>>=)

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
  let inst e = Chk.instantiate_type_variables_expr ctx node_id ty_args e |> unwrap in
  (* The guard of a provided property is an expression of the node body too *)
  let k = match k with
    | A.Provided guard -> A.Provided (inst guard)
    | A.Invariant | A.Reachable _ -> k
  in
  AnnotProperty (pos, name, inst expr, k)
| AnnotMain _ -> ni
| Auto _ -> ni
| IfBlock _
| WhenBlock _
| MatchBlock _
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
| GhostVars (p, GhostVarDec (p2, tis), expr) ->
  let expr = Chk.instantiate_type_variables_expr ctx node_id ty_args expr |> unwrap in
  let tis = List.map (fun (p, id, ty) ->
    (p, id, Chk.instantiate_type_variables ctx p node_id ty ty_args |> unwrap)
  ) tis in
  GhostVars (p, GhostVarDec (p2, tis), expr)
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
  (* Print just the type name for records/ADTs (desugared forms), full form for others *)
  let pp_print_ty_arg ppf = function
    | A.RecordType (_, n, _) -> HString.pp_print_hstring ppf n
    | A.ADT (_, n, _) -> HString.pp_print_hstring ppf n
    | A.EnumType (_, n, _) -> HString.pp_print_hstring ppf n
    | ty -> A.pp_print_lustre_type ppf ty
  in
  let user_name = Format.asprintf
    "%a<%a>"
    HString.pp_print_hstring name
    (Lib.pp_print_list pp_print_ty_arg ";") ty_args |> HString.mk_hstring
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
  | ADT (p, id, cons) ->
    let ctx, gids, cons, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_cons, acc_decls, acc_node_decls_map) (cname, fields) ->
      let ctx, gids, fields, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_fields, acc_decls, acc_node_decls_map) (fname, ty) ->
        let ctx, gids, ty, decls, node_decls_map = gen_poly_decls_ty ctx gids node_id acc_node_decls_map ty in
        ctx, gids, acc_fields @ [(fname, ty)], decls @ acc_decls, node_decls_map
      ) (ctx, gids, [], acc_decls, acc_node_decls_map) fields in
      ctx, gids, acc_cons @ [(cname, fields)], decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) cons in
    ctx, gids, ADT (p, id, cons), decls, node_decls_map
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
  | A.Index (p, e, k) ->
    let ctx, gids, e, decls, ndm = re e in
    ctx, gids, A.Index (p, e, k), decls, ndm
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
  | Ident _ | Last _ | EmptyMap (_, None) | EmptySet (_, None)
  | Const _ | AbstractSymConst _
  | ModeRef _ -> ctx, gids, expr, [], node_decls_map
  | FieldProject (p, expr, id, pk) ->
    let ctx, gids, expr, decls, node_decls_map = rec_call expr in
    ctx, gids, FieldProject (p, expr, id, pk), decls, node_decls_map
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
  | Match (p, e, arms, ty_opt) ->
    let ctx, gids, e, decls1, node_decls_map = rec_call e in
    let ctx, gids, arms, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_arms, acc_decls, acc_node_decls_map) (pat, arm_e) ->
      let ctx, gids, arm_e, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map arm_e in
      ctx, gids, acc_arms @ [(pat, arm_e)], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], decls1, node_decls_map) arms in
    ctx, gids, Match (p, e, arms, ty_opt), decls, node_decls_map
  | ADTTerm (p, ty_args, ctor, args) ->
    let ctx, gids, args, decls, node_decls_map = List.fold_left (fun (ctx, gids, acc_args, acc_decls, acc_node_decls_map) arg ->
      let ctx, gids, arg, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname acc_node_decls_map arg in
      ctx, gids, acc_args @ [arg], decls @ acc_decls, node_decls_map
    ) (ctx, gids, [], [], node_decls_map) args in
    ctx, gids, ADTTerm (p, ty_args, ctor, args), decls, node_decls_map
  | ADTTester (p, e, c) ->
    let ctx, gids, e, decls, node_decls_map = gen_poly_decls_expr ctx gids caller_nname node_decls_map e in
    ctx, gids, ADTTester (p, e, c), decls, node_decls_map

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
  | MatchBlock _ -> assert false (* desugared in lustreDesugarMatchBlocks *)
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
    (* The guard of a provided property may call a polymorphic node too *)
    let ctx, gids, k, decls, node_decls_map = match k with
      | A.Provided guard ->
        let ctx, gids, guard, decls2, node_decls_map =
          gen_poly_decls_expr ctx gids node_id node_decls_map guard
        in
        ctx, gids, A.Provided guard, decls @ decls2, node_decls_map
      | A.Invariant | A.Reachable _ -> ctx, gids, k, decls, node_decls_map
    in
    ctx, gids, AnnotProperty (p, n, expr, k), decls, node_decls_map
  | AnnotMain _ -> ctx, gids, ni, [], node_decls_map
  | Auto _ -> ctx, gids, ni, [], node_decls_map

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

(* ---- ADT Type Monomorphization ---- *)

(* Canonical position-independent key for a (adt_name, ty_args) pair. *)
let adt_mono_key id ty_args =
  Format.asprintf "%a<%a>"
    HString.pp_print_hstring id
    (Lib.pp_print_list A.pp_print_lustre_type ";") ty_args

(* The name an instantiation's constructor is known by: names are global, so
   each instantiation qualifies its own, as the SMT-LIB symbols do *)
let mono_ctor_name mono_name ctor =
  HString.mk_hstring
    (Type.qualified_ctor_name
       (HString.string_of_hstring mono_name) (HString.string_of_hstring ctor))

let rec mentions_ty_var params ty =
  let r = mentions_ty_var params in
  match ty with
  | A.UserType (_, ty_args, id) -> List.mem id params || List.exists r ty_args
  | A.AbstractType (_, id) -> List.mem id params
  | A.RecordType (_, _, fields) -> List.exists (fun (_, _, ty) -> r ty) fields
  | A.ArrayType (_, (ty, _)) | A.Set (_, ty) -> r ty
  | A.TupleType (_, tys) | A.GroupType (_, tys) -> List.exists r tys
  | A.TArr (_, ty1, ty2) | A.Map (_, ty1, ty2) -> r ty1 || r ty2
  | A.RefinementType (_, (_, _, ty), _) -> r ty
  | A.ADT (_, _, ctors) ->
    List.exists (fun (_, fields) -> List.exists (fun (_, ty) -> r ty) fields) ctors
  | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _
  | A.EnumType _ | A.History _ -> false

(* Bind a datatype's type parameters by matching a type as the declaration wrote
   it against the form it takes once the type arguments are substituted in *)
let rec bind_ty_params ps acc declared instance =
  match declared, instance with
  | A.UserType (_, [], p), _ when List.mem p ps ->
    if List.mem_assoc p acc then acc else (p, instance) :: acc
  | A.UserType (_, ds, _), A.UserType (_, is, _)
    when List.length ds = List.length is ->
    List.fold_left2 (bind_ty_params ps) acc ds is
  | A.ArrayType (_, (d, _)), A.ArrayType (_, (i, _))
  | A.Set (_, d), A.Set (_, i)
  | A.RefinementType (_, (_, _, d), _), A.RefinementType (_, (_, _, i), _) ->
    bind_ty_params ps acc d i
  | A.Map (_, d1, d2), A.Map (_, i1, i2)
  | A.TArr (_, d1, d2), A.TArr (_, i1, i2) ->
    bind_ty_params ps (bind_ty_params ps acc d1 i1) d2 i2
  | A.TupleType (_, ds), A.TupleType (_, is)
  | A.GroupType (_, ds), A.GroupType (_, is) when List.length ds = List.length is ->
    List.fold_left2 (bind_ty_params ps) acc ds is
  | A.RecordType (_, _, dfs), A.RecordType (_, _, ifs)
    when List.length dfs = List.length ifs ->
    List.fold_left2 (fun acc (_, _, d) (_, _, i) -> bind_ty_params ps acc d i) acc dfs ifs
  | _ -> acc

(* The type arguments of the instantiation an expanded datatype stands for. Its
   own name is no guide: a field of the parameter type may be headed by it too. *)
let expanded_instance_args ctx id ctors =
  match Ctx.lookup_ty_ty_vars ctx id, Ctx.lookup_ty_syn ctx id [] with
  | Some (_ :: _ as ps), Some (A.ADT (_, _, declared)) ->
    let bindings =
      List.fold_left (fun acc (ctor, fields) ->
        match List.assoc_opt ctor declared with
        | Some dfields when List.length dfields = List.length fields ->
          List.fold_left2 (fun acc (_, d) (_, i) -> bind_ty_params ps acc d i)
            acc dfields fields
        | Some _ | None -> acc
      ) [] ctors
    in
    if List.for_all (fun p -> List.mem_assoc p bindings) ps
    then Some (List.map (fun p -> List.assoc p bindings) ps)
    else
      (* A parameter bound by no field cannot be recovered, and the declaration's
         own name stands for a different sort than the instantiation's *)
      invalid_arg
        (Format.asprintf "expanded_instance_args: unbound type parameters of %a"
           HString.pp_print_hstring id)
  (* A type with no parameters, or no datatype behind the name, is no
     instantiation to begin with *)
  | Some (_ :: _), _ | Some [], _ | None, _ -> None

(* The canonical form of a type argument: synonyms are expanded, so that two
   spellings name one instantiation; a refinement type is preserved *)
let rec canon_ty_arg ctx record ty =
  let r = canon_ty_arg ctx record in
  match ty with
  | A.UserType (pos, ty_args, id) ->
    let ty_args = List.map r ty_args in
    (match Ctx.lookup_ty_syn_body ctx id ty_args with
    | None -> A.UserType (pos, ty_args, id)
    | Some body -> canon_named_ty ctx record pos id ty_args body)
  | A.History (pos, id) ->
    (match Ctx.lookup_ty ctx id with Some ty -> r ty | None -> A.History (pos, id))
  | A.RefinementType (pos, (p, i, ty), e) -> A.RefinementType (pos, (p, i, r ty), e)
  | A.ArrayType (pos, (ty, e)) -> A.ArrayType (pos, (r ty, e))
  | A.Set (pos, ty) -> A.Set (pos, r ty)
  | A.Map (pos, ty1, ty2) -> A.Map (pos, r ty1, r ty2)
  | A.TArr (pos, ty1, ty2) -> A.TArr (pos, r ty1, r ty2)
  | A.TupleType (pos, tys) -> A.TupleType (pos, List.map r tys)
  | A.GroupType (pos, tys) -> A.GroupType (pos, List.map r tys)
  | A.RecordType (pos, id, fields) ->
    A.RecordType (pos, id, List.map (fun (p, i, ty) -> (p, i, r ty)) fields)
  (* An enumeration and a datatype are always declared under the name they
     carry, so the name is the canonical spelling of them *)
  | A.EnumType (pos, id, _) -> A.UserType (pos, [], id)
  | A.ADT (pos, id, ctors) ->
    (match expanded_instance_args ctx id ctors with
    | None -> A.UserType (pos, [], id)
    | Some ty_args -> r (A.UserType (pos, ty_args, id)))
  | A.AbstractType _ | A.Bool _ | A.Int _ | A.Real _
  | A.SBitVector _ | A.UBitVector _ -> ty

(* The canonical form of a named type with the given definition: an
   instantiation, the name of a datatype or an enumeration, or the expansion of
   a synonym that is none of those *)
and canon_named_ty ctx record pos id ty_args body =
  match resolve_instance ctx record pos id ty_args with
  | Some mono_name -> A.UserType (pos, [], mono_name)
  | None ->
    match body with
    | A.ADT _ | A.EnumType _ -> A.UserType (pos, [], id)
    | A.RecordType _ | A.ArrayType _ | A.Set _ | A.Map _ | A.TupleType _
    | A.GroupType _ | A.TArr _ -> A.UserType (pos, ty_args, id)
    | A.UserType _ | A.RefinementType _ | A.History _ | A.AbstractType _
    | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _ ->
      canon_ty_arg ctx record body

(* The name the instantiation a named type resolves to is declared under.
   Resolving reports it, so the name cannot be had without a declaration to
   match. A datatype is named by its own declaration however many synonyms alias
   it; every other synonym is an instantiation of itself. *)
and resolve_instance ctx record pos id ty_args =
  let instance base =
    if ty_args = [] then None
    else
      let ty_args = List.map (canon_ty_arg ctx record) ty_args in
      let mono_name = HString.mk_hstring (adt_mono_key base ty_args) in
      record pos base ty_args mono_name;
      Some mono_name
  in
  match Ctx.lookup_ty_syn_body ctx id ty_args with
  | Some (A.ADT (_, base, _)) -> instance base
  | Some (A.UserType (_, ty_args', id')) ->
    resolve_instance ctx record pos id' ty_args'
  | Some (A.RefinementType _ | A.History _ | A.RecordType _ | A.ArrayType _
         | A.Set _ | A.Map _ | A.TupleType _ | A.GroupType _ | A.TArr _) ->
    instance id
  | Some (A.AbstractType _ | A.EnumType _ | A.Bool _ | A.Int _ | A.Real _
         | A.SBitVector _ | A.UBitVector _)
  | None -> None

(* ---- Rewriting a use of a polymorphic ADT to name its instantiation ---- *)

(* The functions below rewrite every use of a polymorphic ADT to the declaration
   it stands for and report it, so a use cannot be rewritten without one. Each
   site rewrites its type arguments before resolving itself, since resolving
   discards them and an argument may name the only use of an instantiation. *)

let rec rewrite_ty ctx record params ty =
  let r = rewrite_ty ctx record params in
  match ty with
  | A.UserType (pos, ty_args, id) ->
    let ty_args' = List.map r ty_args in
    if ty_args = [] || List.exists (mentions_ty_var params) ty_args then
      A.UserType (pos, ty_args', id)
    else (
      match resolve_instance ctx record pos id ty_args with
      | Some mono_name -> A.UserType (pos, [], mono_name)
      | None -> A.UserType (pos, ty_args', id))
  | A.RefinementType (pos, (p, i, ty), e) ->
    A.RefinementType (pos, (p, i, r ty), rewrite_expr ctx record params e)
  | A.ArrayType (pos, (ty, e)) ->
    A.ArrayType (pos, (r ty, rewrite_expr ctx record params e))
  | A.Set (pos, ty) -> A.Set (pos, r ty)
  | A.Map (pos, ty1, ty2) -> A.Map (pos, r ty1, r ty2)
  | A.TArr (pos, ty1, ty2) -> A.TArr (pos, r ty1, r ty2)
  | A.TupleType (pos, tys) -> A.TupleType (pos, List.map r tys)
  | A.GroupType (pos, tys) -> A.GroupType (pos, List.map r tys)
  | A.RecordType (pos, id, fields) ->
    A.RecordType (pos, id, List.map (fun (p, i, ty) -> (p, i, r ty)) fields)
  | A.ADT (pos, id, ctors) ->
    let over_fields () =
      A.ADT (pos, id,
        List.map (fun (c, fields) ->
          (c, List.map (fun (f, ty) -> (f, r ty)) fields)) ctors)
    in
    (* An expanded instantiation names its instantiation like any other use of it *)
    (match expanded_instance_args ctx id ctors with
    | Some ty_args when not (List.exists (mentions_ty_var params) ty_args) ->
      let expanded = over_fields () in
      (match resolve_instance ctx record pos id ty_args with
      | Some mono_name -> A.UserType (pos, [], mono_name)
      | None -> expanded)
    | Some _ | None -> over_fields ())
  | A.AbstractType _ | A.EnumType _ | A.History _ | A.Bool _ | A.Int _
  | A.Real _ | A.SBitVector _ | A.UBitVector _ -> ty

and rewrite_expr ctx record params expr =
  let r = rewrite_expr ctx record params in
  let rt = rewrite_ty ctx record params in
  match expr with
  | A.ADTTerm (pos, ty_args, ctor, args) ->
    let args = List.map r args in
    let ty_args' = List.map rt ty_args in
    let unresolved () = A.ADTTerm (pos, ty_args', ctor, args) in
    if List.exists (mentions_ty_var params) ty_args then unresolved ()
    else (
      (* A constructor with no ADT left belongs to a non-recursive one,
         desugared away before this pass *)
      match Ctx.lookup_constructor ctx ctor with
      | None -> unresolved ()
      | Some (ty_name, _) ->
        match resolve_instance ctx record pos ty_name ty_args with
        | Some mono_name ->
          A.ADTTerm (pos, [], mono_ctor_name mono_name ctor, args)
        | None -> unresolved ())
  | A.TypeAscription (pos, e, ty) -> A.TypeAscription (pos, r e, rt ty)
  | A.Quantifier (pos, q, tis, e) ->
    A.Quantifier (pos, q, List.map (fun (p, i, ty) -> (p, i, rt ty)) tis, r e)
  | A.AnyOp _ | A.ChooseOp _ -> assert false (* desugared in lustreDesugarAnyChooseOps *)
  (* A record expression names its record type, which for a polymorphic one is
     the instantiation whose value it builds *)
  | A.RecordExpr (pos, id, ty_args, flds) ->
    let flds = List.map (fun (f, e) -> (f, r e)) flds in
    let ty_args' = List.map rt ty_args in
    let unresolved () = A.RecordExpr (pos, id, ty_args', flds) in
    if List.exists (mentions_ty_var params) ty_args then unresolved ()
    else (
      match resolve_instance ctx record pos id ty_args with
      | Some mono_name -> A.RecordExpr (pos, mono_name, [], flds)
      | None -> unresolved ())
  | A.Call (pos, ty_args, id, args) ->
    A.Call (pos, List.map rt ty_args, id, List.map r args)
  | A.EmptyMap (pos, Some (kt, vt)) -> A.EmptyMap (pos, Some (rt kt, rt vt))
  | A.EmptySet (pos, Some ty) -> A.EmptySet (pos, Some (rt ty))
  | A.AbstractSymConst (pos, ty) -> A.AbstractSymConst (pos, rt ty)
  | A.EmptyMap (_, None) | A.EmptySet (_, None)
  | A.Ident _ | A.ModeRef _ | A.Const _ | A.Last _ -> expr
  (* A selector's type annotation names the ADT it was declared in, which is how
     lustreNodeGen.ml finds the declaring constructor *)
  | A.FieldProject (pos, e, f, pk) -> A.FieldProject (pos, r e, f, pk)
  | A.ADTTester (pos, e, ctor) -> A.ADTTester (pos, r e, ctor)
  | A.UnaryOp (pos, op, e) -> A.UnaryOp (pos, op, r e)
  | A.ConvOp (pos, op, e) -> A.ConvOp (pos, op, r e)
  | A.Pre (pos, e) -> A.Pre (pos, r e)
  | A.When (pos, e, c) -> A.When (pos, r e, c)
  | A.Extract (pos, e, i1, i2) -> A.Extract (pos, r e, i1, i2)
  | A.BinaryOp (pos, op, e1, e2) -> A.BinaryOp (pos, op, r e1, r e2)
  | A.CompOp (pos, op, e1, e2) -> A.CompOp (pos, op, r e1, r e2)
  | A.Arrow (pos, e1, e2) -> A.Arrow (pos, r e1, r e2)
  | A.ArrayConstr (pos, e1, e2) -> A.ArrayConstr (pos, r e1, r e2)
  | A.IndexAccess (pos, e1, e2, k) -> A.IndexAccess (pos, r e1, r e2, k)
  | A.StructUpdate (pos, e1, idx, e2) ->
    let over_idx = function
      | A.Label _ as l -> l
      | A.Index (p, e, k) -> A.Index (p, r e, k)
      | A.MapIndex (p, e) -> A.MapIndex (p, r e)
      | A.SetIndex (p, e) -> A.SetIndex (p, r e)
      | A.GenericIndex (p, e) -> A.GenericIndex (p, r e)
    in
    A.StructUpdate (pos, r e1, List.map over_idx idx, Option.map r e2)
  | A.TernaryOp (pos, op, e1, e2, e3) -> A.TernaryOp (pos, op, r e1, r e2, r e3)
  | A.GroupExpr (pos, k, es) -> A.GroupExpr (pos, k, List.map r es)
  | A.Condact (pos, c, e, id, args, defaults) ->
    A.Condact (pos, r c, r e, id, List.map r args, List.map r defaults)
  | A.Activate (pos, id, c, e, args) ->
    A.Activate (pos, id, r c, r e, List.map r args)
  | A.Merge (pos, c, arms) -> A.Merge (pos, c, List.map (fun (i, e) -> (i, r e)) arms)
  | A.RestartEvery (pos, id, args, e) ->
    A.RestartEvery (pos, id, List.map r args, r e)
  | A.Match _ -> assert false (* desugared in lustreDesugarADTs *)

let rewrite_const_decl ctx record params = function
  | A.FreeConst (pos, id, ty) ->
    A.FreeConst (pos, id, rewrite_ty ctx record params ty)
  | A.TypedConst (pos, id, e, ty) ->
    A.TypedConst (pos, id, rewrite_expr ctx record params e,
                  rewrite_ty ctx record params ty)
  | A.UntypedConst (pos, id, e) ->
    A.UntypedConst (pos, id, rewrite_expr ctx record params e)

let rewrite_local_decl ctx record params = function
  | A.NodeConstDecl (pos, cd) ->
    A.NodeConstDecl (pos, rewrite_const_decl ctx record params cd)
  | A.NodeVarDecl (pos, (p, id, ty, cl)) ->
    A.NodeVarDecl (pos, (p, id, rewrite_ty ctx record params ty, cl))

let rewrite_node_item ctx record params item =
  let re = rewrite_expr ctx record params in
  match item with
  | A.Body (Equation (pos, lhs, e)) -> A.Body (Equation (pos, lhs, re e))
  | A.Body (Assert (pos, e)) -> A.Body (Assert (pos, re e))
  (* The guard of a provided property is an expression of the node body too *)
  | A.AnnotProperty (pos, id, e, k) ->
    let k = match k with
      | A.Provided guard -> A.Provided (re guard)
      | A.Invariant | A.Reachable _ -> k
    in
    A.AnnotProperty (pos, id, re e, k)
  | A.AnnotMain _ | A.Auto _ -> item
  | A.IfBlock _ | A.WhenBlock _ | A.MatchBlock _ | A.FrameBlock _ ->
    assert false (* desugared before polymorphic instantiation *)

let rewrite_contract_item ctx record params ci =
  let re = rewrite_expr ctx record params in
  let rt = rewrite_ty ctx record params in
  match ci with
  | A.GhostConst cd -> A.GhostConst (rewrite_const_decl ctx record params cd)
  | A.GhostVars (pos, A.GhostVarDec (p, tis), e) ->
    A.GhostVars (pos, A.GhostVarDec (p, List.map (fun (p, i, ty) -> (p, i, rt ty)) tis), re e)
  | A.Assume (pos, id, s, e) -> A.Assume (pos, id, s, re e)
  | A.Guarantee (pos, id, s, e) -> A.Guarantee (pos, id, s, re e)
  | A.Decreases (pos, e) -> A.Decreases (pos, re e)
  | A.Mode (pos, id, reqs, enss) ->
    A.Mode (pos, id,
      List.map (fun (p, i, e) -> (p, i, re e)) reqs,
      List.map (fun (p, i, e) -> (p, i, re e)) enss)
  | A.ContractCall (pos, id, ty_args, args, outs) ->
    A.ContractCall (pos, id, List.map rt ty_args, List.map re args, outs)
  | A.AssumptionVars _ -> ci

(* Only a datatype's own type parameters stand outside the instantiations of it;
   a node's are opaque types, and it is analyzed over those instantiations *)
let rewrite_decl ctx record decl =
  let params = match decl with
    | A.TypeDecl (_, AliasType (_, _, ps, _)) -> ps
    | A.TypeDecl (_, FreeType _) | A.NodeDecl _ | A.FuncDecl _
    | A.ContractNodeDecl _ | A.ConstDecl _ | A.NodeParamInst _ -> []
  in
  let rt = rewrite_ty ctx record params in
  let over_ips = List.map (fun (p, i, ty, cl, c) -> (p, i, rt ty, cl, c)) in
  let over_ops = List.map (fun (p, i, ty, cl) -> (p, i, rt ty, cl)) in
  let over_locals = List.map (rewrite_local_decl ctx record params) in
  let over_items = List.map (rewrite_node_item ctx record params) in
  let over_contract (p, cis) =
    (p, List.map (rewrite_contract_item ctx record params) cis)
  in
  match decl with
  | A.NodeDecl (sp, (id, ext, opac, ps, ips, ops, locals, items, contract)) ->
    A.NodeDecl (sp, (id, ext, opac, ps, over_ips ips, over_ops ops,
                     over_locals locals, over_items items,
                     Option.map over_contract contract))
  | A.FuncDecl (sp, (id, ext, opac, ps, ips, ops, locals, items, contract), attrs) ->
    A.FuncDecl (sp, (id, ext, opac, ps, over_ips ips, over_ops ops,
                     over_locals locals, over_items items,
                     Option.map over_contract contract), attrs)
  | A.ContractNodeDecl (sp, (id, ps, ips, ops, contract)) ->
    A.ContractNodeDecl (sp, (id, ps, over_ips ips, over_ops ops,
                             over_contract contract))
  | A.ConstDecl (sp, cd) -> A.ConstDecl (sp, rewrite_const_decl ctx record params cd)
  | A.TypeDecl (sp, AliasType (pos, id, ps, ty)) ->
    A.TypeDecl (sp, AliasType (pos, id, ps, rt ty))
  | A.TypeDecl (_, FreeType _) | A.NodeParamInst _ -> decl

(* The generated identifiers of a node carry types and expressions of their own,
   and are compiled alongside the node's. The fields below are every one written
   before this pass; a pass moved ahead of it would have to be added here. *)
let rewrite_gids ctx record gids =
  NI.Map.map (fun (gids : GI.t) ->
    let rt = rewrite_ty ctx record [] in
    let re = rewrite_expr ctx record [] in
    { gids with
      GI.node_args = List.map (fun (id, c, ty, e) -> (id, c, rt ty, re e)) gids.GI.node_args;
      GI.locals = GI.StringMap.map rt gids.GI.locals;
      GI.free_constants = List.map (fun (id, ty) -> (id, rt ty)) gids.GI.free_constants;
      GI.oracles = List.map (fun (id, ty, e) -> (id, rt ty, re e)) gids.GI.oracles;
      GI.ib_oracles = List.map (fun (id, ty) -> (id, rt ty)) gids.GI.ib_oracles;
      GI.empty_sets = List.map (fun (id, ty) -> (id, rt ty)) gids.GI.empty_sets;
      GI.empty_maps = List.map (fun (id, kt, vt) -> (id, rt kt, rt vt)) gids.GI.empty_maps;
      GI.equations =
        List.map (fun (tis, scope, lhs, e, src) ->
          (List.map (fun (p, i, ty) -> (p, i, rt ty)) tis, scope, lhs, re e, src)
        ) gids.GI.equations }
  ) gids

(* ---- Declaring the instantiations a program uses ---- *)

(* A monomorphic declaration to generate: a use that needs it, the type it is
   declared as, and the types it must be declared after *)
type instance = {
  use_pos : Lib.position;
  ty_args : A.lustre_type list;
  body : A.lustre_type;
  refs : HString.t list;
}

(* Type names a type mentions, not looking inside a datatype's constructors *)
let rec type_names_in_ty acc ty =
  match ty with
  | A.UserType (_, ty_args, id) -> List.fold_left type_names_in_ty (id :: acc) ty_args
  | A.AbstractType (_, id) | A.EnumType (_, id, _) | A.History (_, id)
  | A.ADT (_, id, _) -> id :: acc
  | A.RecordType (_, _, fields) ->
    List.fold_left (fun acc (_, _, ty) -> type_names_in_ty acc ty) acc fields
  | A.ArrayType (_, (ty, _)) | A.Set (_, ty)
  | A.RefinementType (_, (_, _, ty), _) -> type_names_in_ty acc ty
  | A.Map (_, ty1, ty2) | A.TArr (_, ty1, ty2) ->
    type_names_in_ty (type_names_in_ty acc ty1) ty2
  | A.TupleType (_, tys) | A.GroupType (_, tys) ->
    List.fold_left type_names_in_ty acc tys
  | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _ -> acc

(* Type names an instantiation's definition mentions, which its declaration must
   follow. A datatype's own name says nothing; its constructor fields do. *)
let instance_refs body =
  match body with
  | A.ADT (_, _, ctors) ->
    List.concat_map (fun (_, fields) ->
      List.concat_map (fun (_, ty) -> type_names_in_ty [] ty) fields) ctors
  | A.UserType _ | A.AbstractType _ | A.TupleType _ | A.GroupType _
  | A.RecordType _ | A.ArrayType _ | A.EnumType _ | A.RefinementType _
  | A.History _ | A.TArr _ | A.Set _ | A.Map _ | A.Bool _ | A.Int _
  | A.Real _ | A.SBitVector _ | A.UBitVector _ -> type_names_in_ty [] body

(* True iff a type is compiled to a single value, as a datatype's field must be.
   A datatype is scalar only when recursive: a non-recursive one becomes a record. *)
let rec is_scalar_field_type ctx ty =
  match ty with
  | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _
  | A.EnumType _ | A.AbstractType _ -> true
  | A.ADT (_, name, ctors) -> LH.is_directly_recursive_adt name ctors
  | A.RefinementType (_, (_, _, ty), _) -> is_scalar_field_type ctx ty
  | A.UserType (_, ty_args, id) ->
    (* A type parameter reaches here as an abstract type, so a name that does not
       resolve is an instantiation this pass failed to declare *)
    (match Ctx.lookup_ty_syn ctx id ty_args with
    | Some ty -> is_scalar_field_type ctx ty
    | None ->
      invalid_arg
        (Format.asprintf "is_scalar_field_type: undeclared type %a"
           A.pp_print_lustre_type ty))
  | A.TupleType _ | A.GroupType _ | A.RecordType _ | A.ArrayType _
  | A.Set _ | A.Map _ | A.TArr _ | A.History _ -> false

(* True iff a type is or contains a refinement type. A datatype is not looked
   inside: a refinement on its own fields is rejected where it is declared. *)
let rec has_refinement ctx ty =
  let r = has_refinement ctx in
  match ty with
  | A.RefinementType _ -> true
  | A.UserType (_, ty_args, id) ->
    (match Ctx.lookup_ty_syn_body ctx id ty_args with
    | Some (A.ADT _) | None -> false
    | Some body -> r body)
  | A.ArrayType (_, (ty, _)) | A.Set (_, ty) -> r ty
  | A.Map (_, ty1, ty2) | A.TArr (_, ty1, ty2) -> r ty1 || r ty2
  | A.TupleType (_, tys) | A.GroupType (_, tys) -> List.exists r tys
  | A.RecordType (_, _, fields) -> List.exists (fun (_, _, ty) -> r ty) fields
  | A.ADT _ | A.AbstractType _ | A.EnumType _ | A.History _ | A.Bool _
  | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _ -> false

(* A recursive datatype's restrictions are checked where it is declared, but a
   type parameter only becomes concrete here *)
let check_instantiation ctx mono_name inst =
  let fields = match inst.body with
    | A.ADT (_, _, ctors) ->
      List.concat_map (fun (_, fields) ->
        List.filter (fun (_, ty) -> not (LH.is_direct_self_reference mono_name ty)) fields
      ) ctors
    | A.UserType _ | A.AbstractType _ | A.TupleType _ | A.GroupType _
    | A.RecordType _ | A.ArrayType _ | A.EnumType _ | A.RefinementType _
    | A.History _ | A.TArr _ | A.Set _ | A.Map _ | A.Bool _ | A.Int _
    | A.Real _ | A.SBitVector _ | A.UBitVector _ -> []
  in
  match List.find_opt (fun (_, ty) -> not (is_scalar_field_type ctx ty)) fields with
  | Some (fname, _) ->
    Chk.type_error inst.use_pos
      (Chk.UnsupportedRecursiveAdtField (mono_name, fname))
  | None ->
    match List.find_opt (fun (_, ty) -> has_refinement ctx ty) fields with
    | Some (fname, _) ->
      Chk.type_error inst.use_pos
        (Chk.UnsupportedRefinementInRecursiveAdtField (mono_name, fname))
    | None ->
      (* A refinement is erased when two types are compared, so an argument
         carrying one would let values cross between two distinct datatypes *)
      match inst.body with
      | A.ADT _ when List.exists (has_refinement ctx) inst.ty_args ->
        Chk.type_error inst.use_pos
          (Chk.UnsupportedRefinementInRecursiveAdtInstantiation mono_name)
      | A.ADT _ | A.UserType _ | A.AbstractType _ | A.TupleType _
      | A.GroupType _ | A.RecordType _ | A.ArrayType _ | A.EnumType _
      | A.RefinementType _ | A.History _ | A.TArr _ | A.Set _ | A.Map _
      | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _ ->
        R.ok ()

(* The datatypes a declared name reaches, when it names a datatype that is not an
   instantiation. Those are declared once, so a cycle through one of them still
   needs the joint declaration a cycle between instantiations would. *)
let datatype_refs ctx name =
  match Ctx.lookup_ty_syn ctx name [] with
  | Some (A.ADT (_, _, ctors)) -> instance_refs (A.ADT (Lib.dummy_pos, name, ctors))
  | Some _ | None -> []

(* The instantiations to declare, a field's before the type that embeds it. Each
   is declared on its own, so a cycle through two of them has no such order. *)
let sort_instances ctx instances =
  (* A name outside [instances] is not declared here, so it takes no place in
     the order; it is followed only to see whether a cycle comes back *)
  let rec visit path acc name =
    if List.mem_assoc name instances && List.mem name acc then R.ok acc
    else if List.mem name path then
      match List.find_opt (fun n -> List.mem_assoc n instances) (name :: path) with
      | None -> R.ok acc
      | Some instance_on_cycle ->
        let inst = List.assoc instance_on_cycle instances in
        let other = if HString.equal name instance_on_cycle then List.hd path else name in
        Chk.type_error inst.use_pos
          (Chk.MutuallyRecursiveDatatypes (instance_on_cycle, other))
    else
      let deps, declared_here = match List.assoc_opt name instances with
        | Some inst -> inst.refs, true
        | None -> datatype_refs ctx name, false
      in
      let deps = List.filter (fun n -> not (HString.equal n name)) deps in
      let* acc = R.seq_chain (visit (name :: path)) acc deps in
      R.ok (if declared_here then acc @ [name] else acc)
  in
  R.seq_chain (visit []) [] (List.map fst instances)

(* Insert each monomorphic declaration after the last declaration it depends on,
   so the instantiations must arrive in dependency order. One that depends on
   nothing declared here is prepended, ahead of every node declaration. *)
let insert_mono_type_decls decls instances =
  let idx_of_name =
    List.mapi (fun i d -> (i, d)) decls
    |> List.filter_map (fun (i, d) -> match d with
       | A.TypeDecl (_, A.AliasType (_, n, _, _))
       | A.TypeDecl (_, A.FreeType (_, n)) -> Some (n, i)
       | A.NodeDecl _ | A.FuncDecl _ | A.ContractNodeDecl _ | A.ConstDecl _
       | A.NodeParamInst _ -> None)
  in
  let placed =
    List.fold_left (fun (anchors, placed) (mono_name, inst, decl) ->
      let anchor =
        List.fold_left (fun acc n ->
          match List.assoc_opt n idx_of_name, List.assoc_opt n anchors with
          | Some i, _ | None, Some i -> max acc i
          | None, None -> acc
        ) (-1) inst.refs
      in
      ((mono_name, anchor) :: anchors, placed @ [(anchor, decl)])
    ) ([], []) instances
    |> snd
  in
  let after i = List.filter (fun (j, _) -> j = i) placed |> List.map snd in
  after (-1) @ List.concat (List.mapi (fun i d -> d :: after i) decls)

let instantiate_polymorphic_adts ctx gids type_decls decls =
  let pos = Lib.dummy_pos in
  let span = { A.start_pos = pos; A.end_pos = pos } in
  (* The instantiations the program uses, in the order they were met *)
  let pending = ref [] in
  let record use_pos base ty_args mono_name =
    if not (List.mem_assoc mono_name !pending) then
      pending := !pending @ [(mono_name, (base, ty_args, use_pos))]
  in
  (* The typing context types the program, so it is rewritten along with it; the
     original keeps resolving names as they were written *)
  let out_ctx =
    Ctx.map_types
      ~in_definition:(fun ps -> rewrite_ty ctx record ps)
      ~in_use:(rewrite_ty ctx record []) ctx
  in
  let type_decls = List.map (rewrite_decl ctx record) type_decls in
  let decls = List.map (rewrite_decl ctx record) decls in
  let gids = rewrite_gids ctx record gids in
  (* An instantiation's definition may name instantiations found nowhere else, so
     rewriting it adds to the list while the list is walked *)
  let rec close i acc =
    if i >= List.length !pending then List.rev acc
    else
      let mono_name, (base, ty_args, use_pos) = List.nth !pending i in
      let body = match Ctx.lookup_ty_syn_body ctx base ty_args with
        | Some body -> body
        | None -> assert false
      in
      (* A datatype is declared under the instantiation's name, and its
         constructors after it, so that a use of one names the instantiation *)
      let body = match body with
        | A.ADT (p, _, ctors) ->
          A.ADT (p, mono_name,
            List.map (fun (ctor, fields) ->
              (mono_ctor_name mono_name ctor,
               List.map (fun (f, ty) -> (f, rewrite_ty ctx record [] ty)) fields)) ctors)
        | body -> rewrite_ty ctx record [] body
      in
      let refs = base :: instance_refs body in
      close (i + 1) ((mono_name, { use_pos; ty_args; body; refs }) :: acc)
  in
  let instances = close 0 [] in
  if instances = [] then R.ok (out_ctx, gids, type_decls, decls)
  else
    (* An instantiation is a type of its own from here on: its name is declared,
       stands for its definition, and owns the constructors of its datatype.
       Declaring them before the checks below is what lets those resolve a field
       whose type is another instantiation. *)
    let out_ctx =
      List.fold_left (fun ctx (mono_name, inst) ->
        let ctx = Ctx.add_ty_decl ctx mono_name in
        let ctx = Ctx.add_ty_syn ctx mono_name inst.body in
        match inst.body with
        | A.ADT (_, _, ctors) ->
          List.fold_left (fun ctx (ctor, fields) ->
            Ctx.add_adt_ctor ctx ctor mono_name (List.map snd fields)
          ) ctx ctors
        | A.UserType _ | A.AbstractType _ | A.TupleType _ | A.GroupType _
        | A.RecordType _ | A.ArrayType _ | A.EnumType _ | A.RefinementType _
        | A.History _ | A.TArr _ | A.Set _ | A.Map _ | A.Bool _ | A.Int _
        | A.Real _ | A.SBitVector _ | A.UBitVector _ -> ctx
      ) out_ctx instances
    in
    let* () =
      R.seq_ (List.map (fun (mono_name, inst) ->
        check_instantiation out_ctx mono_name inst) instances)
    in
    let* order = sort_instances out_ctx instances in
    let insertions =
      List.map (fun mono_name ->
        let inst = List.assoc mono_name instances in
        (mono_name, inst,
         A.TypeDecl (span, A.AliasType (pos, mono_name, [], inst.body)))
      ) order
    in
    let type_decls = insert_mono_type_decls type_decls insertions in
    R.ok (out_ctx, gids, type_decls, decls)

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
