
module TS = TransSys
module SMT  : SolverDriver.S = GenericSMTLIBDriver

module SyMap = UfSymbol.UfSymbolMap
module SySet = UfSymbol.UfSymbolSet
module ScMap = Scope.Map
module ScSet = Scope.Set

module Position = struct
  type t = Lib.position
  let compare = Lib.compare_pos
end
module PosMap = Map.Make(Position)

module A = LustreAst
module AstID = struct
  type t = A.ident
  let compare = compare
end
module IdMap = Map.Make(AstID)

type term_cat = NodeCall of Symbol.t * StateVar.t list
| ContractItem of StateVar.t
| Equation of StateVar.t
| Assertion
| Unknown

type equation = {
    opened: Term.t ;
    closed: Term.t ;
  }

type loc = {
  pos: Lib.position ;
  index: LustreIndex.index ;
}

type ivc = (equation * (loc list) * term_cat) list ScMap.t

type ivc_result = {
  success: bool;
  init: ivc;
  trans: ivc;
}

(* TODO: solve mapping issue with minimized.lus (= minimized test.lus) *)

(* ---------- LUSTRE AST ---------- *)

let counter =
  let last = ref 0 in
  (fun () -> last := !last + 1 ; !last)

let dpos = Lib.dummy_pos
let rand_fun_ident nb = "__rand"^(string_of_int nb)
let new_rand_fun_ident () = rand_fun_ident (counter ())

let max_nb_args = ref 0
let rand_functions = Hashtbl.create 10
let previous_rands = Hashtbl.create 10

let rand_function_name_for _ ts =
  begin
  try Hashtbl.find rand_functions ts
  with Not_found ->
    let new_rand = new_rand_fun_ident () in
    Hashtbl.replace rand_functions ts new_rand ;
    new_rand
  end

let undef_expr pos_sv_map typ expr =
  let pos = A.pos_of_expr expr in
  match pos_sv_map with
  | None -> A.Ident (pos, "_")
  | Some pos_sv_map ->
    let svs = try PosMap.find pos pos_sv_map with Not_found -> [] in
    if svs = []
    then begin
      let i = counter () in
      let n = (List.length typ) in
      if n > !max_nb_args then max_nb_args := n ;
      A.Call(*Param*) (pos, rand_function_name_for n typ, (*typ,*) [Num (dpos, string_of_int i)])
    end else begin
      try Hashtbl.find previous_rands svs
      with Not_found ->
        let i = counter () in
        let n = (List.length typ) in
        if n > !max_nb_args then max_nb_args := n ;
        let res =
          A.Call(*Param*) (pos, rand_function_name_for n typ, (*typ,*) [Num (dpos, string_of_int i)])
        in Hashtbl.replace previous_rands svs res ; res
    end

let parametric_rand_node nb_outputs =
  let rec aux prefix acc nb =
    match nb with
    | 0 -> acc
    | n -> aux prefix ((prefix^(string_of_int (counter ())))::acc) (n-1)
  in
  let ts = aux "t" [] nb_outputs in
  let outs = aux "out" [] nb_outputs
  |> List.map2 (fun t out ->
    dpos,out,A.UserType (dpos, t),A.ClockTrue) ts
  in
  let ts = List.map (fun str -> A.TypeParam str) ts in
  A.NodeDecl (dpos,
    (rand_fun_ident nb_outputs, true, ts, [dpos,"id",A.Int dpos,A.ClockTrue, false],
    outs, [], [], None)
  )

let rand_node name ts =
  let rec aux prefix acc nb =
    match nb with
    | 0 -> acc
    | n -> aux prefix ((prefix^(string_of_int (counter ())))::acc) (n-1)
  in
  let outs = aux "out" [] (List.length ts)
  |> List.map2 (fun t out -> dpos,out,t,A.ClockTrue) ts
  in
  A.NodeDecl (dpos,
    (name, true, [], [dpos,"id",A.Int dpos,A.ClockTrue, false],
    outs, [], [], None)
  )

let nodes_input_types = Hashtbl.create 10
let rec minimize_node_call_args ue lst expr =
  let minimize_arg ident i arg =
    match arg with
    | A.Ident _ -> arg
    | _ ->
      let t = Hashtbl.find nodes_input_types ident |> (fun lst -> List.nth lst i) in
      let (_, expr) = minimize_expr ue lst [t] arg in
      expr
  in
  let rec aux expr =
    match expr with
    | A.True _ | A.False _ | A.Ident _ | A.ModeRef _ | A.Num _ | A.Dec _ | A.Last _
    -> expr
    | A.Call (pos, ident, args) ->
      A.Call (pos, ident, List.mapi (minimize_arg ident) args)
    | A.CallParam (pos, ident, ts, args) ->
      A.CallParam (pos, ident, ts, List.mapi (minimize_arg ident) args)
    | A.RecordProject (p,e,i) -> A.RecordProject (p,aux e,i)
    | A.TupleProject (p,e1,e2) -> A.TupleProject (p,aux e1,aux e2)
    | A.StructUpdate (p,e1,ls,e2) -> A.StructUpdate (p,aux e1,ls,aux e2)
    | A.ToInt (p,e) -> A.ToInt (p,aux e)
    | A.ToUInt8 (p,e) -> A.ToUInt8 (p,aux e)
    | A.ToUInt16 (p,e) -> A.ToUInt16 (p,aux e)
    | A.ToUInt32 (p,e) -> A.ToUInt32 (p,aux e)
    | A.ToUInt64 (p,e) -> A.ToUInt64 (p,aux e)
    | A.ToInt8 (p,e) -> A.ToInt8 (p,aux e)
    | A.ToInt16 (p,e) -> A.ToInt16 (p,aux e)
    | A.ToInt32 (p,e) -> A.ToInt32 (p,aux e)
    | A.ToInt64 (p,e) -> A.ToInt64 (p,aux e)
    | A.ToReal (p,e) -> A.ToReal (p,aux e)
    | A.ExprList (p,es) -> A.ExprList (p,List.map aux es)
    | A.TupleExpr (p,es) -> A.TupleExpr (p,List.map aux es)
    | A.ArrayExpr (p,es) -> A.ArrayExpr (p,List.map aux es)
    | A.ArrayConstr (p,e1,e2) -> A.ArrayConstr (p,aux e1,aux e2)
    | A.ArraySlice (p,e1,(e2,e3)) -> A.ArraySlice (p,aux e1,(aux e2,aux e3))
    | A.ArrayConcat (p,e1,e2) -> A.ArrayConcat (p,aux e1,aux e2)
    | A.RecordExpr (p,id,lst) ->
      A.RecordExpr (p,id,List.map (fun (i,e) -> (i, aux e)) lst)
    | A.Not (p,e) -> A.Not (p,aux e)
    | A.And (p,e1,e2) -> A.And (p,aux e1,aux e2)
    | A.Or (p,e1,e2) -> A.Or (p,aux e1,aux e2)
    | A.Xor (p,e1,e2) -> A.Xor (p,aux e1,aux e2)
    | A.Impl (p,e1,e2) -> A.Impl (p,aux e1,aux e2)
    | A.Forall (p,ids,e) -> A.Forall (p,ids,aux e)
    | A.Exists (p,ids,e) -> A.Exists (p,ids,aux e)
    | A.OneHot (p,es) -> A.OneHot (p,List.map aux es)
    | A.Uminus (p,e) -> A.Uminus (p,aux e)
    | A.Mod (p,e1,e2) -> A.Mod (p,aux e1,aux e2)
    | A.Minus (p,e1,e2) -> A.Minus (p,aux e1,aux e2)
    | A.Plus (p,e1,e2) -> A.Plus (p,aux e1,aux e2)
    | A.Div (p,e1,e2) -> A.Div (p,aux e1,aux e2)
    | A.Times (p,e1,e2) -> A.Times (p,aux e1,aux e2)
    | A.IntDiv (p,e1,e2) -> A.IntDiv (p,aux e1,aux e2)
    | A.BVAnd (p,e1,e2) -> A.BVAnd (p,aux e1,aux e2)
    | A.BVOr (p,e1,e2) -> A.BVOr (p,aux e1,aux e2)
    | A.BVNot (p,e) -> A.BVNot (p,aux e)
    | A.BVShiftL (p,e1,e2) -> A.BVShiftL (p,aux e1,aux e2)
    | A.BVShiftR (p,e1,e2) -> A.BVShiftR (p,aux e1,aux e2)
    | A.Ite (p,e1,e2,e3) -> A.Ite (p,aux e1,aux e2,aux e3)
    | A.With (p,e1,e2,e3) -> A.With (p,aux e1,aux e2,aux e3)
    | A.Eq (p,e1,e2) -> A.Eq (p,aux e1,aux e2)
    | A.Neq (p,e1,e2) -> A.Neq (p,aux e1,aux e2)
    | A.Lte (p,e1,e2) -> A.Lte (p,aux e1,aux e2)
    | A.Lt (p,e1,e2) -> A.Lt (p,aux e1,aux e2)
    | A.Gte (p,e1,e2) -> A.Gte (p,aux e1,aux e2)
    | A.Gt (p,e1,e2) -> A.Gt (p,aux e1,aux e2)
    | A.When (p,e,c) -> A.When (p,aux e,c)
    | A.Current (p,e) -> A.Current (p,aux e)
    | A.Condact (p,e1,e2,id,es1,es2) ->
      A.Condact (p,aux e1,aux e2,id,List.map aux es1,List.map aux es2)
    | A.Activate (p,id,e1,e2,es) ->
      A.Activate (p,id,aux e1,aux e2,List.map aux es)
    | A.Merge (p,id,lst) ->
      A.Merge (p,id,List.map (fun (i,e) -> (i, aux e)) lst)
    | A.RestartEvery (p,id,es,e) -> A.RestartEvery (p,id,List.map aux es,aux e)
    | A.Pre (p,e) -> A.Pre (p,aux e)
    | A.Fby (p,e1,i,e2) -> A.Fby (p,aux e1,i,aux e2)
    | A.Arrow (p,e1,e2) -> A.Arrow (p,aux e1,aux e2)
  in aux expr

and minimize_expr ue lst typ expr =
  let pos = A.pos_of_expr expr in
  if List.exists (fun p -> Lib.compare_pos p pos = 0) lst
  then (false, minimize_node_call_args ue lst expr)
  else (true, ue typ expr)

let tyof_lhs id_typ_map lhs =
  let A.StructDef (pos, items) = lhs in
  let main = List.hd items in
  let rec aux = function
  | A.SingleIdent (_,id) -> [IdMap.find id id_typ_map]
  | A.TupleStructItem (_,items) -> List.map aux items |> List.flatten
  | A.ArraySliceStructItem _ | A.ArrayDef _ | A.FieldSelection _ | A.TupleSelection _
    -> assert false
  in
  let typ = aux main in
  (A.StructDef (pos, [main]), typ)

let minimize_node_eq id_typ_map ue lst = function
  | A.Assert (pos, expr) when
    List.exists (fun p -> Lib.compare_pos p pos = 0) lst ->
    Some (A.Assert (pos, expr))
  | A.Assert _ -> None
  | A.Automaton _ as automaton -> Some automaton
  | A.Equation (pos, lhs, expr) ->
    let (novarindex_lhs, typ) = tyof_lhs id_typ_map lhs in
    let (b, expr) = minimize_expr ue lst typ expr in
    let lhs = if b then novarindex_lhs else lhs in
    Some (A.Equation (pos, lhs, expr))

let minimize_item id_typ_map ue lst = function
  | A.AnnotMain b -> [A.AnnotMain b]
  | A.AnnotProperty (p,str,e) -> [A.AnnotProperty (p,str,e)]
  | A.Body eq ->
    begin match minimize_node_eq id_typ_map ue lst eq with
    | None -> []
    | Some eq -> [A.Body eq]
    end

let build_id_typ_map input output local =
  let add_input acc (_,id,t,_,_) =
    IdMap.add id t acc
  in
  let add_output acc (_,id,t,_) =
    IdMap.add id t acc
  in
  let add_local acc = function
  | A.NodeVarDecl (_,d) -> add_output acc d
  | A.NodeConstDecl (_, A.FreeConst (_,id,t))
  | A.NodeConstDecl (_, A.TypedConst (_,id,_,t)) ->
    IdMap.add id t acc
  | A.NodeConstDecl (_, A.UntypedConst _) ->
    acc (* It is a const anyway, it will not appear at lhs *)
  in
  let acc = List.fold_left add_input IdMap.empty input in
  let acc = List.fold_left add_output acc output in
  List.fold_left add_local acc local

let minimize_contract_node_eq lst cne =
  match cne with
  | A.GhostConst _ | A.GhostVar _ | A.ContractCall _
    -> [cne]
  | A.Assume (pos,_,_)
  | A.Guarantee (pos,_,_) ->
    if List.exists (fun p -> Lib.compare_pos p pos = 0) lst
    then [cne] else []
  | A.Mode (pos,id,req,ens) ->
    let ens = ens |> List.filter
      (fun (pos,_,_) -> List.exists (fun p -> Lib.compare_pos p pos = 0) lst)
    in
    [A.Mode (pos,id,req,ens)]

let minimize_node_decl ue ivc
  ((id, extern, tparams, inputs, outputs, locals, items, spec) as ndecl) =

  let id_typ_map = build_id_typ_map inputs outputs locals in
  let typ_of_input (_,_,t,_,_) = t in
  Hashtbl.replace nodes_input_types id (List.map typ_of_input inputs) ;

  let minimize_with_lst lst =
    let items = List.map (minimize_item id_typ_map ue lst) items |> List.flatten in
    let spec = 
    begin match spec with
      | None -> None
      | Some spec -> List.map (minimize_contract_node_eq lst) spec 
      |> List.flatten |> (fun s -> Some s)
    end
    in
    (id, extern, tparams, inputs, outputs, locals, items, spec)
  in
  
  try
    ScMap.find (Scope.mk_scope [id]) ivc
    |> List.map (fun (_,l,_) -> l) |> List.flatten
    |> List.map (fun l -> l.pos) |> minimize_with_lst
  with Not_found ->
    if Flags.IVC.ivc_enter_nodes ()
    then minimize_with_lst []
    else ndecl

let minimize_contract_decl ivc (id, tparams, inputs, outputs, body) =
  let lst = ScMap.bindings ivc
    |> List.map (fun (_,v) -> v)
    |> List.flatten
    |> List.map (fun (_,l,_) -> l)
    |> List.flatten
    |> List.map (fun l -> l.pos) in
  let body = body
    |> List.map (minimize_contract_node_eq lst)
    |> List.flatten
  in
  (id, tparams, inputs, outputs, body)

let minimize_decl ue ivc = function
  | A.NodeDecl (p, ndecl) ->
    A.NodeDecl (p, minimize_node_decl ue ivc ndecl)
  | A.FuncDecl (p, ndecl) ->
    A.FuncDecl (p, minimize_node_decl ue ivc ndecl)
  | A.ContractNodeDecl (p, cdecl) ->
    A.ContractNodeDecl (p, minimize_contract_decl ivc cdecl)
  | decl -> decl 

(* TODO: take init eqs into account (otherwise it could be unsound) *)
let minimize_lustre_ast ?(valid_lustre=false) all_eqs res ast =
  if not res.success then ast
  else
    let ivc = res.trans in
    let all_eqs = all_eqs.trans in
    let undef_expr =
      if valid_lustre
      then
        (* We construct a map that associate to each position a list of state vars
           that correspond to the state vars characterizing this position (if any) *)
        let pos_sv_map = ScMap.fold
        (fun _ lst acc ->
          List.fold_left
          (fun acc (_,ls,cat) ->
            let svs = match cat with
            | Unknown | Assertion -> []
            | Equation sv -> [sv]
            | ContractItem sv -> [sv]
            | NodeCall (_, svs) -> svs
            in
            List.fold_left
            (fun acc l ->
              let old = try PosMap.find l.pos acc with Not_found -> [] in
              PosMap.add l.pos (svs@old) acc
            )
            acc ls
          )
          acc lst
        ) all_eqs PosMap.empty
        |> PosMap.map (fun lst -> List.sort compare lst) in
        undef_expr (Some pos_sv_map)
      else undef_expr None in
    let minimized = List.map (minimize_decl undef_expr ivc) ast in

    (*let rec aux acc nb =
      match nb with
      | 0 -> acc
      | n -> aux ((rand_node n)::acc) (nb-1)
    in
    aux minimized (!max_nb_args)*)
    Hashtbl.fold (fun ts n acc ->
      (rand_node n ts)::acc
    )
    rand_functions
    minimized

(* ---------- MAPPING BACK ---------- *)

let locs_of_node_call in_sys args =
  args
  |> List.map (fun t -> match Term.destruct t with
  | Var v ->
    let sv = Var.state_var_of_state_var_instance v in
    InputSystem.lustre_definitions_of_state_var in_sys sv
    |> List.map (function
      | LustreNode.CallOutput (p, i) -> [{ pos=p ; index=i }]
      | _ -> []
    )
    |> List.flatten
    |> (fun x -> (sv,x))
  | _ -> assert false
  )
  |> List.fold_left
    (fun (svs, locs) (sv,loc) -> (sv::svs, loc@locs))
    ([], [])

(* The order matters, for this reason we can't use Term.state_vars_of_term *)
let rec find_vars t =
  match Term.destruct t with
  | Var v -> [v]
  | Const _ -> []
  | App (_, lst) ->
    List.map find_vars lst
    |> List.flatten
  | Attr (t, _) -> find_vars t

let locs_of_eq_term in_sys t =
  try
    let sv = find_vars t |> List.hd |> Var.state_var_of_state_var_instance in
    InputSystem.lustre_definitions_of_state_var in_sys sv
    |> List.map (fun def ->
      let p = LustreNode.pos_of_state_var_def def in
      let i = LustreNode.index_of_state_var_def def in
      { pos=p ; index=i }
    )
    |> (fun locs -> (sv, locs))
  with _ -> assert false

let loc_according_to_trans_sys sys eq =
  let terms_pos_map = TS.get_terms_position_map sys in
  try
    let pos = Term.TermMap.find eq.opened terms_pos_map in
    Some { pos=pos; index=[] }
  with Not_found -> None

let add_loc in_sys sys eq =
  try begin
    match loc_according_to_trans_sys sys eq with
    | None ->
      let term = eq.closed in
      begin match Term.destruct term with
      | Term.T.App (s, ts) when
        (match (Symbol.node_of_symbol s) with `UF _ -> true | _ -> false)
        -> (* Case of a node call *)
        let (svs,pos) = locs_of_node_call in_sys ts in
        (eq, pos, NodeCall (s,svs))
      | Term.T.Var _ ->
        let (sv,loc) = locs_of_eq_term in_sys term in
        (eq, loc, ContractItem sv)
      | _ ->
        let (sv,loc) = locs_of_eq_term in_sys term in
        (eq, loc, Equation sv)
      end
    | Some l -> (eq, [l], Assertion)
  end
  with _ -> (* If the input is not a Lustre file, it may fail *)
    (eq, [], Unknown) 

let eqmap_to_ivc in_sys sys = ScMap.map (List.map (add_loc in_sys sys))

(* ---------- UTILITIES ---------- *)

let error_result = { success=false; init=ScMap.empty; trans=ScMap.empty }

let extract_props sys =
  List.filter (function
    | { Property.prop_status = Property.PropInvariant _ } -> true
    | { Property.prop_name } ->
      KEvent.log L_warn "Skipping unproved property %s" prop_name ;
      false
  ) (TS.get_real_properties sys)

let extract_props_names sys =
  List.map (fun { Property.prop_name = n } -> n) (extract_props sys)

let extract_props_terms sys =
  List.map (fun { Property.prop_term = p } -> p) (extract_props sys)
  |> Term.mk_and

let rec deconstruct_conj t =
  match Term.destruct t with
  | Term.T.App (s_and, ts) when Symbol.equal_symbols s_and Symbol.s_and ->
    List.map deconstruct_conj ts |> List.flatten
  | _ -> [t]

(* TODO: Not the right way to do it...
But minimize_invariants does not differantiate two-states and one-state invariants. *)
let rec is_one_step t =
  let open Term in
  match node_of_term t with
  | FreeVar v -> Numeral.leq Numeral.zero (Var.offset_of_state_var_instance v)
  | BoundVar _ | Leaf _ -> true
  | Node (_, lst) | Let (_, lst) ->
    List.map is_one_step lst |> List.for_all (fun b -> b)
  | Exists l | Forall l ->
    let (L (_, t)) = T.node_of_lambda l in 
    is_one_step t
  | Annot (t,_) -> is_one_step t

let extract_toplevel_equations sys =
  let (_,oinit,otrans) = TS.init_trans_open sys in
  let cinit = TS.init_of_bound None sys Numeral.zero
  and ctrans = TS.trans_of_bound None sys Numeral.zero in
  let pack o c = { opened=o ; closed=c } in
  let oinit = deconstruct_conj oinit
  and otrans = deconstruct_conj otrans
  and cinit = deconstruct_conj cinit
  and ctrans = deconstruct_conj ctrans in
  (List.map2 pack oinit cinit, List.map2 pack otrans ctrans)

type nonloc_ivc = (equation list) ScMap.t

let _all_eqs sys =
  let scope = TS.scope_of_trans_sys sys in
  let (init, trans) = extract_toplevel_equations sys in
  let init = ScMap.singleton scope init in
  let trans = ScMap.singleton scope trans in
  if Flags.IVC.ivc_enter_nodes ()
  then
    TS.fold_subsystems ~include_top:false (fun (init_acc, trans_acc) sys ->
      let scope = TS.scope_of_trans_sys sys in
      let (init, trans) = extract_toplevel_equations sys in
      (ScMap.add scope init init_acc, ScMap.add scope trans trans_acc)
    ) (init, trans) sys
  else (init, trans)

let all_eqs in_sys sys =
  let (init, trans) = _all_eqs sys in
  { success=true ; init=eqmap_to_ivc in_sys sys init ;
    trans=eqmap_to_ivc in_sys sys trans }

(* ---------- IVC_UC ---------- *)

let get_logic ?(pathcomp=false) sys =
  let open TermLib in
  match TS.get_logic sys with
  | `Inferred fs when pathcomp ->
    `Inferred
      TermLib.FeatureSet.(sup_logics [fs; of_list [IA; LA; UF]])
  | l -> l

let create_solver ?(pathcomp=false) sys actlits bmin bmax =
  let solver =
    SMTSolver.create_instance ~produce_assignments:pathcomp ~produce_cores:true
    (get_logic ~pathcomp sys) (Flags.Smt.solver ()) in
  List.iter (SMTSolver.declare_fun solver) actlits ;
  TS.declare_sorts_ufs_const sys (SMTSolver.declare_fun solver) (SMTSolver.declare_sort solver) ;
  TS.declare_vars_of_bounds
    sys
    (SMTSolver.declare_fun solver)
    (Numeral.of_int bmin) (Numeral.of_int bmax) ;
  if pathcomp
  then begin
    Compress.init (SMTSolver.declare_fun solver) sys ;
    Compress.incr_k ()
  end ;
  solver

let check_sat solver actlits =
  let act_terms = List.map Actlit.term_of_actlit actlits in
  SMTSolver.check_sat_assuming solver (fun _ -> true) (fun _ -> false) act_terms

let actlit_of_term t = match Term.destruct t with
    | Var _ -> assert false
    | Const s -> Symbol.uf_of_symbol s
    | App _ -> assert false
    | Attr _ -> assert false

let rec interval imin imax =
  if imin > imax then []
  else imin::(interval (imin+1) imax)

let base_k sys b0 init_eq trans_eq prop_eq os_prop_eq k =
  let prop_eq = if k = 0 then os_prop_eq else prop_eq in

  let init_eq =
    init_eq
    |> Term.bump_state (Numeral.of_int b0)
  in

  let trans_eq =
    interval (b0+1) (b0+k)
    |> List.map (fun i -> Term.bump_state (Numeral.of_int i) trans_eq)
    |> Term.mk_and
  in

  let prop_eq =
    prop_eq
    |> Term.bump_state (Numeral.of_int (b0 + k))
  in

  (b0 + k + 1, Term.mk_implies [Term.mk_and [init_eq ; trans_eq]; prop_eq])

let base_until_k sys b0 init_eq trans_eq prop_eq os_prop_eq k =
  interval 0 k
  |> List.fold_left (
    fun (b0, base) i ->
      let (b0, t) = base_k sys b0 init_eq trans_eq prop_eq os_prop_eq i in
      (b0, Term.mk_and [base; t])
  )
  (b0, Term.mk_true ())

let ind_k sys b0 trans_eq inv_eq os_inv_eq prop_eq k =

  let trans_eq =
    interval (b0+1) (b0+1+k)
    |> List.map (fun i -> Term.bump_state (Numeral.of_int i) trans_eq)
    |> Term.mk_and
  in

  let inv_eq = Term.bump_state (Numeral.of_int b0) os_inv_eq in
  let inv_eq =
    interval (b0+1) (b0+k)
    |> List.map (fun i -> Term.bump_state (Numeral.of_int i) inv_eq)
    |> (fun eqs -> inv_eq::eqs)
    |> Term.mk_and
  in

  let prop_eq =
    prop_eq
    |> Term.bump_state (Numeral.of_int (b0 + k + 1))
  in
  
  let path_compress solver =
    (* Try to block the counterexample with path compression *)
    let svi = TS.get_state_var_bounds sys in
    let model = SMTSolver.get_var_values solver svi
        (TS.vars_of_bounds sys (Numeral.of_int b0) (Numeral.of_int (b0+k+1))) in
    let path = Model.path_from_model (TS.state_vars sys) model
        (Numeral.of_int (b0+k+1)) in
    match Compress.check_and_block (SMTSolver.declare_fun solver) sys path with
    | [] -> false
    | compressor ->
      (*KEvent.log_uncond "Compressor: %n"
        (List.length compressor) ;*)
      compressor |> Term.mk_and |> SMTSolver.assert_term solver ;
      true
  in
  let path_compress =
    if b0 = 0 then path_compress
    else begin
      KEvent.log L_warn "Path compression cannot be enabled for a bound different than 0" ;
      (fun _ -> false)
  end
  in
  (b0+k+2, Term.mk_implies [Term.mk_and [trans_eq ; inv_eq]; prop_eq], path_compress)

let k_induction sys b0 init_eq trans_eq prop_eq os_prop_eq k =

  let (b0, ind, path_compress) = ind_k sys b0 trans_eq prop_eq os_prop_eq prop_eq k in
  let (b0, base) = base_until_k sys b0 init_eq trans_eq prop_eq os_prop_eq k in
  (b0, Term.mk_and [base ; ind], path_compress)

type core = (UfSymbol.t list) ScMap.t

let actlits_of_core map = List.flatten (List.map snd (ScMap.bindings map))

let symbols_inter lst1 lst2 =
  SySet.inter (SySet.of_list lst1) (SySet.of_list lst2) |> SySet.elements

let symbols_union lst1 lst2 =
  SySet.union (SySet.of_list lst1) (SySet.of_list lst2) |> SySet.elements

let core_union c1 c2 =
  let merge _ lst1 lst2 = match lst1, lst2 with
  | None, None -> None
  | Some lst, None | None, Some lst -> Some lst
  | Some lst1, Some lst2 -> Some (symbols_union lst1 lst2)
  in
  ScMap.merge merge c1 c2

let filter_core core actlits =
  ScMap.map (symbols_inter actlits) core

let eq_of_scope eqs_map scope =
  try ScMap.find scope eqs_map with Not_found -> Term.mk_true ()

type result = NOT_OK | OK of core

let compute_unsat_core ?(pathcomp=None) sys core init_eqs trans_eqs bmin bmax t =
  let enable_compr = pathcomp <> None in
  let actlits = actlits_of_core core in
  let solver = create_solver ~pathcomp:enable_compr sys actlits bmin bmax in

  (* Define non-top-level nodes *)
  if Flags.IVC.ivc_enter_nodes ()
  then
    sys |> TS.iter_subsystems ~include_top:false (fun t ->
      let define = SMTSolver.define_fun solver in
      let scope = TS.scope_of_trans_sys t in
      let init = eq_of_scope init_eqs scope in
      let trans = eq_of_scope trans_eqs scope in
      define (TS.init_uf_symbol t) (TS.init_formals t) init ;
      define (TS.trans_uf_symbol t) (TS.trans_formals t) trans
    )
  else TS.define_subsystems sys (SMTSolver.define_fun solver) ;

  SMTSolver.assert_term solver t |> ignore ;

  let rec check () =
    if check_sat solver actlits
    then
      if enable_compr then begin
        match pathcomp with
        | None -> assert false
        | Some f ->
          if f solver then check ()
          else NOT_OK
      end
      else NOT_OK
    else
      let res = SMTSolver.get_unsat_core_lits solver
      |> List.map actlit_of_term
      in OK (filter_core core res)
  in

  let res = check () in
  SMTSolver.delete_instance solver ;
  res

let check_k_inductive sys actlits init_eqs trans_eqs prop_eq os_prop_eq k =
  (* In the functions above, k starts at 0 whereas it start at 1 with Kind2 notation *)
  let k = k - 1 in
  let scope = TS.scope_of_trans_sys sys in
  let init_eq = eq_of_scope init_eqs scope in
  let trans_eq = eq_of_scope trans_eqs scope in

  if Flags.BmcKind.compress ()
  then
    let (bmax, t) = base_until_k sys 0 init_eq trans_eq prop_eq os_prop_eq k in
    let bmax = bmax-1 in
    let t = Term.mk_not t in
    let res_base = compute_unsat_core sys actlits init_eqs trans_eqs 0 bmax t in
    match res_base with
    | NOT_OK -> NOT_OK
    | OK core ->
      let (bmax, t, pathcomp) = ind_k sys 0 trans_eq prop_eq os_prop_eq prop_eq k in
      let bmax = bmax-1 in
      let t = Term.mk_not t in
      let res_ind = compute_unsat_core ~pathcomp:(Some pathcomp) sys actlits init_eqs trans_eqs 0 bmax t in
      begin match res_ind with
      | NOT_OK -> NOT_OK
      | OK core' -> OK (core_union core core')
      end
  else
    let (bmax, t, _) = k_induction sys 0 init_eq trans_eq prop_eq os_prop_eq k in
    let bmax = bmax-1 in
    let t = Term.mk_not t in
    compute_unsat_core sys actlits init_eqs trans_eqs 0 bmax t

let is_empty_core c =
  ScMap.for_all (fun _ v -> v = []) c

let core_size c =
  ScMap.fold (fun _ lst acc -> acc + (List.length lst)) c 0

let pick_core c =
  let c = ScMap.filter (fun _ lst -> lst <> []) c in
  let (scope, lst) = List.hd (ScMap.bindings c) in
  match lst with
  | [] -> assert false
  | hd::lst -> (scope, hd, ScMap.add scope lst c)

exception NotKInductive

(** Implements the algorithm IVC_UC *)
let ivc_uc_ ?(minimize_init=false) ?(approximate=false) sys =
  let scope = TS.scope_of_trans_sys sys in
  let k, invs = CertifChecker.minimize_invariants sys None in
  (* Sometimes fail when giving 'Some (TS.invars_of_bound sys Numeral.zero)' as 2nd parameter *)
  let os_invs = List.filter is_one_step invs in
  let prop = extract_props_terms sys in
  let os_prop = Term.mk_and (prop::os_invs) in
  let prop = Term.mk_and (prop::invs) in
  KEvent.log L_info "Inductive property: %a" Term.pp_print_term prop ;
  KEvent.log L_info "One-step inductive property: %a" Term.pp_print_term os_prop ;
  KEvent.log L_info "Value of k: %n" k ;

  (* Activation litterals and utilities *)
  let add_to_bindings (aib, atb) sys =
    let bind_with_fresh_lit scope lst =
      List.map (fun t -> (Actlit.fresh_actlit (), scope, t)) lst
    in
    let (init, trans) = extract_toplevel_equations sys in
    let scope = TS.scope_of_trans_sys sys in
    let aib' = bind_with_fresh_lit scope init in
    let atb' = bind_with_fresh_lit scope trans in
    (aib'@aib, atb'@atb)
  in
  let (init_bindings, trans_bindings) =
    if Flags.IVC.ivc_enter_nodes ()
    then
      TS.fold_subsystems ~include_top:false (add_to_bindings) ([], []) sys
    else
      ([], [])
  in
  let (init_bindings, trans_bindings) =
    add_to_bindings (init_bindings, trans_bindings) sys
  in

  let add_to_core acc (actlit,scope,_) =
    let old = try ScMap.find scope acc with Not_found -> [] in
    ScMap.add scope (actlit::old) acc
  in
  let core_init = List.fold_left add_to_core ScMap.empty init_bindings in
  let core_trans = List.fold_left add_to_core ScMap.empty trans_bindings in

  let actlits_terms_map =
    List.fold_left (fun acc (k,_,v) -> SyMap.add k v acc)
      SyMap.empty (init_bindings@trans_bindings)
  in
  let eq_of_actlit ?(with_act=false) opened a =
    let t = SyMap.find a actlits_terms_map in
    let t = if opened then t.opened else t.closed in
    if with_act
    then (* Term.mk_eq *) Term.mk_implies [Actlit.term_of_actlit a ; t]
    else t
  in

  (* Minimization *)
  let rec minimize check keep test =
    match check keep test with
    | NOT_OK -> (*KEvent.log_uncond "Not k-inductive." ;*) None 
    | OK core ->
      (*KEvent.log_uncond "UNSAT core eliminated %n equations."
        (core_size test - core_size core) ;*)
      if approximate
      then Some (core_union keep core)
      else
        if is_empty_core core
        then Some keep
        else begin
          let (scope, symb, test) = pick_core core in
          begin match minimize check keep test with
          | None -> minimize check (core_union (ScMap.singleton scope [symb]) keep) test
          | Some res -> Some res
          end
        end
  in

  let eqs_of_current_state keep test =
    let eqs_map_union c1 c2 =
      let merge _ lst1 lst2 = match lst1, lst2 with
      | None, None -> None
      | Some lst, None | None, Some lst -> Some lst
      | Some lst1, Some lst2 -> Some (lst1@lst2)
      in
      ScMap.merge merge c1 c2
    in
    let keep = ScMap.mapi
      (fun s v -> List.map (eq_of_actlit (not (Scope.equal s scope))) v) keep in
    let test = ScMap.mapi
      (fun s v -> List.map (eq_of_actlit ~with_act:true (not (Scope.equal s scope))) v) test in
    let combined = eqs_map_union keep test in
    ScMap.map (fun v -> Term.mk_and v) combined
  in

  let core_to_eqmap core =
    ScMap.map (fun v -> List.map
      (fun s -> {opened=eq_of_actlit true s ; closed=eq_of_actlit false s}) v)
      core
  in

  let init_eqs = eqs_of_current_state core_init ScMap.empty in
  let check_trans keep test =
    let eqs = eqs_of_current_state keep test in
    check_k_inductive sys test init_eqs eqs prop os_prop k
  in
  let (core_trans, trans_res) = match minimize check_trans ScMap.empty core_trans with
  | None -> raise NotKInductive
  | Some acts -> (acts, core_to_eqmap acts)
  in

  let (core_init, init_res) =
    if minimize_init then
      let trans_eqs = eqs_of_current_state core_trans ScMap.empty in
      let check_init keep test =
        let eqs = eqs_of_current_state keep test in
        check_k_inductive sys test eqs trans_eqs prop os_prop k
      in
      match minimize check_init ScMap.empty core_init with
      | None -> raise NotKInductive
      | Some acts -> (acts, core_to_eqmap acts)
  else
    (core_init, core_to_eqmap core_init)
  in
  (init_res, trans_res)

let ivc_uc in_sys ?(minimize_init=false) ?(approximate=false) sys =
  try (
    let (init, trans) =
      ivc_uc_ ~minimize_init:minimize_init ~approximate:approximate sys in
    { success=true; init=eqmap_to_ivc in_sys sys init ;
      trans=eqmap_to_ivc in_sys sys trans }
  ) with
  | NotKInductive ->
    KEvent.log L_error "Properties are not k-inductive." ;
    error_result

(* ---------- IVC_BF ---------- *)

let reset_ts prop_names sys =
  if Flags.IVC.ivc_enter_nodes ()
  then TS.clear_all_invariants sys
  else TS.clear_invariants sys ;
  List.iter
    (fun str -> TS.force_set_prop_unknown sys str)
    prop_names

let check_result prop_names sys =
  List.for_all
    (fun str -> match TS.get_prop_status sys str with
    | Property.PropInvariant _ -> true
    | _ -> false)
    prop_names

let eqmap_union m1 m2 =
  let merge _ lst1 lst2 = match lst1, lst2 with
  | None, None -> None
  | Some lst, None | None, Some lst -> Some lst
  | Some lst1, Some lst2 -> Some (lst1@lst2)
  in
  ScMap.merge merge m1 m2

let is_empty_eqmap = is_empty_core

let pick_eqmap = pick_core

exception CannotProve

(* TODO: constants (like in test.lus) are sometimes wrongly removed because they still are present in the init system *)
(** Implements the algorithm IVC_BF *)
let ivc_bf_ in_sys param analyze sys init trans =
  let param = Analysis.param_clone param in
  let sys = TS.copy sys in
  let prop_names = extract_props_names sys in
  let modules = Flags.enabled () in

  (* Minimization *)
  let rec minimize check keep test =
    if check keep test then
      if is_empty_eqmap test
      then Some keep
      else
        let (scope, eq, test) = pick_eqmap test in
        match minimize check keep test with
        | None ->
          minimize check (eqmap_union (ScMap.singleton scope [eq]) keep) test
        | Some res -> Some res
    else None
  in

  let prepare_ts_for_check keep test =
    reset_ts prop_names sys ;
    let union = eqmap_union keep test in
    let prepare_subsystem sys =
      let scope = TS.scope_of_trans_sys sys in
      let eqs =
        try Some (ScMap.find scope union)
        with Not_found -> if Flags.IVC.ivc_enter_nodes () then Some [] else None
      in
      begin match eqs with
      | None -> ()
      | Some eqs ->
        let init_eq =
          (try List.map (fun eq -> eq.opened) (ScMap.find scope init)
          with Not_found -> [])
        |> Term.mk_and in
        let trans_eq = List.map (fun eq -> eq.opened) eqs
        |> Term.mk_and in
        TS.set_init_trans sys init_eq trans_eq 
      end
    in
    TS.iter_subsystems ~include_top:true prepare_subsystem sys
  in
  let check keep test =
    prepare_ts_for_check keep test ;
    let old_log_level = Lib.get_log_level () in
    Lib.set_log_level L_off ;
    analyze false modules in_sys param sys ;
    Lib.set_log_level old_log_level;
    check_result prop_names sys
  in

  let trans =
    begin match minimize check ScMap.empty trans with
    | None -> raise CannotProve
    | Some res -> res
    end
  in
  (init, trans)

let ivc_bf in_sys param analyze sys =
  try (
    let (init, trans) = _all_eqs sys in
    let (init, trans) = ivc_bf_ in_sys param analyze sys init trans in
    { success=true; init=init |> eqmap_to_ivc in_sys sys ;
      trans=trans |> eqmap_to_ivc in_sys sys }
  ) with
  | CannotProve ->
    KEvent.log L_error "Cannot prove the properties." ;
    error_result

(** Implements the algorithm IVC_UCBF *)
let ivc_ucbf in_sys param analyze sys =
  try (
    let (init, trans) = ivc_uc_ sys in
    let (init, trans) = ivc_bf_ in_sys param analyze sys init trans in
    { success=true; init=init |> eqmap_to_ivc in_sys sys ;
      trans=trans |> eqmap_to_ivc in_sys sys }
  ) with
  | NotKInductive ->
    KEvent.log L_error "Properties are not k-inductive." ;
    error_result
  | CannotProve ->
    KEvent.log L_error "Cannot prove the properties." ;
    error_result
