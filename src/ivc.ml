
module TS = TransSys
module SMT  : SolverDriver.S = GenericSMTLIBDriver

module SyMap = UfSymbol.UfSymbolMap
module SySet = UfSymbol.UfSymbolSet
module ScMap = Scope.Map
module ScSet = Scope.Set
module SVSet = StateVar.StateVarSet
module SVMap = StateVar.StateVarMap
module SVSMap = Map.Make(SVSet)

module Position = struct
  type t = Lib.position
  let compare = Lib.compare_pos
end
module PosMap = Map.Make(Position)
module PosSet = Set.Make(Position)

module A = LustreAst
module AstID = struct
  type t = A.ident
  let compare = compare
end
module IdMap = Map.Make(AstID)

type term_cat = NodeCall of string * SVSet.t
| ContractItem of StateVar.t
| Equation of StateVar.t
| Assertion of StateVar.t
| Unknown

type equation = {
  init_opened: Term.t ;
  init_closed: Term.t ;
  trans_opened: Term.t ;
  trans_closed: Term.t ;
}

type loc = {
  pos: Lib.position ;
  index: LustreIndex.index ;
}

type loc_equation = equation * (loc list) * term_cat

type ivc = loc_equation list ScMap.t

let rec interval imin imax =
  if imin > imax then []
  else imin::(interval (imin+1) imax)

(* ---------- PRETTY PRINTING ---------- *)

let aux_vars sys =
  let usr_name =
    assert (List.length LustreIdent.user_scope = 1) ;
    List.hd LustreIdent.user_scope
  in
  List.filter
    (fun sv ->
      not ( List.mem usr_name (StateVar.scope_of_state_var sv) )
    )
    (TS.state_vars sys)

let compute_var_map in_sys sys =
  let aux_vars = TS.fold_subsystems ~include_top:true (fun acc sys -> (aux_vars sys)@acc) [] sys in
  InputSystem.mk_state_var_to_lustre_name_map in_sys aux_vars

let pp_print_json fmt json =
  Yojson.Basic.pretty_to_string json
  |> Format.fprintf fmt "%s"

let pp_print_loc fmt {pos=pos ; index=index} =
  match index with
  | [] -> Lib.pp_print_pos fmt pos
  | index ->
    Format.fprintf fmt "%a (index %a)"
      Lib.pp_print_pos pos (LustreIndex.pp_print_index false) index

let pp_print_loc_xml fmt {pos=pos ; index=index} =
  let (_,row,col) = Lib.file_row_col_of_pos pos in
  match index with
  | [] -> Format.fprintf fmt "<Position line=%i column=%i />" row col
  | index ->
    Format.fprintf fmt "<Position line=%i column=%i index=\"%a\" />"
      row col (LustreIndex.pp_print_index false) index

let loc2json {pos=pos ; index=index} =
  let (_,row,col) = Lib.file_row_col_of_pos pos in
  match index with
  | [] ->
    `Assoc [("objectType", `String "position") ; ("line", `Int row) ; ("column", `Int col)]
  | index ->
    `Assoc [("objectType", `String "position") ; ("line", `Int row) ; ("column", `Int col) ;
      ("index", `String (Format.asprintf "%a" (LustreIndex.pp_print_index false) index))]

let pp_print_locs fmt = function
| [] -> Format.fprintf fmt "None"
| hd::lst ->
  pp_print_loc fmt hd ;
  List.iter (Format.fprintf fmt " and %a" pp_print_loc) lst

let pp_print_locs_xml fmt =
  List.iter (pp_print_loc_xml fmt)

let locs2json lst =
  `List (List.map loc2json lst)

let expr_pp_print var_map fmt expr =
  LustreExpr.pp_print_term_as_expr_mvar false var_map fmt expr

let cat_to_string = function
  | NodeCall _ -> "Node call"
  | ContractItem _ -> "Contract item"
  | Equation _ -> "Equation"
  | Assertion _ -> "Assertion"
  | Unknown -> "Unknown element"

let eq_expr_pp_print ?(init=false) var_map fmt (eq, _, cat) =
  match cat with
  | NodeCall (n,_) -> Format.fprintf fmt "%s" n
  | ContractItem _  | Equation _ | Assertion _ | Unknown ->
    if init
    then expr_pp_print var_map fmt eq.init_closed
    else expr_pp_print var_map fmt eq.trans_closed

let pp_print_loc_eq_ var_map fmt (eq, loc, cat) =
  Format.fprintf fmt "%s %a at position %a" (cat_to_string cat)
    (eq_expr_pp_print var_map) (eq, loc, cat) pp_print_locs loc

let pp_print_loc_eq_xml var_map fmt (eq, loc, cat) =
  Format.fprintf fmt "<Equation cat=\"%s\" init=\"%a\" trans=\"%a\">%a</Equation>"
    (cat_to_string cat) (eq_expr_pp_print ~init:true var_map) (eq, loc, cat)
    (eq_expr_pp_print var_map) (eq, loc, cat) pp_print_locs_xml loc

let loc_eq2json var_map (eq, loc, cat) =
  `Assoc [("objectType", `String "equation") ; ("cat", `String (cat_to_string cat)) ;
    ("init", `String (Format.asprintf "%a" (eq_expr_pp_print ~init:true var_map) (eq, loc, cat))) ;
    ("trans", `String (Format.asprintf "%a" (eq_expr_pp_print var_map) (eq, loc, cat))) ;
    ("positions", locs2json loc)
  ]

let pp_print_loc_eq in_sys sys =
  let var_map = compute_var_map in_sys sys in
  pp_print_loc_eq_ var_map

let pp_print_loc_eqs_ var_map fmt =
  let print = pp_print_loc_eq_ var_map in
  List.iter (Format.fprintf fmt "%a\n" print)

let pp_print_loc_eqs_xml var_map fmt =
  let print = pp_print_loc_eq_xml var_map in
  List.iter (Format.fprintf fmt "%a\n" print)

let loc_eqs2json var_map lst =
  `List (List.map (loc_eq2json var_map) lst)

let pp_print_loc_eqs in_sys sys =
  let var_map = compute_var_map in_sys sys in
  pp_print_loc_eqs_ var_map

let pp_print_ivc in_sys sys title fmt =
  let var_map = compute_var_map in_sys sys in
  let print = pp_print_loc_eqs_ var_map in
  Format.fprintf fmt "========== %s ==========\n\n" title ;
  ScMap.iter (fun scope eqs -> 
    Format.fprintf fmt "----- %s -----\n" (Scope.to_string scope) ;
    Format.fprintf fmt "%a\n" print eqs
  )

let impl_to_string = function
| `IVC_AUC -> "AUC"
| `IVC_UC -> "UC"
| `IVC_UCBF -> "UCBF"
| `IVC_BF -> "BF"
| `UMIVC -> "UMIVC"

let pp_print_categories fmt =
  List.iter (function
    | `NODE_CALL -> Format.fprintf fmt "node_calls "
    | `CONTRACT_ITEM -> Format.fprintf fmt "contracts "
    | `EQUATION -> Format.fprintf fmt "equations "
    | `ASSERTION -> Format.fprintf fmt "assertions "
    | `UNKNOWN -> Format.fprintf fmt "unknown "
  )

let pp_print_ivc_xml in_sys sys title fmt ivc =
  let var_map = compute_var_map in_sys sys in
  let print = pp_print_loc_eqs_xml var_map in
  Format.fprintf fmt "<IVC title=\"%s\" category=\"%a\" enter_nodes=%b impl=\"%s\">\n" title
    pp_print_categories (Flags.IVC.ivc_elements ()) (Flags.IVC.ivc_enter_nodes ())
    (impl_to_string (Flags.IVC.ivc_impl ())) ;
  ScMap.iter (fun scope eqs -> 
    Format.fprintf fmt "<scope name=\"%s\">\n" (Scope.to_string scope) ;
    Format.fprintf fmt "%a" print eqs ;
    Format.fprintf fmt "</scope>\n\n"
  ) ivc ;
  Format.fprintf fmt "</IVC>\n"

let ivc2json in_sys sys title ivc =
  let var_map = compute_var_map in_sys sys in
  let loc_eqs2json = loc_eqs2json var_map in
  `Assoc [
    ("objectType", `String "ivc") ;
    ("title", `String title) ;
    ("category", `String (Format.asprintf "%a" pp_print_categories (Flags.IVC.ivc_elements ()))) ;
    ("enterNodes", `Bool (Flags.IVC.ivc_enter_nodes ())) ;
    ("impl", `String (impl_to_string (Flags.IVC.ivc_impl ()))) ;
    ("value", `List (List.map (fun (scope, eqs) ->
      `Assoc [
        ("objectType", `String "scope") ;
        ("name", `String (Scope.to_string scope)) ;
        ("value", loc_eqs2json eqs)
      ]
    ) (ScMap.bindings ivc)))
  ]

let pp_print_ivc_json in_sys sys title fmt ivc =
  pp_print_json fmt (ivc2json in_sys sys title ivc)

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

let rec unannot_pos = function
  | A.Bool _ -> A.Bool dpos
  | A.Int _ -> A.Int dpos
  | A.UInt8 _ -> A.UInt8 dpos
  | A.UInt16 _ -> A.UInt16 dpos
  | A.UInt32 _ -> A.UInt32 dpos
  | A.UInt64 _ -> A.UInt64 dpos
  | A.Int8 _ -> A.Int8 dpos
  | A.Int16 _ -> A.Int16 dpos
  | A.Int32 _ -> A.Int32 dpos
  | A.Int64 _ -> A.Int64 dpos
  | A.IntRange (_,e1,e2) -> A.IntRange (dpos,e1,e2)
  | A.Real _ -> A.Real dpos
  | A.UserType (_,id) -> A.UserType (dpos,id)
  | A.TupleType (_,ts) -> A.TupleType (dpos, List.map unannot_pos ts)
  | A.RecordType (_,tids) ->
    let aux (_,id,t) = (dpos,id,unannot_pos t) in
    A.RecordType (dpos,List.map aux tids)
  | A.ArrayType (_,(t,e)) -> A.ArrayType (dpos,(unannot_pos t,e))
  | A.EnumType (_,id,ids) -> A.EnumType (dpos,id,ids)

let rand_function_name_for _ ts =
  let ts = List.map unannot_pos ts in
  begin
  try Hashtbl.find rand_functions ts
  with Not_found ->
    let new_rand = new_rand_fun_ident () in
    Hashtbl.replace rand_functions ts new_rand ;
    new_rand
  end

let undef_expr pos_sv_map const_expr typ expr =
  let pos = A.pos_of_expr expr in
  match pos_sv_map with
  | None -> A.Ident (pos, "_")
  | Some pos_sv_map ->
    if const_expr then expr (* a call to __rand is not a valid constant expression *)
    else
      let svs = try PosMap.find pos pos_sv_map with Not_found -> SVSet.empty in
      if SVSet.is_empty svs
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

and ast_contains p ast =
  let rec aux ast =
    if p ast then true
    else match ast with
    | A.True _ | A.False _ | A.Ident _ | A.ModeRef _ | A.Num _ | A.Dec _ | A.Last _
      -> false
    | A.Call (_, _, args) | A.CallParam (_, _, _, args) ->
      List.map aux args
      |> List.exists (fun x -> x)
    | A.ToInt (_,e) | A.ToUInt8 (_,e) | A.ToUInt16 (_,e) | A.ToUInt32 (_,e) | A.ToUInt64 (_,e)
    | A.ToInt8 (_,e) | A.ToInt16 (_,e) | A.ToInt32 (_,e) | A.ToInt64 (_,e) | A.ToReal (_,e)
    | A.Not (_,e) | A.RecordProject (_,e,_) | A.Forall (_,_,e) | A.Exists (_,_,e)
    | A.Uminus (_,e) | A.BVNot (_,e) | A.When (_,e,_) | A.Current (_,e) | A.Pre (_,e) ->
      aux e
    | A.StructUpdate (_,e1,_,e2) | A.ArrayConstr (_,e1,e2)
    | A.ArrayConcat (_,e1,e2) | A.TupleProject (_,e1,e2)
    | A.And (_,e1,e2) | A.Or (_,e1,e2) | A.Xor (_,e1,e2) | A.Impl (_,e1,e2)
    | A.Mod (_,e1,e2) | A.Minus (_,e1,e2) | A.Plus (_,e1,e2) | A.Div (_,e1,e2)
    | A.Times (_,e1,e2) | A.IntDiv (_,e1,e2) | A.BVAnd (_,e1,e2) | A.BVOr (_,e1,e2)
    | A.BVShiftL (_,e1,e2) | A.BVShiftR (_,e1,e2)
    | A.Eq (_,e1,e2) | A.Neq (_,e1,e2) | A.Lte (_,e1,e2) | A.Lt (_,e1,e2)
    | A.Gte (_,e1,e2) | A.Gt (_,e1,e2) | A.Fby (_,e1,_,e2) | A.Arrow (_,e1,e2) ->
      aux e1 || aux e2
    | A.TupleExpr (_,es) | A.ArrayExpr (_,es) | A.ExprList (_,es) | A.OneHot (_,es) ->
      List.map aux es
      |> List.exists (fun x -> x)
    | A.ArraySlice (_,e1,(e2,e3))
    | A.Ite (_,e1,e2,e3) | A.With (_,e1,e2,e3) ->
      aux e1 || aux e2 || aux e3
    | A.RecordExpr (_,_,lst) | A.Merge (_,_,lst) ->
      List.map (fun (_,e) -> aux e) lst
      |> List.exists (fun x -> x)
    | A.Condact (_,e1,e2,_,es1,es2) ->
      List.map aux (e1::e2::(es1@es2))
      |> List.exists (fun x -> x)
    | A.Activate (_,_,e1,e2,es) ->
      List.map aux (e1::e2::es)
      |> List.exists (fun x -> x)
    | A.RestartEvery (_,_,es,e) ->
      List.map aux (e::es)
      |> List.exists (fun x -> x)
  in
  aux ast

and minimize_expr ue lst typ expr =
  let all_pos = PosSet.of_list lst in
  let keep_expr expr =
    PosSet.mem (A.pos_of_expr expr) all_pos
  in
  if ast_contains keep_expr expr
  then (false, minimize_node_call_args ue lst expr)
  else (true, ue typ expr)

let tyof_lhs id_typ_map lhs =
  let A.StructDef (pos, items) = lhs in
  let rec aux = function
  | A.SingleIdent (_,id) as e -> [e, IdMap.find id id_typ_map]
  | A.ArrayDef (pos,id,_) -> [A.SingleIdent (pos,id), IdMap.find id id_typ_map]
  | A.TupleStructItem _ | A.ArraySliceStructItem _ | A.FieldSelection _ | A.TupleSelection _
    -> assert false
  in
  let (items,typ) = List.map aux items |> List.flatten |> List.split in
  (A.StructDef (pos, items), typ)

let minimize_node_eq id_typ_map ue lst = function
  | A.Assert (pos, expr) when
    List.exists (fun p -> Lib.compare_pos p pos = 0) lst ->
    Some (A.Assert (pos, expr))
  | A.Assert _ -> None
  | A.Automaton _ as automaton -> Some automaton
  | A.Equation (pos, lhs, expr) ->
    let (novarindex_lhs, typ) = tyof_lhs id_typ_map lhs in
    let (b, expr) = minimize_expr (ue false) lst typ expr in
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

let minimize_const_decl ue lst = function
  | A.UntypedConst (p,id,e) -> A.UntypedConst (p,id,e)
  | A.FreeConst (p,id,t) -> A.FreeConst (p,id,t)
  | A.TypedConst (p,id,e,t) ->
    (* Constants are inlined most of time so they may not appear as equations *)
    (* Therefore we should not minimize them *)
    (*let (_,e) = minimize_expr (ue true) lst [t] e in*)
    A.TypedConst (p,id,e,t)

let minimize_node_local_decl ue lst = function
  | A.NodeConstDecl (p,d) ->
    A.NodeConstDecl (p,minimize_const_decl ue lst d)
  | A.NodeVarDecl (p,d) -> A.NodeVarDecl (p,d)

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

let minimize_contract_node_eq ue lst cne =
  match cne with
  | A.ContractCall _ -> [cne]
  | A.GhostConst d -> [A.GhostConst (minimize_const_decl ue lst d)]
  | A.GhostVar d -> [A.GhostVar (minimize_const_decl ue lst d)]
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
      | Some spec -> List.map (minimize_contract_node_eq ue lst) spec 
      |> List.flatten |> (fun s -> Some s)
    end
    in
    let locals = List.map (minimize_node_local_decl ue lst) locals in
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

let minimize_contract_decl ue ivc (id, tparams, inputs, outputs, body) =
  let lst = ScMap.bindings ivc
    |> List.map (fun (_,v) -> v)
    |> List.flatten
    |> List.map (fun (_,l,_) -> l)
    |> List.flatten
    |> List.map (fun l -> l.pos) in
  let body = body
    |> List.map (minimize_contract_node_eq ue lst)
    |> List.flatten
  in
  (id, tparams, inputs, outputs, body)

let minimize_decl ue ivc = function
  | A.NodeDecl (p, ndecl) ->
    A.NodeDecl (p, minimize_node_decl ue ivc ndecl)
  | A.FuncDecl (p, ndecl) ->
    A.FuncDecl (p, minimize_node_decl ue ivc ndecl)
  | A.ContractNodeDecl (p, cdecl) ->
    A.ContractNodeDecl (p, minimize_contract_decl ue ivc cdecl)
  | decl -> decl 

let minimize_lustre_ast ?(valid_lustre=false) ivc_all ivc ast =
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
          | Unknown -> SVSet.empty
          | Equation sv | Assertion sv | ContractItem sv -> SVSet.singleton sv
          | NodeCall (_, svs) -> svs
          in
          List.fold_left
          (fun acc l ->
            let old = try PosMap.find l.pos acc with Not_found -> SVSet.empty in
            PosMap.add l.pos (SVSet.union svs old) acc
          )
          acc ls
        )
        acc lst
      ) ivc_all PosMap.empty in
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

let locs_of_node_call in_sys output_svs =
  output_svs
  |> SVSet.elements
  |> List.map (fun sv ->
      InputSystem.lustre_definitions_of_state_var in_sys sv
      |> List.map
        (fun d -> { pos=LustreNode.pos_of_state_var_def d ; index=LustreNode.index_of_state_var_def d })
  )
  |> List.flatten

let rec sublist i count lst =
  match i, count, lst with
  | _, 0, _ -> []
  | _, _, [] -> assert false
  | 0, k, hd::lst -> hd::(sublist 0 (k-1) lst)
  | i, k, _::lst -> sublist (i-1) k lst

let name_and_svs_of_node_call in_sys s args =
  (* Retrieve name of node *)
  let regexp = Printf.sprintf "^\\(%s\\|%s\\)_\\(.+\\)_[0-9]+$"
    Lib.ReservedIds.init_uf_string Lib.ReservedIds.trans_uf_string
    |> Str.regexp in
  let name = Symbol.string_of_symbol s in
  let name =
    if Str.string_match regexp name 0 
    then Str.matched_group 2 name
    else name
  in
  (* Retrieve number of inputs/outputs *)
  let node = InputSystem.find_lustre_node (Scope.mk_scope [Ident.of_string name]) in_sys in
  let nb_inputs = LustreIndex.cardinal (node.LustreNode.inputs) in
  let nb_oracles = List.length (node.LustreNode.oracles) in
  let nb_outputs = LustreIndex.cardinal (node.LustreNode.outputs) in
  (* Retrieve output statevars *)
  let svs = sublist (nb_inputs+nb_oracles) nb_outputs args
  |> List.map (fun t -> match Term.destruct t with
    | Var v -> Var.state_var_of_state_var_instance v
    | _ -> assert false
  )
  in
  (name, (*List.sort_uniq StateVar.compare_state_vars*)SVSet.of_list svs)

(* The order matters, for this reason we can't use Term.state_vars_of_term *)
let rec find_vars t =
  match Term.destruct t with
  | Var v -> [v]
  | Const _ -> []
  | App (_, lst) ->
    List.map find_vars lst
    |> List.flatten
  | Attr (t, _) -> find_vars t

let sv_of_term t = 
  find_vars t |> List.hd |> Var.state_var_of_state_var_instance

let locs_of_eq_term in_sys t =
  try
    let has_contract_items = ref false in
    let has_asserts = ref false in
    let sv = sv_of_term t in
    InputSystem.lustre_definitions_of_state_var in_sys sv
    |> List.map (fun def ->
      (match def with LustreNode.Assertion _ -> has_asserts := true
        | LustreNode.ContractItem _ -> has_contract_items := true | _ -> ());
      let p = LustreNode.pos_of_state_var_def def in
      let i = LustreNode.index_of_state_var_def def in
      { pos=p ; index=i }
    )
    |> (fun locs ->
      if !has_contract_items then (ContractItem sv, locs)
      else if !has_asserts then (Assertion sv, locs)
      else (Equation sv, locs)
    )
  with _ -> assert false

let compare_loc {pos=pos;index=index} {pos=pos';index=index'} =
  match Lib.compare_pos pos pos' with
  | 0 -> LustreIndex.compare_indexes index index'
  | n -> n

let normalize_loc lst =
  List.sort_uniq compare_loc lst

let add_loc in_sys eq =
  try
    let term = eq.trans_closed in
    begin match Term.destruct term with
    | Term.T.App (s, ts) when
      (match (Symbol.node_of_symbol s) with `UF _ -> true | _ -> false)
      -> (* Case of a node call *)
      let (name, svs) = name_and_svs_of_node_call in_sys s ts in
      let loc = locs_of_node_call in_sys svs in
      (eq, normalize_loc loc, NodeCall (name,svs))
    | _ ->
      let (cat,loc) = locs_of_eq_term in_sys term in
      (eq, normalize_loc loc, cat)
    end
  with _ -> (* If the input is not a Lustre file, it may fail *)
    (eq, [], Unknown)

let eqmap_to_ivc in_sys = ScMap.map (List.map (add_loc in_sys))

let svs_of_term in_sys t =
  match Term.destruct t with
  | Term.T.App (s, ts) when
    (match (Symbol.node_of_symbol s) with `UF _ -> true | _ -> false)
    -> (* Case of a node call *)
    let (_, svs) = name_and_svs_of_node_call in_sys s ts in
    svs
  | _ -> SVSet.singleton (sv_of_term t)

(* ---------- UTILITIES ---------- *)

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

exception InitTransMismatch of int * int

let extract_toplevel_equations in_sys sys =
  let (_,oinit,otrans) = TS.init_trans_open sys in
  let cinit = TS.init_of_bound None sys Numeral.zero
  and ctrans = TS.trans_of_bound None sys Numeral.zero in
  let oinit = deconstruct_conj oinit
  and otrans = deconstruct_conj otrans
  and cinit = deconstruct_conj cinit
  and ctrans = deconstruct_conj ctrans in
  let init = List.combine oinit cinit
  and trans = List.combine otrans ctrans in
  let mk_map = List.fold_left (fun acc (o,c) ->
    let svs = svs_of_term in_sys c in
    let (o,c) =
      try
        let (o',c') = SVSMap.find svs acc in
        (Term.mk_and [o;o'], Term.mk_and [c;c'])
      with Not_found -> (o,c) in
    SVSMap.add svs (o,c) acc
  ) SVSMap.empty
  in
  let init_bindings = mk_map init |> SVSMap.bindings
  and trans_bindings = mk_map trans |> SVSMap.bindings in
  let init_n = List.length init_bindings
  and trans_n = List.length trans_bindings in
  if init_n <> trans_n then raise (InitTransMismatch (init_n, trans_n)) ;
  List.map2 (fun (ki,(oi,ci)) (kt,(ot,ct)) ->
    if SVSet.compare ki kt <> 0
    then raise (InitTransMismatch (init_n, trans_n)) ;
    { init_opened=oi ; init_closed=ci ; trans_opened=ot ; trans_closed=ct }
  ) init_bindings trans_bindings

let check_loc_eq_category (_,_,cat) =
  let cats = Flags.IVC.ivc_elements () in
  let cat = match cat with
  | NodeCall _ -> `NODE_CALL
  | ContractItem _ -> `CONTRACT_ITEM
  | Equation _ -> `EQUATION
  | Assertion _ -> `ASSERTION
  | Unknown -> `UNKNOWN
  in
  List.mem cat cats

let should_minimize_equation in_sys eq =
  check_loc_eq_category (add_loc in_sys eq)

let separate_by_predicate f lst =
  let lst = List.map (fun e -> (f e, e)) lst in
  let ok = List.filter fst lst in
  let not_ok = List.filter (fun (ok,_) -> not ok) lst in
  (List.map snd not_ok, List.map snd ok)

let separate_loc_eqs_by_category =
  separate_by_predicate check_loc_eq_category

let separate_equations_by_category in_sys =
  separate_by_predicate (should_minimize_equation in_sys)

let separate_scmap f scmap =
  ScMap.fold (fun k v (map1,map2) ->
    let (v1,v2) = f v in
    (ScMap.add k v1 map1, ScMap.add k v2 map2)
  ) scmap (ScMap.empty, ScMap.empty)

let separate_ivc_by_category =
  separate_scmap separate_loc_eqs_by_category

type eqmap = (equation list) ScMap.t

let separate_eqmap_by_category in_sys =
  separate_scmap (separate_equations_by_category in_sys)

let _all_eqs in_sys sys =
  let scope = TS.scope_of_trans_sys sys in
  let eqs = extract_toplevel_equations in_sys sys in
  let eqmap = ScMap.singleton scope eqs in
  if Flags.IVC.ivc_enter_nodes ()
  then
    TS.fold_subsystems ~include_top:false (fun eqmap sys ->
      let scope = TS.scope_of_trans_sys sys in
      let eqs = extract_toplevel_equations in_sys sys in
      ScMap.add scope eqs eqmap
    ) eqmap sys
  else eqmap

let all_eqs in_sys sys =
  let eqmap = _all_eqs in_sys sys in
  eqmap_to_ivc in_sys eqmap

let term_of_eq init closed eq =
  if init && closed then eq.init_closed
  else if init then eq.init_opened
  else if closed then eq.trans_closed
  else eq.trans_opened

(* ---------- IVC_UC ---------- *)

let get_logic ?(pathcomp=false) sys =
  let open TermLib in
  match TS.get_logic sys with
  | `Inferred fs when pathcomp ->
    `Inferred
      TermLib.FeatureSet.(sup_logics [fs; of_list [IA; LA; UF]])
  | l -> l

let create_solver ?(pathcomp=false) ?(approximate=false) sys actlits bmin bmax =
  let solver =
    SMTSolver.create_instance ~timeout:(Flags.IVC.ivc_uc_timeout ())
    ~produce_assignments:pathcomp ~produce_cores:true
    ~minimize_cores:(not approximate) (get_logic ~pathcomp sys) (Flags.Smt.solver ()) in
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
  let actlits = SySet.of_list actlits in
  ScMap.map (fun lst -> SySet.of_list lst |> SySet.inter actlits |> SySet.elements) core


let term_of_scope term_map scope =
  try ScMap.find scope term_map with Not_found -> Term.mk_true ()

type result = NOT_OK | OK of core

let compute_unsat_core ?(pathcomp=None) ?(approximate=false)
  sys core init_terms trans_terms bmin bmax t =

  let enable_compr = pathcomp <> None in
  let actlits = actlits_of_core core in
  let solver =
    create_solver ~pathcomp:enable_compr ~approximate:approximate
    sys actlits bmin bmax in

  (* Define non-top-level nodes *)
  if Flags.IVC.ivc_enter_nodes ()
  then
    sys |> TS.iter_subsystems ~include_top:false (fun t ->
      let define = SMTSolver.define_fun solver in
      let scope = TS.scope_of_trans_sys t in
      let init = term_of_scope init_terms scope in
      let trans = term_of_scope trans_terms scope in
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

let is_empty_core c =
  ScMap.for_all (fun _ v -> v = []) c

let core_size c =
  ScMap.fold (fun _ lst acc -> acc + (List.length lst)) c 0

let check_k_inductive ?(approximate=false) sys actlits init_terms trans_terms prop os_prop k =
  (* In the functions above, k starts at 0 whereas it start at 1 with Kind2 notation *)
  let k = k - 1 in
  let scope = TS.scope_of_trans_sys sys in
  let init_eq = term_of_scope init_terms scope in
  let trans_eq = term_of_scope trans_terms scope in

  if Flags.BmcKind.compress ()
  then
    let (bmax, t) = base_until_k sys 0 init_eq trans_eq prop os_prop k in
    let bmax = bmax-1 in
    let t = Term.mk_not t in
    let res_base =
      compute_unsat_core ~approximate:approximate
      sys actlits init_terms trans_terms 0 bmax t in
    match res_base with
    | NOT_OK -> NOT_OK
    | OK core ->
      let (bmax, t, pathcomp) = ind_k sys 0 trans_eq prop os_prop prop k in
      let bmax = bmax-1 in
      let t = Term.mk_not t in
      let res_ind =
        compute_unsat_core ~pathcomp:(Some pathcomp) ~approximate:approximate
        sys actlits init_terms trans_terms 0 bmax t in
      begin match res_ind with
      | NOT_OK -> NOT_OK
      | OK core' -> OK (core_union core core')
      end
  else
    let (bmax, t, _) = k_induction sys 0 init_eq trans_eq prop os_prop k in
    let bmax = bmax-1 in
    let t = Term.mk_not t in
    compute_unsat_core ~approximate:approximate
    sys actlits init_terms trans_terms 0 bmax t

let lstmap_union c1 c2 =
  let merge _ lst1 lst2 = match lst1, lst2 with
  | None, None -> None
  | Some lst, None | None, Some lst -> Some lst
  | Some lst1, Some lst2 -> Some (lst1@lst2)
  in
  ScMap.merge merge c1 c2

let pick_core c =
  let c = ScMap.filter (fun _ lst -> lst <> []) c in
  let (scope, lst) = List.hd (ScMap.bindings c) in
  match lst with
  | [] -> assert false
  | hd::lst -> (scope, hd, ScMap.add scope lst c)

let eq_of_actlit actlits_eqs_map ?(with_act=false) a =
  let eq = SyMap.find a actlits_eqs_map in
  if with_act
  then
    let guard t =
      (* Term.mk_eq *)
      Term.mk_implies [Actlit.term_of_actlit a ; t]
    in
    { init_opened=guard eq.init_opened ; init_closed=guard eq.init_closed ;
      trans_opened=guard eq.trans_opened ; trans_closed=guard eq.trans_closed }
  else eq

exception NotKInductive

(** Implements the algorithm IVC_UC *)
let ivc_uc_ in_sys ?(approximate=false) sys =

  let scope = TS.scope_of_trans_sys sys in
  let k, invs = CertifChecker.minimize_invariants sys None in
  let os_invs = List.filter is_one_step invs in
  let prop = extract_props_terms sys in
  let os_prop = Term.mk_and (prop::os_invs) in
  let prop = Term.mk_and (prop::invs) in
  KEvent.log L_info "Inductive property: %a" Term.pp_print_term prop ;
  KEvent.log L_info "One-step inductive property: %a" Term.pp_print_term os_prop ;
  KEvent.log L_info "Value of k: %n" k ;

  (* Activation litterals, core and mapping to equations *)
  let add_to_bindings act_bindings sys =
    let eqs = extract_toplevel_equations in_sys sys in
    let scope = TS.scope_of_trans_sys sys in
    let act_bindings' =
      List.map (fun eq -> (Actlit.fresh_actlit (), scope, eq)) eqs in
    act_bindings'@act_bindings
  in
  let act_bindings =
    if Flags.IVC.ivc_enter_nodes ()
    then TS.fold_subsystems ~include_top:false (add_to_bindings) [] sys
    else []
  in
  let act_bindings = add_to_bindings act_bindings sys in

  let actlits_eqs_map =
    List.fold_left (fun acc (k,_,v) -> SyMap.add k v acc)
      SyMap.empty act_bindings
  in
  let eq_of_actlit = eq_of_actlit actlits_eqs_map in

  let add_to_core (keep, test) (actlit,scope,eq) =
    if should_minimize_equation in_sys eq
    then
      let old = try ScMap.find scope test with Not_found -> [] in
      (keep, ScMap.add scope (actlit::old) test)
    else
      let old = try ScMap.find scope keep with Not_found -> [] in
      (ScMap.add scope (actlit::old) keep, test)
  in
  let (keep,test) = List.fold_left add_to_core (ScMap.empty,ScMap.empty) act_bindings in

  (* Minimization *)
  (* If Z3 is used, we use the 'minimize cores' feature
    so we do not need to minimize them manually *)
  let z3_used = match Flags.Smt.solver () with `Z3_SMTLIB -> true | _ -> false in
  let has_timeout = ref false in
  let rec minimize ?(skip_first_check=false) check keep test =
    let first_check =
      if skip_first_check
      then OK test
      else
        try
          check (approximate || !has_timeout) keep test
        with SMTSolver.Timeout -> (
          has_timeout := true ;
          OK test
        )
    in
    match first_check with
    | NOT_OK -> (*KEvent.log_uncond "Not k-inductive." ;*) None 
    | OK core ->
      (*KEvent.log_uncond "UNSAT core eliminated %n equations."
        (core_size test - core_size core) ;*)
      if approximate || (z3_used && not !has_timeout)
      then Some (core_union keep core)
      else
        if is_empty_core core
        then Some keep
        else begin
          let (scope, symb, test) = pick_core core in
          begin match minimize check keep test with
          | None -> minimize check ~skip_first_check:true
            (core_union (ScMap.singleton scope [symb]) keep) test
          | Some res -> Some res
          end
        end
  in

  let terms_of_current_state keep test =
    let aux with_act init core =
      ScMap.mapi (fun s lst -> List.map 
        (fun a ->
          let eq = eq_of_actlit ~with_act:with_act a in
          term_of_eq init (Scope.equal s scope) eq
        )
        lst)
        core
    in
    let keep_init = aux false true keep in
    let keep_trans = aux false false keep in
    let test_init = aux true true test in
    let test_trans = aux true false test in
    let init = lstmap_union keep_init test_init
    |> ScMap.map (fun t -> Term.mk_and t) in
    let trans = lstmap_union keep_trans test_trans
    |> ScMap.map (fun t -> Term.mk_and t) in
    (init, trans)
  in

  let core_to_eqmap core =
    ScMap.map (fun v -> List.map eq_of_actlit v) core
  in

  let check approximate keep test =
    KEvent.log L_info "Minimizing using an UNSAT core... (%i left)" (core_size test) ;
    let (init, trans) = terms_of_current_state keep test in
    check_k_inductive ~approximate:approximate sys test init trans prop os_prop k
  in
  match minimize check keep test with
  | None -> raise NotKInductive
  | Some core -> core_to_eqmap core

let ivc_uc in_sys ?(approximate=false) sys =
  try (
    let eqmap = ivc_uc_ in_sys ~approximate:approximate sys in
    Some (eqmap_to_ivc in_sys eqmap)
  ) with
  | NotKInductive ->
    KEvent.log L_error "Properties are not k-inductive." ;
    None
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)\n" i t ;
    None

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

let is_empty_eqmap = is_empty_core
let eqmap_size = core_size
let pick_eqmap = pick_core

exception CannotProve

(** Implements the algorithm IVC_BF *)
let ivc_bf_ in_sys param analyze sys eqmap =
  let param = Analysis.param_clone param in
  let sys = TS.copy sys in
  let prop_names = extract_props_names sys in
  let modules = Flags.enabled () in

  let (keep, test) = separate_eqmap_by_category in_sys eqmap in

  (* Minimization *)
  let rec minimize ?(skip_first_check=false) check keep test =
    if skip_first_check || check keep test then
      if is_empty_eqmap test
      then Some keep
      else
        let (scope, eq, test) = pick_eqmap test in
        match minimize check keep test with
        | None ->
          minimize ~skip_first_check:true check (lstmap_union (ScMap.singleton scope [eq]) keep) test
        | Some res -> Some res
    else None
  in

  let prepare_ts_for_check keep test =
    reset_ts prop_names sys ;
    let union = lstmap_union keep test in
    let prepare_subsystem sys =
      let scope = TS.scope_of_trans_sys sys in
      let eqs =
        try Some (ScMap.find scope union)
        with Not_found -> if Flags.IVC.ivc_enter_nodes () then Some [] else None
      in
      begin match eqs with
      | None -> ()
      | Some eqs ->
        let init_eq = List.map (fun eq -> eq.init_opened) eqs
        |> Term.mk_and in
        let trans_eq = List.map (fun eq -> eq.trans_opened) eqs
        |> Term.mk_and in
        TS.set_init_trans sys init_eq trans_eq 
      end
    in
    TS.iter_subsystems ~include_top:true prepare_subsystem sys
  in
  let check keep test =
    KEvent.log L_info "Minimizing using bruteforce... (%i left)" (eqmap_size test) ;
    prepare_ts_for_check keep test ;
    let old_log_level = Lib.get_log_level () in
    Lib.set_log_level L_off ;
    analyze false modules in_sys param sys ;
    Lib.set_log_level old_log_level;
    check_result prop_names sys
  in

  begin match minimize check keep test with
  | None -> raise CannotProve
  | Some eqmap -> eqmap
  end

let ivc_bf in_sys param analyze sys =
  try (
    let eqmap = _all_eqs in_sys sys in
    let eqmap = ivc_bf_ in_sys param analyze sys eqmap in
    Some (eqmap_to_ivc in_sys eqmap)
  ) with
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)\n" i t ;
    None
  | CannotProve ->
    KEvent.log L_error "Cannot prove the properties." ;
    None

(** Implements the algorithm IVC_UCBF *)
let ivc_ucbf in_sys param analyze sys =
  try (
    let eqmap = ivc_uc_ in_sys sys in
    let eqmap = ivc_bf_ in_sys param analyze sys eqmap in
    Some (eqmap_to_ivc in_sys eqmap)
  ) with
  | NotKInductive ->
    KEvent.log L_error "Properties are not k-inductive." ;
    None
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)\n" i t ;
    None
  | CannotProve ->
    KEvent.log L_error "Cannot prove the properties." ;
    None

(* ---------- AUTOMATED DEBUGGING ---------- *)

let actsvs_of_core = actlits_of_core

let filter_core core actsvs =
  let actsvs = SVSet.of_list actsvs in
  ScMap.map (fun lst -> SVSet.of_list lst |> SVSet.inter actsvs |> SVSet.elements) core

let eq_of_actsv actsv_eqs_map ?(with_act=false) sv =
  let eq = SVMap.find sv actsv_eqs_map in
  if with_act
  then
    let guard t =
      (* Term.mk_eq *)
      Term.mk_implies [Term.mk_not (Term.mk_var (Var.mk_const_state_var sv)) ; t]
    in
    { init_opened=guard eq.init_opened ; init_closed=guard eq.init_closed ;
      trans_opened=guard eq.trans_opened ; trans_closed=guard eq.trans_closed }
  else eq

let get_counterexample_actsvs prop_names sys actsvs =
  let rec aux = function
  | [] -> None
  | p::prop_names ->
    begin match TS.get_prop_status sys p with
      | Property.PropFalse cex ->
        let svs = SVSet.of_list actsvs in
        cex
        |> List.filter (fun (sv, values) -> SVSet.mem sv svs)
        |> List.filter (fun (_, values) -> match List.hd values with
            | Model.Term t -> Term.equal t (Term.mk_true ())
            | _ -> false
            )
        |> List.map fst
        |> (fun x -> Some x)
      | _ -> aux prop_names
    end
  in
  aux prop_names

let exactly_k_true svs k =
  let cptl = svs
  |> List.map (fun sv -> Term.mk_var (Var.mk_const_state_var sv))
  |> List.map (fun t -> Term.mk_ite t (Term.mk_num_of_int 1) (Term.mk_num_of_int 0))
  in
  let sum = Term.mk_plus cptl in
  Term.mk_eq [sum; Term.mk_num_of_int k]

let at_least_one_false svs =
  svs
  |> List.map (fun sv -> Term.mk_not (Term.mk_var (Var.mk_const_state_var sv)))
  |> Term.mk_or

let compute_cs check_ts sys prop_names actsvs_eqs_map keep test k already_found =
  let eq_of_actsv = eq_of_actsv actsvs_eqs_map in
  let actsvs = actsvs_of_core test in

  let not_already_found =
    already_found
    |> List.map at_least_one_false
    |> Term.mk_and
  in

  let prepare_ts_for_check keep test =
    reset_ts prop_names sys ;
    let prepare_subsystem sys =
      let scope = TS.scope_of_trans_sys sys in
      let keep_actsvs =
        try Some (ScMap.find scope keep)
        with Not_found -> if Flags.IVC.ivc_enter_nodes () then Some [] else None
      in
      let test_actsvs =
        try Some (ScMap.find scope test)
        with Not_found -> if Flags.IVC.ivc_enter_nodes () then Some [] else None
      in
      let actsvs =
        match keep_actsvs, test_actsvs with
        | None, None -> None
        | Some k, None -> Some (k, [])
        | None, Some t -> Some ([], t)
        | Some k, Some t -> Some (k, t)
      in
      begin match actsvs with
      | None -> ()
      | Some (ks,ts) ->
        let eqs =
          (List.map (fun k -> eq_of_actsv ~with_act:false k) ks) @
          (List.map (fun t -> eq_of_actsv ~with_act:true t) ts)
        in
        let init_eq = List.map (fun eq -> eq.init_opened) eqs
        |> Term.mk_and in
        let trans_eq = List.map (fun eq -> eq.trans_opened) eqs
        |> Term.mk_and in
        TS.set_init_trans sys init_eq trans_eq 
      end
    in
    TS.iter_subsystems ~include_top:true prepare_subsystem sys ;
    let (_,init_eq,trans_eq) = TS.init_trans_open sys in
    let init_eq =
      Term.mk_and ((exactly_k_true actsvs k) (* Cardinality constraint *)
      ::not_already_found            (* 'Not already found' constraint *)
      ::(deconstruct_conj init_eq)) in
    TS.set_init_trans sys init_eq trans_eq
  in

  KEvent.log L_info "Computing a correction set using automated debugging..." ;
  prepare_ts_for_check keep test ;
  let old_log_level = Lib.get_log_level () in
  Lib.set_log_level L_off ;
  check_ts sys ;
  Lib.set_log_level old_log_level;
  match get_counterexample_actsvs prop_names sys actsvs with
  | None -> None
  | Some actsvs ->
    assert (List.length actsvs = k) ;
    Some (filter_core test actsvs)

let compute_all_cs check_ts sys prop_names actsvs_eqs_map keep test k =
  let rec aux acc already_found =
    match compute_cs
      check_ts sys prop_names actsvs_eqs_map keep test k already_found with
    | None -> acc
    | Some core -> aux (core::acc) (actsvs_of_core core::already_found)
  in
  aux [] []

let compute_mcs check_ts sys prop_names actsvs_eqs_map keep test =
  ()

let compute_all_mcs check_ts sys prop_names actsvs_eqs_map keep test =
  ()

(* ---------- UMIVC ---------- *)

let actsvs_counter =
  let last = ref 0 in
  (fun () -> last := !last + 1 ; !last)

let fresh_actsv_name () =
  Printf.sprintf "__umivc_%i" (actsvs_counter ())

let umivc in_sys param analyze sys k =

  let param = Analysis.param_clone param in
  let sys = TS.copy sys in
  let prop_names = extract_props_names sys in
  let modules = Flags.enabled () in
  let check_ts = analyze false modules in_sys param in

  (* Activation litterals, core and mapping to equations *)
  let add_to_bindings act_bindings sys =
    let eqs = extract_toplevel_equations in_sys sys in
    let scope = TS.scope_of_trans_sys sys in
    let act_bindings' =
      List.map (fun eq ->
      let actsv =
        StateVar.mk_state_var ~is_input:false ~is_const:true
        (fresh_actsv_name ()) [] (Type.mk_bool ()) in
      (actsv, scope, eq)
    ) eqs in
    act_bindings'@act_bindings
  in
  let act_bindings =
    if Flags.IVC.ivc_enter_nodes ()
    then TS.fold_subsystems ~include_top:false (add_to_bindings) [] sys
    else []
  in
  let act_bindings = add_to_bindings act_bindings sys in

  let actsvs_eqs_map =
    List.fold_left (fun acc (k,_,v) -> SVMap.add k v acc)
      SVMap.empty act_bindings
  in

  let add_to_core (keep, test) (actsv,scope,eq) =
    if should_minimize_equation in_sys eq
    then
      let old = try ScMap.find scope test with Not_found -> [] in
      (keep, ScMap.add scope (actsv::old) test)
    else
      let old = try ScMap.find scope keep with Not_found -> [] in
      (ScMap.add scope (actsv::old) keep, test)
  in
  let (keep,test) = List.fold_left add_to_core (ScMap.empty,ScMap.empty) act_bindings in

  (* Add actsvs to the transition system (at top level) *)
  let actsvs = actsvs_of_core test in
  List.iter (fun sv -> TS.add_global_const sys (Var.mk_const_state_var sv)) actsvs ;

  (* Test *)
  let n = List.length actsvs in
  for k=0 to n do
    let css = compute_all_cs check_ts sys prop_names actsvs_eqs_map keep test k in
    KEvent.log_uncond "Number of CS for k=%n : %n" k (List.length css)
  done ;
  []
