(* This file is part of the Kind 2 model checker.

   Copyright (c) 2019-2020 by the Board of Trustees of the University of Iowa

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

open ModelElement

module TS = TransSys
module ScMap = Scope.Map
module SVSet = StateVar.StateVarSet

module Position = struct
  type t = Lib.position
  let compare = Lib.compare_pos
end
module PosMap = Map.Make(Position)
module PosSet = Set.Make(Position)

module A = LustreAst
module H = LustreAstHelpers

module AstID = struct
  type t = A.ident
  let compare = compare
end

module IdMap = Map.Make(AstID)

type 'a result =
| Solution of 'a
| NoSolution
| Error of string

type 'a analyze_func =
    bool -> bool ->
    Lib.kind_module list ->
    'a InputSystem.t ->
    Analysis.param ->
    TransSys.t ->
    unit

type counterexample = (StateVar.t * Model.value list) list

type additional_info = {
  approximation: bool
}

(* Represents an Inductive Validity Core. The first element correspond to the properties
   for whch the IVC has been computed, and the second element is the core (= set of equations) itself. *)
type ivc = Property.t list * loc_core * additional_info

(* Represents a Maximal Unsafe Abstraction (or, depending on the context, a Minimal Correction Set).
   The first element is a tuple that indicates a property that is unsatisfied by the core,
   together with the corresponding counterexample.
   The second element is the core (= set of equations) itself. *)
type mcs = (Property.t * counterexample) * loc_core * additional_info

(* ---------- PRETTY PRINTING ---------- *)

let is_ivc_approx (_,_, {approximation}) = approximation
let is_mcs_approx (_,_, {approximation}) = approximation

let ivc_to_print_data in_sys sys core_class time (_,loc_core,info) =
  let cpd = loc_core_to_print_data in_sys sys core_class time loc_core in
  attach_approx_to_print_data cpd info.approximation

let mcs_to_print_data in_sys sys core_class time ((prop, cex), loc_core, info) =
  let cpd = loc_core_to_print_data in_sys sys core_class time loc_core in
  let cpd = attach_property_to_print_data cpd prop in
  let cpd = attach_counterexample_to_print_data cpd cex in
  attach_approx_to_print_data cpd info.approximation

let pp_print_mcs_legacy in_sys param sys ((prop, cex), core, _) (_, core_compl, _) =
  let prop_name = prop.Property.prop_name in
  let sys = TS.copy sys in
  let wa_model =
    all_wa_names_of_loc_core core_compl
    |>  List.map (fun str -> (str, true))
  in
  let wa_model' =
      all_wa_names_of_loc_core core
    |>  List.map (fun str -> (str, false))
  in
  TS.set_prop_unknown sys prop_name ;
  let wa_model = wa_model@wa_model' in
  KEvent.cex_wam cex wa_model in_sys param sys prop_name

let pp_print_no_mcs_legacy prop sys =
  let prop_name = prop.Property.prop_name in
  let sys = TS.copy sys in

  match prop.Property.prop_status with
  | PropInvariant cert ->
    TS.set_prop_unknown sys prop_name ;
    KEvent.proved_wam cert sys prop_name
  | _ -> KEvent.unknown_wam sys prop_name


let timeout = ref false

let print_timeout_warning () =
  timeout := true ;
  KEvent.log L_warn "An analysis has timeout..."

let print_uc_error_note () =
  KEvent.log L_note "Cannot solve the UNSAT core..."

(* ---------- LUSTRE AST ---------- *)

let counter =
  let last = ref 0 in
  (fun () -> last := !last + 1 ; !last)

let dpos = Lib.dummy_pos
let dspan = { A.start_pos = dpos; A.end_pos = dpos }
let rand_fun_ident nb = "__rand"^(string_of_int nb)
let new_rand_fun_ident () = rand_fun_ident (counter ())

let max_nb_args = ref 0
let rand_functions = Hashtbl.create 10
let previous_rands = Hashtbl.create 10

let rec unannot_pos = function
  | A.TVar (_, i) -> A.TVar (dpos, i)
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
  | A.AbstractType (_, id) -> A.AbstractType (dpos,id)
  | A.TupleType (_,ts) -> A.TupleType (dpos, List.map unannot_pos ts)
  | A.GroupType (_,ts) -> A.GroupType (dpos, List.map unannot_pos ts)
  | A.RecordType (_,tids) ->
    let aux (_,id,t) = (dpos,id,unannot_pos t) in
    A.RecordType (dpos,List.map aux tids)
  | A.ArrayType (_,(t,e)) -> A.ArrayType (dpos,(unannot_pos t,e))
  | A.EnumType (_,id,ids) -> A.EnumType (dpos,id,ids)
  | A.TArr (_, a_ty, r_ty) -> A.TArr (dpos, a_ty, r_ty)
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
  let pos = H.pos_of_expr expr in
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
        A.Call(*Param*)
          (pos, rand_function_name_for n typ, (*typ,*) [Const (dpos, Num (string_of_int i))])
      end else begin
        try Hashtbl.find previous_rands svs
        with Not_found ->
          let i = counter () in
          let n = (List.length typ) in
          if n > !max_nb_args then max_nb_args := n ;
          let res = A.Call(*Param*)
            (pos, rand_function_name_for n typ, (*typ,*) [Const (dpos, Num (string_of_int i))])
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
  A.NodeDecl (dspan,
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
  A.NodeDecl (dspan,
    (name, true, [], [dpos,"id",A.Int dpos,A.ClockTrue, false],
    outs, [], [], None)
  )

let nodes_input_types = Hashtbl.create 10
let rec minimize_node_call_args ue lst expr =
  let minimize_arg ident i arg =
    match arg with
    | A.Ident _ | A.ModeRef _ | A.RecordProject _ | A.TupleProject _ -> arg
    | _ ->
      let t = Hashtbl.find nodes_input_types ident |> (fun lst -> List.nth lst i) in
      let (_, expr) = minimize_expr ue lst [t] arg in
      expr
  in
  let rec aux expr =
    match expr with
    | A.Const _ | A.Ident _ | A.ModeRef _ | A.Last _
    -> expr
    | A.Call (pos, ident, args) ->
      A.Call (pos, ident, List.mapi (minimize_arg ident) args)
    | A.CallParam (pos, ident, ts, args) ->
      A.CallParam (pos, ident, ts, List.mapi (minimize_arg ident) args)
    | A.RecordProject (p,e,i) -> A.RecordProject (p,aux e,i)
    | A.TupleProject (p,e1,e2) -> A.TupleProject (p,aux e1, e2)
    | A.StructUpdate (p,e1,ls,e2) -> A.StructUpdate (p,aux e1,ls,aux e2)
    | A.ConvOp (p,op,e) -> A.ConvOp (p,op,aux e)
    | A.GroupExpr (p,ge,es) -> A.GroupExpr (p,ge,List.map aux es)
    | A.ArrayConstr (p,e1,e2) -> A.ArrayConstr (p,aux e1,aux e2)
    | A.ArraySlice (p,e1,(e2,e3)) -> A.ArraySlice (p,aux e1,(aux e2,aux e3))
    | A.ArrayIndex (p,e1, e2) -> A.ArrayIndex (p,aux e1,aux e2)
    | A.ArrayConcat (p,e1,e2) -> A.ArrayConcat (p,aux e1,aux e2)
    | A.RecordExpr (p,id,lst) ->
      A.RecordExpr (p,id,List.map (fun (i,e) -> (i, aux e)) lst)
    | A.UnaryOp (p,op,e) -> A.UnaryOp (p,op,aux e)
    | A.BinaryOp (p,op,e1,e2) -> A.BinaryOp (p,op,aux e1,aux e2)
    | A.Quantifier (p,q,ids,e) -> A.Quantifier (p,q,ids,aux e)
    | A.NArityOp (p,op,es) -> A.NArityOp (p,op,List.map aux es)
    | A.TernaryOp (p,op,e1,e2,e3) -> A.TernaryOp (p,op,aux e1,aux e2,aux e3)
    | A.CompOp (p,op,e1,e2) -> A.CompOp (p,op,aux e1,aux e2)
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
    | A.Const _ | A.Ident _ | A.ModeRef _ | A.Last _
      -> false
    | A.Call (_, _, args) | A.CallParam (_, _, _, args) ->
      List.map aux args
      |> List.exists (fun x -> x)
    | A.ConvOp (_,_,e) | A.UnaryOp (_,_,e) | A.RecordProject (_,e,_)
      | A.TupleProject (_,e,_) | A.Quantifier (_,_,_,e)
      | A.When (_,e,_) | A.Current (_,e) | A.Pre (_,e) ->
      aux e
    | A.StructUpdate (_,e1,_,e2) | A.ArrayConstr (_,e1,e2)
      | A.ArrayConcat (_,e1,e2) | A.ArrayIndex (_,e1,e2) 
      | A.BinaryOp (_,_,e1,e2) | A.CompOp (_,_,e1,e2) | A.Fby (_,e1,_,e2)
      | A.Arrow (_,e1,e2) -> aux e1 || aux e2
    | A.GroupExpr (_,_,es) | A.NArityOp (_,_,es) ->
      List.map aux es
      |> List.exists (fun x -> x)
    | A.ArraySlice (_,e1,(e2,e3)) | A.TernaryOp (_,_,e1,e2,e3) ->
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
    PosSet.mem (H.pos_of_expr expr) all_pos
  in
  if ast_contains keep_expr expr
  then (false, minimize_node_call_args ue lst expr)
  else (true, ue typ expr)

let tyof_lhs id_typ_map lhs =
  let A.StructDef (pos, items) = lhs in
  let aux = function
  | A.SingleIdent (_,id) as e -> [e, IdMap.find id id_typ_map]
  | A.ArrayDef (pos,id,_) -> [A.SingleIdent (pos,id), IdMap.find id id_typ_map]
  | A.TupleStructItem _ | A.ArraySliceStructItem _ | A.FieldSelection _ | A.TupleSelection _
    -> assert false
  in
  let (items,typ) = List.map aux items |> List.flatten |> List.split in
  (A.StructDef (pos, items), typ)

let minimize_node_eq id_typ_map ue lst = function
  | A.Assert (pos, expr) when
    List.exists (fun p -> Lib.equal_pos p pos) lst ->
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
  | A.Assume (pos,_,_,_)
  | A.Guarantee (pos,_,_,_) ->
    if List.exists (fun p -> Lib.equal_pos p pos) lst
    then [cne] else []
  | A.Mode (pos,id,req,ens) ->
    let ens = ens |> List.filter
      (fun (pos,_,_) -> List.exists (fun p -> Lib.equal_pos p pos) lst)
    in
    [A.Mode (pos,id,req,ens)]

let minimize_node_decl ue loc_core
  ((id, extern, tparams, inputs, outputs, locals, items, spec) as ndecl) =

  let id_typ_map = build_id_typ_map inputs outputs locals in

  let minimize_with_lst lst =
    let items = List.map (minimize_item id_typ_map ue lst) items |> List.flatten in
    let spec = 
    begin match spec with
      | None -> None
      | Some spec -> List.map (minimize_contract_node_eq ue lst) spec 
      |> List.flatten |> (fun s -> if s = [] then None else Some s)
    end
    in
    let locals = List.map (minimize_node_local_decl ue lst) locals in
    (id, extern, tparams, inputs, outputs, locals, items, spec)
  in
  
  let scope = (Scope.mk_scope [id]) in
  if List.exists (fun sc -> Scope.equal sc scope) (scopes_of_loc_core loc_core)
  then (
    get_model_elements_of_scope loc_core scope
    |> List.map get_positions_of_model_element
    |> List.flatten |> minimize_with_lst
  )
  else (
    if Flags.IVC.ivc_only_main_node ()
    then ndecl
    else minimize_with_lst []
  )

let minimize_contract_decl ue loc_core (id, tparams, inputs, outputs, body) =
  let lst = scopes_of_loc_core loc_core
    |> List.map (get_model_elements_of_scope loc_core)
    |> List.flatten
    |> List.map get_positions_of_model_element
    |> List.flatten
  in
  let body = body
    |> List.map (minimize_contract_node_eq ue lst)
    |> List.flatten
  in
  let body = if body = []
    then [A.Guarantee (dpos, None, false, A.Const(dpos, A.True))]
    else body
  in
  (id, tparams, inputs, outputs, body)

let minimize_decl ue loc_core = function
  | A.NodeDecl (span, ndecl) ->
    A.NodeDecl (span, minimize_node_decl ue loc_core ndecl)
  | A.FuncDecl (span, ndecl) ->
    A.FuncDecl (span, minimize_node_decl ue loc_core ndecl)
  | A.ContractNodeDecl (span, cdecl) ->
    A.ContractNodeDecl (span, minimize_contract_decl ue loc_core cdecl)
  | decl -> decl 

let fill_input_types_hashtbl ast =
  let aux_node_decl (id, _, _, inputs, _, _, _, _) =
    let typ_of_input (_,_,t,_,_) = t in
    Hashtbl.replace nodes_input_types id (List.map typ_of_input inputs) ;
  in
  let aux_decl = function
  | A.NodeDecl (_, ndecl) | A.FuncDecl (_, ndecl) -> aux_node_decl ndecl
  | _ -> ()
  in
  List.iter aux_decl ast

let minimize_lustre_ast ?(valid_lustre=false) in_sys (_,loc_core,_) ast =
  fill_input_types_hashtbl ast ;
  let undef_expr =
    if valid_lustre
    then
      (* We construct a map that associate to each position a list of state vars
          that correspond to the state vars characterizing this position (if any) *)
      let pos_sv_map = List.fold_left
      (fun acc node ->
        List.fold_left
        (fun acc sv ->
          List.fold_left
          (fun acc def ->
            let pos = LustreNode.pos_of_state_var_def def in
            let old = try PosMap.find pos acc with Not_found -> SVSet.empty in
            PosMap.add pos (SVSet.add sv old) acc
          )
          acc (LustreNode.get_state_var_defs sv)
        )
        acc (LustreNode.get_all_state_vars node)
      ) PosMap.empty (InputSystem.retrieve_lustre_nodes in_sys) in
      undef_expr (Some pos_sv_map)
    else undef_expr None in
  let minimized = List.map (minimize_decl undef_expr loc_core) ast in

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

(* ---------- UTILITIES ---------- *)

(*
let rec simplify_term t =
  let open Term.T in
  match Term.destruct t with
    (* Rewrite v1 /\ v1 = t into t *)
    | App (s, [t1 ; t2]) when Symbol.equal_symbols s (Symbol.s_and) ->
      begin match (Term.destruct t1, Term.destruct t2) with
      | (Var v, App (s, [t1 ; t2])) when Symbol.equal_symbols s (Symbol.s_eq) ->
        begin match Term.destruct t1 with
        | Var v' when Var.equal_vars v v' -> t2
        | _ -> t
        end
      | _ -> t
      end
    | _ -> t
*)

let rec interval imin imax =
  if imin > imax then []
  else imin::(interval (imin+1) imax)

let make_ts_analyzer in_sys ?(stop_after_disprove=true) ?(no_copy=false) param analyze sys =
  let param = Analysis.param_clone param in
  let sys = if no_copy then sys else TS.copy sys in
  let modules = Flags.enabled () in
  sys, (fun sys -> analyze false stop_after_disprove modules in_sys param sys)

let props_names props =
  List.map (fun { Property.prop_name = n } -> n) props

let props_terms props =
  List.map (fun { Property.prop_term = p } -> p) props

let props_term props =
  props_terms props |> Term.mk_and

let extract_all_props_names sys =
  List.map (fun { Property.prop_name = n } -> n) (TS.get_properties sys)

let separate_loc_core_by_category scope cats =
  filter_loc_core_by_categories scope cats

let separate_ivc_by_category scope (props, core, info) =
  let (core1, core2) = separate_loc_core_by_category scope (Flags.IVC.ivc_category ()) core
  in (props, core1, info), (props, core2, info)

let separate_mcs_by_category scope (data, core, info) =
  let (core1, core2) = separate_loc_core_by_category scope (Flags.MCS.mcs_category ()) core
  in (data, core1, info), (data, core2, info)

let complement_of_ivc in_sys sys (props, core, info) =
  let only_top_level = Flags.IVC.ivc_only_main_node () in
  loc_core_diff (full_loc_core_for_sys in_sys sys ~only_top_level) core
  |> (fun x -> (props, x, info))

let complement_of_mcs in_sys sys (props_cex, core, info) =
  let only_top_level = Flags.MCS.mcs_only_main_node () in
  loc_core_diff (full_loc_core_for_sys in_sys sys ~only_top_level) core
  |> (fun x -> (props_cex, x, info))

let reset_ts enter_nodes sys =
  let set_props_unknown sys =
    List.iter
      (fun str -> TS.set_prop_unknown sys str)
      (extract_all_props_names sys)
  in
  if enter_nodes
  then (
    TS.clear_all_invariants sys ;
    TS.iter_subsystems ~include_top:true set_props_unknown sys
  )
  else (
    TS.clear_invariants sys ;
    set_props_unknown sys
  )

let remove_other_props sys prop_names =
  let aux prop_names acc sys =
    let props = TS.get_properties sys in
    let aux prop =
      let name = prop.Property.prop_name in
      List.exists (fun n -> n = name) prop_names
    in
    List.filter aux props
    |> TS.set_subsystem_properties acc (TS.scope_of_trans_sys sys)
  in
  let sys = TS.fold_subsystems ~include_top:false (aux []) sys sys
  in aux prop_names sys sys

let add_as_candidate os_invs sys =
  let _cnt = ref 0 in
  let cnt () =
    _cnt := !_cnt + 1 ;
    !_cnt
  in
  let create_candidate t =
    Property.{
      prop_name = Format.sprintf "%%inv_%i" (cnt ()) ;
      prop_source = Property.Candidate None ;
      prop_term = t ;
      prop_status = PropUnknown
    }
  in
  let props = List.map create_candidate os_invs in
  let props = props @ (TS.get_properties sys) in
  TS.set_subsystem_properties sys (TS.scope_of_trans_sys sys) props

let actlits_of_core core =
  let aux acc scope =
    (get_actlits_of_scope core scope)@acc
  in
  List.fold_left aux [] (scopes_of_core core)

let actsvs_of_core core =
  actlits_of_core core
  |> List.map (get_sv_of_actlit core)

let term_of_scope term_map scope =
  try ScMap.find scope term_map with Not_found -> Term.mk_true ()

let is_empty_core c = (core_size c) = 0

let lstmap_union scmap1 scmap2 =
  let merge _ lst1 lst2 = match lst1, lst2 with
  | None, None -> None
  | Some lst, None | None, Some lst -> Some lst
  | Some lst1, Some lst2 -> Some (lst1@lst2)
  in
  ScMap.merge merge scmap1 scmap2

let generate_initial_cores in_sys sys enter_nodes cats =
  timeout := false ;
  let full_loc_core = full_loc_core_for_sys in_sys sys ~only_top_level:(not enter_nodes) in
  let scope = TransSys.scope_of_trans_sys sys in
  let (test, keep) = separate_loc_core_by_category scope cats full_loc_core in
  (loc_core_to_new_core keep, loc_core_to_new_core test)

let pick_element_of_core core =
  match pick_element_of_core core with
  | None -> assert false
  | Some r -> r

(* ---------- MCS COMPUTATION ---------- *)

let eq_of_actlit core ?(with_act=false) actlit =
  let eq = get_ts_equation_of_actlit core actlit in
  if with_act
  then
    let sv = get_sv_of_actlit core actlit in
    let guard t =
      (* Term.mk_eq *)
      Term.mk_implies [Term.mk_not (Term.mk_var (Var.mk_const_state_var sv)) ; t]
    in
    { init_opened=guard eq.init_opened ; init_closed=guard eq.init_closed ;
      trans_opened=guard eq.trans_opened ; trans_closed=guard eq.trans_closed }
  else eq

let is_model_value_true = function
  | Model.Term t -> Term.equal t (Term.mk_true ())
  | _ -> false

let get_counterexample_actsvs prop_names sys actsvs =
  let rec aux = function
  | [] ->
    if List.for_all (fun p ->
      match TS.get_prop_status sys p with
      | Property.PropInvariant _ -> true
      | _ -> false) prop_names
    then None
    else (print_timeout_warning () ; None)
  | p::prop_names ->
    begin match TS.get_prop_status sys p with
      | Property.PropFalse cex ->
        let svs = SVSet.of_list actsvs in
        cex
        |> List.filter (fun (sv, values) -> SVSet.mem sv svs)
        |> List.filter (fun (_, values) ->
              is_model_value_true (List.hd values)
            )
        |> List.map fst
        |> (fun x -> Some (x, (p,cex)))
      | _ -> aux prop_names
    end
  in
  aux prop_names

let get_counterexamples_actsvs prop_names sys actsvs =
  let rec aux = function
  | [] -> []
  | p::prop_names ->
    begin match TS.get_prop_status sys p with
      | Property.PropFalse cex ->
        let svs = SVSet.of_list actsvs in
        cex
        |> List.filter (fun (sv, values) -> SVSet.mem sv svs)
        |> List.filter (fun (_, values) ->
              is_model_value_true (List.hd values)
            )
        |> List.map fst
        |> (fun x -> (x, (p,cex))::(aux prop_names))
      | _ -> aux prop_names
    end
  in
  aux prop_names

let exactly_k_true svs k =
  let cptl = svs
  |> List.map (fun sv -> Term.mk_var (Var.mk_const_state_var sv))
  |> List.map (fun t -> Term.mk_ite t (Term.mk_num_of_int 1) (Term.mk_num_of_int 0))
  in
  let sum =
    match cptl with
    | [] -> Term.mk_num_of_int 0
    | _ -> Term.mk_plus cptl
  in
  Term.mk_eq [sum; Term.mk_num_of_int k]

let at_most_k_true svs k =
  let cptl = svs
  |> List.map (fun sv -> Term.mk_var (Var.mk_const_state_var sv))
  |> List.map (fun t -> Term.mk_ite t (Term.mk_num_of_int 1) (Term.mk_num_of_int 0))
  in
  let sum =
    match cptl with
    | [] -> Term.mk_num_of_int 0
    | _ -> Term.mk_plus cptl
  in
  Term.mk_leq [sum; Term.mk_num_of_int k]

let at_least_one_false svs =
  svs
  |> List.map (fun sv -> Term.mk_not (Term.mk_var (Var.mk_const_state_var sv)))
  |> Term.mk_or

let at_least_one_true svs =
  svs
  |> List.map (fun sv -> Term.mk_var (Var.mk_const_state_var sv))
  |> Term.mk_or

let prepare_ts_for_cs_check sys enter_nodes init_consts keep test =
  let eq_of_actlit = eq_of_actlit (core_union keep test) in
  let main_scope = TS.scope_of_trans_sys sys in
  reset_ts enter_nodes sys ;
  let prepare_subsystem acc sys =
    let scope = TS.scope_of_trans_sys sys in
    let (keep_actlits, test_actlits) =
      if enter_nodes || Scope.equal scope main_scope
      then (Some (get_actlits_of_scope keep scope),
            Some (get_actlits_of_scope test scope))
      else (None, None)
    in
    let actlits =
      match keep_actlits, test_actlits with
      | None, None -> None
      | Some k, None -> Some (k, [])
      | None, Some t -> Some ([], t)
      | Some k, Some t -> Some (k, t)
    in
    begin match actlits with
    | None -> acc
    | Some (ks,ts) ->
      let eqs =
        (List.map (fun k -> eq_of_actlit ~with_act:false k) ks) @
        (List.map (fun t -> eq_of_actlit ~with_act:true t) ts)
      in
      let init_eq = List.map (fun eq -> eq.init_opened) eqs
      |> Term.mk_and in
      let trans_eq = List.map (fun eq -> eq.trans_opened) eqs
      |> Term.mk_and in
      TS.set_subsystem_equations acc scope init_eq trans_eq
    end
  in
  let sys = TS.fold_subsystems ~include_top:true prepare_subsystem sys sys in
  let (_,init_eq,trans_eq) = TS.init_trans_open sys in
  let init_eq =
    Term.mk_and (List.rev_append init_consts [init_eq])
  in
  TS.set_subsystem_equations sys (TS.scope_of_trans_sys sys) init_eq trans_eq


let compute_cs_aux check_ts sys prop_names enter_nodes keep test k ?(exact_card=true) already_found =
  let actsvs = actsvs_of_core test in

  let not_already_found =
    already_found
    |> List.map at_least_one_false
    |> Term.mk_and
  in

  let init_consts =
    [
      not_already_found;         (* 'Not already found' constraint *)
      (if exact_card then exactly_k_true actsvs k else at_most_k_true actsvs k) (* Cardinality constraint *)
    ]
  in
  let sys = prepare_ts_for_cs_check sys enter_nodes init_consts keep test in
  let old_log_level = Lib.get_log_level () in
  Format.print_flush () ;
  Lib.set_log_level L_off ;
  check_ts sys ;
  Lib.set_log_level old_log_level;
  (sys, actsvs)

let compute_cs check_ts sys prop_names enter_nodes keep test k ?(exact_card=true) already_found =
  let (sys, actsvs) =
    compute_cs_aux check_ts sys prop_names enter_nodes keep test k ~exact_card already_found in
  match get_counterexample_actsvs prop_names sys actsvs with
  | None -> None
  | Some (actsvs, cex) ->
    assert (List.length actsvs <= k) ;
    Some (filter_core_svs actsvs test, cex)

let compute_approx_mcs_for_each_prop check_ts sys prop_names enter_nodes
  ?(max_mcs_cardinality= -1) keep test =
  KEvent.log L_info "Computing a correction set of maximal cardinality..." ;
  let n = core_size test in
  let n =
    if max_mcs_cardinality >= 0 && max_mcs_cardinality < n
    then max_mcs_cardinality
    else n
  in
  let (sys, actsvs) =
    compute_cs_aux check_ts sys prop_names enter_nodes keep test n ~exact_card:false [] in
  get_counterexamples_actsvs prop_names sys actsvs
  |> List.map (fun(actsvs, cex) ->
    assert (List.length actsvs <= n) ;
    (filter_core_svs actsvs test, cex)
  )

let compute_all_cs check_ts sys prop_names enter_nodes ?(cont=(fun _ -> ()))
  keep test k already_found =

  let rec aux acc already_found =
    match compute_cs
      check_ts sys prop_names enter_nodes keep test k already_found with
    | None -> acc
    | Some (core, cex) ->
      cont (core, cex) ;
      aux ((core, cex)::acc) (actsvs_of_core core::already_found)
  in
  aux [] already_found


let create_smt_solver logic =
  let solver = Flags.Smt.solver () in
  match solver with
  | `Z3_SMTLIB -> (
    SMTSolver.create_instance
      (TermLib.add_quantifiers logic)
      solver
  )
  | _ -> (
    failwith "Max-SMT is not supported by SMT solver or \
              implementation is not available"
  )

(* Computes a Minimal Cut Set that is minimal with respect to
   any solution whose associated counterexample has the same
   length than the counterexample provided ([cex]).
*)
let compute_local_cs sys prop_names enter_nodes cex keep test =
  let k = (Property.length_of_cex cex) - 1 in

  let num_k = Numeral.of_int k in

  let sys = prepare_ts_for_cs_check sys enter_nodes [] keep test in

  let solver = create_smt_solver (TS.get_logic sys) in
  TS.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero num_k;

  TS.init_of_bound None sys Numeral.zero
  |> SMTSolver.assert_term solver;
  for i = 0 to (k - 1) do
    TS.trans_of_bound None sys (Numeral.of_int (i+1))
    |> SMTSolver.assert_term solver
  done;

  let actsvs = actsvs_of_core test in

  let actsv_terms =
    List.map
      (fun sv -> Term.mk_var (Var.mk_const_state_var sv))
      actsvs
  in

  List.iter
    (fun t -> SMTSolver.assert_soft_term solver (Term.mk_not t) 1)
    actsv_terms;

  let props =
    TransSys.get_real_properties sys
    |> List.filter (fun p -> List.mem p.Property.prop_name prop_names)
  in

  let prop_conj =
    Term.mk_and (List.map (fun p -> p.Property.prop_term) props)
  in

  let prop_at_last_step =
    Term.bump_state num_k prop_conj
  in
  SMTSolver.assert_term solver (Term.negate prop_at_last_step);

  try (
    let sat = SMTSolver.check_sat solver in
    assert (sat);

    let model =
      (* SMTSolver.get_model solver *)
      SMTSolver.get_var_values
        solver
        (TransSys.get_state_var_bounds sys)
        (TransSys.vars_of_bounds sys Numeral.zero num_k)
    in

    let eval term =
      Eval.eval_term (TS.uf_defs sys) model term
      |> Eval.bool_of_value
    in

    let falsified_prop =
      try
        List.find
          (fun p ->
            let prop_at_last_step =
              Term.bump_state num_k p.Property.prop_term
            in
            not (eval prop_at_last_step)
          )
          props
      with Not_found ->
        assert false
    in

    (* Extract counterexample from solver *)
    let cex =
      Model.path_from_model
        (TS.state_vars sys) model num_k
      |> Model.path_to_list
    in

    let active_svs =
      List.combine actsvs actsv_terms
      |> List.filter (fun (sv, t) -> eval t)
      |> List.map fst
    in

    let core = filter_core_svs active_svs test in

    Some (core, (falsified_prop.Property.prop_name, cex))
  )
  with
  | SMTSolver.Unknown -> None

let compute_mcs check_ts sys prop_names enter_nodes ?(max_mcs_cardinality= -1)
  ?(initial_solution=None) ?(approx=false) keep test
=
  KEvent.log L_info "Computing a MCS..." ;
  let n = core_size test in
  let n =
    if max_mcs_cardinality >= 0 && max_mcs_cardinality < n
    then max_mcs_cardinality
    else n
  in
  let n = match initial_solution with
  | None -> n
  | Some (core, _) -> (core_size core) - 1 in
  if approx then (
    let sol =
      match initial_solution with
      | None -> compute_cs check_ts sys prop_names enter_nodes keep test n ~exact_card:false []
      | _ -> initial_solution
    in
    match sol with
    | None -> None
    | Some (_, (_, cex)) -> (
      match compute_local_cs sys prop_names enter_nodes cex keep test with
      | None -> sol
      | res -> res
    )
  )
  else (
    (* Increasing cardinality... *)
    (*let rec aux k =
      if k <= n
      then
        match compute_cs check_ts sys prop_names enter_nodes keep test k [] with
        | None -> aux (k+1)
        | Some res -> Some res
      else None
    in
    aux 0*)
    (* Decreasing cardinality... *)
    let rec aux k previous_res =
      if k >= 0
      then
        match compute_cs check_ts sys prop_names enter_nodes keep test k ~exact_card:false [] with
        | None -> previous_res
        | Some (core, cex) -> aux ((core_size core)-1) (Some (core, cex))
      else previous_res
    in
    aux n initial_solution
  )

let compute_all_mcs check_ts sys prop_names enter_nodes
  ?(max_mcs_cardinality= -1) ?(initial_solution=None) ?(cont=(fun _ -> ())) keep test =

  KEvent.log L_info "Computing all MCSs..." ;
  match compute_mcs check_ts sys prop_names enter_nodes
    ~max_mcs_cardinality ~initial_solution keep test with
  | None -> []
  | Some (res, res_cex) ->
    cont (res, res_cex) ;
    let n = core_size test in
    let n =
      if max_mcs_cardinality >= 0 && max_mcs_cardinality < n
      then max_mcs_cardinality
      else n
    in
    let k = core_size res in
    let rec aux acc already_found k =
      if k < n
      (* We do not need to go up to 'n', because if the whole set is a MCS, 
         then it will be found by the initial 'compute_mcs' call *)
      then
        let (new_mcs, cex) = compute_all_cs
          check_ts sys prop_names enter_nodes ~cont keep test k already_found
          |> List.split in
        let already_found = (List.map actsvs_of_core new_mcs)@already_found in
        aux ((List.combine new_mcs cex)@acc) already_found (k+1)
      else acc
    in
    aux [(res, res_cex)] [actsvs_of_core res] k

(* ---------- IVC_UC ---------- *)

let are_props_safe props =
  props |> List.for_all
  (function
  | { Property.prop_status = Property.PropInvariant _ } -> true
  | _ -> false)

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

let check_sat_assuming solver actlits =
  let act_terms = List.map Actlit.term_of_actlit actlits in
  SMTSolver.check_sat_assuming solver
    (fun _ -> true, [])
    (fun _ -> false, SMTSolver.get_unsat_core_lits solver)
    act_terms

let actlit_of_term t = match Term.destruct t with
    | Var _ -> assert false
    | Const s -> Symbol.uf_of_symbol s
    | App _ -> assert false

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

  let os_inv_eq = Term.bump_state (Numeral.of_int b0) os_inv_eq in
  let inv_eq =
    interval (b0+1) (b0+k)
    |> List.map (fun i -> Term.bump_state (Numeral.of_int i) inv_eq)
    |> (fun eqs -> os_inv_eq::eqs)
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
      (*KEvent.log_uncond "Compressor: %n" (List.length compressor) ;*)
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

type core_result = NOT_OK | OK of core

let compute_unsat_core ?(pathcomp=None) ?(approximate=false)
  sys enter_nodes core init_terms trans_terms bmin bmax t =

  let enable_compr = pathcomp <> None in
  let actlits = actlits_of_core core in
  let solver =
    create_solver ~pathcomp:enable_compr ~approximate:approximate
    sys actlits bmin bmax in

  (* Define non-top-level nodes *)
  if enter_nodes
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

  let check_sat =
    if actlits = []
    then (fun () -> SMTSolver.check_sat solver, [])
    else (fun () -> check_sat_assuming solver actlits)
  in
  let rec check () =
    let (sat, unsat_core) = check_sat () in
    if sat
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
      let res = unsat_core
      |> List.map actlit_of_term
      in OK (filter_core res core)
  in

  let res = check () in
  SMTSolver.delete_instance solver ;
  res

let check_k_inductive ?(approximate=false) sys enter_nodes core init_terms trans_terms prop os_prop k =
  (* In the functions above, k starts at 0 whereas it starts at 1 with Kind2 notation *)
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
        sys enter_nodes core init_terms trans_terms 0 bmax t in
    match res_base with
    | NOT_OK -> NOT_OK
    | OK core' ->
      let (bmax, t, pathcomp) = ind_k sys 0 trans_eq prop os_prop prop k in
      let bmax = bmax-1 in
      let t = Term.mk_not t in
      let res_ind =
        compute_unsat_core ~pathcomp:(Some pathcomp) ~approximate:approximate
          sys enter_nodes core init_terms trans_terms 0 bmax t in
      begin match res_ind with
      | NOT_OK -> NOT_OK
      | OK core'' -> OK (core_union core' core'')
      end
  else
    let (bmax, t, _) = k_induction sys 0 init_eq trans_eq prop os_prop k in
    let bmax = bmax-1 in
    let t = Term.mk_not t in
    compute_unsat_core ~approximate:approximate
      sys enter_nodes core init_terms trans_terms 0 bmax t

let eq_of_actlit core ?(with_act=false) a =
  let eq = get_ts_equation_of_actlit core a in
  if with_act
  then
    let guard t =
      (* Term.mk_eq *)
      Term.mk_implies [Actlit.term_of_actlit a ; t]
    in
    { init_opened=guard eq.init_opened ; init_closed=guard eq.init_closed ;
      trans_opened=guard eq.trans_opened ; trans_closed=guard eq.trans_closed }
  else eq

(** Implements the approximate algorithm (using Unsat Cores) *)
let ivc_uc_ in_sys ?(approximate=false) sys props enter_nodes keep test =

  let scope = TS.scope_of_trans_sys sys in
  let props = props_terms props in
  let k, invs = CertifChecker.minimize_invariants sys (Some props) None in
  let os_invs = List.filter (fun t -> CertifChecker.is_two_state t |> not) invs in
  let prop = Term.mk_and props in
  let os_prop = Term.mk_and (prop::os_invs) in
  let prop = Term.mk_and (prop::invs) in
  KEvent.log L_info "Inductive property: %a" Term.pp_print_term prop ;
  KEvent.log L_info "One-step inductive property: %a" Term.pp_print_term os_prop ;
  KEvent.log L_info "Value of k: %n" k ;

  let eq_of_actlit = eq_of_actlit (core_union keep test) in
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
          check approximate keep test
        with SMTSolver.Timeout -> (
          has_timeout := true ;
          NOT_OK
        )
    in
    match first_check with
    | NOT_OK -> (*KEvent.log_uncond "Not k-inductive." ;*) None 
    | OK core ->
      (*KEvent.log_uncond "UNSAT core eliminated %n equations."
        (core_size test - core_size core) ;*)
      if approximate || z3_used || is_empty_core core
      then Some (core_union keep core)
      else begin
        let (scope, actlit, test) = pick_element_of_core core in
        begin match minimize check keep test with
        | None -> minimize check ~skip_first_check:true
          (add_from_other_core core scope actlit keep) test
        | Some res -> Some res
        end
      end
  in

  let terms_of_current_state keep test =
    let aux with_act init core =
      List.fold_left (fun acc s ->
        let eqs =
          get_actlits_of_scope core s
          |> List.map 
            (fun a ->
              let eq = eq_of_actlit ~with_act:with_act a in
              term_of_ts_eq ~init ~closed:(Scope.equal s scope) eq
            )
        in
        ScMap.add s eqs acc
      ) ScMap.empty (scopes_of_core core) 
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

  let check approximate keep' test =
    let remaining = (core_size test) + 1 in
    let total = remaining + (core_size keep') in
    if not approximate && not z3_used
    then KEvent.log L_info "Minimizing using an UNSAT core... (%i elements in the IVC, %i checks left)" total remaining
    else KEvent.log L_info "Minimizing using an UNSAT core... (%i elements in the IVC)" total ;
    let (init, trans) = terms_of_current_state (core_union keep keep') test in
    check_k_inductive ~approximate:approximate sys enter_nodes test init trans prop os_prop k
  in
  let res = match minimize check empty_core test with
  | None ->
    if !has_timeout then test
    else (print_uc_error_note () ; test)
  | Some core ->
    (if !has_timeout
    then KEvent.log L_warn "The UNSAT core has timeout..."
    ) ; core
  in (os_invs, res)

let ivc_uc in_sys ?(approximate=false) sys props =
  try (
    let enter_nodes = Flags.IVC.ivc_only_main_node () |> not in
    let (keep, test) = generate_initial_cores in_sys sys enter_nodes (Flags.IVC.ivc_category ()) in
    let (_, test) = ivc_uc_ in_sys ~approximate:approximate sys props enter_nodes keep test in
    Solution (props, core_to_loc_core in_sys (core_union keep test), { approximation = true })
  ) with
  | CertifChecker.CouldNotProve _ ->
    if are_props_safe props
    then (KEvent.log L_error "Cannot reprove properties." ;
          Error "Cannot reprove properties")
    else NoSolution
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)" i t ;
    Error "Init and trans equations mismatch"

(* ---------- MUST SET ---------- *)

let must_set_ in_sys ?(uc_res=None) check_ts sys props enter_nodes keep test =

  (* If uc_res is None,
  we minimize using UC first and we retrieve the minimized invariants in the same time *)
  let (os_invs, reduced_test) =
  match uc_res with
  | Some (os_invs, reduced_test) -> (os_invs, reduced_test)
  | None -> ivc_uc_ in_sys sys props enter_nodes keep test
  in
  let increased_keep = core_diff (core_union keep test) reduced_test in

  let prop_names = props_names props in
  let sys = remove_other_props sys prop_names in
  let sys = add_as_candidate os_invs sys in

  (* Add actsvs to the CS transition system (at top level) *)
  let actsvs = actsvs_of_core reduced_test in
  let sys = List.fold_left (fun acc sv -> TS.add_global_constant acc (Var.mk_const_state_var sv)) sys actsvs in

  let core =
    compute_all_cs check_ts sys prop_names enter_nodes increased_keep reduced_test 1 []
    |> List.map fst
    |> List.fold_left core_union empty_core
  in
  (os_invs, core)

let must_set in_sys param analyze sys props =
  try (
    let enter_nodes = Flags.IVC.ivc_only_main_node () |> not in
    let (keep, test) = generate_initial_cores in_sys sys enter_nodes (Flags.IVC.ivc_category ()) in
    let (sys, check_ts) = make_ts_analyzer in_sys param analyze sys in
    let (_, must) = must_set_ in_sys check_ts sys props enter_nodes keep test in
    Solution (props, core_to_loc_core in_sys (core_union keep must), { approximation = !timeout })
  ) with
  | CertifChecker.CouldNotProve _ ->
    if are_props_safe props
    then (KEvent.log L_error "Cannot reprove properties." ;
          Error "Cannot reprove properties")
    else NoSolution
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)" i t ;
    Error "Init and trans equations mismatch"

(* ---------- IVC_BF ---------- *)

exception CannotProve

let check_result_safe prop_names sys =
  if
    List.for_all
      (fun str -> match TS.get_prop_status sys str with
      | Property.PropInvariant _ -> true
      | _ -> false)
      prop_names
  then true
  else if List.exists
      (fun str -> match TS.get_prop_status sys str with
      | Property.PropFalse _ -> true
      | _ -> false)
      prop_names
  then false
  else (print_timeout_warning () ; false)

let check_core check_ts sys prop_names enter_nodes core =
  let main_scope = TS.scope_of_trans_sys sys in
  let prepare_ts_for_check sys core =
    reset_ts enter_nodes sys ;
    let prepare_subsystem acc sys =
      let scope = TS.scope_of_trans_sys sys in
      let eqs =
        if enter_nodes || Scope.equal scope main_scope
        then Some (get_actlits_of_scope core scope |> List.map (get_ts_equation_of_actlit core))
        else None
      in
      begin match eqs with
      | None -> acc
      | Some eqs ->
        let init_eq = List.map (fun eq -> eq.init_opened) eqs
        |> Term.mk_and in
        let trans_eq = List.map (fun eq -> eq.trans_opened) eqs
        |> Term.mk_and in
        TS.set_subsystem_equations acc scope init_eq trans_eq 
      end
    in
    TS.fold_subsystems ~include_top:true prepare_subsystem sys sys
  in
  let check core =
    let sys = prepare_ts_for_check sys core in
    let old_log_level = Lib.get_log_level () in
    Format.print_flush () ;
    Lib.set_log_level L_off ;
    check_ts sys ;
    Lib.set_log_level old_log_level;
    check_result_safe prop_names sys
  in
  check core

(** Implements the bruteforce algorithm *)
let ivc_bf_ in_sys ?(os_invs=[]) check_ts sys props enter_nodes keep test =
  let prop_names = props_names props in
  let sys = remove_other_props sys prop_names in
  let sys = add_as_candidate os_invs sys in
  (* Minimization *)
  let rec minimize ?(skip_first_check=false) check keep test =
    if skip_first_check || check keep test then
      if is_empty_core test
      then Some keep
      else
        let (scope, actlit, test') = pick_element_of_core test in
        match minimize check keep test' with
        | None ->
          minimize ~skip_first_check:true check (add_from_other_core test scope actlit keep) test'
        | Some res -> Some res
    else None
  in

  let check keep' test =
    let remaining = (core_size test) + 1 in
    let total = remaining + (core_size keep') in
    KEvent.log L_info "Minimizing using bruteforce... (%i elements in the IVC, %i checks left)" total remaining ;
    core_union keep keep'
    |> core_union test
    |> check_core check_ts sys prop_names enter_nodes
  in

  begin match minimize check empty_core test with
  | None -> raise CannotProve
  | Some core -> core
  end

(** Compute the MUST set and then call IVC_BF if needed *)
let ivc_must_bf_ test must_cont in_sys ?(os_invs=[]) check_ts sys props enter_nodes keep reduced_test =
  let prop_names = props_names props in

  let timeout_bkp = !timeout in
  let (os_invs, must) =
    let uc_res = Some (os_invs, reduced_test) in
    must_set_ in_sys ~uc_res check_ts sys props enter_nodes keep test in
  must_cont must ;
  let keep = core_union keep must in
  let test = core_diff test must in
  let sys = remove_other_props sys prop_names in
  let sys = add_as_candidate os_invs sys in
  if check_core check_ts sys prop_names enter_nodes keep
  then (
    KEvent.log L_info "MUST set is a valid IVC." ;
    keep
  )
  else (
    timeout := timeout_bkp ;
    KEvent.log L_info "MUST set is not a valid IVC. Minimizing with bruteforce..." ;
    ivc_bf_ in_sys ~os_invs check_ts sys props enter_nodes keep test
    |> core_union must
  )

(** Implements the algorithm 'Unsat Core, then bruteforce' *)
let ivc_ucbf in_sys ?(use_must_set=None) param analyze sys props =
  try (
    let enter_nodes = Flags.IVC.ivc_only_main_node () |> not in
    let (keep, test) = generate_initial_cores in_sys sys enter_nodes (Flags.IVC.ivc_category ()) in
    let ivc_bf_ = match use_must_set with
    | Some f ->
      (fun x -> (props, core_to_loc_core in_sys (core_union keep x), { approximation = !timeout }) |> f)
      |> ivc_must_bf_ test
    | None -> ivc_bf_ in
    let (sys, check_ts) = make_ts_analyzer in_sys param analyze sys in
    let (os_invs, test) = ivc_uc_ in_sys sys props enter_nodes keep test in
    let test = ivc_bf_ in_sys ~os_invs check_ts sys props enter_nodes keep test in
    Solution (props, core_to_loc_core in_sys (core_union keep test), { approximation = !timeout })
  ) with
  | CannotProve | CertifChecker.CouldNotProve _ ->
    if are_props_safe props
    then (KEvent.log L_error "Cannot reprove properties." ;
          Error "Cannot reprove properties")
    else NoSolution
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)" i t ;
    Error "Init and trans equations mismatch"

(* ---------- UMIVC ---------- *)

let get_unexplored map actsvs =
  if SMTSolver.check_sat map
  then
    let hashtbl = StateVar.StateVarHashtbl.create 0 in
    let model =
      List.map (fun sv -> Var.mk_const_state_var sv) actsvs
      |> SMTSolver.get_var_values map hashtbl in
    actsvs
    |> List.filter (fun sv ->
      Var.mk_const_state_var sv
      |> Var.VarHashtbl.find model
      |> is_model_value_true
    )
    |> (fun x -> Some x)
  else
    None

let get_unexplored_with_card map actsvs n =
  SMTSolver.push map ;
  exactly_k_true actsvs n |> SMTSolver.assert_term map ;
  let res = get_unexplored map actsvs in
  SMTSolver.pop map ;
  res

let get_unexplored_min map actsvs =
  let n = List.length actsvs in
  let rec aux k =
    if k > n then None
    else match get_unexplored_with_card map actsvs k with
    | None -> aux (k+1)
    | Some res -> Some res
  in
  aux 0

let get_unexplored_max map actsvs =
  let n = List.length actsvs in
  let rec aux k =
    if k < 0 then None
    else match get_unexplored_with_card map actsvs k with
    | None -> aux (k-1)
    | Some res -> Some res
  in
  aux n

let block_up map s =
  at_least_one_false s
  |> SMTSolver.assert_term map

let svs_diff svs1 svs2 =
  SVSet.diff (SVSet.of_list svs1) (SVSet.of_list svs2)
  |> SVSet.elements

let block_down map s =
  at_least_one_true s
  |> SMTSolver.assert_term map

type unexplored_type = Min | Max

let umivc_ in_sys ?(os_invs=[]) make_ts_analyzer sys props k enter_nodes
  ?(stop_after=0) cont keep test =
  let prop_names = props_names props in
  (*let sys_original = sys in*)
  let (sys_cs, check_ts_cs) = make_ts_analyzer sys in
  let (sys, check_ts) = make_ts_analyzer sys in
  let sys = remove_other_props sys prop_names in
  let sys = add_as_candidate os_invs sys in
  let sys_cs = remove_other_props sys_cs prop_names in
  let sys_cs = add_as_candidate os_invs sys_cs in

  let eq_of_actlit = get_ts_equation_of_actlit (core_union keep test) in
  (* If test is empty, we can return *)
  let n = core_size test in
  if not (are_props_safe props) then (true, [])
  else if n = 0 then (cont test ; (true, [test]))
  else (
    (* Add actsvs to the CS transition system (at top level) *)
    let actsvs = actsvs_of_core test in
    let sys_cs = List.fold_left (fun acc sv -> TS.add_global_constant acc (Var.mk_const_state_var sv)) sys_cs actsvs in

    (* Initialize the seed map *)
    let map = SMTSolver.create_instance ~produce_assignments:true
      (`Inferred (TermLib.FeatureSet.of_list [IA; LA])) (Flags.Smt.solver ()) in
    actsvs
    |> List.map Var.mk_const_state_var
    |> Var.declare_constant_vars (SMTSolver.declare_fun map) ;

    (* Utility functions *)
    (*let get_unexplored () = get_unexplored map actsvs in*)
    let get_unexplored_min () = get_unexplored_min map actsvs in
    let get_unexplored_max () = get_unexplored_max map actsvs in
    let block_up = block_up map in
    let block_down = block_down map in
    let compute_mcs = compute_mcs check_ts_cs sys_cs prop_names enter_nodes in
    let compute_mcs k t = match compute_mcs k t with
      | None -> t
      | Some (r, _) -> r in
    let compute_all_mcs = compute_all_mcs check_ts_cs sys_cs prop_names enter_nodes in
    let compute_all_mcs k t max_mcs_cardinality =
      List.map fst (compute_all_mcs ~max_mcs_cardinality k t) in

    (* Check safety *)
    let main_scope = TS.scope_of_trans_sys sys in
    let prepare_ts_for_check sys keep =
      reset_ts enter_nodes sys ;
      let prepare_subsystem acc sys =
        let scope = TS.scope_of_trans_sys sys in
        let actlits =
          if enter_nodes || Scope.equal scope main_scope
          then Some (get_actlits_of_scope keep scope)
          else None
        in
        begin match actlits with
        | None -> acc
        | Some actlits ->
          let eqs = List.map eq_of_actlit actlits in
          let init_eq = List.map (fun eq -> eq.init_opened) eqs
          |> Term.mk_and in
          let trans_eq = List.map (fun eq -> eq.trans_opened) eqs
          |> Term.mk_and in
          TS.set_subsystem_equations acc scope init_eq trans_eq 
        end
      in
      TS.fold_subsystems ~include_top:true prepare_subsystem sys sys
    in
    let check keep =
      KEvent.log L_info "Testing safety of next seed..." ;
      let sys = prepare_ts_for_check sys keep in
      let old_log_level = Lib.get_log_level () in
      Format.print_flush () ;
      Lib.set_log_level L_off ;
      check_ts sys ;
      Lib.set_log_level old_log_level;
      check_result_safe prop_names sys
    in

    (* Compute MIVC *)
    let compute_mivc core =
      (*check (core_union keep core) |> ignore ;*) (* Not needed because a check is done before *)
      let (os_invs, test) = ivc_uc_ in_sys sys props enter_nodes keep core in
      ivc_bf_ in_sys ~os_invs check_ts sys props enter_nodes keep test
    in

    (* ----- Part 1 : CAMUS ----- *)
    KEvent.log L_info "Phase 1: CAMUS" ;
    let k = if k > n || k < 0 then n else k in
    let is_camus = k >= n in
    let is_marco = k <= 0 in

    let timeout_bkp = !timeout in
    if not is_marco then (
      KEvent.log L_info "Computing all MCS of cardinality smaller than %n..." k ;
      compute_all_mcs keep test k |>
      List.iter (
        fun mcs ->
          let mua = core_diff test mcs in
          block_down (actsvs_of_core mua)
      )
    ) ;
    let is_camus = is_camus && not !timeout in
    timeout := timeout_bkp ;

    (* ----- Part 2 : DETERMINING STRATEGY ----- *)
    let get_unexplored_auto =
      if is_camus
      then (fun () -> Min, get_unexplored_min ())
      else if is_marco
      then (fun () -> Max, get_unexplored_max ())
      else (* Implements GetUnexploredZZ *) (
        let last_was_min = ref true in
        (fun () ->
          last_was_min := not (!last_was_min) ;
          if !last_was_min
          then Min, get_unexplored_min ()
          else Max, get_unexplored_max ()
        )
      )
    in
    (* ----- Part 3 : MARCO ----- *)
    let approx = ref false in
    KEvent.log L_info "Phase 2: MARCO" ;
    let rec next acc =
      match get_unexplored_auto () with
      | _, None -> acc
      | typ, Some actsvs ->
        let seed = filter_core_svs actsvs test in
        if is_camus || check (core_union keep seed)
        then (
          (* Implements shrink(seed) using UCBF *)
          let mivc = if typ = Min && not !approx then seed else compute_mivc seed in
          (* Save and Block up *)
          cont mivc ;
          let new_acc = mivc::acc in
          timeout := timeout_bkp ;
          if List.length new_acc = stop_after
          then (approx := true ; new_acc)
          else (
            block_up (actsvs_of_core mivc) ;
            next new_acc
          )
        ) else (
          approx := !approx || !timeout ; (* If the safety check failed, we cannot guarantee that solutions will be complete *)
          (* Implements grow(seed) using MCS computation *)
          let mcs = if typ = Max then (core_diff test seed)
          else compute_mcs (core_union keep seed) (core_diff test seed) in
          timeout := timeout_bkp ;
          (* Block down *)
          block_down (actsvs_of_core mcs) ;
          next acc
        )
    in

    let all_mivc = next [] in
    SMTSolver.delete_instance map ;
    (not !approx, all_mivc)
  )

let must_umivc_ must_cont in_sys make_ts_analyzer sys props k enter_nodes
  ?(stop_after=0) cont keep test =
  let prop_names = props_names props in
  let (sys', check_ts') = make_ts_analyzer sys in

  let timeout_bkp = !timeout in
  let (os_invs, must) = must_set_ in_sys check_ts' sys' props enter_nodes keep test in
  must_cont must ;
  let keep = core_union keep must in
  let test = core_diff test must in
  let sys' = remove_other_props sys' prop_names in
  let sys' = add_as_candidate os_invs sys' in
  if check_core check_ts' sys' prop_names enter_nodes keep
  then (
    KEvent.log L_info "MUST set is a valid IVC." ;
    cont keep ;
    true, [keep]
  )
  else (
    timeout := timeout_bkp ;
    KEvent.log L_info "MUST set is not a valid IVC. Running UMIVC..." ;
    let post core = core_union core must in
    let cont core = core |> post |> cont in
    umivc_ in_sys ~os_invs make_ts_analyzer sys props k enter_nodes ~stop_after cont keep test
    |> (fun (complete, ivcs) -> complete, List.map post ivcs)
  )

(** Implements the algorithm UMIVC. *)
let umivc in_sys ?(use_must_set=None) ?(stop_after=0) param analyze sys props k cont =
  try (
    let enter_nodes = Flags.IVC.ivc_only_main_node () |> not in
    let (keep, test) = generate_initial_cores in_sys sys enter_nodes (Flags.IVC.ivc_category ()) in
    let make_ts_analyzer = make_ts_analyzer in_sys param analyze in
    let umivc_ = match use_must_set with
      | Some f ->
        (fun x -> (props, core_to_loc_core in_sys (core_union keep x), { approximation = !timeout }) |> f)
        |> (fun cont -> must_umivc_ cont in_sys make_ts_analyzer)
      | None -> umivc_ in_sys make_ts_analyzer in
    let res = ref [] in
    let cont test =
      let ivc = (props, core_to_loc_core in_sys (core_union keep test), { approximation = !timeout }) in
      res := ivc::(!res) ;
      cont ivc
    in
    let (complete, _) = umivc_ sys props k enter_nodes ~stop_after cont keep test in
    complete, List.rev (!res)
  ) with
  | CannotProve | CertifChecker.CouldNotProve _ ->
    if are_props_safe props
    then (KEvent.log L_error "Cannot reprove properties." ; (false, []))
    else (false, [])
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)" i t ;
    (false, [])

(* ---------- MINIMAL CORRECTION SETS ---------- *)

let mcs_ in_sys ?(os_invs=[]) check_ts sys props all enter_nodes
  ?(initial_solution=None) ?(max_mcs_cardinality= -1) ?(approx= false) cont keep test =
  let prop_names = props_names props in
  let sys = remove_other_props sys prop_names in
  let sys = add_as_candidate os_invs sys in

  (* Add actsvs to the CS transition system (at top level) *)
  let actsvs = actsvs_of_core test in
  let sys = List.fold_left (fun acc sv -> TS.add_global_constant acc (Var.mk_const_state_var sv)) sys actsvs in

  let initial_solution = match initial_solution with
  | None -> None
  | Some (({ Property.prop_name }, cex), loc_core, info) ->
    Some (loc_core_to_filtered_core loc_core test, (prop_name, cex))
  in

  let compute_mcs =
    compute_mcs check_ts sys prop_names enter_nodes ~max_mcs_cardinality ~initial_solution ~approx
  in
  let compute_all_mcs =
    compute_all_mcs check_ts sys prop_names enter_nodes ~max_mcs_cardinality ~initial_solution ~cont
  in

  let mcs =
    if all then compute_all_mcs keep test
    else
      match compute_mcs keep test with
      | None -> []
      | Some res -> cont res ; [res]
  in
  mcs |> List.map (fun (core, cex) -> (core, cex))

(* Compute one/all Maximal Unsafe Abstraction(s). *)
let mcs in_sys param analyze sys props
  ?(initial_solution=None) ?(max_mcs_cardinality= -1) all approx cont =
  let approx = approx && (not all) in
  try (
    let enter_nodes = Flags.MCS.mcs_only_main_node () |> not in
    let elements = (Flags.MCS.mcs_category ()) in
    let (keep, test) = generate_initial_cores in_sys sys enter_nodes elements in
    let (sys, check_ts) = make_ts_analyzer in_sys param analyze sys in
    let res = ref [] in
    let cont (test, (prop,cex)) =
      let mcs = ((TS.property_of_name sys prop, cex),
                 core_to_loc_core in_sys (core_union keep test),
                 { approximation = !timeout || approx }) in
      res := mcs::(!res) ;
      cont mcs
    in
    let _ =
      mcs_ in_sys check_ts sys props all enter_nodes ~initial_solution ~max_mcs_cardinality ~approx cont keep test
    in
    not (!timeout || approx), List.rev (!res)
  ) with
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)" i t ;
    (false, [])

let mcs_initial_analysis_ in_sys ?(os_invs=[]) check_ts sys enter_nodes
  ?(max_mcs_cardinality= -1) keep test =
  let props = TS.get_real_properties sys in
  let prop_names = props_names props in
  let sys = remove_other_props sys prop_names in
  let sys = add_as_candidate os_invs sys in

  (* Add actsvs to the CS transition system (at top level) *)
  let actsvs = actsvs_of_core test in
  let sys = List.fold_left (fun acc sv -> TS.add_global_constant acc (Var.mk_const_state_var sv)) sys actsvs in

  compute_approx_mcs_for_each_prop check_ts sys prop_names enter_nodes ~max_mcs_cardinality keep test
  |> List.map (fun (core, (p, cex)) -> (p, (core, (p, cex))))

let mcs_initial_analysis in_sys param analyze ?(max_mcs_cardinality= -1) sys =
  try (
    let enter_nodes = Flags.MCS.mcs_only_main_node () |> not in
    let elements = (Flags.MCS.mcs_category ()) in
    let (keep, test) = generate_initial_cores in_sys sys enter_nodes elements in
    let (sys, check_ts) = make_ts_analyzer in_sys ~stop_after_disprove:false ~no_copy:true param analyze sys in

    let res_to_mcs (test, (prop,cex)) =
      ((TS.property_of_name sys prop, cex),
        core_to_loc_core in_sys (core_union keep test),
        { approximation = true })
    in

    mcs_initial_analysis_ in_sys check_ts sys enter_nodes ~max_mcs_cardinality keep test
    |> List.map (fun (p, res) -> (TS.property_of_name sys p, res_to_mcs res))
  ) with
  | InitTransMismatch (i,t) ->
    KEvent.log L_error "Init and trans equations mismatch (%i init %i trans)" i t ;
    []

