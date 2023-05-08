(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

open Dolmen

module KindTerm = Term
module E = CmcErrors
module Ids = Lib.ReservedIds

(* Instantiate a module for parsing logic languages *)
module Id = Std.Id
module Term = Std.Term
module Statement = Std.Statement
module DU = DolmenUtils

module I = LustreIdent

let (let*) = Res.(>>=)

type id = Id.t

type subsystem_scope = string list
type sys_var_mapping = (subsystem_scope * StateVar.t list) list

type base_trans_system = {
  top: bool;
  name: id;
  input_svars: (Id.t * StateVar.t) list;
  output_svars: (Id.t * StateVar.t) list;
  local_svars: (Id.t * StateVar.t) list;
  local_subsys_svars: (Id.t * StateVar.t) list;
  _init_map: (Id.t * Var.t) list;
  trans_map: (Id.t * Var.t) list;
  scope: string list;
  init_flag: StateVar.t;
  state_vars: StateVar.t list;
  init_uf_symbol: UfSymbol.t;
  init_formals: Var.t list;
  init_term: KindTerm.t;
  trans_uf_symbol: UfSymbol.t;
  trans_formals: Var.t list;
  trans_term: KindTerm.t;
  subsystems: (Id.t * TransSys.instance list) list;
  props: Property.t list;
}

let rec mk_subsys_structure sys = {
  SubSystem.scope = TransSys.scope_of_trans_sys sys;
  source = sys;
  has_contract = false;
  has_impl = true;
  has_modes = false;
  subsystems =
    TransSys.get_subsystems sys
    |> List.map mk_subsys_structure;
}

(* Used to map transition system instances to subsystem names for pretty printing *)
(* Remove if a better solution is found *)
type subsystem_instance_name_data = {
  map: (Lib.position * Id.t) list;
  counter: int;
}

let empty_subsystem_instance_name_data = {
  map = [];
  counter = 0;
}

type definitions = {
  system_defs: base_trans_system list;
  functions: TransSys.d_fun list;
  enums: DU.enum list;
  ufunctions: UfSymbol.t list;
  name_map: subsystem_instance_name_data;
  const_decls: ((Id.t * StateVar.t) list * (Id.t * Var.t) list) ;
}

let empty_definitions = {
  system_defs = [];
  functions = [];
  enums = [];
  ufunctions = [];
  name_map = empty_subsystem_instance_name_data;
  const_decls = [], [];
}

(* Additional data needed for counter example printing *)
(* May want to reduce this information in the future. *)
type metadata = {
  name_map: subsystem_instance_name_data;
  sys_var_mapping: (string list * StateVar.t list) list;
  enum_defs: DU.enum list;
}

let find_trans_system trans_systems search_name = 
  List.find ( fun ({name; _ }: base_trans_system) -> Id.equal search_name name) trans_systems 

let error ?(pos=Lib.dummy_pos) e = Error (`CmcInterpreterError (pos, e))

let find_system definitions name =
  let systems = definitions.system_defs in
  List.find_opt (fun (system : base_trans_system) -> Id.equal system.name name) systems

let update_system (definitions : definitions) (updated_system : base_trans_system) = 
  (* Assumes that the system exists in the list *)
  let rec func (definitions : base_trans_system list) id c = match definitions with
  | [] -> raise(Failure "Not Found")
  | hd::tl -> if (Id.equal hd.name id) then c else func tl id (c+1) in
  let sys_index = func definitions.system_defs updated_system.name 0 in
  {definitions with 
  system_defs = List.mapi (fun i def -> if i = sys_index then updated_system else def) definitions.system_defs }

let mk_single_state_var sys_name (id, var_type) = 
  (* Simplified mk_var for non-input non-constant, single state vars *)
  let svar =
    let name = DU.dolmen_id_to_string id in
    let scope = (sys_name :: "impl" :: I.user_scope) in
    StateVar.mk_state_var
      ~is_input:false ~is_const:false ~for_inv_gen:false
      name scope var_type
    in
    (id, svar)

let mk_var ?(for_inv_gen=true) sys_name is_input is_const (init_map, trans_map, svars) (id, var_type) = 
  (* TODO Verify (or likely correct) that defined vars have valid names *)
  let svar =
    let name = DU.dolmen_id_to_string id in
    let scope = (sys_name :: "impl" :: I.user_scope) in
    StateVar.mk_state_var
      ~is_input ~is_const ~for_inv_gen
      name scope var_type
    in
  let prev_base = Numeral.pred TransSys.trans_base in (* Why is this the previous value? ?*)

  if is_const then 
    let prev_mapping = (id, Var.mk_const_state_var svar) in
    (prev_mapping :: init_map, prev_mapping :: trans_map, svars @ [(id, svar)])
  else
    let prev_mapping = (id, Var.mk_state_var_instance svar prev_base) in
    let next_id = DU.prime id in
    let next_mapping = (next_id, Var.mk_state_var_instance svar TransSys.trans_base) in
    (prev_mapping :: init_map, prev_mapping :: next_mapping :: trans_map, svars @ [(id, svar)])

let mk_vars enums sys_name is_input mappings dolmen_terms = 
  let vars = List.map (DU.dolmen_term_to_id_type enums) (DU.opt_list_to_list dolmen_terms) in
  List.fold_left (mk_var sys_name is_input false) mappings vars

(** A mapping of unprimed vars to their primed state. 
    Specifically used for invariant props in the transition system. *)
let mk_inv_map init_map trans_map =  
  init_map |> List.map (fun (unprimed_var, _) -> 
    let primed_var = DU.prime unprimed_var in 
    (unprimed_var, List.assoc primed_var trans_map )
  ) 

(** Translate CMC init sexp into Kind2 Term. Ands init with the inv property *)
let mk_init_term enums ({ init; inv}: Statement.sys_def) init_flag const_map init_map inv_map =
  (* Flag representing the init state*)
  let init_flag_t =
      Var.mk_state_var_instance init_flag TransSys.init_base
      |> KindTerm.mk_var
  in
  KindTerm.mk_and (init_flag_t :: 
                   DU.opt_dolmen_term_to_expr enums (const_map @ init_map) init :: 
                   DU.opt_dolmen_term_to_expr enums (const_map @ inv_map) inv :: 
                   []
                  )

let mk_trans_term enum_map ({ trans; inv}: Statement.sys_def) init_flag const_map inv_map trans_map =
  (* Flag representing the init state*)
  let init_flag_t =
    Var.mk_state_var_instance init_flag TransSys.trans_base
    |> KindTerm.mk_var
  in

  (* TODO Reintroduce support for OnlyChange
     Refer old sexp interpreter. May want to add this in DolmelUtils and create a new ast type for this
     *)
  (* let trans = process_only_change sys_def trans in *)

  KindTerm.mk_and (KindTerm.mk_not init_flag_t :: DU.opt_dolmen_term_to_expr enum_map (const_map @ trans_map) trans :: DU.opt_dolmen_term_to_expr enum_map (const_map @ inv_map) inv :: [])

  let mk_subsystems enums parent_sys_name parent_sys_svars parent_init_map parent_trans_map other_systems subsystem_names = 
    let mk_inst sys_state_vars subsys_state_vars =
      let map_down, map_up =
        List.fold_left2 (fun (map_down, map_up) sys_state_var subsys_state_var ->
            StateVar.StateVarMap.add subsys_state_var sys_state_var map_down,
            StateVar.StateVarMap.add sys_state_var subsys_state_var map_up
        ) StateVar.StateVarMap.(empty, empty) sys_state_vars subsys_state_vars
      in 
      {   TransSys.pos =  { pos_fname = ""; Lib.pos_lnum = 0; Lib.pos_cnum = -1 };
          map_down;
          map_up;
          guard_clock = (fun _ t -> t);
          assumes = None } in

    let find_parent_svars parent_svars subsys_svars = List.map (fun param -> 
      let prop_id = DU.dolmen_symbol_term_to_id param in
      prop_id, List.assoc prop_id parent_svars
    ) subsys_svars in

    List.map (fun (local_subsystem_name, subsystem_name, params) -> 
      let subsystem = find_trans_system other_systems subsystem_name in

      let subsystem_input_svars = subsystem.input_svars in
      let subsystem_output_svars = subsystem.output_svars in
      let subsystem_local_svars =  subsystem.local_svars @ subsystem.local_subsys_svars in
      let init_local = mk_single_state_var parent_sys_name (DU.append_to_id local_subsystem_name "_init", Type.t_bool) in
      
      (* This contains all of the non-locals of the subsystem*)
      let parent_sys_svars = find_parent_svars parent_sys_svars params in
      assert ((List.length parent_sys_svars) == (List.length (subsystem_input_svars @ subsystem_output_svars))) ;

      (* These are the new statevars of the parent system that will be used as the local vars of the subsystem *)
      let local_init_map, local_trans_map, renamed_local_svars = (List.fold_left 
        (fun mapping (name, svar) -> 
          mk_var ~for_inv_gen:(StateVar.for_inv_gen svar) parent_sys_name false false mapping 
            (DU.join_ids local_subsystem_name name, StateVar.type_of_state_var svar)
        ) 
      ) ([], [], []) (subsystem_local_svars) in

      let local_init_map, local_trans_map, _ = mk_var parent_sys_name false false (local_init_map, local_trans_map, []) (fst init_local, StateVar.type_of_state_var (snd init_local)) in
            
      (* These are the actual state vars of the  defined subsystem*)
      let subsys_svars = (subsystem.state_vars)  in 

      (* These are the statevars of the parent system that were passed to the subsystem call
          including the local vars that we just created. *)
      let named_parent_sys_svars = (init_local :: parent_sys_svars @ renamed_local_svars) in
      let renamed_local_svars = init_local :: renamed_local_svars in
      let parent_sys_svars = List.map snd named_parent_sys_svars in

      let inst = local_subsystem_name, (mk_inst subsys_svars parent_sys_svars) in

      (* Make init and trans terms for parentt transition system *)
      let subsys_init_flag = subsystem.init_flag in
      let init_flag_mapping = (Id.mk (Id.ns subsystem.name) ( StateVar.name_of_state_var subsys_init_flag), Var.mk_state_var_instance subsys_init_flag TransSys.init_base) in
      let init_flag_prime_mapping = (DU.prime (fst init_local), Var.mk_state_var_instance (snd init_local) TransSys.trans_base) in
      let subsys_init_map = init_flag_mapping :: local_init_map @ parent_init_map in         
      let subsys_trans_map = init_flag_mapping :: init_flag_prime_mapping :: local_trans_map @ parent_trans_map in         
      let cur = List.map (fun (id, _) -> DU.dolmen_term_to_expr enums subsys_init_map (Term.const id)) named_parent_sys_svars in 
      let next =List.map (fun (id, _) -> DU.dolmen_term_to_expr enums subsys_trans_map (Term.const (DU.prime id))) named_parent_sys_svars in 
      let subsys_formulas = KindTerm.mk_uf subsystem.init_uf_symbol  cur,
      KindTerm.mk_uf subsystem.trans_uf_symbol  (next@cur) in

      (* ((subsystem name, (local name, local instance)), new locals), (init formula, trans formula)) *)
      (((subsystem.name, inst), renamed_local_svars), subsys_formulas)
    ) subsystem_names
    
let get_enum_constraint env init_map trans_map (id, svar) = 
  (* Needed because the Enum KindType does not actual constrain 
     the variables to values within the range *)
  let svar_type = StateVar.type_of_state_var svar in
  (if Type.is_enum svar_type then
    let id_term = DU.dolmen_id_to_kind_term env.enums init_map id in
    let primed_id_term = DU.dolmen_id_to_kind_term env.enums trans_map (DU.prime id) in

    let low, high = Type.bounds_of_int_range svar_type in
    let low_term = KindTerm.mk_num_of_int (Numeral.to_int low) in
    let high_term = KindTerm.mk_num_of_int (Numeral.to_int high) in

    Some ((KindTerm.mk_and [(KindTerm.mk_geq [id_term;  low_term]); (KindTerm.mk_leq [id_term;  high_term])]),
          (KindTerm.mk_and [(KindTerm.mk_geq [primed_id_term;  low_term]); (KindTerm.mk_leq [primed_id_term;  high_term])]))
  else
    None)

let get_enum_constraints env init_map trans_map svars = List.fold_left 
  (fun (init_constraints, trans_constraints) svar ->  
    match get_enum_constraint env init_map trans_map svar with
      | Some (unprimed, primed) -> (unprimed :: init_constraints,unprimed :: primed :: trans_constraints)
      | None -> (init_constraints, trans_constraints)
  ) ([], []) svars 

(** Process the CMC [define-system] command. *)
let mk_base_trans_system (env: definitions) (sys_def: Statement.sys_def) = 
  let system_name = DU.dolmen_id_to_string sys_def.id in
  let scope = [system_name] in
  let init_flag = StateVar.mk_init_flag scope in

  let init_map, trans_map, input_svars = mk_vars env.enums system_name true ([], [], []) sys_def.input in
  let init_map, trans_map, output_svars = mk_vars env.enums system_name false (init_map, trans_map, []) sys_def.output in
  let init_map, trans_map, local_svars = mk_vars env.enums system_name false (init_map, trans_map, []) sys_def.local in

  let init_enum_constraints, trans_enum_constraints = get_enum_constraints env init_map trans_map (input_svars @ output_svars @ local_svars) in

  let _, const_map = env.const_decls in
  (* Const svars are not added to symb_svars because 
     they are added to the global constant attribute of the trans system *)

  let symb_svars = input_svars @ output_svars @ local_svars  in (*S*)

  (* Process subsystems *)
  let subsystem_defs = mk_subsystems env.enums system_name symb_svars init_map trans_map env.system_defs sys_def.subs in
  let named_subsystems = List.map fst (List.map fst subsystem_defs) in 
  let subsys_locals = List.flatten (List.map snd (List.map fst subsystem_defs)) in 

  let subsystems, name_map = List.fold_left (fun ((subsystems_acc : (Id.t * TransSys.instance list) list), name_map) (subsys_name, (instance_name, instance)) -> 
    let pos = TransSys.({instance.pos with pos_lnum = name_map.counter}) in
    let inst = {instance with TransSys.pos = pos} in
    let name_map = {map = (pos, instance_name) :: name_map.map ; counter = name_map.counter + 1} in 

    let subsys = match List.assoc_opt subsys_name subsystems_acc with
    | Some other_instances ->  List.remove_assoc subsys_name subsystems_acc @ [(subsys_name, other_instances @ [inst])]
    | None -> subsystems_acc @ [(subsys_name, [inst])]in

    subsys, name_map
  ) ([], env.name_map) named_subsystems  in

  let subsys_formulas = List.map snd subsystem_defs in
  let subsys_init = List.map fst subsys_formulas in
  let subsys_trans = List.map snd subsys_formulas in

  
  let inv_map_for_init = init_map in (* For notational puposes only. Just need the inv map for the init formula. *)
  let inv_map_for_trans = mk_inv_map init_map trans_map in
  
  let init_term = 
    KindTerm.mk_and ((mk_init_term env.enums sys_def init_flag const_map init_map inv_map_for_init) :: init_enum_constraints @ subsys_init )
  in
 
  let trans_term = 
    KindTerm.mk_and ((mk_trans_term env.enums sys_def init_flag const_map inv_map_for_trans trans_map) :: trans_enum_constraints @ subsys_trans )
  in

  let state_vars =
    init_flag :: List.map snd (symb_svars @ subsys_locals)
   in

  let init_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.init_base
    )
    state_vars
  in

  let init_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.init_uf_string system_name)
      (List.map Var.type_of_var init_formals)
      Type.t_bool
  in

  let trans_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.trans_base
    )
    state_vars
    @
    List.map (fun sv ->
      Var.mk_state_var_instance
        sv (TransSys.trans_base |> Numeral.pred)
    )
    state_vars
  in
  
  let trans_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.trans_uf_string system_name)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in
  (* let local_svars = subsys_locals @ local_svars in *)

  {top=false; scope; name=sys_def.id;  input_svars; output_svars; local_svars; local_subsys_svars=subsys_locals; _init_map=init_map; trans_map; init_flag; state_vars; init_uf_symbol; init_formals; init_term; trans_uf_symbol; trans_formals; trans_term; subsystems; props=[]}, name_map

let rename_check_vars enums (sys_def : base_trans_system) (system_check : Statement.sys_check) = 
  (* Requires that the sys_def and check_def match *)
  (* TODO Support underscores *)
  assert (Id.equal sys_def.name system_check.id) ;
  let system_name = DU.dolmen_id_to_string sys_def.name in
  let init_map, trans_map, _ = mk_vars enums system_name true ([], [], []) system_check.input in
  let init_map, trans_map, _ = mk_vars enums system_name false (init_map, trans_map, []) system_check.output in
  let _, trans_map, _ = mk_vars enums system_name false (init_map, trans_map, []) system_check.local in

  List.map2 (fun map chk -> (fst chk,  snd map)) sys_def.trans_map trans_map  

(** Reachibility queries in terms of invariance *)
(* Simply states that the invariant variable must equal the formula. Makes no other claims *)
let mk_trans_invar_prop_eqs enums one_query_prop_svars (system_check : Statement.sys_check) two_state_bound_var_map =  
  one_query_prop_svars |> List.map (fun ((id: id), (svar: StateVar.t)) ->
    (* Typechecker should allow us to assume that the reachability prop is defined *)
    let prop = List.assoc id system_check.reachable in
    let prop = KindTerm.mk_not (DU.dolmen_term_to_expr enums two_state_bound_var_map prop) in
    let var = Var.mk_state_var_instance svar Numeral.zero in
      (KindTerm.mk_eq
        [KindTerm.mk_var var; prop])
    |> KindTerm.bump_state Numeral.one
  )


  let mk_init_invar_prop_eqs enums one_query_prop_svars (system_check : Statement.sys_check) two_state_bound_var_map =  
  one_query_prop_svars |> List.map (fun ((id: id), (svar: StateVar.t)) ->
    (* Typechecker should allow us to assume that the reachability prop is defined *)
    let prop = List.assoc id system_check.reachable in
    let prop = KindTerm.mk_not (DU.dolmen_term_to_expr enums two_state_bound_var_map prop) in
    let var = Var.mk_state_var_instance svar TransSys.init_base in
      (KindTerm.mk_eq
        [KindTerm.mk_var var; prop])
  )

let mk_rprops enums (system_check : Statement.sys_check) two_state_bound_var_map = 
  let reachability_svars = system_check.reachable |> List.map (fun (prop_id, _) ->
    let system_name = DU.dolmen_id_to_string system_check.id in
    let scope = (system_name :: I.reserved_scope) in

    let reachable_name = DU.dolmen_id_to_string prop_id in

    let svar = StateVar.mk_state_var
      ~is_input:false ~is_const:false ~for_inv_gen:true
      reachable_name scope Type.t_bool in

    (prop_id, svar)
  ) in
  let init_invar_props = mk_init_invar_prop_eqs enums reachability_svars system_check two_state_bound_var_map in
  let trans_invar_props = mk_trans_invar_prop_eqs enums reachability_svars system_check two_state_bound_var_map in
  (reachability_svars, init_invar_props, trans_invar_props)

let mk_query (rprop_svars : (id * StateVar.t) list) query =
  let query_id, query_body = query in

  let reachability_svars = List.map (fun reachability_prop -> 
    let prop_id = DU.dolmen_symbol_term_to_id reachability_prop in
    List.assoc prop_id rprop_svars) query_body in

  (* We or instead of and because the whole reachability query must be notted for invariance*)
  let mk_var_kind_term svar = KindTerm.mk_var (Var.mk_state_var_instance svar TransSys.prop_base) in
  (query_id, KindTerm.mk_or (List.map mk_var_kind_term reachability_svars);)

let check_trans_system enums base_system (system_check: Statement.sys_check) = 
  (* Map renamed check sys state vars (primed and unprimed) to actual system vars *)
  let check_map = rename_check_vars enums base_system system_check in

  (* Make svars, init terms, and trans terms for each reachability prop *)
  let reachability_svars, rprop_init_terms, rprop_trans_terms = mk_rprops enums system_check check_map in
  
  (* Create a statevar for each reachability prop within a query *)
  (* Other reachability props are ignored *)
  let queries = system_check.queries |> List.map (mk_query reachability_svars) in

  (* Placeholder for when assumption ,fairness, etc are added *)
  let prop_svars = List.map snd reachability_svars in

  let init_term = KindTerm.mk_and ( base_system.init_term :: rprop_init_terms ) in
  let trans_term = KindTerm.mk_and ( base_system.trans_term :: rprop_trans_terms ) in
  
  let props = (*C*)
     queries |> List.map (fun (query_id, query_term) ->
      {      

        Property.prop_name = DU.dolmen_id_to_string query_id; (*Used to prepend invar-property-*)
        prop_source = Property.PropAnnot Lib.dummy_pos;
        prop_term = query_term;
        prop_status = Property.PropUnknown
      }
    )
  in

  let state_vars =
    base_system.state_vars @ prop_svars
   in

  let init_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.init_base
    )
    state_vars
  in

  let init_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.asprintf "%s_%a_checked" Ids.init_uf_string Id.print system_check.id)  (*TODO need to change name to support multiple checks*)
      (List.map Var.type_of_var init_formals)
      Type.t_bool
  in

  let trans_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.trans_base
    )
    state_vars
    @
    List.map (fun sv ->
      Var.mk_state_var_instance
        sv (TransSys.trans_base |> Numeral.pred)
    )
    state_vars
  in

  let trans_uf_symbol =
    (* TODO we are redeclaring uf symbol with updated type
       This is bad, to get around it we add checked to it. 
       We may need to postpone the initial declararion when checks are present if 
        we want to stop this *)
    UfSymbol.mk_uf_symbol
      (Format.asprintf "%s_%a_checked" Ids.trans_uf_string Id.print system_check.id)  (*TODO need to change name to support multiple checks*)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in

  {base_system with 
    init_term; trans_term; props;
    state_vars; 
    init_formals; init_uf_symbol;
    trans_formals; trans_uf_symbol}


let declare_const (const_decls, const_map) name return_type =   
  let const_map, _, const_decls = mk_var "const-decl" false true (const_map, [], const_decls) (name, return_type) in
  (const_decls, const_map)
  
let declare_fun name args return_type = 
  let mk_fresh_vars types =
    let vars = List.map Var.mk_fresh_var types in
    List.map (fun var -> (Var.hstring_of_free_var var, var)) vars in
  let s_name = DU.dolmen_id_to_string name in
  let named_vars = mk_fresh_vars args in
  let vars = List.map snd named_vars in
  let uf_name = UfSymbol.mk_uf_symbol
    s_name
    (List.map Var.type_of_var vars)
    return_type
  in
  uf_name

let define_fun enums name args return_type body = 
  let s_name = DU.dolmen_id_to_string name in
  let named_vars, _, _ = mk_vars enums s_name true ([], [], []) (Some args) in  
  let vars = List.map snd named_vars in
  let uf_name = UfSymbol.mk_uf_symbol
    s_name
    (List.map Var.type_of_var vars)
    return_type
  in

  let body_term = DU.dolmen_term_to_expr enums named_vars body in
  TransSys.mk_d_fun uf_name return_type vars body_term 

let process_enum_definition name attrs =
  let count = Numeral.zero in
  let enum_type = Type.mk_type (Type.IntRange (count, (Numeral.of_int ((List.length attrs) - 1)), Type.Enum)) in
  let enum, _ = attrs |> List.fold_left ( fun (enums, count) enum_var -> 
      (DU.{enums with to_int = (enum_var, count) :: enums.to_int ; to_str = (count, enum_var) :: enums.to_str}, Numeral.(count + Numeral.one))
    ) ((DU.empty_enum name enum_type), count) 
  in
  enum

let process_decl (definitions : definitions) (dec : Statement.decl) = 
  match dec with
  | Abstract (dec : Statement.abstract) -> (
    let param_types, return_type = DU.dolmen_binding_to_types definitions.enums dec.ty in
    match param_types with 
      | [] -> 
        let const_decls = declare_const definitions.const_decls dec.id return_type  in
        {definitions with const_decls}
      | param_types -> 
        let uf_name = declare_fun dec.id param_types return_type in
        {definitions with ufunctions = uf_name :: definitions.ufunctions}
  )
  | Record _ -> failwith "TODO: Record type function declarations are not yet supported. What are they?"
  | Inductive (r: Statement.inductive) -> 
    (* Delcare enum and Declare datatype *)
    (* These inductive decls may be for more than just there. Currently we only support the format of delare enums *)
    (* Assertions are present to try to prevent silent failures if a non-enum decl is passed. *)
    assert (List.length r.vars == 0);
    assert (List.length r.vars == 0);
    List.iter (fun ts -> assert (List.length ts == 0)) (List.map snd r.cstrs);

    let enum_attrs = List.map fst r.cstrs in

    {definitions with enums = (process_enum_definition r.id enum_attrs) :: definitions.enums}


let process_def definitions (def : Statement.def) = 
  let d_fun = define_fun definitions.enums def.id def.params (DU.type_of_dolmen_term definitions.enums def.ret_ty) def.body in 
  {definitions with functions = d_fun :: definitions.functions}
  
let process_command definitions Statement.({id; descr; _; }) = 
  let* defs = definitions in
  match descr with
    (* (define-system symbol attrs)*)
  | Statement.Def_sys s -> 
    let sys_def, name_map = mk_base_trans_system defs s in

    Ok {defs with system_defs = sys_def :: defs.system_defs ; name_map;}
    
  | Statement.Chk_sys c ->
    (* Assuming check systems come after system definitions. 
       Changes will be needed if we want to remove this assumption. *)
    let* checked_system = 
      match find_system defs c.id with
       | Some system -> Ok (check_trans_system defs.enums system c)
       | None -> (error (E.SystemNotFound c.id)) in

    Ok (update_system defs checked_system)

  (* (declare-fun name args type) *)
  | Statement.Decls fun_decls -> 
    Ok (List.fold_left process_decl defs fun_decls.contents)

  (* (define-fun name args type) *)
  | Statement.Defs fun_defs -> 
    Ok (List.fold_left process_def defs fun_defs.contents)

  | Statement.Set_logic _ -> 
    (* TODO Actually do something here? *)
    Ok defs
  | _ -> (error (E.NotSuppoted (DU.dolmen_opt_id_to_string id)))

(* Open and parse from file *)
let of_file filename = 

  (* Parse and Typecheck file with Dolmen *)
  let statements = DU.process filename in
  
  let* cmc_defs =
    List.fold_left process_command (Ok empty_definitions) statements
  in

  let cmc_sys_defs = {(List.hd cmc_defs.system_defs) with top=true} :: (List.tl cmc_defs.system_defs) in

  let enum_defs = cmc_defs.enums in

  let sys_var_mapping = List.map (fun base_transys -> (
    let primary_vars = (base_transys.input_svars @ base_transys.output_svars @ base_transys.local_svars) |>
          List.map snd in
    (base_transys.scope, primary_vars)
  )) cmc_sys_defs in

  let name_map = cmc_defs.name_map in

  let mk_trans_system global_const_vars other_trans_systems (base : base_trans_system)  =
    let name = base.name in
    let subs = base.subsystems |> List.map (fun (name, local_instances) -> 
      (List.assoc name other_trans_systems, local_instances)) (* subsystems *)
    in
    let sys, _ = 
      TransSys.mk_trans_sys
        base.scope
        None (* No instance variable *)
        base.init_flag
        base.state_vars
        StateVar.StateVarSet.empty (* underapproximation *)
        (StateVar.StateVarHashtbl.create 7) (* state_var_bounds *)
        global_const_vars (* global_consts *)
        (if base.top then cmc_defs.ufunctions else []) (* ufs *)
        (if base.top then cmc_defs.functions else []) (* defs *)
        base.init_uf_symbol
        base.init_formals
        base.init_term
        base.trans_uf_symbol
        base.trans_formals
        base.trans_term
        subs
        base.props
        (* fg_props *)
        (None, []) (* mode_requires *)
        (Invs.empty ()) (* invariants *)
    in
    (name, sys) :: other_trans_systems
  in

  let const_global_vars = List.map snd (snd cmc_defs.const_decls) in 

  let trans_systems = (List.rev cmc_sys_defs) |> List.fold_left (mk_trans_system const_global_vars) [] in
  
  let top_sys = snd (List.hd trans_systems) in

  (* Format.printf "CMC_SYS: %a@." (TransSys.pp_print_subsystems true) top_sys; *)

  Ok (mk_subsys_structure top_sys, {name_map; sys_var_mapping; enum_defs})
