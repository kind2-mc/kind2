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
module Loc = Std.Loc
module Id = Std.Id
module Term = Std.Term
module Statement = Std.Statement
module M = Class.Logic.Make(Loc)(Id)(Term)(Statement)
module DU = DolmenUtils

module I = LustreIdent

let (let*) = Res.(>>=)

type loc = Loc.t
type id = Id.t
type term = Term.t
type statement = Statement.t

type def = {name: id}

type subsystem_scope = string list
type sys_var_mapping = (subsystem_scope * StateVar.t list) list

type system_def = {
  name: id;
  input: (id * Type.t) list;
  output: (id * Type.t) list;
  local: (id * Type.t) list;
  init: term option;
  trans: term option;
  inv:  term option;

  (*          ( sys_name * ( local_name * inputs list) list ) list    *)
  subsystems: (id * (id * id list) list) list;
}

let match_sys_def sys_def v = 
  List.find ( fun {name; _ } -> Id.equal name v) sys_def 

type base_trans_system = {
  top: bool;
  name: id;
  (* sys_def: system_def; *) (* TODO may need to reintroduce if determined to be nessisary for cex printing *)
  input_svars: (Id.t * StateVar.t) list; (* TODO remove ID if not used *)
  output_svars: (Id.t * StateVar.t) list;
  local_svars: (Id.t * StateVar.t) list;
  init_map: (Id.t * Var.t) list;
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

type env = {
  base_trans_systems: ( Id.t * base_trans_system ) list;
  defined_functions: TransSys.d_fun list;
  declared_functions: UfSymbol.t list;
  global_constants: StateVar.t list;
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

(* TODO: This is not yet populated
   Make sure that this is still the best method and implement if so
   Also define its purpose here*)
type subsystem_instance_name_data = {
  map: (Lib.position * HString.t) list;
  counter: int;
}

let empty_subsystem_instance_name_data = {
  map = [];
  counter = 0;
}

type enum = {
  name: HString.t;
  get_type: Type.t;
  to_int: (HString.t * Numeral.t) list;
  to_str: (Numeral.t * HString.t) list;
}

let empty_enum name enum_type = {
  name = name;
  get_type = enum_type;
  to_int = [];
  to_str = [];
}

type definitions = {
  system_defs: base_trans_system list;
  functions: TransSys.d_fun list; (* Not yet populated *)
  enums: enum list; (* Not yet populated *)
  ufunctions: UfSymbol.t list; (* Not yet populated *)
  name_map: subsystem_instance_name_data; (* Not yet populated *)
  (* TODO Others *)
}

let empty_definitions = {
  system_defs = [];
  functions = [];
  enums = [];
  ufunctions = [];
  name_map = empty_subsystem_instance_name_data;
}

(* TODO Remove position from error if it is never used *)
let error ?(pos=Lib.dummy_pos) e = Error (`CmcInterpreterError (pos, e))

let mk_var sys_name is_input is_const (init_map, trans_map, svars) (id, var_type) = 
  let svar =
    let name = DU.dolmen_id_to_string id in
    let scope = (sys_name :: "impl" :: I.user_scope) in
    StateVar.mk_state_var
      ~is_input ~is_const ~for_inv_gen:true
      name scope var_type
    in
    Format.printf "%a\n" StateVar.pp_print_state_var_debug svar;
    let prev_base = Numeral.pred TransSys.trans_base in (* Why is this the previous value? ?*)
    let next_id = DU.prime id in
    let prev_mapping = (id, Var.mk_state_var_instance svar prev_base) in
    let next_mapping = (next_id, Var.mk_state_var_instance svar TransSys.trans_base) in
    (prev_mapping :: init_map, next_mapping :: trans_map, (id, svar) :: svars)

let mk_vars sys_name is_input mappings dolmen_terms = 
  let vars = List.map DU.dolmen_term_to_id_type (DU.opt_list_to_list dolmen_terms) in
  List.fold_left (mk_var sys_name is_input false) mappings vars

(** A mapping of unprimed vars to their primed state. 
    Specifically used for invariant props in the transition system. *)
let mk_inv_map init_map trans_map =  
  init_map |> List.map (fun (unprimed_var, _) -> 
    let primed_var = DU.prime unprimed_var in 
    (unprimed_var, List.assoc primed_var trans_map )
  ) 

(** Translate CMC init sexp into Kind2 Term. Ands init with the inv property *)
let mk_init_term ({ init; inv}: Statement.sys_def) init_flag const_map init_map inv_map =
  (* Flag representing the init state*)
  let init_flag_t =
      Var.mk_state_var_instance init_flag TransSys.init_base
      |> KindTerm.mk_var
  in

  KindTerm.mk_and (init_flag_t :: 
                   DU.opt_dolmen_term_to_expr (const_map @ init_map) init :: 
                   DU.opt_dolmen_term_to_expr (const_map @ inv_map) inv :: 
                   []
                  )

let mk_trans_term ({ trans; inv}: Statement.sys_def) init_flag const_map inv_map trans_map =
  (* Flag representing the init state*)
  let init_flag_t =
    Var.mk_state_var_instance init_flag TransSys.trans_base
    |> KindTerm.mk_var
  in

  (* TODO Reintroduce support for OnlyChange
     Refer old sexp interpreter. May want to add this in DolmelUtils and create a new ast type for this
     *)
  (* let trans = process_only_change sys_def trans in *)

  KindTerm.mk_and (KindTerm.mk_not init_flag_t :: DU.opt_dolmen_term_to_expr (const_map @ trans_map) trans :: DU.opt_dolmen_term_to_expr (const_map @ inv_map) inv :: [])



(** Process the CMC [define-system] command. *)
let mk_base_trans_system env (sys_def: Statement.sys_def) = 
  let system_name = DU.dolmen_id_to_string sys_def.id in
  let scope = [system_name] in
  let init_flag = StateVar.mk_init_flag scope in

  let init_map, trans_map, input_svars = mk_vars system_name true ([], [], []) sys_def.input in
  let init_map, trans_map, output_svars = mk_vars system_name true (init_map, trans_map, []) sys_def.output in
  let init_map, trans_map, local_svars = mk_vars system_name true (init_map, trans_map, []) sys_def.local in

  (* TODO May need to make this an assoc list as in the sexp interpreter *)
  let symb_svars = input_svars @ output_svars @ local_svars in (*S*)

  (* TODO Lots of subsystem stuff here *)
  
  (* let const_map = mk_init_map const_decls in *)
  let const_map = [] in (* TODO *)
  
  let inv_map_for_init = init_map in (* For notational puposes only. Just need the inv map for the init formula. *)
  let inv_map_for_trans = mk_inv_map init_map trans_map in
  
  (* TODO More subsystem stuff here. Refer to old sexp interpreter *)
  
  (* let subsystem_defs = mk_subsystems prev_trans_systems system_name cmc_sys_def.subsystems symb_svars in *)
  (* let named_subsystems = List.map fst subsystem_defs in  *)
  (* let subsystems, name_map = ... *) 
  (* TODO namemap should take the previous name map and add info to it 
    the previous namemap should be passed to this function (see sexp implementation) *)
  let subsystems, name_map = [], empty_subsystem_instance_name_data in
  (* let subsys_call_maps = List.map fst (List.map snd subsystem_defs) in *)
  (* let subsys_locals = List.flatten (List.map snd (List.map snd subsystem_defs)) in *)
  let subsys_locals = [] in
  (* let subsys_terms = ... *)
  (* let subsys_init = List.map fst subsys_terms in *)
  let subsys_init = [] in
  (* let subsys_trans = List.map snd subsys_terms in *)
  let subsys_trans = [] in

  let init_term = 
    KindTerm.mk_and ((mk_init_term sys_def init_flag const_map init_map inv_map_for_init) :: subsys_init )
  in
 
  let trans_term = 
    KindTerm.mk_and ((mk_trans_term sys_def init_flag const_map inv_map_for_trans trans_map) :: subsys_trans )
  in

  let state_vars =
    init_flag :: List.map snd (symb_svars @ subsys_locals)
   in

  let init_formals =  (* BOTH NEEDS SEPERATED *)
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.init_base
    )
    state_vars
  in


  let init_uf_symbol = (* BOTH NEEDS SEPERATED *)
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.init_uf_string system_name)
      (List.map Var.type_of_var init_formals)
      Type.t_bool
  in

  let trans_formals = (* BOTH NEEDS SEPERATED *)
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
  
  let trans_uf_symbol =  (* BOTH NEEDS SEPERATED *)
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.trans_uf_string system_name)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in
  Format.printf "CMC_SYS: %s." (UfSymbol.name_of_uf_symbol trans_uf_symbol) ;

  let symb_svars = symb_svars @ subsys_locals  in 
  {top=false; scope; name=sys_def.id;  input_svars; output_svars; local_svars; init_map; trans_map; init_flag; state_vars; init_uf_symbol; init_formals; init_term; trans_uf_symbol; trans_formals; trans_term; subsystems; props=[]}, name_map


let process_command definitions Statement.({id; descr; attrs; loc}) = 
  let* defs = definitions in
  match descr with
    (* (define-system symbol attrs)*)
  | Statement.Def_sys s -> 
    (* TODO update name_map instead of replaceing it *)
    let sys_def, name_map = mk_base_trans_system definitions s in

    Ok {defs with system_defs = sys_def :: defs.system_defs ; name_map;}
  |Statement.Set_logic l -> 
    (* TODO Actually do something here *)
    Ok defs
  | _ -> (error (E.NotSuppoted (DU.dolmen_opt_id_to_string id)))

(* Open and parse from file *)
let of_file filename = 

  (* Parse and Typecheck file with Dolmen *)
  let format, _, statements = M.parse_file filename in
  
  let* cmc_defs =
    List.fold_left process_command (Ok empty_definitions) statements
  in

  let cmc_sys_defs = cmc_defs.system_defs in
  Format.printf "LEN: %d@." (List.length cmc_sys_defs);

  (* TODO *)
  (* let enum_defs = cmc_defs.enums in *)
  let enum_defs = [] in
  (* We should no longer need to generate a sys ordering or
     determine cyclic system dependencies beacuse our typechecker verifys this.
     The typechecker requires that subsystems are defined before they are referenced.
     If we decide to remove this restriction, changes will need to be made
     to the typechecker and we will need to reintroduce the system ordering. *)

  (* TODO Match check_system commands with the system definitions and apply the props *)
  (* let cmc_check_defs = cmc_defs.system_checks in *)

  (* TODO create a mapping for systems to their vars like in the sexp interpreter. 
     This is required for counterexample printing. *)
  (* let sys_var_mapping = ...*)  
  let sys_var_mapping = [] in

  (* TODO implement after subsystems are used for CEX printing *)
  let name_map = cmc_defs.name_map in

  let mk_trans_system global_const_svars other_trans_systems (base : base_trans_system)  =
    let name = base.name in
    let subs = base.subsystems |> List.map (fun (name, local_instances) -> 
      (List.assoc name other_trans_systems, local_instances)) (* subsystems *)
    in
    let global_const_vars = List.map Var.mk_const_state_var global_const_svars in
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

  (* TODO Add global vars to this list *)
  let const_global_vars = [] in (* List.map snd cmc_defs.const_decls in *)
  let trans_systems = cmc_sys_defs |> List.fold_left (mk_trans_system const_global_vars) [] in
  
  let top_sys = snd (List.hd trans_systems) in

    (* NOTE: This was originaly commented out *)
  Format.printf "CMC_SYS: %a@." (TransSys.pp_print_subsystems true) top_sys;

  (* TODO pass all extra params for cex printing *)
  Ok (mk_subsys_structure top_sys, name_map, sys_var_mapping, enum_defs)
  (* Ok (mk_subsys_structure top_sys) *)

  (* (error (E.Impossible "CMC Interpreter with Dolmen not finished!")) *)

