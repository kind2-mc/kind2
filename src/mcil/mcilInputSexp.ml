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

module Ids = Lib.ReservedIds


module HS = HStringSExpr
module D = GenericSMTLIBDriver
module I = LustreIdent

open Dolmen

(* Instantiate a module for parsing logic languages *)
module M = Class.Logic.Make(Std.Loc)(Std.Id)(Std.Term)(Std.Statement)

module G = Graph.Make(struct
  type t = HString.t

  let compare id1 id2 = HString.compare id1 id2 

  let pp_print_t = HString.pp_print_hstring
end)


let conv = D.smtlib_string_sexpr_conv
let conv_type_of_sexpr = conv.D.type_of_sexpr
let conv_term_of_sexpr = conv.D.expr_of_string_sexpr conv

(** SMTLIB Keywords*)
let s_set_info = HString.mk_hstring "set-info"
let s_set_option = HString.mk_hstring "set-option"
let s_set_logic = HString.mk_hstring "set-logic"
let s_declare_sort = HString.mk_hstring "declare-sort"
let s_define_sort = HString.mk_hstring "define-sort"
let s_declare_const = HString.mk_hstring "declare-const"
let s_define_const = HString.mk_hstring "define-const"
let s_declare_fun = HString.mk_hstring "declare-fun"
let s_define_fun = HString.mk_hstring "define-fun"

(** Additional MCIL Keywords*)
let s_define_system = HString.mk_hstring "define-system"
let s_check_system = HString.mk_hstring "check-system"
let s_enum_definition = HString.mk_hstring "declare-enum-sort"
let s_input = HString.mk_hstring ":input"
let s_output = HString.mk_hstring ":output"
let s_local = HString.mk_hstring ":local"
let s_init = HString.mk_hstring ":init"
let s_trans = HString.mk_hstring ":trans"
let s_inv = HString.mk_hstring ":inv"
let s_subsystem = HString.mk_hstring ":subsys"
let s_reachable = HString.mk_hstring ":reachable"
let s_query = HString.mk_hstring ":query"
let s_only_change = HString.mk_hstring "OnlyChange"
let s_equal = HString.mk_hstring "="

(* type error = [
  | `McilTypeCheckerError of Lib.position * McilTypeChecker.error_kind
] *)

type subsystem_scope = string list
type sys_var_mapping = (subsystem_scope * StateVar.t list) list

type subsystem_instance_name_data = {
  map: (Lib.position * HString.t) list;
  counter: int;
}

let empty_subsystem_instance_name_data = {
  map = [];
  counter = 0;
}


type system_def = {
  name: HString.t;
  input: (HString.t * Type.t) list;
  output: (HString.t * Type.t) list;
  local: (HString.t * Type.t) list;
  init: HS.t option;
  trans: HS.t option;
  inv:  HS.t option;

  (*          ( sys_name * ( local_name * inputs list) list ) list    *)
  subsystems: (HString.t * (HString.t * HString.t list) list) list;
}

let empty_system_def = {
  name = HString.mk_hstring "";
  input = [];
  output = [];
  local = [];
  init = None;
  trans = None;
  inv = None;
  subsystems = [];
}

type check_system = {
  name: HString.t;
  input: (HString.t * Type.t) option list;
  output: (HString.t * Type.t) option list;
  local: (HString.t * Type.t) option list option;
  reachable: (HString.t * HS.t) list;
  query: (HString.t * HS.t) list;
}

let empty_check_system = {
  name = HString.mk_hstring "";
  input = [];
  output = [];
  local = None;
  reachable = [];
  query = [];
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
  system_checks: (HString.t * check_system) list;
  system_defs: (HString.t * system_def) list;
  enums: enum list;
  functions: TransSys.d_fun list;
  ufunctions: UfSymbol.t list;
  const_decls: (HString.t * StateVar.t) list;
}

let empty_definitions = {
  system_checks = [];
  system_defs = [];
  enums = [];
  functions = [];
  ufunctions = [];
  const_decls = [];
}

let mk_var sys_name is_input is_const (var, var_type) = 
  let svar =
    let name = HString.string_of_hstring var in
    let scope = (sys_name :: "impl" :: I.user_scope) in
    StateVar.mk_state_var
      ~is_input ~is_const ~for_inv_gen:true
      name scope var_type
    in
    (var, svar)

let mk_const_var var var_type = 
  mk_var "const-decl" false true (var, var_type)
  
let mk_vars sys_name is_input = List.map (mk_var sys_name is_input false)

let gen_enum_conversion_map enums =
  enums |> List.fold_left (fun to_int_maps {to_int} -> 
    (* Ensure each string is in only one enum *)
    let checked_enum_values = List.map (fun (str_rep, int_rep) -> 
        if List.mem_assoc str_rep to_int_maps then failwith (Format.asprintf "Enum value `%a` is defined twice." HString.pp_print_hstring str_rep)
        else (str_rep, (HString.mk_hstring (Int.to_string (Numeral.to_int int_rep))))
      ) to_int in
    checked_enum_values @ to_int_maps
  ) []

let enum_name_to_type enums enum_name =
  let enum = List.find (fun enum -> enum.name == enum_name) enums in
  enum.get_type

let is_enum_type_str enums enum_name = 
  let enum = List.find_opt (fun enum -> enum.name == enum_name) enums in
  match enum with 
  | Some _ -> true
  | _ -> false

let rec translate_sexp_atoms map sexp  =
  match sexp with
  | HS.List sexps -> HS.List (List.map (translate_sexp_atoms map) sexps)
  | HS.Atom exp -> match List.assoc_opt exp map with
    | Some trans_exp -> HS.Atom trans_exp
    | None -> HS.Atom exp


(** Gets the type of an s-expression*)
let get_type ty =
  (* Simplified version of VMTs implementation for now. Not using custom sorts yet. *)
  (* Wrapper used here to encourage expansion later *)
  conv_type_of_sexpr ty

let declare_const enums name fun_type =   
  let const_type = if is_enum_type_str enums fun_type 
  then 
    enum_name_to_type enums fun_type 
  else 
    get_type (HS.Atom fun_type) in
  mk_const_var name const_type 

(** Parse a list of sexp representing variable declarations *)
let parse_variable_declarations_opt enums = List.map (
  function (* parse variable names and types.*)
  | HS.List (HS.Atom var_name :: HS.Atom var_type :: []) -> (
    let ty = if is_enum_type_str enums var_type then enum_name_to_type enums var_type else get_type (HS.Atom var_type) in
    Some (var_name, ty)
  )
  | HS.Atom a when a == (HString.mk_hstring "_") -> None
  (* TODO: When custom types are implemented will need to allow lists for arg types *)
  (* For now lists and other imporperly formatted args will throw an error, may want to silently ignore in the future *)
  | HS.List (HS.Atom _ :: HS.List var_type :: []) ->  failwith (Format.asprintf "Custom variable type ( %a ) not yet supported. Please use Int, Bool, Real, or an enum sort." HS.pp_print_sexpr_list var_type)
  | e -> failwith (Format.asprintf "Malformed state variable %a" HS.pp_print_sexpr e)
)

let parse_variable_declarations enums vars = List.filter_map (fun a -> a) (parse_variable_declarations_opt enums vars)


let declare_fun enums name fun_type args = 
  let s_name = HString.string_of_hstring name in
  let svars = mk_vars s_name true (parse_variable_declarations enums args) in
  let named_vars = List.map (fun (name, sv) ->
    name, Var.mk_state_var_instance sv TransSys.init_base
  )
  svars in
  let vars = List.map snd named_vars in
  let ty = if is_enum_type_str enums fun_type then enum_name_to_type enums fun_type else get_type (HS.Atom fun_type) in
  let uf_name = UfSymbol.mk_uf_symbol
    s_name
    (List.map Var.type_of_var vars)
    ty
  in
  uf_name, ty, named_vars

let only_change total_vars change_vars =
  (* Might want to require one parm, but not strictly nessisary*)
  let change_vars_hs = change_vars |> List.map (fun name -> 
    match name with
    | HS.Atom hs_name when List.mem_assoc hs_name total_vars -> hs_name 
    | _ -> failwith (Format.asprintf "Invalid parameter `%a` given to OnlyChange constructor." HS.pp_print_sexpr name)) in
  let const_var_exprs = 
    total_vars |> List.filter_map (fun (name, _) ->
      if List.mem name change_vars_hs then (None) else (
        let expr = (HS.Atom s_equal) :: 
                   (HS.Atom name) :: 
                   (HS.Atom (HString.mk_hstring (HString.string_of_hstring name ^ "'"))) :: 
                   [] in
        Some (HS.List expr)
      )
    ) in 
  match const_var_exprs with
  | [] -> None
  | _ -> Some ( HS.List ( (HS.Atom (HString.mk_hstring "and") ) :: const_var_exprs ) )


(* let rec process_only_change sys_def trans_sexp = 
  match trans_sexp with
  | HS.Atom a -> HS.Atom a
  | HS.List list -> match list with
    | HS.Atom cmd :: args when cmd == s_only_change -> only_change (sys_def.output @ sys_def.local) args
    | _  -> HS.List ( list |> List.map (process_only_change sys_def) ) *)


let rec process_only_change_helper (sys_def: system_def) trans_sexp = 
  match trans_sexp with
  | HS.Atom a -> Some (HS.Atom a)
  | HS.List list -> match list with
    | HS.Atom cmd :: args when cmd == s_only_change -> (only_change (sys_def.output @ sys_def.local) args)
    | _  -> Some (HS.List ( list |> List.filter_map (process_only_change_helper sys_def) ) )
    
let process_only_change (sys_def: system_def) trans_sexp_opt = 
  match trans_sexp_opt with
  | None -> None
  | Some trans_sexp ->
    match process_only_change_helper sys_def trans_sexp with
    | Some HS.List [] -> None
    | None -> None
    | other -> other

let process_enum_definition name attrs =
  let count = Numeral.zero in
  
  let enum_type = Type.mk_type (Type.IntRange (count, (Numeral.of_int ((List.length attrs) - 1)), Type.Enum)) in
  
  let enum, _ = attrs |> List.fold_left ( fun (enums, count) enum_var -> match enum_var with
    | HS.Atom enum -> 
      ({enums with to_int = (enum, count) :: enums.to_int ; to_str = (count, enum) :: enums.to_str}, Numeral.(count + Numeral.one))
    | _ -> failwith (Format.asprintf "Invalid s-expresion found in enum definition `%s`." (HString.string_of_hstring name))
  ) ((empty_enum name enum_type), count) in
  enum

let rec process_check_system definitions check_def attrs = 
  match attrs with
  | HS.Atom arg :: HS.List inputs :: other when arg == s_input -> (
    let sys_inputs = parse_variable_declarations_opt definitions.enums inputs in 
    process_check_system definitions
      (* may want to remove append and just replace. 
         Depends what we want to do about multiple input statements. *)
      { check_def with input = sys_inputs @ check_def.input} 
      other
  )
  | HS.Atom arg :: HS.List outputs :: other when arg == s_output -> (
    let sys_outputs = parse_variable_declarations_opt definitions.enums outputs in 
    process_check_system definitions
      { check_def with output = sys_outputs @ check_def.output}
      other
  )
  | HS.Atom arg :: HS.List locals :: other when arg == s_local -> (
    let sys_locals = parse_variable_declarations_opt definitions.enums locals in 
    let other_locals = match check_def.local with None -> [] | Some locals -> locals in
    process_check_system definitions
      { check_def with local = Some (sys_locals @ other_locals)}
      other
  )
  (* Could use a less specific match so that we can throw meaningful errors.*)
  | HS.Atom arg :: HS.List [HS.Atom symb; formula] :: other when arg == s_reachable -> (
    process_check_system definitions
      (* may want to remove append and just replace. 
         Depends what we want to do about multiple input statements. *)
      { check_def with reachable = (symb, translate_sexp_atoms (gen_enum_conversion_map definitions.enums) formula) :: check_def.reachable} 
      other
  )
  | HS.Atom arg :: HS.List [HS.Atom symb; formula] :: other when arg == s_query -> (
    process_check_system definitions
      (* may want to remove append and just replace. 
         Depends what we want to do about multiple input statements. *)
      { check_def with query = (symb, formula) :: check_def.query} 
      other
  )
  | _ -> check_def

let define_fun definitions name fun_type args body = 
  let uf_name, ty, named_vars = declare_fun definitions.enums name fun_type args in
  let vars = List.map snd named_vars in

  let body_with_translated_enums = translate_sexp_atoms (gen_enum_conversion_map definitions.enums) body in
  let body_term = conv_term_of_sexpr named_vars body_with_translated_enums in
  TransSys.mk_d_fun uf_name ty vars body_term 


(** Process the MCIL [define-system] command. *)
let rec process_define_system definitions (sys_def: system_def) attrs =  
  match attrs with
  | HS.Atom arg :: HS.List inputs :: other when arg == s_input -> (
    let sys_inputs = parse_variable_declarations definitions.enums inputs in 
    process_define_system definitions
      (* may want to remove append and just replace. 
         Depends what we want to do about multiple input statements. *)
      { sys_def with input = sys_inputs @ sys_def.input} 
      other
  )
  
  | HS.Atom arg :: HS.List outputs :: other when arg == s_output -> (
    let sys_outputs = parse_variable_declarations definitions.enums outputs in 
    process_define_system definitions
      { sys_def with output = sys_outputs @ sys_def.output}
      other
  )

  | HS.Atom arg :: HS.List locals :: other when arg == s_local -> (
    let sys_locals = parse_variable_declarations definitions.enums locals in 
    process_define_system definitions
      { sys_def with local = sys_locals @ sys_def.local}
      other
  )

  (* What should we do if init appears twice?? raising error for now *)
  | HS.Atom arg :: init_eq :: other when arg == s_init -> (
    match sys_def.init with
    | Some _ -> failwith (Format.asprintf "Multiple :init formulas detected for system %s." (HString.string_of_hstring sys_def.name))
    | None -> (
      process_define_system definitions
      { sys_def with init = Some (translate_sexp_atoms (gen_enum_conversion_map definitions.enums) init_eq)} (* May want to change when the enum replacement happens later *)
      other
    )
  )

  | HS.Atom arg :: trans_eq :: other when arg == s_trans ->  (
    match sys_def.trans with
    | Some _ -> failwith (Format.asprintf "Multiple :trans formulas detected for system %s." (HString.string_of_hstring sys_def.name))
    | None -> (
      process_define_system definitions
      { sys_def with trans = Some (translate_sexp_atoms (gen_enum_conversion_map definitions.enums) trans_eq)} (* May want to change when the enum replacement happens later *)
      other
    )
  )

  | HS.Atom arg :: inv_eq :: other when arg == s_inv -> (
    match sys_def.inv with
    | Some _ -> failwith (Format.asprintf "Multiple :inv formulas detected for system %s." (HString.string_of_hstring sys_def.name))
    | None -> (
      process_define_system definitions
      { sys_def with inv = Some (translate_sexp_atoms (gen_enum_conversion_map definitions.enums) inv_eq)} (* May want to change when the enum replacement happens later *)
      other
    )
  )

  | HS.Atom arg ::  HS.List ( HS.Atom local_synonym_name :: HS.List (HS.Atom subsys_name :: subsys_inputs) :: []) :: other when arg == s_subsystem -> (
    let validate_local_name = 
      let local_sys_defs = List.concat (List.map snd sys_def.subsystems) in 
      match List.assoc_opt local_synonym_name local_sys_defs with 
      (* Create another localdef for subsys *)
      | None -> ()
      (* TODO: Ensure there is not a duplicate local def for different subsystems *)
      (* Duplicate local def for same subsystem *)
      | Some _ -> failwith (Format.asprintf "Local subsystem name `%s` found multiple definitions in `%s`." (HString.string_of_hstring local_synonym_name) (HString.string_of_hstring sys_def.name))
    in
    (* Fail if local name is already defined for this sys *)
    validate_local_name ;

    let inputs = subsys_inputs |> List.map (fun input -> match input with
        | HS.Atom input_name -> input_name
        | other -> failwith  (Format.asprintf "Parameters of a subsystem must be a variable name. %a of subsystem call %s is not " (HS.pp_print_sexpr) other (HString.string_of_hstring subsys_name))
        ) in
    
    match List.assoc_opt subsys_name sys_def.subsystems with
    (* subsys has one or more local defs*)
    | Some subsys -> (
      (* Prevent duplicates from being in list, important later when traversing list*)
      let others = List.remove_assoc subsys_name sys_def.subsystems in
      
      process_define_system definitions
        { sys_def with subsystems = ((subsys_name, (local_synonym_name, inputs) :: subsys) :: others)}
        other
      )
    (* create first local def for given subsystem *)
    | None -> (
      process_define_system definitions
      { sys_def with subsystems = ((subsys_name, (local_synonym_name, inputs) :: []) :: sys_def.subsystems)}
      other
    )
  )

  | HS.Atom invalid_arg :: arg_val :: other when HString.get invalid_arg 0 == ':' -> (
    match arg_val with (* Only remove two parameters when the second is not an arg *)
    | HS.Atom v when HString.get v 0 <> ':' -> process_define_system definitions sys_def other
    | HS.List _ -> process_define_system definitions sys_def other
    | _ -> process_define_system definitions sys_def ( arg_val :: other )
  )
  | HS.Atom invalid_arg :: other when HString.get invalid_arg 0 == ':' -> process_define_system definitions sys_def other
  | [] -> sys_def
  | _ -> failwith (Format.asprintf "Invalid define-system parameter: %a" HS.pp_print_sexpr_list attrs)

(** Parse one sexp and append it's interpretation into the mcil data structure*)
let process_command definitions = fun def -> match def with
(* (define-system symbol attrs)*)
| HS.List ( HS.Atom cmd :: HS.Atom symb :: attrs ) when cmd == s_define_system -> (
  {definitions with system_defs = ( symb, process_define_system definitions { empty_system_def with name = symb} attrs) :: definitions.system_defs}
)

(* (check-system symbol attrs)*)
| HS.List ( HS.Atom cmd :: HS.Atom symb :: attrs ) when cmd == s_check_system -> (
  
  {definitions with system_checks =
    (symb, process_check_system definitions { empty_check_system with name = symb} attrs) :: (* Will throw an error if the sys is not defined *)
    definitions.system_checks (* appending to front of assoc list is the same as updating. Could remove later if desired *)
  }
)

(* (declare-enum-sort name states)*)
| HS.List ( HS.Atom cmd :: HS.Atom name :: [ HS.List (attrs) ] ) when cmd == s_enum_definition -> (
  {definitions with enums = process_enum_definition name attrs :: definitions.enums}
)

(* (declare-fun name args type) *)
| HS.List ( HS.Atom cmd :: HS.Atom name :: HS.List args :: HS.Atom fun_type :: []) when cmd == s_declare_fun -> (
  match args with
  | [] -> 
    let const_decl_var = declare_const definitions.enums name fun_type in
    {definitions with const_decls = const_decl_var :: definitions.const_decls}
  | args ->   
    let uf_name, _, _ = declare_fun definitions.enums name fun_type args in
    {definitions with ufunctions = uf_name :: definitions.ufunctions}

)

(* (define-fun name args type term) *)
| HS.List ( HS.Atom cmd :: HS.Atom name :: HS.List args :: HS.Atom fun_type :: body :: []) when cmd == s_define_fun -> (
  let d_fun = define_fun definitions name fun_type args body in 
  {definitions with functions = definitions.functions @ d_fun :: []}
)

(* (declare-const name type) *)
| HS.List ( HS.Atom cmd :: HS.Atom name :: HS.Atom fun_type :: []) when cmd == s_declare_const -> (
  (* let uf_name, _, _ = declare_fun definitions.enums name fun_type [] in *)
  let const_decl_var = declare_const definitions.enums name fun_type in
  {definitions with const_decls = const_decl_var :: definitions.const_decls}
)

(* (define-const name args type term) *)
| HS.List ( HS.Atom cmd :: HS.Atom name :: HS.Atom fun_type :: body :: []) when cmd == s_define_const -> (
  let d_fun = define_fun definitions name fun_type [] body in 
  {definitions with functions = definitions.functions @ d_fun :: []}
)

| HS.List ( HS.Atom cmd :: HS.Atom _ :: _ ) when cmd == s_define_system -> failwith (Format.asprintf
"Invalid MCIL-LIBs command: %a" HS.pp_print_sexpr (HS.Atom cmd))

(* ... *)
(* Add back all SMT-LIB interpretations here*)
| c -> failwith (Format.asprintf
  "Invalid MCIL-LIBs command: %a" HS.pp_print_sexpr c)

(** Translate mcil var representation into Kind2 *)
let mk_state_vars sys_name input output local = (
  mk_vars sys_name true input @ 
  mk_vars sys_name false output @ 
  mk_vars sys_name false local
)

let mk_trans_map_opt (symb_svars: (HString.t * StateVar.t) option list) =
  List.fold_left 
      (fun acc var ->
        match var with 
        | Some (symb, svar) -> 
          let prev_base = Numeral.pred TransSys.trans_base in (* Why is this the previous value? ?*)
          let next_symb = HString.mk_hstring ( ( HString.string_of_hstring symb ) ^ "'" ) in
          Some (symb, Var.mk_state_var_instance svar prev_base) ::
          Some (next_symb, Var.mk_state_var_instance svar TransSys.trans_base) ::
          acc
        | _ -> None :: None :: acc
      )
      []
      symb_svars

let mk_trans_map (symb_svars: (HString.t * StateVar.t) list) =
  List.fold_left 
      (fun acc (symb, svar) ->
        let prev_base = Numeral.pred TransSys.trans_base in (* Why is this the previous value? ?*)
        let next_symb = HString.mk_hstring ( ( HString.string_of_hstring symb ) ^ "'" ) in
        (symb, Var.mk_state_var_instance svar prev_base) ::
        (next_symb, Var.mk_state_var_instance svar TransSys.trans_base) ::
        acc
      )
      []
      symb_svars

let mk_init_map (symb_svars: (HString.t * StateVar.t) list) =
  List.map
  (fun (symb, svar) ->
    (symb, Var.mk_state_var_instance svar TransSys.init_base)
  )
  symb_svars

(** A mapping of unprimed vars to their primed state. 
    Specifically used for invariant props in the transition system. *)
  let mk_inv_map init_map trans_map =  
    init_map |> List.map (fun (unprimed_var, _) -> 
    let primed_var = HString.concat2 unprimed_var (HString.mk_hstring "'") in 
    (unprimed_var, List.assoc primed_var trans_map )
  ) 

(* Create state variables for each invariant property *)
(* Currently simplified in the following ways:
    Assumes check systems only have one reachability statement in them
    Creates one state var for that reachability statement and no others. *)
  
let mk_invar_prop_svars sys_name { query ; reachable } =
  query |> List.map (fun (name, body) ->
    assert (List.length reachable == 1) ;
    let reachable_name = fst (List.hd reachable) in
    let full_name = Format.sprintf "%s" (HString.string_of_hstring reachable_name) in
    (* For now we make the simplifing assumption that there is only one reachable statement *)

    let scope = (sys_name :: I.reserved_scope) in
    StateVar.mk_state_var
      ~is_input:false ~is_const:false ~for_inv_gen:true
      full_name scope Type.t_bool,
    (name, body)
  )

(** Convert query s-exp into a term *)
let process_query reachable map body = 
  match body with
  | HS.List l_body -> l_body |> List.map (fun q_prop ->
    match q_prop with
    | HS.Atom q_prop_s when List.mem_assoc q_prop_s reachable -> 
      (* Must not the reachability query to make it in terms of invariance *)
      Term.mk_not (conv_term_of_sexpr map (List.assoc q_prop_s reachable))
      (* TODO Add cases for assumption, possibly also fairness and current *)
    | _ ->  failwith (Format.asprintf "Body of query malformed.") (* Make better msg in the future *)
  ) |> Term.mk_and (* Will require a different method here *)
  | _ -> failwith (Format.asprintf "Body of query malformed.") (* Make better msg in the future *)

let mk_init_invar_prop_eqs prop_svars reachable inv_map = 
  (* WARNING MAY NEED TO SUPPORT TWO STATES HERE (Only one state currently supported) *)
    prop_svars |> List.map (fun (svar, (_, term)) ->
      (* may need to differentiate querys from others if we have more inv props in the future *)
      let prop_def = process_query reachable inv_map term in (* while inv_map is used here it was not made specificly for this form of invariance *)
      let var = Var.mk_state_var_instance svar TransSys.init_base in
      Term.mk_eq [Term.mk_var var; prop_def]
    )

(** Reachibility queries in terms of invariance *)
(* Simply states that the invariant variable must equal the formula. Makes no other claims *)
let mk_trans_invar_prop_eqs prop_svars reachable inv_map =  (* WARNING MAY NEED TO SUPPORT TWO STATES HERE (Only one state currently supported) *)
  prop_svars |> List.map (fun (svar, (_, term)) ->
    let prop_def = process_query reachable inv_map term in (* while inv_map is used here it was not made specificly for this form of invariance *)
    let var = Var.mk_state_var_instance svar Numeral.zero in
      (Term.mk_eq
        [Term.mk_var var; prop_def])
    |> Term.bump_state Numeral.one
  )

(** Translate MCIL init sexp into Kind2 Term. Ands init with the inv property *)
let mk_init_term { init; inv} init_flag const_map init_map inv_map =
  (* Flag representing the init state*)
  let init_flag_t =
      Var.mk_state_var_instance init_flag TransSys.init_base
      |> Term.mk_var
  in

  match init, inv with
  | None, None -> init_flag_t                           (* The two inv maps are used to capture both a and a' *)
  | None, Some inv -> Term.mk_and (init_flag_t :: conv_term_of_sexpr (const_map @ inv_map) inv :: [])
  | Some init, None -> Term.mk_and (init_flag_t :: conv_term_of_sexpr (const_map @ init_map) init :: [])
  | Some init, Some inv -> 
    Term.mk_and (init_flag_t :: conv_term_of_sexpr (const_map @ init_map) init :: conv_term_of_sexpr (const_map @ inv_map) inv :: [])

  
(** Translate MCIL trans sexp into Kind2 Term. Ands init with the inv property *)
let mk_trans_term sys_def init_flag const_map inv_map trans_map =
  (* Flag representing the init state*)
  let init_flag_t =
    Var.mk_state_var_instance init_flag TransSys.trans_base
    |> Term.mk_var
  in
  match (process_only_change sys_def sys_def.trans), sys_def.inv with
  | None, None -> Term.mk_not init_flag_t                           (* The two inv maps are used to capture both a and a' *)
  | None, Some inv -> Term.mk_and (Term.mk_not init_flag_t :: conv_term_of_sexpr (const_map @ inv_map) inv :: [])
  | Some trans, None -> Term.mk_and (Term.mk_not init_flag_t :: conv_term_of_sexpr (const_map @ trans_map) trans :: [])
  | Some trans, Some inv -> 
    Term.mk_and (Term.mk_not init_flag_t :: conv_term_of_sexpr (const_map @ trans_map) trans :: conv_term_of_sexpr (const_map @ inv_map) inv :: [])

let rec mk_subsys_structure sys =
  { SubSystem.scope = TransSys.scope_of_trans_sys sys;
    source = sys;
    has_contract = false;
    has_impl = true;
    has_modes = false;
    subsystems =
      TransSys.get_subsystems sys
      |> List.map mk_subsys_structure;
  }

type base_trans_system = {
  top: bool;
  mcil_sys_def: system_def;
  symb_svars: (HString.t * StateVar.t) list;
  init_map: (HString.t * Var.t) list;
  trans_map: (HString.t * Var.t) list;
  scope: string list;
  init_flag: StateVar.t;
  state_vars: StateVar.t list;
  init_uf_symbol: UfSymbol.t;
  init_formals: Var.t list;
  init_term: Term.t;
  trans_uf_symbol: UfSymbol.t;
  trans_formals: Var.t list;
  trans_term: Term.t;
  subsystems: (HString.t * TransSys.instance list) list;
  props: Property.t list;
}

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
      assumes = None }

let mk_subsystems (prev_trans_systems: (HString.t * base_trans_system) list) sys_name (subsystems: (HString.t * (HString.t * HString.t list) list) list) (symb_svars: (HString.t * StateVar.t) list) = 
  subsystems |> List.map (fun (subsystem_name, local_defs) ->
    (* TODO if sys var names are not defined in parents it wont fail here, but it will fail much later on
      May want to add checking here so we can fail earlier. *)
    let subsys_trans_def = List.assoc subsystem_name prev_trans_systems in
    let get_svars symb_svars = List.map (fun (input_name, _) -> List.assoc input_name symb_svars) in
    
    let subsys_init_svar = subsys_trans_def.init_flag in
    let subsys_input_svars = get_svars subsys_trans_def.symb_svars subsys_trans_def.mcil_sys_def.input in
    let subsys_output_svars = get_svars subsys_trans_def.symb_svars subsys_trans_def.mcil_sys_def.output in

    let subsys_local_assoc_list = subsys_trans_def.symb_svars |> List.filter_map (fun symb_svar -> 
      match symb_svar with 
      | _ when List.assoc_opt (fst symb_svar) ( subsys_trans_def.mcil_sys_def.input @  subsys_trans_def.mcil_sys_def.output) = None -> Some (fst symb_svar, StateVar.type_of_state_var (snd symb_svar))
      | _ -> None

      ) in
    
    (* These are the svars that are passed as positional parms to the subsystem call *)

    let local_instances = local_defs |> List.map (fun (local_name, parameters) -> 
      (* These are the svars that are passed as positional parms to the subsystem call *)
      let transys_parameters = parameters |> List.map (fun parameter -> List.assoc parameter symb_svars)  in

      (* These are the local vars that must be created then passed as positional parms to the subsystem call *)
      let init_local = mk_var sys_name false false (HString.concat2 local_name (HString.mk_hstring "_init"), Type.t_bool) in
      let renamed_local_svarss = (subsys_local_assoc_list) |> 
        (List.map (fun (name, var_type) -> ((HString.concat (HString.mk_hstring "_") ( local_name :: name :: []) ), var_type)) ) in
      let new_transys_locals = mk_vars sys_name false (renamed_local_svarss) in

      let subsys_svars = (subsys_init_svar :: subsys_input_svars @ subsys_output_svars @ (get_svars subsys_trans_def.symb_svars subsys_local_assoc_list))  in 
      
      let transys_svars = ((snd init_local) :: transys_parameters @ (List.map snd new_transys_locals)) in
      
      let inst = (mk_inst subsys_svars transys_svars, local_name) in

      ((transys_svars, init_local :: new_transys_locals), inst)
    ) in

    let ret = (List.map fst local_instances) in

    let call_map =  (List.map fst ret) in
    let new_locals = List.flatten (List.map snd ret) in

    (subsystem_name, List.map snd local_instances), (call_map, new_locals)


    (* let new_transys_locals = mk_vars sys_name false (List.map (fun (name, _) -> )subsys_trans_def.mcil_sys_def.local)in

    (* TODO make failure message more clear when the lists do not match in size. *)
    let in_out_vars = subsys_mcil_def.input @ subsys_mcil_def.output |> local_defs |> List.map2 fun renamings 
    let 
    let instances = local_defs |> List.map (fun (local_name, sys_vars) ->
      ()
    ) in 
    subsys_locals, subsystem_defs *)
)

let mk_base_trans_system const_decls instance_name_map prev_trans_systems (mcil_sys_def: system_def) = 
  let system_name = HString.string_of_hstring mcil_sys_def.name in
  let scope = [system_name] in
  let init_flag = StateVar.mk_init_flag scope in

  let symb_svars = mk_state_vars system_name mcil_sys_def.input mcil_sys_def.output mcil_sys_def.local in (*S*)
  
  let subsystem_defs = mk_subsystems prev_trans_systems system_name mcil_sys_def.subsystems symb_svars in
  let named_subsystems = List.map fst subsystem_defs in 
  
  let subsystems, name_map = List.fold_left (fun (subsystems_acc, name_map) (subsys_name, (instance_list: (TransSys.instance * HString.t) list)) -> 
      
      let instances, instance_name_map = List.fold_left (fun (instances_acc, name_map) (instance, instance_name) -> 
        let pos = TransSys.({instance.pos with pos_lnum = name_map.counter}) in

        let inst = {instance with TransSys.pos = pos} in

        let name_map = {map = (pos, instance_name) :: name_map.map ; counter = name_map.counter + 1} in 

      instances_acc @ [inst] , name_map
      ) ([], name_map) instance_list in 

      ( subsystems_acc @ [(subsys_name, instances)], instance_name_map )
    ) ([], instance_name_map) named_subsystems  in
(* 
  let subsystems = named_subsystems in
  let name_map = empty_subsystem_instance_name_data in *)

  let subsys_call_maps = List.map fst (List.map snd subsystem_defs) in
  let subsys_locals = List.flatten (List.map snd (List.map snd subsystem_defs)) in

  (* let symb_svars = symb_svars @ subsys_locals  in  *)
  
  let const_map = mk_init_map const_decls in (* TODO: May want to rename mk_init_map  since it is used for consts *)
  let init_map = mk_init_map symb_svars in 
  let trans_map = mk_trans_map symb_svars in 
  
  let inv_map_for_init = init_map in (* For notational puposes only. Just need the inv map for the init formula. *)
  let inv_map_for_trans = mk_inv_map init_map trans_map in
(* 
  let subsys_init = subsystems |> List.map (fun (name, instances) -> 
    let subsys_name = UfSymbol.name_of_uf_symbol (List.assoc prev_trans_systems name) in
    let subsys_init_terms = instances |> List.mapi (fun i _ -> 
        Term.mk_and conv_term_of_sexpr init_map (HS.Atom (HString.mk_hstring (Printf.sprintf "%s_%i" subsys_name i))) :: ()
      )
  ) in *)

 
  let subsys_terms =  subsys_call_maps |> (subsystems |> List.map2 (fun ((name: HString.t), _) instance_call_maps -> 
    (* let subsys_name = UfSymbol.name_of_uf_symbol (List.assoc name prev_trans_systems ).init_uf_symbol in *)
    instance_call_maps |> List.map (fun call_map -> 
        let subsys_init_flag = (List.assoc name prev_trans_systems).init_flag in
        let init_flag_mapping = (HString.mk_hstring ( StateVar.name_of_state_var subsys_init_flag), subsys_init_flag) in
        let subsys_init_map = init_map @ (mk_init_map (init_flag_mapping :: subsys_locals)) in         
        let subsys_trans_map = trans_map @ (mk_trans_map (init_flag_mapping :: subsys_locals)) in         
        let cur = List.map (fun m -> (conv_term_of_sexpr subsys_init_map (HS.Atom (HString.mk_hstring (StateVar.name_of_state_var m))))) call_map in 
        let next = List.map (fun m -> (conv_term_of_sexpr subsys_trans_map (HS.Atom (HString.mk_hstring ((StateVar.name_of_state_var m)^"'"))))) call_map in 
        Term.mk_uf (List.assoc name prev_trans_systems ).init_uf_symbol  cur,
        Term.mk_uf (List.assoc name prev_trans_systems ).trans_uf_symbol  (next@cur)
    )
  ) )  |> (List.flatten) in 

  let subsys_init = List.map fst subsys_terms in
  let subsys_trans = List.map snd subsys_terms in

  let init_term = 
    Term.mk_and ((mk_init_term mcil_sys_def init_flag const_map init_map inv_map_for_init) :: subsys_init )
  in

  let trans_term = 
    Term.mk_and ((mk_trans_term mcil_sys_def init_flag const_map inv_map_for_trans trans_map) :: subsys_trans )
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
  Format.printf "MCIL_SYS: %s." (UfSymbol.name_of_uf_symbol trans_uf_symbol);

  let symb_svars = symb_svars @ subsys_locals  in 
  {top=false; scope; mcil_sys_def; symb_svars; init_map; trans_map; init_flag; state_vars; init_uf_symbol; init_formals; init_term; trans_uf_symbol; trans_formals; trans_term; subsystems; props=[]}, name_map

let rename_check_vars system_name {mcil_sys_def; trans_map} mcil_check_def = 
  let chk_inp, chk_out, chk_local = mcil_check_def.input, mcil_check_def.output, mcil_check_def.local in
  let chk_local = match chk_local with 
  | Some chk_local -> chk_local
  | None -> mcil_sys_def.local |> List.map (fun _ -> None) in
  assert (List.compare_lengths mcil_sys_def.input chk_inp == 0) ;
  assert (List.compare_lengths mcil_sys_def.output chk_out == 0) ;
  assert (List.compare_lengths mcil_sys_def.local chk_local == 0) ;

  let mk_vars sys_name is_input = List.map (fun e -> match e with 
  | Some e ->Some (mk_var sys_name is_input false e)
  | None -> None) in 

  (* Translate mcil var representation into Kind2 *)
  let mk_state_vars sys_name input output local = (
    mk_vars sys_name true input @ 
    mk_vars sys_name false output @ 
    mk_vars sys_name false local
  ) in 

  let chk_state_vars_opt = mk_state_vars system_name chk_inp chk_out chk_local in
  let chk_trans_map = mk_trans_map_opt chk_state_vars_opt in (*S*)

  (chk_trans_map |> ( trans_map |> List.map2 (fun map chk ->
    match chk with
    | Some chk -> Some (fst chk,  snd map)
    | None -> None
  ) )) |> List.filter_map (fun a -> a) 


let check_trans_system system_name base_system (mcil_check_def: check_system)= 
  (* TODO Produce better error handling here*)
  let check_map = rename_check_vars system_name base_system mcil_check_def in
  
  (* let chk_inv_map = chk_init_map in *)

  let invar_prop_svars = mk_invar_prop_svars system_name mcil_check_def in  (*C*)
  let prop_svars = invar_prop_svars in (* Present to support concat in the future *)  (*C*)
  
  
  
  let init_term = Term.mk_and ( base_system.init_term :: mk_init_invar_prop_eqs prop_svars mcil_check_def.reachable check_map ) in
  let trans_term = Term.mk_and ( base_system.trans_term :: mk_trans_invar_prop_eqs prop_svars mcil_check_def.reachable check_map ) in
  
  let props = (*C*)
    invar_prop_svars |> List.map (fun (svar, (name, _)) ->
      let var = Var.mk_state_var_instance svar TransSys.prop_base in
      {
        Property.prop_name = Format.sprintf "%s" (HString.string_of_hstring name); (*Used to prepend invar-property-*)
        prop_source = Property.PropAnnot Lib.dummy_pos;
        prop_term = Term.mk_var var;
        prop_status = Property.PropUnknown
      }
    )
  in

  let state_vars =
    base_system.state_vars @ List.map fst prop_svars
   in

  let init_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.init_base
    )
    state_vars
  in

  let init_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.init_uf_string "check_"^system_name)  (*TODO need to change name to support multiple checks*)
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
      (Format.sprintf "%s_%s" Ids.trans_uf_string "check_"^system_name) (*TODO need to change name to support multiple checks*)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in

  {base_system with 
    init_term; trans_term; props;
    state_vars; 
    init_formals; init_uf_symbol;
    trans_formals; trans_uf_symbol}


(* Parse from input channel *)
let of_channel in_ch = 

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  (* let sexps = List.map fst sexps in *)

  let mcil_defs =
    List.fold_left process_command empty_definitions sexps
  in

  let mcil_sys_defs = mcil_defs.system_defs in

  let enum_defs = mcil_defs.enums in

  (* TODO: Check for cycles in subsystems. See lustre/lustreArrayDependencies.ml and utils/graph.ml *)
  let mk_subsys_dag (mcil_sys_defs: (HString.t * system_def) list) = 
    (* First add all verticies *)
    let graph = mcil_sys_defs |> List.fold_left ( fun graph (name, _)  ->
      G.add_vertex graph name
    ) G.empty in
    
    (* Generate pairs for each subsys edge *)
    let edge_pairs = mcil_sys_defs |> List.fold_left ( fun ep (name, ({subsystems}: system_def))  ->
      (* currently does not check anything about local namings only checks overall subsys dependancies *)
      let sys_edges = subsystems |> List.map ( fun (target_name, _) ->
        (name, target_name)
      ) in 
      sys_edges @ ep
    ) [] in

    (* now add edges to all subsystems *)
    edge_pairs |> List.fold_left ( fun graph (src, tgt)  ->
      (* mk_edge fails when verticies are not in graph *)
      (* This is desired but we may want to catch to provide better messaging *)
      let edge = G.mk_edge src tgt in
      G.add_edge graph edge
    ) graph
  in

  

  let subsys_graph = mk_subsys_dag mcil_sys_defs in

  (* Will now throw an error if there is a cycle in the graph *)
    (* Again may want to catch in the future for better messages *)
  let sys_ordering = G.topological_sort subsys_graph in

  (* DEBUG messages for now *)
  Format.printf "%a" G.pp_print_graph subsys_graph;
  List.iter (Format.printf "%a" HString.pp_print_hstring) sys_ordering;

  (* NEXT steps
     1. rewrite mk_base_trans_system to actually make a trans system. May need to save additional data for props later
     2. call funct in 1 for each sys in sys_ordering 
      2a. create and add subsystems to trans systems
     3. modify check system to modify trans systems rather then intermed data struct 
     4. process each trans sys that has a check (just one for now) *)

  let mcil_check_defs = mcil_defs.system_checks in
  let length = List.length sys_ordering in

  let base_trans_systems, (name_map, _) = sys_ordering |> List.fold_left ( fun (prev_trans_systems, (prev_instance_map, index)) sys_name -> 
    let top = index == length - 1 in
    let mcil_sys_def = List.assoc sys_name mcil_sys_defs in
    let mcil_check_def_opt = List.assoc_opt sys_name mcil_check_defs in 
    let base_system, name_map = mk_base_trans_system mcil_defs.const_decls prev_instance_map prev_trans_systems mcil_sys_def in
    match mcil_check_def_opt with 
    | Some mcil_check_def -> prev_trans_systems @ (mcil_sys_def.name, check_trans_system (HString.string_of_hstring mcil_sys_def.name) {base_system with top} mcil_check_def) :: [], (name_map, index + 1)
    | None -> prev_trans_systems @ (mcil_sys_def.name, {base_system with top}) :: [], (name_map, index + 1)
  ) ([], (empty_subsystem_instance_name_data, 0)) in
(* 
  let mk_inst init_flag sys formal_vars =
    let map_down, map_up =
      List.fold_left (fun (map_down, map_up) vf ->
          let v =
            if StateVar.equal_state_vars vf (TransSys.init_flag_state_var sys)
            then init_flag
            else add_scope_state_var [obs_name] vf
          in
          StateVar.StateVarMap.add v vf map_down,
          StateVar.StateVarMap.add vf v map_up
        ) StateVar.StateVarMap.(empty, empty) formal_vars
    in
    sys,
    [ { TransSys.pos = Lib.dummy_pos;
        map_down;
        map_up;
        guard_clock = (fun _ t -> t);
        assumes = None } ] in

  let create_trans_system base_trans_systems = 
    base_trans_systems |> List.fold_left ( fun base_trans_system ->
      let subsystem_definitions = base_trans_system.mcil_sys_def.subsystems in 
        (*          ( sys_name * ( local_name * inputs list) list ) list    *)
  (* subsystems: (HString.t * (HString.t * HS.t list) list) list; *)
  (* [ { TransSys.pos = Lib.dummy_pos;
      map_down;
      map_up;
      guard_clock = (fun _ t -> t);
      assumes = None } ]
       *)
      let mk_subsystems = subsystem_definitions |> List.map (fun (subsystem_name, local_defs) ->
        let instances = local_defs |> List.map (fun (local_name, sys_vars) ->
          mk_inst base_trans_system.init_flag 
        )
      )
    ) 
  [] in *)
  
  let sys_var_mapping = List.fold_left (fun var_map (_, base_transys) -> (
    let primary_vars = (base_transys.mcil_sys_def.input @ base_transys.mcil_sys_def.output @ base_transys.mcil_sys_def.local) |>
          List.map (fun v -> List.assoc (fst v) base_transys.symb_svars) in
    (base_transys.scope, primary_vars) :: var_map
  )) [] base_trans_systems in

  let mk_trans_system global_const_svars other_trans_systems base_trans_system  =
    let (name: HString.t), base = base_trans_system in
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
        (if base.top then mcil_defs.ufunctions else []) (* ufs *)
        (if base.top then mcil_defs.functions else []) (* defs *)
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

  let const_global_vars = List.map snd mcil_defs.const_decls in
  let trans_systems = base_trans_systems |> List.fold_left (mk_trans_system const_global_vars) [] in
  
  (* let mcil_sys_def =  snd (head mcil_sys_defs) in (* temporary support for only one system def *)
  let mcil_check_def = List.assoc mcil_sys_def.name mcil_check_defs in *)

  (* let base_system = mk_base_trans_system [] mcil_sys_def in 
  let chk_sys = check_trans_system (HString.string_of_hstring mcil_sys_def.name) base_system mcil_check_def in
   *)

  (* TEMP *)
  (* TODO: *)
  let top_sys = snd (List.hd trans_systems) in

    (* NOTE: This was originaly commented out *)
  Format.printf "MCIL_SYS: %a@." (TransSys.pp_print_subsystems true) top_sys;

  Ok (mk_subsys_structure top_sys, name_map, sys_var_mapping, enum_defs)
  (* mk_subsys_structure top_sys, name_map, sys_var_mapping, enum_defs *)


  (* Print Here ... Use Format.printf
  Printf.printf ... *)
  


(* Open and parse from file *)
let of_file filename = 

  (* Open the given file for reading *)
  let use_file = open_in filename in
  let format, _, statements = M.parse_file filename in
  Format.printf "DONE" ;
  List.iter (Format.printf "%a" Std.Statement.print) statements ;


  let in_ch = use_file in

  of_channel in_ch

