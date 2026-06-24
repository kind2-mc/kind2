(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

exception UnsupportedFileFormat of string

module S = SubSystem
module N = LustreNode
module R = LustreReporting
module E = LustreErrors
module A = Analysis
module NI = NodeId
module D = LustreIndex
module Expr = LustreExpr

module SVar = StateVar

module SVS = SVar.StateVarSet
module SVM = SVar.StateVarMap

module IntSet = Stdlib.Set.Make(Int)

type _ t =
| Lustre : (N.t S.t list * LustreGlobals.t * LustreAst.declaration list) -> N.t t
| Moxi: (TransSys.t S.t * string list) list -> TransSys.t t
(* Lustre systems supports multiple entry points (main subsystems) *)
| Native : TransSys.t S.t -> TransSys.t t
| Horn : unit S.t -> unit t

let read_input_lustre only_parse input_file =
  match LustreInput.of_file only_parse input_file with
  | Ok (Some in_sys) -> Some (Lustre in_sys)
  | Ok None -> None
  | Error e -> R.fail_at_position (E.error_position e) (E.error_message e)

let translate_contracts_lustre = ContractsToProps.translate_file

let read_input_native input_file = Native (NativeInput.of_file input_file)

let read_input_moxi input_file =
  match MoxiInput.of_file input_file with
  | Ok system_checks -> Some (Moxi system_checks)
  | Error (MoxiInput.UnexpectedChar (pos, c)) ->
    Format.eprintf "%a: error: unexpected character ‘%c’@."
      Lib.pp_print_position pos c;
    None
  | Error (MoxiInput.SyntaxError pos) ->
    Format.eprintf "%a: syntax error@." Lib.pp_print_position pos;
    None

(*let read_input_horn input_file = assert false*)

let ordered_scopes_of (type s) : s t -> Scope.t list = function
  | Lustre (main_subs, _, _) ->
    S.all_subsystems_of_list main_subs
    |> List.map (fun { S.scope } -> scope)

  | Moxi checks ->
    let main_subs = List.map fst checks in
    S.all_subsystems_of_list main_subs
    |> List.map (fun { S.scope } -> scope)

  | Native subsystem ->
    S.all_subsystems subsystem
    |> List.map (fun { S.scope } -> scope)

  | Horn _ -> assert false

let analyzable_subsystems (type s) : s t -> s S.t list = function
  | Lustre (main_subs, _, _) ->
    let subsystems' =
      if Flags.modular () then S.all_subsystems_of_list main_subs
      else main_subs
    in
    subsystems'
    |> List.filter (fun s ->
      Strategy.is_candidate_for_analysis (S.strategy_info_of s))

  | Moxi checks -> let main_subs = List.map fst checks in main_subs

  | Native subsystem ->
    let subsystems' =
      if Flags.modular () then S.all_subsystems subsystem
      else [subsystem]
    in
    subsystems'
    |> List.filter (fun s ->
      Strategy.is_candidate_for_analysis (S.strategy_info_of s))

  | Horn _ -> assert false

(* Uid generator for test generation params.

/!\
    This is _wrong_.
    There's gonna be collision with the UIDs for regular analysis. Right now
    analyses and testgen are separate so that's fine, but be careful in the
    future.
/!\

*)
let testgen_uid_ref = ref 1
let get_testgen_uid () =
  let uid = !testgen_uid_ref in
  testgen_uid_ref := uid + 1 ;
  uid

(** Returns the analysis param for [top] that abstracts all its abstractable
    subsystems if [top] has a contract. *)
let maximal_abstraction_for_testgen (type s)
: s t -> Scope.t -> A.assumptions -> A.param option = function

  | Lustre (main_subs, _, _) -> (fun top assumptions ->

    (* Collects all subsystems, abstracting them if possible. *)
    let rec collect map = function
      | sub :: tail ->
        collect (Scope.Map.add sub.S.scope sub.S.has_contract map) tail
      | [] -> Some map
    in

    (* Finds [top] in the subsystems, and then calls [collect]. *)
    let rec get_abstraction_for_top = function
      | sub :: tail ->
        if sub.S.scope = top then
          (* Sub is the system we're looking for. *)
          if sub.S.has_contract then
            (* System has contracts, collecting subsystems. *)
            collect (Scope.Map.add sub.S.scope false Scope.Map.empty) tail
          else
            (* System has no contracts. *)
            None
        else
          (* Sub is not the system we're looking for, skipping. *)
          get_abstraction_for_top tail
      | [] ->
        Format.asprintf
          "system %a does not exist, cannot generate param for testgen"
          Scope.pp_print_scope_internal top
        |> failwith
    in

    match
      S.all_subsystems_of_list main_subs |> get_abstraction_for_top
    with

    (* Top is not abstractable. *)
    | None -> None

    (* All good. *)
    | Some map -> Some (
      A.First {
        A.top = top ;
        A.uid = get_testgen_uid () ;
        A.abstraction_map = map ;
        A.assumptions = assumptions ;
      }
    )

  )

  | Moxi _ -> assert false
  | Native _ -> assert false
  | Horn _ -> assert false

let next_analysis_of_strategy (type s)
: s t -> 'a -> A.param option = function

  | Lustre (main_subs, _, _) -> (
    fun results ->
      let scope_and_strategy =
        List.map (fun ({ S.scope } as sub) ->
          scope, S.strategy_info_of sub)
      in
      let all_syss =
        scope_and_strategy (S.all_subsystems_of_list main_subs)
      in
      if Flags.modular () then (
        let subs_of_scope scope =
          let { S.subsystems } as sub = S.find_subsystem_of_list main_subs scope in
          subsystems
          |> List.map (
            fun scope ->
              scope, S.strategy_info_of (S.find_subsystem sub scope)
          )
        in
        Strategy.next_modular_analysis results subs_of_scope all_syss
      )
      else (
        let main_syss = scope_and_strategy main_subs in
        Strategy.next_monolithic_analysis results main_syss all_syss
      )
  )

  | Native subsystem -> (
    fun results ->
      let scope_and_strategy =
        List.map (fun ({ S.scope } as sub) ->
          scope, S.strategy_info_of sub)
      in
      let all_syss =
        scope_and_strategy (S.all_subsystems subsystem)
      in
      if Flags.modular () then (
        let subs_of_scope scope =
          let { S.subsystems } as sub = S.find_subsystem subsystem scope in
          subsystems
          |> List.map (
            fun scope ->
              scope, S.strategy_info_of (S.find_subsystem sub scope)
          )
        in
        Strategy.next_modular_analysis results subs_of_scope all_syss
      )
      else (
        let main_syss = scope_and_strategy [subsystem] in
        Strategy.next_monolithic_analysis results main_syss all_syss
      )
  )
  
  | Moxi checks -> 
    fun results ->
      let scope_and_strategy =
        List.map (fun ({ S.scope } as sub) ->
          scope, S.strategy_info_of sub)
      in
      let main_subs = List.map fst checks in
      let all_syss =
        scope_and_strategy (S.all_subsystems_of_list main_subs)
      in
      if Flags.modular () then (
        let subs_of_scope scope =
          let { S.subsystems } as sub = S.find_subsystem_of_list main_subs scope in
          subsystems
          |> List.map (
            fun scope ->
              scope, S.strategy_info_of (S.find_subsystem sub scope)
          )
        in
        Strategy.next_modular_analysis results subs_of_scope all_syss
      )
      else (
        let main_syss = scope_and_strategy main_subs in
        Strategy.next_monolithic_analysis results main_syss all_syss
      )
  | Horn _ -> (function _ -> assert false)


let moxi_params (type s) (input_system : s t) =
  let param_for_subsystem sub =
    A.First {
      A.top = sub.S.scope ;
      A.uid = A.get_uid () ;
      A.abstraction_map = Scope.Map.empty ;
      A.assumptions = Scope.Map.empty ;
    }
  in
  match input_system with
  | Moxi checks ->
    let main_subs = List.map fst checks in
    List.map param_for_subsystem main_subs
  | _ -> []

let mcs_params (type s) (input_system : s t) =
  let param_for_subsystem sub =
    let scope, abstraction_map =
     sub.S.scope, (* Abstraction map *)
      List.fold_left (
        fun abs_map ({ S.scope; S.has_impl; S.has_contract }) ->
          if Flags.Contracts.compositional () then
            Scope.Map.add scope
              ((not has_impl || has_contract)
              && not (Scope.equal sub.S.scope scope))
              abs_map
          else
            Scope.Map.add scope (not has_impl) abs_map
        )
        Scope.Map.empty (S.all_subsystems sub)
    in
    A.First {
      A.top = scope ;
      A.uid = A.get_uid () ;
      A.abstraction_map = abstraction_map ;
      A.assumptions = Scope.Map.empty ;
    }
  in
  match input_system with
  | Lustre (main_subs, _, _) ->
    let subs =
      if Flags.modular ()
      then
        S.all_subsystems_of_list main_subs
        |> List.rev
      else
        main_subs
    in
    subs
    |> List.filter (fun { S.has_impl } -> has_impl)
    |> List.map param_for_subsystem
  | Native sub ->
    let subs =
      if Flags.modular ()
      then
        S.all_subsystems sub
        |> List.rev
      else
        [sub]
    in
    subs
    |> List.filter (fun { S.has_impl } -> has_impl)
    |> List.map param_for_subsystem

  | Moxi _ -> raise (UnsupportedFileFormat "MoXI")
  | Horn _ -> raise (UnsupportedFileFormat "Horn")


let contract_check_params (type s) (input_system : s t) =

  let param_for_subsystem sub =
    let scope = sub.S.scope in
    let subsystems = 
      List.map (fun s -> S.find_subsystem sub s) sub.S.subsystems
    in
    (A.ContractCheck {
      A.top = scope ;
      A.uid = A.get_uid () ;
      A.abstraction_map =
        List.fold_left
          (fun acc { S.scope; S.has_impl } ->
            Scope.Map.add scope (not has_impl) acc
          )
          (Scope.Map.singleton scope true)
          subsystems;
      A.assumptions = Scope.Map.empty ;
    }, sub.S.has_contract)
  in

  match input_system with
  | Lustre (main_subs, _, _) -> (
    S.all_subsystems_of_list main_subs
    |> List.filter (fun s -> not s.S.has_impl) 
    |> List.map param_for_subsystem
  )
  | Moxi _ -> []
  | Native _ -> []
  | Horn _ -> []

let interpreter_param (type s) (input_system : s t) =

  let scope, abstraction_map =
    match input_system with
    | Lustre (main_subs, _, _) ->
      let {S.scope} as sub =
        match main_subs with
        | [sub] -> sub
        | _ ->
          let msg =
            Format.asprintf
              "two or more top nodes detected, please select one with --lus_main or a single --%%MAIN annotation"
          in
          failwith msg
      in 
      (scope,
      List.fold_left (
        fun abs_map ({ S.scope; S.has_impl }) ->
          Scope.Map.add scope (not has_impl) abs_map
        )
        Scope.Map.empty (S.all_subsystems sub)
      )
    | Native ({S.scope} as sub) -> (scope,
      List.fold_left (
        fun abs_map ({ S.scope; S.has_impl }) ->
          Scope.Map.add scope (not has_impl) abs_map
        )
        Scope.Map.empty (S.all_subsystems sub)
    )
    | Moxi _ -> raise (UnsupportedFileFormat "MoXI")
    | Horn _ -> raise (UnsupportedFileFormat "Horn")
  in

  A.Interpreter {
    A.top = scope ;
    A.uid = A.get_uid () ;
    A.abstraction_map = abstraction_map ;
    A.assumptions = Scope.Map.empty ;
  }

let retrieve_lustre_nodes (type s) : s t -> N.t list =
  (function
  | Lustre (main_subs, _, _) -> 
    let subsystems = S.all_subsystems_of_list main_subs in
    List.map (fun sb -> sb.S.source) subsystems
  | Moxi _ -> failwith "Unsupported input system: MoXI"
  | Native _ -> failwith "Unsupported input system: Native"
  | Horn _ -> failwith "Unsupported input system: Horn"
  )

let retrieve_lustre_nodes_of_scope (type s) : s t -> Scope.t -> N.t list =
  (function
  | Lustre (main_subs, _, _) -> (fun scope ->
    S.find_subsystem_of_list main_subs scope |> N.nodes_of_subsystem
    )
  | Moxi _ -> failwith "Unsupported input system: MoXI"
  | Native _ -> failwith "Unsupported input system: Native"
  | Horn _ -> failwith "Unsupported input system: Horn"
  )

let contain_partially_defined_system (type s) (in_sys : s t) (top : Scope.t) =
  match in_sys with
  | Lustre _ -> (
    retrieve_lustre_nodes_of_scope in_sys top
    |> List.exists N.partially_defined
  )
  | Moxi _ -> failwith "Unsupported input system: MoXI"
  | Native _ -> failwith "Unsupported input system: Native"
  | Horn _ -> failwith "Unsupported input system: Native"

let get_lustre_node (type s) (input_system : s t) scope =
  match input_system with
  | Lustre (main_subs, _, _) -> (
    try Some (S.find_subsystem_of_list main_subs scope).S.source
    with Not_found -> None
  )
  | Moxi _ -> None
  | Native _ -> None
  | Horn _ -> None

let get_node_internal_name in_sys scope = 
  match get_lustre_node in_sys scope with 
  | Some node -> NodeId.get_internal_name node.node_id |> LustreIdent.of_hstring
  | None -> Lib.string_of_t Scope.pp_print_scope_internal scope |> LustreIdent.mk_string_ident

let get_node_user_name in_sys scope =
  match get_lustre_node in_sys scope with
  | Some node -> NodeId.get_user_name node.node_id |> LustreIdent.of_hstring
  | None -> Lib.string_of_t Scope.pp_print_scope_internal scope |> LustreIdent.mk_string_ident

let get_node_id in_sys scope =
  match get_lustre_node in_sys scope with 
  | Some { node_id; } -> node_id
  | None -> 
    NI.mk_node_id (Lib.string_of_t Scope.pp_print_scope_internal scope |> HString.mk_hstring)

let pp_print_subsystems_debug (type s) : Format.formatter -> s t -> unit =
  (fun fmt in_sys ->
    let lustre_nodes = retrieve_lustre_nodes in_sys in
    List.iter (Format.fprintf fmt "%a@." N.pp_print_node_debug) lustre_nodes
  )

let pp_print_state_var_instances_debug (type s) : Format.formatter -> s t -> unit =
  (fun fmt in_sys ->
    let lustre_nodes = retrieve_lustre_nodes in_sys in
    List.iter (
      Format.fprintf fmt "%a@." N.pp_print_state_var_instances_debug
    ) lustre_nodes
  )

let pp_print_state_var_defs_debug (type s) : Format.formatter -> s t -> unit =
  (fun fmt in_sys ->
    let lustre_nodes = retrieve_lustre_nodes in_sys in
    List.iter (
      Format.fprintf fmt "%a@." N.pp_print_state_var_defs_debug
    ) lustre_nodes
  )

let lustre_definitions_of_state_var (type s) (input_system : s t) state_var =
  match input_system with
  | Lustre _ -> N.get_state_var_defs state_var
  | Moxi _ -> failwith "Unsupported input system: MoXI"
  | Native _ -> failwith "Unsupported input system: Native"
  | Horn _ -> failwith "Unsupported input system: Horn"

let lustre_source_ast (type s) (input_system : s t) =
  match input_system with
  | Lustre (_,_,ast) -> ast
  | Moxi _ -> failwith "Unsupported input system: MoXI"
  | Native _ -> failwith "Unsupported input system: Native"
  | Horn _ -> failwith "Unsupported input system: Horn"

(* Return a transition system with [top] as the main system, sliced to
   abstractions and implementations as in [abstraction_map]. *)
let trans_sys_of_analysis (type s)
?(preserve_sig = false)
?(slice_nodes = Flags.slice_nodes ())
?(add_functional_constraints = true)
?slice_to_prop
: s t -> A.param -> TransSys.t * s t = function

  | Lustre (main_subs, globals, ast) -> (
    function analysis ->
      let t, s =
          let options =
            {
              LustreTransSys.preserve_sig;
              slice_nodes;
              add_functional_constraints;
              slice_to_prop
            }
          in
          LustreTransSys.trans_sys_of_nodes
            ~options globals main_subs analysis
      in
      t, Lustre ([s], globals, ast)
    )

  | Moxi checks -> (function analysis ->
    let { A.top } = A.info_of_param analysis in
    let main_subs = List.map fst checks in
    let sub = SubSystem.find_subsystem_of_list main_subs top in
    (sub.S.source, Native sub)
  )
  | Native sub -> (fun _ -> sub.S.source, Native sub)
    
  | Horn _ -> assert false



let pp_print_path_pt
(type s) ?(full_contract = false) (input_system : s t) trans_sys first_is_init ppf model =
  match input_system with 

  | Lustre (main_subs, globals, _) ->
    let sub =
      let scope = TransSys.scope_of_trans_sys trans_sys in
      S.find_subsystem_of_list main_subs scope
    in
    LustrePath.pp_print_path_pt ~full_contract:full_contract trans_sys globals sub first_is_init ppf model

  | Moxi _ ->
    Format.eprintf "pp_print_path_pt not implemented for MoXI input@.";
    ()

  | Native _ ->
    Format.eprintf "pp_print_path_pt not implemented for native input@.";
    ()
    (* assert false *)

  | Horn _ -> assert false


let pp_print_path_xml
(type s) (input_system : s t) trans_sys first_is_init ppf model =

  match input_system with 

  | Lustre (main_subs, globals, _) ->
    let sub =
      let scope = TransSys.scope_of_trans_sys trans_sys in
      S.find_subsystem_of_list main_subs scope
    in
    LustrePath.pp_print_path_xml
      trans_sys globals sub first_is_init ppf model

  | Moxi _ ->
    Format.eprintf "pp_print_path_xml not implemented for MoXI input@.";
    assert false;

  | Native _ ->
    Format.eprintf "pp_print_path_xml not implemented for native input@.";
    assert false;


  | Horn _ -> assert false

let pp_print_path_json_testgen
(type s) (input_system : s t) trans_sys first_is_init ppf model  =

  match input_system with

  | Lustre (main_subs, globals, _) ->
    let sub =
      let scope = TransSys.scope_of_trans_sys trans_sys in
      S.find_subsystem_of_list main_subs scope
    in
    LustrePath.pp_print_path_json_testgen
      trans_sys globals sub first_is_init ppf model

    | Moxi _ ->
    Format.eprintf "pp_print_path_json_testgen not implemented for MoXI input@.";
    assert false;

  | Native _ ->
    Format.eprintf "pp_print_path_json_testgen not implemented for native input@.";
    assert false;

  | Horn _ -> assert false



let pp_print_path_json
(type s) (input_system : s t) trans_sys first_is_init ppf model =

  match input_system with

  | Lustre (main_subs, globals, _) ->
    let sub =
      let scope = TransSys.scope_of_trans_sys trans_sys in
      S.find_subsystem_of_list main_subs scope
    in
    LustrePath.pp_print_path_json
      trans_sys globals sub first_is_init ppf model

  | Moxi _ ->
    Format.eprintf "pp_print_path_json not implemented for MoXI input@.";
    assert false;

  | Native _ ->
    Format.eprintf "pp_print_path_json not implemented for native input@.";
    assert false;

  | Horn _ -> assert false


let pp_print_path_in_csv
(type s) (input_system : s t) trans_sys first_is_init ppf model =
  match input_system with

  | Lustre (main_subs, globals, _) ->
    let sub =
      let scope = TransSys.scope_of_trans_sys trans_sys in
      S.find_subsystem_of_list main_subs scope
    in
    LustrePath.pp_print_path_in_csv
      trans_sys globals sub first_is_init ppf model

  | Moxi _ ->
    Format.eprintf "pp_print_path_in_csv not implemented for MoXI input";
    assert false

  | Native _ ->
    Format.eprintf "pp_print_path_in_csv not implemented for native input";
    assert false

  | Horn _ -> assert false


let reconstruct_lustre_streams (type s) (input_system : s t) state_vars =
  match input_system with 
  | Lustre (main_subs, _, _) ->
    LustrePath.reconstruct_lustre_streams main_subs state_vars
  | Moxi _ -> assert false
  | Native _ -> assert false
  | Horn _ -> assert false


let mk_state_var_to_lustre_name_map (type s):
  s t -> StateVar.t list -> string StateVar.StateVarMap.t =
fun sys vars ->
  SVM.fold
    (fun sv l acc ->
      (* If there is more than one alias, the first one is used *)
      let sv', path = List.hd l in
      let scope =
        List.fold_left
          (fun acc (lid, n, _) ->
            Format.asprintf "%a[%d]"
              (LustreIdent.pp_print_ident true) lid n :: acc
          )
          []
          path
      in
      let var_name = StateVar.name_of_state_var sv' in
      let full_name =
        String.concat "." (List.rev (var_name :: scope))
      in
      (* Format.printf "%a -> %s@." StateVar.pp_print_state_var sv full_name ; *)
      SVM.add sv full_name acc
    )
    (reconstruct_lustre_streams sys vars)
    SVM.empty


let call_state_var_to_lustre_reference (type s):
s t -> StateVar.t list -> string StateVar.StateVarMap.t =
fun sys vars ->
SVM.fold
  (fun sv l acc ->
    (* If there is more than one alias, the first one is used *)
    let sv', path = List.hd l in
    let scope =
      List.fold_left
        (fun acc (lid, n, _) ->
          Format.asprintf "%a[%d]"
            (LustreIdent.pp_print_ident true) lid n :: acc
        )
        []
        path
    in
    match scope with
    | [] -> acc
    | _ -> (
      let var_name = StateVar.name_of_state_var sv' in
      let full_name =
        String.concat "." (List.rev (var_name :: scope))
      in
      (* Format.printf "%a -> %s@." StateVar.pp_print_state_var sv full_name ; *)
      SVM.add sv full_name acc
    )
  )
  (reconstruct_lustre_streams sys vars)
  SVM.empty

let pp_print_term_as_expr
  (type s) (in_sys : s t) sys =
  let var_map =
    let aux_vars =
      let usr_name =
        assert (List.length LustreIdent.user_scope = 1) ;
        List.hd LustreIdent.user_scope
      in
      List.filter
        (fun sv ->
          not ( List.mem usr_name (StateVar.scope_of_state_var sv) )
        )
        (TransSys.state_vars sys)
    in
    mk_state_var_to_lustre_name_map in_sys aux_vars
  in
  LustreExpr.pp_print_term_as_expr_mvar false var_map


let is_lustre_input (type s) (input_system : s t) =
  match input_system with 
  | Lustre _ -> true
  | _ -> false

let is_moxi_input (type s) (input_system : s t) =
  match input_system with 
  | Moxi _ -> true
  | _ -> false

let slice_to_abstraction
(type s) (input_sys: s t) analysis trans_sys: s t =

  let scope = TransSys.scope_of_trans_sys trans_sys in

  (* Slicing is input-specific *)
  match input_sys with 

  (* Slice Lustre subnode to property term *)
  | Lustre (main_subs, globals, ast) ->

    let subsystem' =
      let sub = S.find_subsystem_of_list main_subs scope in
        LustreSlicing.slice_to_abstraction
          (Flags.slice_nodes () == `On) analysis sub
    in

    Lustre ([subsystem'], globals, ast)

  (* No slicing in native input *)
  | _ -> input_sys


let slice_to_abstraction_and_property
(type s) (input_sys: s t) analysis trans_sys cex prop
: TransSys.t * TransSys.instance list * (SVar.t * _) list * Term.t * s t = 

  (*
  (* Filter values at instants of subsystem. *)
  let filter_out_values = match input_sys with 

    | Lustre (subsystem, _) -> (fun scope { TransSys.pos } cex v -> 
          
      (* Get node cals in subsystem of scope. *)
      let { S.source = { N.calls } } = 
        S.find_subsystem subsystem scope 
      in
    
      (* Get clock of node call identified by its position. *)
      let { N.call_cond } = 
        List.find (fun {
            N.call_node_id; N.call_pos
          } -> call_pos = pos
        ) calls
      in

      (* Node call has an activation condition? *)
      match call_cond with 

        (* State variable for activation condition. *)
        | [_; N.CActivate clock_state_var] 
        | N.CActivate clock_state_var :: _ -> 

          (* Get values of activation condition from model. *)
          let clock_values = List.assq clock_state_var cex in

          (* Need to preserve order of values *)
          List.fold_right2 (fun cv v a -> match cv with

            (* Value of clock at this instant. *)
            | Model.Term t -> 

             (* Clock is true: keep value at instant. *)
             if Term.equal t Term.t_true then 
               v :: a

             (* Clock is false: skip instant. *)
             else if Term.equal t Term.t_false then 
               a

             (* Clock must be Boolean. *)
             else 
               assert false

            (* TODO: models with arrays. *)
            | _ -> assert false
            ) clock_values v []
            
        (* Keep all instants for node calls without activation
           condition. *)
        | _ -> v

    )

    (* Clocked node calls are only in Lustre, no filtering of instants in
       models for native input. *)
    | Native subsystem -> (fun _ _ _ v -> v)

    (* Clocked node calls are only in Lustre, no filtering of instants in
       models for Horn input. *)
    | Horn subsystem -> (fun _ _ _ v -> v)

  in  

  (* Map counterexample and property to S. *)
  let trans_sys', instances, cex', prop' =
    TransSys.map_cex_prop_to_subsystem 
      filter_out_values trans_sys cex prop
  in
  *)
  let trans_sys', instances, cex', prop' =
    trans_sys, [], cex, prop
  in

  let scope = TransSys.scope_of_trans_sys trans_sys' in

  (* Replace top system with subsystem for slicing. *)
  let analysis' =
    A.First {
      (A.info_of_param analysis)
      with A.top = scope
    }
  in

  (* Return subsystem that contains the property *)
  trans_sys', instances, cex', prop'.Property.prop_term, (

    (* Slicing is input-specific *)
    match input_sys with 

    (* Slice Lustre subnode to property term *)
    | Lustre (main_subs, globals, ast) ->

      let subsystem' =
        let sub = S.find_subsystem_of_list main_subs scope in
        LustreSlicing.slice_to_abstraction_and_property
          analysis' prop' sub
      in

      Lustre ([subsystem'], globals, ast)

    (* No slicing in MoXI input *)
    | Moxi m -> Moxi m

    (* No slicing in native input *)
    | Native subsystem -> Native subsystem

    (* No slicing in Horn input *)
    | Horn subsystem -> Horn subsystem
  )


let contract_gen_param (type s): s t -> Scope.t -> (A.param * (Scope.t -> N.t)) =
fun sys -> fun top ->
  match sys with
  | Lustre (main_subs, _, _) -> (
    let scope_and_strategy =
      List.map (fun ({ S.scope } as sub) ->
        scope, S.strategy_info_of sub)
    in
    match
      Strategy.next_monolithic_analysis
        (A.mk_results ())
        [top, S.strategy_info_of (S.find_subsystem_of_list main_subs top)]
        (scope_and_strategy (S.all_subsystems_of_list main_subs))
    with
    | None ->
      failwith "could not generate contract generation analysis parameter"
    | Some param ->
      param, (fun scope -> (S.find_subsystem_of_list main_subs scope).S.source)
  )
  | Moxi _ ->
    failwith "can't generate contracts from MoXI input: unsupported"
  | Native _ ->
    failwith "can't generate contracts from native input: unsupported"
  | Horn _ ->
    failwith "can't generate contracts from horn clause input: unsupported"

let state_var_dependencies (type s):
  s t -> (StateVar.StateVarSet.t StateVar.StateVarMap.t) Scope.Map.t =
function
  | Lustre (subsystem, _, _) -> (

    S.all_subsystems_of_list subsystem
    |> List.rev (* Process leaves first *)
    |> List.fold_left (fun (map, deps) { S.scope ; S.source } ->

      if Scope.Map.mem scope map then (map, deps)

      else (

        let init_node_deps, init_call_deps =
          LustreSlicing.state_var_dependencies true deps source
        in

        let tras_node_deps, trans_call_deps =
          LustreSlicing.state_var_dependencies false deps source
        in

        let sv_map =
          List.fold_left
            (fun sv_map (sv, deps) -> SVM.add sv deps sv_map)
            SVM.empty
            init_node_deps
          |> (fun sv_map ->
            List.fold_left
              (fun sv_map (sv, deps) ->
                SVM.update sv (function
                  | None -> Some deps
                  | Some deps' -> Some (SVS.union deps deps')
                )
                sv_map
              )
              sv_map
              tras_node_deps
          )
        in

        let node_name = source.N.node_id in

        Scope.Map.add scope sv_map map,
        (node_name, (init_call_deps, trans_call_deps)) :: deps

      )
    )
    (Scope.Map.empty, [])
    |> fst

  )

  | Moxi _ -> raise (UnsupportedFileFormat "MoXI")

  | Native _ -> raise (UnsupportedFileFormat "Native")

  | Horn _ -> raise (UnsupportedFileFormat "Horn")

let get_bv_sizes' (type s) : (IntSet.t -> SVar.t -> IntSet.t) -> s t -> IntSet.t = 
fun over_svar -> function 
| Lustre (main_subs, globals, _) -> 
  let subsystems = S.all_subsystems_of_list main_subs in 
  let sources = List.map (fun subsys -> subsys.S.source) subsystems in 
  (* Get sizes from every Lustre node *)
  List.fold_left (fun acc source -> 
    (* Oracle sizes *)
    let acc = List.fold_left over_svar acc source.N.oracles in 
    (* Input sizes *)
    let acc = List.fold_left over_svar acc (LustreIndex.values source.N.inputs) in 
    (* Output sizes *)
    let acc = List.fold_left over_svar acc (LustreIndex.values source.N.outputs) in 
    (* Local sizes *)
    let acc = List.fold_left over_svar acc (List.concat_map LustreIndex.values source.N.locals) in
    (* Global sizes *)
    List.fold_left over_svar acc (SVar.StateVarHashtbl.to_seq_keys globals.state_var_bounds |> List.of_seq)
  ) IntSet.empty sources
| Moxi checks -> 
  let subsystems = List.map fst checks in 
  let sources = List.map (fun subsys -> subsys.S.source) subsystems in 
  let state_vars = List.concat_map TransSys.state_vars sources in
  List.fold_left over_svar IntSet.empty state_vars
| Native sub -> 
  let subsystems = S.all_subsystems sub in
  let sources = List.map (fun subsys -> subsys.S.source) subsystems in 
  let state_vars = List.concat_map TransSys.state_vars sources in
  List.fold_left over_svar IntSet.empty state_vars
| Horn _ -> IntSet.empty

let get_bv_sizes (type s) : s t -> IntSet.t 
= fun sys -> 
  let over_svar = (fun acc svar ->
    let ty = SVar.type_of_state_var svar in 
    match Type.node_of_type ty with 
    | Type.BV width -> IntSet.add width acc
    | _ -> acc  
  ) in
  get_bv_sizes' over_svar sys
  
let get_ubv_sizes (type s) : s t -> IntSet.t 
= fun sys -> 
  let over_svar = (fun acc svar ->
    let ty = SVar.type_of_state_var svar in 
    match Type.node_of_type ty with 
    | Type.UBV width -> IntSet.add width acc
    | _ -> acc  
  ) in
  get_bv_sizes' over_svar sys

let current_state_props (type s): s t -> Scope.t -> string list =
fun sys -> fun top ->
  match sys with
  | Moxi checks -> (
    match List.find_opt (fun ({S.scope}, _) -> scope = top) checks with
    | Some (_, props) -> props
    | _ -> []
  )
  | Lustre _ -> []
  | Native _ -> []
  | Horn _ -> []

let prefix_system (type s) (input_system : s t) prefix : s t = match input_system with
  | Lustre (main_subs, globals, ast) ->

    let h_prefix = HString.mk_hstring prefix in

    let rename_node_id (node_id: NI.t) : NI.t =
      NI.mk_node_id
        ~node_type:(NI.get_node_type node_id)
        ~monomorphization: (NI.get_monomorphization node_id)
        ~user_name: (NI.get_user_name node_id |> HString.concat2 h_prefix)
        (NI.get_name node_id |> HString.concat2 h_prefix)
    in

    let rename_scope scope = match scope with
              | x :: xs -> (prefix ^ x) :: xs
              | [] -> assert false
    in

    let rename_state_var (sv: StateVar.t) : StateVar.t =
      StateVar.mk_state_var
        ~is_input:(StateVar.is_input sv)
        ~is_const:(StateVar.is_const sv)
        ~for_inv_gen:(StateVar.for_inv_gen sv)
        (StateVar.name_of_state_var sv)
        (StateVar.scope_of_state_var sv |> rename_scope)
        (StateVar.type_of_state_var sv)
    in

    let rename_svar (svar: LustreContract.svar) : LustreContract.svar =
      { svar with
      svar = rename_state_var svar.svar
      }
    in

    let rename_mode (mode: LustreContract.mode) : LustreContract.mode =
      { mode with
      requires = List.map rename_svar mode.requires;
      ensures = List.map rename_svar mode.ensures;
      }
    in

    let rename_contract (contract : LustreContract.t) : LustreContract.t =
      {
        assumes = List.map rename_svar contract.assumes;
        sofar_assump = (
          match contract.sofar_assump with
          | None -> None
          | Some v -> Some (rename_state_var v)
        );
        guarantees = List.map (fun (sv, candidate) -> (rename_svar sv, candidate)) contract.guarantees;
        modes = List.map rename_mode contract.modes;
      }
    in

    let rename_node_call (call: N.node_call) : N.node_call =
      { call with
        call_node_id = rename_node_id call.call_node_id;
        call_cond = List.map ( function
        | N.CActivate sv -> N.CActivate (rename_state_var sv)
        | N.CRestart sv -> N.CRestart (rename_state_var sv)
        ) call.call_cond
        ;
        call_inputs = D.map rename_state_var call.call_inputs;
        call_oracles = List.map rename_state_var call.call_oracles;
        call_outputs = D.map rename_state_var call.call_outputs;
      }
    in

    let rename_var = Var.map_state_var rename_state_var in

    let rename_expr = LustreExpr.map_vars rename_var in

    let rename_equation (eq : N.equation) : N.equation =
      let (lhs, expr) = eq in
      let (sv, wtf) = lhs in
      let new_wtf = List.map (function
      | Expr.Bound expr -> Expr.Bound (LustreExpr.map_vars_expr rename_var expr)
      | Expr.Fixed expr -> Expr.Fixed (LustreExpr.map_vars_expr rename_var expr)
      | Expr.Unbound expr -> Expr.Unbound (Option.map (LustreExpr.map_vars_expr rename_var) expr)
      ) wtf
      in
      ((rename_state_var sv, new_wtf), rename_expr expr)
    in

    let rename_node (node: N.t) : N.t =
      let result = { node with
        node_id = rename_node_id node.node_id;
        instance = rename_state_var node.instance;
        init_flag = rename_state_var node.init_flag;
        inputs = D.map rename_state_var node.inputs;
        oracles = List.map rename_state_var node.oracles;
        outputs = D.map rename_state_var node.outputs;
        locals = List.map (D.map rename_state_var) node.locals ;
        equations = List.map rename_equation node.equations;
        calls = List.map rename_node_call node.calls;
        asserts = List.map (fun (pos, sv) -> (pos, rename_state_var sv)) node.asserts;
        props = List.map (fun (sv, str, source, kind, expr) -> (rename_state_var sv, str, source, kind, expr)) node.props;
        contract = Option.map rename_contract node.contract;
        state_var_source_map = SVM.fold
          (fun sv source acc -> SVM.add (rename_state_var sv) source acc )
          node.state_var_source_map SVM.empty;
        (* oracle state var map *)
        state_var_expr_map = node.state_var_expr_map
          |> StateVar.StateVarHashtbl.to_seq
          |> Seq.map (fun (sv, expr) -> (rename_state_var sv, rename_expr expr))
          |> StateVar.StateVarHashtbl.of_seq;
        assumption_svars = SVS.map rename_state_var node.assumption_svars;
        (* history_svars *)
      } in
      result
    in

    let rename_sys (root : N.t SubSystem.t) : N.t SubSystem.t =
      let new_global_map = Scope.Hashtbl.create (Scope.Hashtbl.length root.map) in

      let rec rename (sub : N.t SubSystem.t) : N.t SubSystem.t =
        let new_scope = rename_scope sub.scope in
        let new_source = rename_node sub.source in
        let new_subsystems = List.map rename_scope sub.subsystems in

        let new_sub = {
          sub with
          scope = new_scope;
          source = new_source;
          subsystems = new_subsystems;
          map = new_global_map;
        } in

        Scope.Hashtbl.add new_global_map new_scope new_sub;

        sub.subsystems |> List.iter (fun scope ->
          if not (Scope.Hashtbl.mem new_global_map scope) then
            rename (Scope.Hashtbl.find root.map scope) |> ignore
        );
        
        new_sub
      in
      rename root
    in
    let main_subs = List.map rename_sys main_subs in
    Lustre (main_subs, globals, ast)
  | _ -> input_system


let monitor_param (type s) (input_system : s t) =
  let scope, abstraction_map =
    match input_system with
    | Lustre (main_subs, _, _) ->
      
      let {S.scope} as sub =
        match main_subs with
        | [sub] -> sub
        | _ ->
          let msg =
            Format.asprintf
              "two or more top nodes detected, please select one with --lus_main or a single --%%MAIN annotation"
          in
          failwith msg
      in 
      (scope,
       List.fold_left (
        fun abs_map ({ S.scope; S.has_impl }) ->
          Scope.Map.add scope ( Scope.equal scope sub.scope || not has_impl) abs_map
        )
        Scope.Map.empty (S.all_subsystems sub)
       )
    | Native ({S.scope} as sub) -> (scope,
      List.fold_left (
        fun abs_map ({ S.scope; S.has_impl }) ->
          Scope.Map.add scope (not has_impl) abs_map
        )
        Scope.Map.empty (S.all_subsystems sub)
    )
    | Moxi _ -> raise (UnsupportedFileFormat "MoXI")
    | Horn _ -> raise (UnsupportedFileFormat "Horn")
  in
  (* let map_print ppf (m: bool Scope.Map.t) = 
    Scope.Map.iter (fun k v -> Format.fprintf ppf "%d -> %b@\n" (length k) v) m
  in
  Format.printf "%a" map_print (abstraction_map)  ; *)
    (* Scope.Map.iter (fun k v ->
    Printf.printf "%s -> %b\n" (String.concat ", " k) v
  ) abstraction_map ; *)
  A.ContractMonitor {
    A.top = scope ;
    A.uid = A.get_uid () ;
    A.abstraction_map = abstraction_map ; 
    A.assumptions = Scope.Map.empty ;
  }

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
