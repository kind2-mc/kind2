(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020-2021 by the Board of Trustees of the University of Iowa

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

open Realizability

module ISys = InputSystem
module TSys = TransSys

module LN = LustreNode
module LC = LustreContract
module ME = ModelElement
module VS = Var.VarSet

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module UFM = UfSymbol.UfSymbolMap


let get_assumption_vars in_sys sys =
  let scope = TSys.scope_of_trans_sys sys in
  
  match ISys.get_lustre_node in_sys scope with
  | Some { LN.contract } -> (
    match contract with
    | Some { LC.sofar_assump } -> (
      let svar_deps =
        match Scope.Map.find_opt scope (ISys.state_var_dependencies in_sys) with
        | Some deps -> deps
        | None -> assert false
      in
      try (
        SVM.find sofar_assump svar_deps
        |> SVS.add sofar_assump
      ) with Not_found -> assert false
    )
    | None -> SVS.empty
  )
  | None -> assert false


let compute_input_system_svars in_sys sys =
  let scope = TSys.scope_of_trans_sys sys in
  match ISys.get_lustre_node in_sys scope with
  | Some { LN.inputs; LN.locals; LN.outputs } -> (
    let outputs =
      List.map snd (LustreIndex.bindings outputs) |> SVS.of_list
    in
    let inputs =
      List.map snd (LustreIndex.bindings inputs) |> SVS.of_list
    in
    let locals =
      locals |> List.map (fun l ->
        List.map snd (LustreIndex.bindings l)
      )
      |> List.concat |> SVS.of_list
    in
    SVS.union outputs inputs |> SVS.union locals
  )
  | None -> assert false


let get_node_calls in_sys sys =
  let scope = TSys.scope_of_trans_sys sys in
  match ISys.get_lustre_node in_sys scope with
  | Some { LN.calls } -> calls
  | None -> assert false


let compute_assump_instance_vars in_sys sys assumption_vars =
  let in_sys_svars = compute_input_system_svars in_sys sys in
  let node_calls = get_node_calls in_sys sys in
  let instances =
    TSys.get_subsystem_instances sys |> List.map snd |> List.concat
  in
  List.fold_left
    (fun acc_vars { TSys.pos; TSys.map_down } ->
      let r =
        List.find_opt
          (fun { LN.call_pos } -> Lib.equal_pos pos call_pos)
          node_calls
      in
      match r with
      | Some { LN.call_outputs } -> (
        let call_outputs =
          List.map snd (LustreIndex.bindings call_outputs) |> SVS.of_list
        in
        if SVS.inter call_outputs assumption_vars |> SVS.is_empty then
          acc_vars
        else (
          let call_vars =
            SVM.fold (fun sv _ acc -> SVS.add sv acc) map_down SVS.empty
          in
          let trans_svars =
            call_vars
            |> SVS.filter (fun sv -> SVS.mem sv in_sys_svars |> not)
          in
          SVS.union acc_vars trans_svars
        )
      )
      | None -> assert false
    )
    SVS.empty
    instances

let compute_controllable_vars in_sys sys vars_at_1 =
  let assumption_vars =
    let avars = get_assumption_vars in_sys sys in
    SVS.union avars (compute_assump_instance_vars in_sys sys avars)
  in

  let controllable_vars_at_0 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.zero Numeral.zero
    |> List.filter (fun v ->
      not (Var.is_const_state_var v) &&
      let sv = Var.state_var_of_state_var_instance v in
      not (StateVar.is_input sv) &&
      not (SVS.mem sv assumption_vars)
    )
  in

  let controllable_vars_at_1 =
    vars_at_1
    |> List.filter (fun v ->
      let sv = Var.state_var_of_state_var_instance v in
      not (StateVar.is_input sv) &&
      not (SVS.mem sv assumption_vars)
    )
  in

  controllable_vars_at_0, controllable_vars_at_1


let check_contract_realizability in_sys sys =

  (*Format.printf "%a@." InputSystem.pp_print_subsystems_debug in_sys;*)

  let vars_at_1 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.one Numeral.one
    |> List.filter (fun v -> not (Var.is_const_state_var v))
  in

  let controllable_vars_at_0, controllable_vars_at_1 =
    compute_controllable_vars in_sys sys vars_at_1
  in

  let call_output_args =
    let instances =
      TSys.get_subsystem_instances sys |> List.map fst
    in
    List.fold_left
      (fun acc called_sys ->
        let scope = TSys.scope_of_trans_sys called_sys in
        let init_uf_symbol = TSys.init_uf_symbol called_sys in
        let trans_uf_symbol = TSys.trans_uf_symbol called_sys in
        match ISys.get_lustre_node in_sys scope with
        | None -> assert false
        | Some { LN.inputs; LN.oracles; LN.outputs } -> (
          let nb_inputs = LustreIndex.cardinal inputs in
          let nb_oracles = List.length oracles in
          let nb_outputs = LustreIndex.cardinal outputs in
          UFM.add init_uf_symbol (nb_inputs+nb_oracles, nb_outputs) acc
          |> UFM.add trans_uf_symbol (nb_inputs+nb_oracles, nb_outputs)
        )
      )
      UFM.empty
      instances
  in

  let vars_of_term term =
    match Term.destruct term with
    | Term.T.App (s, args) when
      (match (Symbol.node_of_symbol s) with `UF _ -> true | _ -> false)
      -> ( (* Case of a node call *)
      let ufs = Symbol.uf_of_symbol s in
      match UFM.find_opt ufs call_output_args with
      | None -> Term.vars_of_term term
      | Some (s, k) -> (
        Lib.list_slice args s (s+k-1)
        |> List.fold_left
          (fun acc t -> VS.union acc (Term.vars_of_term t))
          VS.empty
      )
    )
    | _ -> Term.vars_of_term term
  in

  realizability_check
    vars_of_term sys controllable_vars_at_0 vars_at_1 controllable_vars_at_1


let compute_unviable_trace_and_core analyze in_sys param sys u_result =

  let vars_at_1 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.one Numeral.one
    |> List.filter (fun v -> not (Var.is_const_state_var v))
  in

  let controllable_vars_at_0, controllable_vars_at_1 =
    compute_controllable_vars in_sys sys vars_at_1
  in

  Realizability.compute_deadlocking_trace_and_conflict
    analyze in_sys param sys controllable_vars_at_0 controllable_vars_at_1 u_result
    

let core_desc = "conflicting constraints"

let pp_print_realizability_result_pt
  analyze in_sys param sys fmt result =
  (* Update time *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  let scope = (Analysis.info_of_param param).top in

  let print_not_unknown_result tag =
    Format.fprintf
      fmt
      "@[<hov>%t Contract of node %a was proven %s after %.3fs.@]@.@."
      tag
      Scope.pp_print_scope scope
      (Realizability.result_to_string result)
      (Stat.get_float Stat.analysis_time) ;
  in

  match result with
  | Unknown -> (
    Format.fprintf 
      fmt
      "@[<hov>%t Could not determine whether the contract of \
        %a is realizable or not after %.3fs.@]@.@."
      Pretty.warning_tag
      Scope.pp_print_scope scope
      (Stat.get_float Stat.analysis_time)
  )
  | Realizable _ ->
    print_not_unknown_result Pretty.success_tag

  | Unrealizable u_res ->
    print_not_unknown_result Pretty.failure_tag ;

    if Flags.Contracts.print_deadlock () || Flags.Contracts.dump_deadlock () then (
      KEvent.log L_note "Computing deadlocking trace and conflict..." ;
      let trace, core =
        compute_unviable_trace_and_core
          analyze in_sys param sys u_res
      in
      let cpd =
        ME.loc_core_to_print_data in_sys sys core_desc None core
      in
      (* Store dump_cex value *)
      let dump_cex = Flags.dump_cex () in 
      (* dump_deadlock uses same infrastructure as dump_cex*)
      Flags.set_dump_cex (Flags.Contracts.dump_deadlock ()) ; 
      Format.fprintf
        fmt
        "@[<v>%a@]@."
        (KEvent.pp_print_trace_pt
          ~title:"Deadlocking trace" ~color:"red" (Flags.dump_cex ())
          L_warn in_sys param sys None true)
        trace ;
      (* Restore dump_cex value *)
      Flags.set_dump_cex dump_cex ;

      Format.fprintf
        fmt
        "%a"
        (ME.pp_print_core_data in_sys param sys) cpd ;

      Format.pp_print_flush fmt ()
    )


let pp_print_realizability_result_json
  analyze in_sys param sys fmt result =
  (* Update time *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  let pp_print_trace_and_core =
    match result with
    | Unrealizable u_res -> (
      if Flags.Contracts.print_deadlock () then (
        let trace, core =
          compute_unviable_trace_and_core
            analyze in_sys param sys u_res
        in
        (fun fmt ->
          let cpd =
            ME.loc_core_to_print_data in_sys sys core_desc None core
          in
          Format.fprintf
          fmt
          ",@,%a,@,\
          \"conflictingSet\" : %a"
          (KEvent.pp_print_trace_json
            ~object_name:"deadlockingTrace" in_sys param sys None true)
          trace
          (ME.pp_print_core_data_json in_sys param sys) cpd
        )
      )
      else (fun _ -> ())
    )
    | _ -> (fun _ -> ())
  in
  Format.fprintf 
    fmt
    ",@.{@[<v 1>@,\
    \"objectType\" : \"realizabilityCheck\",@,\
    \"runtime\" : {\
      \"unit\" : \"sec\", \
      \"timeout\" : false, \
      \"value\" : %.3f\
    },@,\
    \"result\" : \"%s\"%t\
    @]@.}@.\
  "
  (Stat.get_float Stat.analysis_time)
  (Realizability.result_to_string result)
  pp_print_trace_and_core


let pp_print_realizability_result_xml
  analyze in_sys param sys fmt result =
  let tag = "RealizabilityCheck" in
  (* Update time *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  let pp_print_trace_and_core =
    match result with
    | Unrealizable u_res -> (
      if Flags.Contracts.print_deadlock () then (
        let trace, core =
          compute_unviable_trace_and_core
            analyze in_sys param sys u_res
        in
        (fun fmt ->
          let cpd =
            ME.loc_core_to_print_data in_sys sys core_desc None core
          in
          Format.fprintf
          fmt
          "@,%a@,%a"
          (KEvent.pp_print_trace_xml
            ~tag:"DeadlockingTrace" in_sys param sys None true)
          trace
          (ME.pp_print_core_data_xml ~tag:"ConflictingSet" in_sys param sys) cpd
        )
      )
      else (fun _ -> ())
    )
    | _ -> (fun _ -> ())
  in
  Format.fprintf 
    fmt
    ("@[<hv 2><%s>@,\
      <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
      <Result>%s</Result>%t@;<0 -2>\
      </%s>@]@.")
    tag
    (Stat.get_float Stat.analysis_time)
    (Realizability.result_to_string result)
    pp_print_trace_and_core
    tag


type satisfiability_result =
  | Satisfiable
  | Unsatisfiable
  | Unknown

let satisfiability_result_to_string = function
  | Satisfiable -> "satisfiable"
  | Unsatisfiable -> "unsatisfiable"
  | Unknown -> "unknown"

let check_contract_satisfiability sys =

  let sys, const_svars =
    TSys.enforce_constantness_via_equations sys
  in

  let vars_at_0 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.zero Numeral.zero
  in

  let vars_at_1 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.one Numeral.one
  in

  let res =
    realizability_check
      Term.vars_of_term (* It doesn't matter since all variables are controllable *)
      sys vars_at_0 vars_at_1 vars_at_1
  in

  List.iter (fun sv -> StateVar.set_const true sv) const_svars ;

  match res with
  | Realizable _ -> Satisfiable
  | Unrealizable _ -> Unsatisfiable
  | Unknown -> Unknown


let pp_print_satisfiability_result_pt param fmt result =
  (* Update time *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  let scope = (Analysis.info_of_param param).top in
  match result with
  | Unknown -> (
    Format.fprintf 
      fmt
      "@[<hov>%t Could not determine whether the contract of \
        %a is satisfiable or not after %.3fs.@]@."
      Pretty.warning_tag
      Scope.pp_print_scope scope
      (Stat.get_float Stat.analysis_time)
  )
  | _ -> (
    let tag =
      match result with
      | Satisfiable -> Pretty.success_tag
      | Unsatisfiable -> Pretty.failure_tag
      | Unknown -> assert false
    in
    Format.fprintf 
      fmt
      "@[<hov>%t Contract of node %a was proven %s after %.3fs.@]@.@."
      tag
      Scope.pp_print_scope scope
      (satisfiability_result_to_string result)
      (Stat.get_float Stat.analysis_time)
  )

let pp_print_satisfiability_result_json fmt result =
  (* Update time *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  Format.fprintf 
    fmt
    ",@.{@[<v 1>@,\
    \"objectType\" : \"satisfiabilityCheck\",@,\
    \"runtime\" : {\
      \"unit\" : \"sec\", \
      \"timeout\" : false, \
      \"value\" : %.3f\
    },@,\
    \"result\" : \"%s\"\
    @]@.}@.\
  "
  (Stat.get_float Stat.analysis_time)
  (satisfiability_result_to_string result)

let pp_print_satisfiability_result_xml fmt result =
  let tag = "SatisfiabilityCheck" in
  (* Update time *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  Format.fprintf 
    fmt
    ("@[<hv 2><%s>@,\
      <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
      <Result>%s</Result>@;<0 -2>\
      </%s>@]@.")
    tag
    (Stat.get_float Stat.analysis_time)
    (satisfiability_result_to_string result)
    tag
