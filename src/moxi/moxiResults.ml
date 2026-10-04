(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

module TS = TransSys
module SVM = StateVar.StateVarMap

let join_maps (top_to_sys: StateVar.t SVM.t) (sys_to_subsys: StateVar.t SVM.t) = 
  List.fold_left (fun map (subsys_val, sys_val)  ->
    let top_val = StateVar.StateVarMap.find_opt sys_val top_to_sys in
    match top_val with 
    | None ->       StateVar.StateVarMap.add subsys_val sys_val map
    | Some value ->  StateVar.StateVarMap.add subsys_val value map 
) StateVar.StateVarMap.empty (SVM.bindings sys_to_subsys)

let get_state_var_vals_at_k ?(prefix="") trans_sys model_assoc_list k map = 
  let sys_vars = TransSys.state_vars trans_sys in
  (TransSys.state_vars trans_sys) |> List.filter_map (fun state_var -> 
    let state_var_opt = List.find_opt (fun v -> v == state_var) sys_vars in
    match state_var_opt with 
    | None -> None
    | Some sys_state_var when not (StateVar.for_inv_gen sys_state_var) -> None (* Filter out init flags *)
    (* May want to find a more robust way to filter out invar_props*)
    (* | _ when String.starts_with ~prefix: "invar_prop." (StateVar.name_of_state_var state_var) -> None Filter out invar_props *)
    | Some sys_state_var -> (
      let var_name = prefix ^ StateVar.name_of_state_var sys_state_var in 
      let translated_svar = StateVar.StateVarMap.find sys_state_var map in
      let svar_state_values = List.assoc translated_svar model_assoc_list in
      let svar_kth_state_value = List.nth svar_state_values (Numeral.to_int k) in 
      let state_value_changed = 
        (Numeral.to_int k) == 0 || 
        not (Model.equal_value (List.nth svar_state_values ((Numeral.to_int k) - 1)) 
                               svar_kth_state_value) 
      in
      match svar_kth_state_value with
      | Model.Term value -> 
        Some (var_name, Term.string_of_term value, state_value_changed)
      | Model.Map _ ->
        Some (var_name, "[...]", true)
      | _ -> 
        failwith (Format.asprintf "Received unexpected model value. Unable to construct counterexample.")
    )
  )

let rec get_state_var_vals_at_k_all ?(map=None) ?(prefix="") trans_sys (model_assoc_list: (StateVar.t * Model.value list) list) k = 
  let sys_map = match map with 
    | None -> (* Create the identity map for the top trans system *)
      List.fold_left (fun map sys_state_var  ->
          StateVar.StateVarMap.add sys_state_var sys_state_var map
      ) StateVar.StateVarMap.empty (TransSys.state_vars trans_sys)
    | Some map -> 
      map
  in 
  
  let help k subsystems =
    List.map (fun (subsys_transys, TransSys.({ map_up; })) ->
      let map = Some (join_maps sys_map map_up) in
      let subsys_name = TransSys.scope_of_trans_sys subsys_transys |> Lib.string_of_t Scope.pp_print_scope_internal in
      let prefix = prefix ^ subsys_name ^ "::" in
      (get_state_var_vals_at_k_all ~map ~prefix subsys_transys model_assoc_list k)
    ) subsystems in

  let instances = 
    (TransSys.get_subsystem_instances trans_sys) |> 
    List.map (fun (subsys, subsys_instances) -> 
      (List.map (fun instance -> (subsys, instance)) subsys_instances)
    ) |> 
    List.flatten 
  in 

  (* For now, we remove the (non-reachability) variables in the check-system renamings. 
     This could reasonably change in the future.
  *)
  let trans_sys_state_vars = 
    if prefix = "" then [] else get_state_var_vals_at_k ~prefix trans_sys model_assoc_list k sys_map 
  in
  let subsys_state_vars = (help k instances) in
  List.flatten (trans_sys_state_vars :: subsys_state_vars)

let pp_print_str_var_val ppf (state_var, value, changed) =
  if changed then 
    Format.fprintf ppf "(%s %s) " state_var value   
  else 
    if false then (* TODO: Get flag for condensed output *)
      ()
    else
      Format.fprintf ppf "@{<black>(%s %s)@} " state_var value 



let pp_print_last_step_of_trace (trans_sys : TransSys.t) path ppf k =
  let reachability_prop = TransSys.get_properties trans_sys in
  let reachability_svars =
    List.map (fun Property.({prop_term}) ->
      StateVar.StateVarSet.elements (Term.state_vars_of_term prop_term)
    ) reachability_prop |> List.flatten in

  let model_list = Model.path_to_list path in
  let formatted_svar_names = get_state_var_vals_at_k_all trans_sys model_list k in
  let any_change =
    List.fold_left (fun change_detected (_, _, svar_changed) ->
      change_detected || svar_changed
    ) false formatted_svar_names
  in

  let reachability_var_names = List.map (fun svar ->
    StateVar.name_of_state_var svar) reachability_svars
  in
  let formatted_svar_names = List.filter (fun (var, _, _) ->
    not (List.exists (String.equal var) reachability_var_names)
  ) formatted_svar_names in

  if any_change then
    Format.fprintf ppf "(%a %a)"
      Numeral.pp_print_numeral k
      (Lib.pp_print_list pp_print_str_var_val "") formatted_svar_names
  else
    if false then (* TODO: Get flag for condensed output *)
      ()
    else
      Format.fprintf ppf "@{<black>(%a %a)@}"
        Numeral.pp_print_numeral k
        (Lib.pp_print_list pp_print_str_var_val " ") formatted_svar_names

let pp_print_step_of_trace (trans_sys : TransSys.t) path ppf k = 
  let reachability_prop = TransSys.get_properties trans_sys in
  let reachability_svars = 
    List.map (fun Property.({prop_term}) -> 
      StateVar.StateVarSet.elements (Term.state_vars_of_term prop_term)
    ) reachability_prop |> List.flatten in
  
  (* Reachable svars may have duplicates if referenced in multiple queries. Filter them out.  *)
  let reachability_svars = 
    List.fold_left (fun rvars rvar -> 
      if (List.exists (StateVar.equal_state_vars rvar) rvars) 
      then rvars 
      else rvar :: rvars
    ) [] reachability_svars |> List.rev in

  let model_list = Model.path_to_list path in
  let values = List.map (fun reachability_svar -> 
    List.nth (List.assoc reachability_svar model_list) (Numeral.to_int k + 1)
  ) reachability_svars  in
  let reachability_values = List.map2 (fun value reachability_svar -> 
    if (Numeral.to_int k) == 0 then 
      (reachability_svar, value, true)
    else 
      reachability_svar, 
      value, 
      not (Model.equal_value value (List.nth (List.assoc reachability_svar model_list) ((Numeral.to_int k)) ))
    ) values reachability_svars
   in
  let reachability_change = List.fold_left (fun changed (_, _, change) -> 
    changed || change
  ) false reachability_values in
  let formatted_svar_names = get_state_var_vals_at_k_all trans_sys model_list k in
  let any_change = 
    reachability_change 
    ||
    List.fold_left (fun change_detected (_, _, svar_changed) -> 
      change_detected || svar_changed
    ) false formatted_svar_names
  in

  (* To check reachability, we were checking invariance of the negation of the reachability query. 
     When displaying the value of the reachability condition, we need to un-negate it. *)
  let reachability_values = List.map (fun (svar, value, changed) -> match value with 
    | Model.Term value -> 
      let negated_value = not (Term.bool_of_term value) in
      StateVar.name_of_state_var svar, string_of_bool negated_value, changed 
    | _ -> assert false 
  ) reachability_values in
  let reachability_var_names = List.map (fun (name, _, _) -> name) reachability_values in
  let formatted_svar_names = List.filter (fun (var, _, _) ->
    not (List.exists (String.equal var) reachability_var_names) 
  ) formatted_svar_names in

  if any_change then
    Format.fprintf ppf "(%a %a %a)" 
      Numeral.pp_print_numeral k 
      (Lib.pp_print_list pp_print_str_var_val "") formatted_svar_names
      (Lib.pp_print_list pp_print_str_var_val "") reachability_values
  else
    if false then (* TODO: Get flag for condensed output *)
      ()
    else
      Format.fprintf ppf "@{<black>(%a %a %a)@}" 
        Numeral.pp_print_numeral k 
        (Lib.pp_print_list pp_print_str_var_val " ") formatted_svar_names
        (Lib.pp_print_list pp_print_str_var_val "") reachability_values
    
let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) ((Numeral.of_int n) :: acc)
  in aux j [] 

let pp_print_trail is_current_state trans_sys ppf path =
  let range = 0 -- (Model.path_length path - 2) in

  (match range with
  | [] -> ()
  | _ ->
    Format.fprintf ppf "%a@,"
      (Lib.pp_print_list (pp_print_step_of_trace trans_sys path) "@,") range );

  (* Only show the last state if it is not a property of the current state. *)
  if not is_current_state then
    (* In the last state, do not print value of reachability variables *)
    Format.fprintf ppf "%a@,"
      (pp_print_last_step_of_trace trans_sys path)
      (Numeral.of_int (Model.path_length path - 1))

let pp_print_cex_trail trans_sys prop_name prefix is_current_state ppf cex = 
  Format.fprintf ppf "@[<hv 2>:trail@ (%s%s (@[<v>@,%a@])@,) @]@,"
    prop_name
    (if prefix then "_prefix" else "_lasso")
    (pp_print_trail is_current_state trans_sys) (Model.path_of_list cex)

let pp_print_prop_trail trans_sys current_state_props ppf prop =
  let prop_name = prop.Property.prop_name in
  let is_current_state =
    List.mem prop_name current_state_props
  in
  match Property.get_prop_status prop with 
  | PropFalse cex -> 
    (pp_print_cex_trail trans_sys prop_name true is_current_state ppf cex)
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> () 

let pp_print_prop_trace _ prop = 
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropFalse _ -> 
    Format.printf "@[<hv 2>:trace@ (@[<v>%s :prefix %s@])@]@,"
      (prop_name ^ "_trace")
      (prop_name ^ "_prefix")
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> () 

let has_model _trans_sys _svar_path = 
  false 
  (* List.exists (fun svar -> List.mem_assoc svar svar_path)
    (TransSys.global_const_state_vars trans_sys) *)

let pp_print_const_decl _ppf (svar, svar_value_path) =
  let svar_type = StateVar.type_of_state_var svar in
  (* These should be constant; assume that all values are the same *)
  let const_value = List.hd svar_value_path in

  match List.find_all (fun value -> 
    not (Model.equal_value value const_value)
  ) (List.tl svar_value_path) with
  | [] -> 
    Format.printf "(define-fun %s () %a %a)" 
      (StateVar.name_of_state_var svar) 
      Type.pp_print_type svar_type 
      (Model.pp_print_value ?as_type:(Some svar_type)) const_value
  
  | _ -> 
    failwith (Format.asprintf 
      "Recieved unexpected model value. Unable to construct counterexample.\n
       Variable %a should be constant but was assigned multiple values. %a"
      StateVar.pp_print_state_var svar 
      (Lib.pp_print_list Model.pp_print_value ", ") svar_value_path) 

let pp_print_const_decls: TransSys.t -> Format.formatter -> (StateVar.t * Model.value list) list -> unit 
= fun trans_sys _ppf svar_path -> 
  let const_svars = List.map (fun svar -> 
    svar, List.assoc svar svar_path
  ) (TransSys.global_const_state_vars trans_sys) in
  Format.printf "%a" (Lib.pp_print_list pp_print_const_decl "@,") const_svars

let pp_print_model trans_sys prop_name _ppf path =
  if has_model trans_sys path then 
    Format.printf "%s@,%a@," (prop_name ^ "_model") (pp_print_const_decls trans_sys) path
  else 
    Format.printf "%s ()" (prop_name ^ "_model")

let pp_print_prop_model: TransSys.t -> Format.formatter -> Property.t -> unit 
= fun trans_sys _ppf prop ->
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropFalse cex -> 
    Format.printf "@[<hv 2>:model@ (@[<v>%a@]@])@,"
      (pp_print_model trans_sys prop_name) cex
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> ()

let pp_print_prop_cert _ppf prop = 
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropInvariant (k, inv) -> 
    Format.printf "@[<hv 2>:certificate@ (@[<v>%s :inv %a :k %i@])@]@,"
      (prop_name ^ "_cert")
      (LustreExpr.pp_print_term_as_expr false)
      inv
      k
  | PropFalse _ 
  | PropKTrue _
  | PropUnknown -> ()

let prop_result_info prop_name prop_result = match prop_result with 
| Property.PropFalse _ -> Format.sprintf ":model %s_model :trace %s_trace" prop_name prop_name
| PropInvariant _ -> Format.sprintf ":certificate %s_cert" prop_name
| PropKTrue _
| PropUnknown -> ""

let pp_print_prop_result _ppf prop =
  let prop_name = prop.Property.prop_name in
  let prop_result = Property.get_prop_status prop in
  let result = match prop_result with
  | PropFalse _ -> "sat"
  | PropInvariant _ -> "unsat"
  | PropKTrue _ 
  | PropUnknown -> "unknown"
  in
  Format.printf "@[<hv 2>:query@ @[<v>@[<hv 1>(%s@ %s %s)@]@]@]@,"
    prop_name result 
    (prop_result_info prop_name prop_result)

let pp_print_results: TransSys.t -> _ InputSystem.t -> Property.t list -> unit 
= fun trans_sys in_sys props ->
  let current_state_props =
    InputSystem.current_state_props in_sys (TS.scope_of_trans_sys trans_sys)
  in
  Format.printf
  "@[<v 1>(check-system-response @,\
   @[<hv 2>:verbosity@ %s@]@,\
    %a\
    %a\
    %a\
    %a\
    %a\
    )@]@.@."
  (if false then "condensed" else "full") (* TODO: Get flag for condensed output *)
  (Lib.pp_print_list pp_print_prop_result "") props
  (Lib.pp_print_list pp_print_prop_trace "") props
  (Lib.pp_print_list (pp_print_prop_model trans_sys) "") props
  (Lib.pp_print_list (pp_print_prop_trail trans_sys current_state_props) "") props
  (Lib.pp_print_list pp_print_prop_cert "") props
