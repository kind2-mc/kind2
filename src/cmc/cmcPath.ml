(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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
open Lib

module T = TransSys
module SVT = StateVar.StateVarHashtbl
module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet

let sat = "sat" 
let unsat = "unsat"
let unknown = "unknown"

type result = {
  name: HString.t;
}

type model_path_as_list = (StateVar.t * Model.value list) list

(* (* TODO UNCOMMENT BLOCK AND FIX ERRORS *)

Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_json ppf (path, const_map) =

  (* Delegate to recursive function *)
  Format.fprintf ppf "@,{@[<v 1>@,\
  \"blockType\" : \"ps\",@,\
  \"name\" : \"pa\"\
  @]@,}\
 " 

(* 
let rec get_trail
  (type s) (input_system : s InputSystem.t) (trans_sys : TransSys.t) disproved prefix model =
  let subsys_trails = trans_sys.subsystems |> List.map (fun (subsystem, instance) -> (pp_trail ) ) in 
  model  *)


(* let get_trail' 
  (trans_sys : TransSys.t) disproved ppf path =
  Format. ppf "%a" (Model.pp_print_model) (Model.model_at_k_of_path path (Numeral.of_int 1)) *)

let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) ((Numeral.of_int n) :: acc)
  in aux j [] 


let pp_map_binding ppf (a, b) = 
  Format.fprintf ppf "(%a -> %a)" StateVar.pp_print_state_var a StateVar.pp_print_state_var b

let pp_map ppf map = 
  Format.fprintf ppf "(%a)" (pp_print_list (pp_map_binding) " ") (SVM.bindings map)


let join_maps (top_to_sys: StateVar.t SVM.t) (sys_to_subsys: StateVar.t SVM.t) = 
  List.fold_left (fun map (subsys_val, sys_val)  ->
    (* Format.printf "VAR: %a@." StateVar.pp_print_state_var  (subsys_val); Format.printf "VAR: %a@." StateVar.pp_print_state_var  (sys_val); *)
    let top_val = StateVar.StateVarMap.find_opt sys_val top_to_sys in
    match top_val with 
    | None ->       StateVar.StateVarMap.add subsys_val sys_val map
    | Some value ->  StateVar.StateVarMap.add subsys_val value map 
) StateVar.StateVarMap.(empty) (SVM.bindings sys_to_subsys)

let get_state_var_vals_at_k trans_sys var_map model_assoc_list k ?(prefix = "") map enums = 
  let sys_vars = List.assoc (TransSys.scope_of_trans_sys trans_sys) var_map in
  (TransSys.state_vars trans_sys) |> List.filter_map (fun state_var -> 
    let state_var_opt = List.find_opt (fun v -> v == state_var) sys_vars in
    match state_var_opt with 
    | None -> None
    | Some sys_state_var when not (StateVar.for_inv_gen sys_state_var) -> None (* Filter out init flags *)
    (* May want to find a more robust way to filter out invar_props*)
    (* | _ when String.starts_with ~prefix: "invar_prop." (StateVar.name_of_state_var state_var) -> None Filter out invar_props *)
    | Some sys_state_var -> (
      let var_name = prefix ^ StateVar.name_of_state_var sys_state_var in 
      (* Format.printf "SYSTEM: %a@." Scope.pp_print_scope  (TransSys.scope_of_trans_sys trans_sys); *)
      (* Format.printf "MAP: %a@." pp_map map ; *)
      let translated_svar = StateVar.StateVarMap.find sys_state_var map in
      let state_var_type = StateVar.type_of_state_var translated_svar in
      let enum_opt = List.find_opt (fun DolmenUtils.({get_type}) -> Type.equal_types get_type state_var_type) enums in
      let svar_state_values = List.assoc translated_svar model_assoc_list in
      let svar_kth_state_value = List.nth svar_state_values (Numeral.to_int k) in 
      let state_value_changed = (Numeral.to_int k) == 0 || not (Model.equal_value (List.nth svar_state_values ((Numeral.to_int k) - 1)) svar_kth_state_value) in
      match svar_kth_state_value with
      | Model.Term value -> (
        match enum_opt with
        | Some enum -> ((
          let pair = List.find (fun (numeral, str) -> Term.equal value (Term.mk_num numeral)) enum.to_str in
          (* Format.printf "LENGTH %i" (List.length enum.to_str); *)
          let str_rep = DolmenUtils.dolmen_id_to_string (snd pair) in
          Some (var_name, str_rep, state_value_changed)))
        | _ -> Some (var_name, Term.string_of_term value, state_value_changed)
      )
      | _ -> failwith (Format.asprintf "Recieved unexpected model value. Unable to construct counter example.")
      
    )
  )


let rec get_state_var_vals_at_k_all trans_sys name_map var_map (model_assoc_list: (StateVar.t * Model.value list) list) k prefix ?(map = None) enums = 
  let sys_map = match map with 
    | None -> (* Create the identity map for the top trans system*)
      List.fold_left (fun map sys_state_var  ->
          StateVar.StateVarMap.add sys_state_var sys_state_var map
      ) StateVar.StateVarMap.(empty) (TransSys.state_vars trans_sys)
    | Some map -> 
      map
  in 
  
  let help k subsystems =
    List.map (fun (subsys_transys, TransSys.({map_up; pos})) ->
      let map = Some (join_maps sys_map map_up) in
      let name = Scope.to_string (TransSys.scope_of_trans_sys subsys_transys) in 
      (get_state_var_vals_at_k_all subsys_transys name_map var_map model_assoc_list k (prefix ^ (DolmenUtils.dolmen_id_to_string (List.assoc pos name_map)) ^ "::") ~map enums)
    ) subsystems in

  (* Note, the instances below no longer function as an assoc list*)
  let instances = (TransSys.get_subsystem_instances trans_sys) |> List.map (fun (subsys, subsys_instances) -> (List.map (fun instance -> (subsys, instance)) subsys_instances)) in 
  let instances = List.flatten instances in
  let subsys_state_vars = (help k instances)  in
  let a = (get_state_var_vals_at_k trans_sys var_map model_assoc_list k ~prefix sys_map enums) :: subsys_state_vars in 
  List.flatten a

(* 
let pp_var assoc_list ppf var_name =
  Format.fprintf ppf "(%s %a)" (StateVar.name_of_state_var (Var.state_var_of_state_var_instance var_name)) (Model.pp_print_value ?as_type: None) (List.assoc var_name assoc_list)   

let pp_step_of_trace (trans_sys : TransSys.t) disproved ppf (model, k) = 
  Format.fprintf ppf "(%a)" (pp_print_list (pp_var (Model.to_list model)) " " ) (List.map (fun f -> Var.mk_state_var_instance f k) (TransSys.state_vars trans_sys))
  (* Model.pp_print_model ppf model *)

  let pp_states (trans_sys : TransSys.t) disproved ppf path = 
  (* (range 0 Model.path_length path) *)
  let a =  List.map (fun i -> ( Model.model_at_k_of_path path (Numeral.of_int i), Numeral.of_int i)) ( 0 -- ((Model.path_length path)-1)) in

  Format.fprintf ppf  "%a" (pp_print_list (pp_step_of_trace trans_sys disproved) "@,") a *)

let pp_str_var_val ppf (state_var, value, changed) =
  if changed then 
    Format.fprintf ppf "(%s %s) " (state_var) (value)    
  else 
    if Flags.condensed_cmc_output () then
      ()
    else
      Format.fprintf ppf "@{<black>(%s %s)@} " (state_var) (value)   

let pp_state_var_val ppf (state_var, value, changed) =
  let name = StateVar.name_of_state_var state_var in 
  pp_str_var_val ppf (name, value, changed)

let pp_reach_prop ppf (state_var, value, changed) =
  let name = StateVar.name_of_state_var state_var in 
  match value with 
  | Model.Term t ->   
    if changed then 
      Format.fprintf ppf "(%s %a)" (name) (Term.pp_print_term) t
    else 
      if Flags.condensed_cmc_output () then
        ()
      else
        Format.fprintf ppf "@{<black>(%s %a)@}" (name) (Term.pp_print_term) t
  | _ -> ()

let pp_step_of_trace (trans_sys : TransSys.t) name_map var_map path enums ppf k = 
  let reachability_prop = TransSys.get_properties trans_sys in
  let reachability_svars = List.map (fun Property.({prop_term}) -> StateVar.StateVarSet.elements (Term.state_vars_of_term prop_term)) reachability_prop |> List.flatten in
  
  (* Reachable svars may have duplicates if referenced in multiple queries. Filter them out.  *)
  let reachability_svars = List.fold_left (fun rvars rvar -> if (List.exists (StateVar.equal_state_vars rvar) rvars) then rvars else rvar :: rvars) [] reachability_svars |> List.rev in

  let model_list = Model.path_to_list path in
  let values = List.map (fun reachability_svar -> List.nth (List.assoc reachability_svar model_list) (Numeral.to_int k)) reachability_svars  in
  let reachability_values = List.map2 (fun value reachability_svar -> 
    if (Numeral.to_int k) == 0 then 
      (reachability_svar, value, true)
    else 
      (reachability_svar, value, 
        not (Model.equal_value value (List.nth (List.assoc reachability_svar model_list) ((Numeral.to_int k)-1) ))
      )
    ) values reachability_svars
   in

  let reachability_change = List.fold_left (fun changed (_, _, change) -> changed || change) false reachability_values in
  
  let formatted_svar_names = get_state_var_vals_at_k_all trans_sys name_map var_map (model_list) k "" ?map: None enums in

  let any_change = (List.fold_left (fun change_detected (_, _, svar_changed) -> change_detected || svar_changed) false formatted_svar_names) 
  || reachability_change in
  if any_change then
    Format.fprintf ppf "(%a %a%a)" Numeral.pp_print_numeral k (pp_print_list pp_str_var_val "" ) formatted_svar_names (pp_print_list pp_reach_prop " ") reachability_values
  else
    if Flags.condensed_cmc_output () then
      ()
    else
      Format.fprintf ppf "@{<black>(%a %a %a)@}" Numeral.pp_print_numeral k (pp_print_list pp_str_var_val " " ) formatted_svar_names (pp_print_list pp_reach_prop " ") reachability_values
    

let pp_states (trans_sys : TransSys.t) name_map var_map enums ppf path = 
  Format.fprintf ppf  "%a" (pp_print_list (pp_step_of_trace trans_sys name_map var_map path enums) "@,") ( 0 -- ((Model.path_length path)-1))


let pp_const_decl ppf const_decl_path =
  let svar = fst const_decl_path in
  let svar_type = StateVar.type_of_state_var svar in
  let svar_value_path = snd const_decl_path in
  (* These should be constant, assume that all values are the same *)
  let const_value = List.hd svar_value_path in

  match List.find_all (fun value -> not (Model.equal_value value const_value)) (List.tl svar_value_path) with
  | [] -> Format.fprintf ppf "(define-fun %s () %a %a)" (StateVar.name_of_state_var svar) Type.pp_print_type svar_type (Model.pp_print_value ?as_type:(Some svar_type)) const_value
  
  | _ -> failwith (Format.asprintf "Recieved unexpected model value. Unable to construct counter example.\n
                                    Variable %a should be constant but was assigned multiple values. %a"
                                    StateVar.pp_print_state_var svar (pp_print_list Model.pp_print_value ", ") svar_value_path) 
  

let pp_const_decls trans_sys ppf svar_path = 
  let const_svars = List.map (fun svar -> svar, List.assoc svar svar_path) (TransSys.global_const_state_vars trans_sys) in
  Format.fprintf ppf "%a" (pp_print_list pp_const_decl "@,") const_svars

let has_model trans_sys svar_path = 
  List.length (List.map (fun svar -> svar, List.assoc svar svar_path) (TransSys.global_const_state_vars trans_sys)) > 0

let pp_trail
(CmcInput.({name_map; sys_var_mapping; enum_defs}) : CmcInput.metadata) (trans_sys : TransSys.t) ppf path =
  (* let a = TransSys.get_function_symbols trans_sys in *)
  (* Model.pp_print_path ppf path ;  (* FOR DEBUGGING*) *)
  (* Format.fprintf ppf  "%a" (pp_print_list StateVar.pp_print_state_var_debug " ") (TransSys.state_vars trans_sys) ; *)

  Format.fprintf ppf "%a@," (pp_states trans_sys name_map.map sys_var_mapping enum_defs) path
  (* Model.pp_print_path ppf path *)


(* Basic model dprinting implementation, may want to enhance in the future *)
let pp_model trans_sys prop_name ppf path =
  if has_model trans_sys path then 
    Format.fprintf ppf "%s@,%a@," (prop_name^"_model") (pp_const_decls trans_sys) path
else 
  Format.fprintf ppf "%s ()" (prop_name^"_model")

let pp_trail_cmc metadata trans_sys prop_name prefix ppf cex = 
  Format.fprintf ppf
    "@[<hv 2>:trail@ (%s%s (@[<v>@,%a@])@,) @]@,"
    prop_name
    (if prefix then "_prefix" else "_lasso")
    (pp_trail metadata trans_sys)
      (Model.path_of_list cex)


let pp_prop_cmc ppf (prop_name, result) = 
  Format.fprintf ppf
    "@[<hv 1>(%s@ %s)@]" 
    prop_name
    result

let cex_cmc metadata trans_sys prop ppf cex =
  Format.fprintf ppf
  "@[<v 1>(response @,\
    @[<hv 2>:result@ (@[<v>%a@])@]@,\
    @[<hv 2>:model@ (@[<v>@,%a@]@])@,\
    %a\
    @[<hv 2>:trace@ (%s :prefix %s@,) @]@,\
    )@.@."
  pp_prop_cmc (prop, "sat")
  (pp_model trans_sys prop)
  cex
  (pp_trail_cmc metadata trans_sys prop true) 
  cex
  prop
  (prop ^ "_prefix")

let pp_prop_result_info prop ppf status =
  if status == sat then
    Format.fprintf ppf ":model %s_model :trace %s_trace" prop prop
  else if status == unsat then 
    Format.fprintf ppf ":certificate %s_cert" prop
else ()

let pp_prop_result prop ppf status=
  Format.fprintf ppf
  "@[<hv 2>:query@ @[<v>@[<hv 1>(%s@ %s %a)@]@]@]@,"
  prop status 
  (pp_prop_result_info prop) status

(** Output proved or unknown property in CMC standard format 
    In this case proving a cmc property means that we proved the test to be unreachable
    Thus proving that the property is unsat. *)
let unsat_unknown_cmc ppf prop status = 
  Format.fprintf ppf
    "@[<v 1>(check-system-response @,\
      @[<hv 2>:result@ (@[<v>%a@])@]@,\
      @[<hv 2>:model@ (@[<v>...@])@]@.\
    )@.@."
    pp_prop_cmc (prop, status)

let print_prop_result ppf prop =
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
        | PropFalse _ -> (pp_prop_result prop_name ppf sat);
        | PropInvariant _
        | PropKTrue _ -> (pp_prop_result prop_name ppf unsat) ;
        | PropUnknown -> (pp_prop_result prop_name ppf unknown) ;
;;
let print_prop_trace ppf prop =
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
        | PropFalse _ -> Format.fprintf ppf 
                          "@[<hv 2>:trace@ (@[<v>%s :prefix %s@])@]@,"
                          (prop_name ^ "_trace")
                          (prop_name ^ "_prefix")
        | PropInvariant _
        | PropKTrue _ 
        | PropUnknown -> () ;
;;

let print_prop_model trans_sys ppf prop =
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
        | PropFalse cex -> Format.fprintf ppf 
                          "@[<hv 2>:model@ (@[<v>%a@]@])@,"
                          (pp_model trans_sys prop_name)
                          cex
        | PropInvariant _
        | PropKTrue _ 
        | PropUnknown -> () ;
;;

let print_prop_trail trans_sys metadata ppf prop =
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with 
        | PropFalse cex -> (pp_trail_cmc metadata trans_sys prop_name true ppf cex) 
        | PropInvariant _
        | PropKTrue _ 
        | PropUnknown -> () ;
;;

let print_prop_cert ppf prop =
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
        | PropFalse cex -> () 
        | PropInvariant (k, inv) -> Format.fprintf ppf 
                                    "@[<hv 2>:certificate@ (@[<v>%s :inv %a :k %i@])@]@,"
                                    (prop_name ^ "_cert")
                                    Term.pp_print_term
                                    inv
                                    k
        | PropKTrue k -> Format.fprintf ppf 
                          "@[<hv 2>:certificate@ (@[<v>%s :inv None :k %i@])@]@,"
                          (prop_name ^ "_cert")
                          k
        | PropUnknown -> () ;
;;

let print_cmc_props metadata trans_sys props =
  Format.printf
  "@[<v 1>(check-system-response @,\
   @[<hv 2>:verbosity@ %s@]@,\
    %a\
    %a\
    %a\
    %a\
    %a\
    )@]@.@."
  (if Flags.condensed_cmc_output () then "condensed" else "full")
  (Lib.pp_print_list print_prop_result "") props
  (Lib.pp_print_list print_prop_trace "") (props)
  (Lib.pp_print_list (print_prop_model trans_sys) "") (props)
  (Lib.pp_print_list (print_prop_trail trans_sys metadata) "") (props)
  (Lib.pp_print_list print_prop_cert  "") (props)


  (* Format.printf "%a" (Lib.pp_print_list (print_cmc_prop metadata trans_sys) "\n") (props); *)
;;
