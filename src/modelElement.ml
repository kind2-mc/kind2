(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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
module SyMap = UfSymbol.UfSymbolMap
module SySet = UfSymbol.UfSymbolSet
module ScMap = Scope.Map
module SVSet = StateVar.StateVarSet

(* Represents an equation of the transition system.
   It is not specific to the 'equation' model elements
   of the source lustre program
   (any model element can be represented by this 'equation' type) *)
type ts_equation = {
  init_opened: Term.t ;
  init_closed: Term.t ;
  trans_opened: Term.t ;
  trans_closed: Term.t ;
}

(* Each equation in the core is identified by a uninterpreted function symbol (UfSymbol.t)
   (it can also be used as an activation litteral).
   The first item is a mapping from scopes to the list of equations
   (represented by their UfSymbol identifier) that are present in the core.
   The second item is a mapping from equation identifiers to their corresponding [ts_equation] object
   and a fresh state var that can be used as an activation litteral for this equation.
*)
type core = (UfSymbol.t list) ScMap.t * (ts_equation * StateVar.t) SyMap.t

type loc = {
  pos: Lib.position ;
  index: LustreIndex.index ;
}

type term_cat =
| NodeCall of string * SVSet.t
| ContractItem of StateVar.t * LustreContract.svar * LustreNode.contract_item_type
| Equation of StateVar.t
| Assertion of StateVar.t
| Unknown

module Equation = struct
  type t = ts_equation
  let compare t1 t2 =
    match Term.compare t1.trans_opened t2.trans_opened with
    | 0 -> Term.compare t1.init_opened t2.init_opened
    | n -> n
  let equal t1 t2 = compare t1 t2 = 0
end
module EqSet = Set.Make(Equation)

let scmap_size c =
  ScMap.fold (fun _ lst acc -> acc + (List.length lst)) c 0

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

let lustre_name_of_sv var_map sv =
  let usr_name =
    assert (List.length LustreIdent.user_scope = 1) ;
    List.hd LustreIdent.user_scope
  in
  if List.mem usr_name (StateVar.scope_of_state_var sv)
  then StateVar.name_of_state_var sv
  else StateVar.StateVarMap.find sv var_map

type term_print_data = {
  name: string ;
  category: string ;
  position: Lib.position ;
}

type core_print_data = {
  core_class: string ;
  property: string option ; (* Only for MCSs *)
  counterexample: ((StateVar.t * Model.value list) list) option ; (* Only for MCSs *)
  time: float option ;
  size: int ;
  approx: bool option ;
  elements: term_print_data list ScMap.t ;
}

let pp_print_locs_short =
  Lib.pp_print_list (
    fun fmt {pos} ->
      Format.fprintf fmt "%a" Lib.pp_print_line_and_column pos
  ) ""

(* The last position is the main one (the first one added) *)
let last_position_of_locs locs =
  (List.hd (List.rev locs)).pos

let print_data_of_loc_equation var_map (_, locs, cat) =
  if locs = []
  then None
  else
    match cat with
    | Unknown -> None
    | NodeCall (name, _) ->
      Some {
        name = name ;
        category = "Node Call" ;
        position = last_position_of_locs locs ;
      }
    | Equation sv ->
      (
        try
          Some {
            name = lustre_name_of_sv var_map sv ;
            category = "Equation" ;
            position = last_position_of_locs locs ;
          }
        with Not_found -> None
      )
    | Assertion _ ->
      Some {
        name = Format.asprintf "assertion%a" pp_print_locs_short locs ;
        category = "Assertion" ;
        position = last_position_of_locs locs ;
      }
    | ContractItem (_, svar, typ) ->
      let (kind, category) = 
        match typ with
        | LustreNode.WeakAssumption -> ("weakly_assume", "Assumption")
        | LustreNode.WeakGuarantee -> ("weakly_guarantee", "Guarantee")
        | LustreNode.Assumption -> ("assume", "Assumption")
        | LustreNode.Guarantee -> ("guarantee", "Guarantee")
        | LustreNode.Require -> ("require", "Require")
        | LustreNode.Ensure -> ("ensure", "Ensure")
      in
      Some {
        name = LustreContract.prop_name_of_svar svar kind "" ;
        category ;
        position = last_position_of_locs locs ;
      }

let printable_elements_of_core in_sys sys core =
  let var_map = compute_var_map in_sys sys in
  let aux lst =
    lst
    |> List.map (print_data_of_loc_equation var_map)
    |> List.filter (function Some _ -> true | None -> false)
    |> List.map (function Some x -> x | None -> assert false)
  in
  core
  |> ScMap.map aux (* Build map *)
  |> ScMap.filter (fun _ lst -> lst <> []) (* Remove empty entries *)

let loc_core_to_print_data in_sys sys core_class time lc =
  let elements = printable_elements_of_core in_sys sys lc in
  {
    core_class ;
    property = None ;
    counterexample = None ;
    approx = None ;
    time ;
    elements ;
    size = scmap_size elements ;
  }

let attach_counterexample_to_print_data data cex =
  { data with counterexample = Some cex }

let attach_property_to_print_data data prop =
  { data with property = Some prop.Property.prop_name }

let attach_approx_to_print_data data approx =
  { data with approx = Some approx }

let print_mcs_counterexample in_sys param sys typ fmt (prop, cex) =
  try
    if Flags.MCS.print_mcs_counterexample ()
    then
      match typ with
      | `PT ->
        KEvent.pp_print_counterexample_pt L_warn in_sys param sys (Some prop) true fmt cex
      | `XML ->
        KEvent.pp_print_counterexample_xml in_sys param sys (Some prop) true fmt cex
      | `JSON ->
        KEvent.pp_print_counterexample_json in_sys param sys (Some prop) true fmt cex
  with _ -> ()

let format_name_for_pt str =
  String.capitalize_ascii (String.lowercase_ascii str)

let format_name_for_json str =
  String.uncapitalize_ascii str
  |> Str.global_replace (Str.regexp " ") ""

let format_name_for_xml str =
  String.lowercase_ascii str
  |> Str.global_replace (Str.regexp " ") "_"

let pp_print_core_data in_sys param sys fmt cpd =
  let print_elt elt =
    Format.fprintf fmt "%s @{<blue_b>%s@} at position %a@ "
      (format_name_for_pt elt.category) elt.name
      Lib.pp_print_line_and_column elt.position
  in
  let print_node scope lst =
    Format.fprintf fmt "@{<b>Node@} @{<blue>%s@}@ " (Scope.to_string scope) ;
    Format.fprintf fmt "  @[<v>" ;
    List.iter print_elt lst ;
    Format.fprintf fmt "@]@ "
  in
  (match cpd.property with
  | None -> Format.fprintf fmt "@{<b>%s (%i elements):@}@."
    (String.uppercase_ascii cpd.core_class) cpd.size
  | Some n -> Format.fprintf fmt "@{<b>%s (%i elements)@} for property @{<blue_b>%s@}:@."
    (String.uppercase_ascii cpd.core_class) cpd.size n
  ) ;
  Format.fprintf fmt "  @[<v>" ;
  ScMap.iter print_node cpd.elements ;
  (match cpd.counterexample, cpd.property with
  | Some cex, Some p ->
    print_mcs_counterexample in_sys param sys `PT fmt (p,cex)
  | _, _ -> ()
  ) ;
  Format.fprintf fmt "@]@."

let pp_print_json fmt json =
  Yojson.Basic.pretty_to_string json
  |> Format.fprintf fmt "%s"

let pp_print_core_data_json in_sys param sys fmt cpd =
  let json_of_elt elt =
    let (file, row, col) = Lib.file_row_col_of_pos elt.position in
    `Assoc ([
      ("category", `String (format_name_for_json elt.category)) ;
      ("name", `String elt.name) ;
      ("line", `Int row) ;
      ("column", `Int col) ;
    ] @
    (if file = "" then [] else [("file", `String file)])
    )
  in
  let assoc = [
    ("objectType", `String "modelElementSet") ;
    ("class", `String cpd.core_class) ;
    ("size", `Int cpd.size) ;
  ] in
  let assoc = assoc @ (
    match cpd.property with
    | None -> []
    | Some n -> [("property", `String n)]
  )
  in
  let assoc = assoc @ (
    match cpd.time with
    | None -> []
    | Some f -> [("runtime", `Assoc [("unit", `String "sec") ; ("value", `Float f) ; ("timeout", `Bool false)])]
  )
  in
  let assoc = assoc @ (
    match cpd.approx with
    | None -> []
    | Some b -> [("approximate", `Bool b)]
  )
  in
  let assoc = assoc @ ([
    ("nodes", `List (List.map (fun (scope, elts) ->
      `Assoc [
        ("name", `String (Scope.to_string scope)) ;
        ("elements", `List (List.map json_of_elt elts))
      ]
    ) (ScMap.bindings cpd.elements)))
  ])
  in
  let assoc = assoc @
    (match cpd.counterexample, cpd.property with
    | Some cex, Some p ->
      let str = Format.asprintf "%a"
        (print_mcs_counterexample in_sys param sys `JSON) (p, cex) in
      if String.equal str "" then []
      else (
          match Yojson.Basic.from_string ("{"^str^"}") with
          | `Assoc json -> json
          | _ -> assert false
      )
    | _, _ -> []
    )
  in
  pp_print_json fmt (`Assoc assoc)

let pp_print_core_data_xml ?(tag="ModelElementSet") in_sys param sys fmt cpd =
  let fst = ref true in
  let print_node scope elts =
    if not !fst then Format.fprintf fmt "@ " else fst := false ;
    let fst = ref true in
    let print_elt elt =
      if not !fst then Format.fprintf fmt "@ " else fst := false ;
      let (file, row, col) = Lib.file_row_col_of_pos elt.position in
      Format.fprintf fmt "<Element category=\"%s\" name=\"%s\" line=\"%i\" column=\"%i\"%s/>"
        (format_name_for_xml elt.category) elt.name row col (if file = "" then "" else Format.asprintf " file=\"%s\"" file)
    in
    Format.fprintf fmt "<Node name=\"%s\">@   @[<v>" (Scope.to_string scope) ;
    List.iter print_elt elts ;
    Format.fprintf fmt "@]@ </Node>"
  in
  Format.fprintf fmt "<%s class=\"%s\" size=\"%i\"%s%s>@.  @[<v>"
    tag cpd.core_class cpd.size
    (match cpd.property with None -> "" | Some n -> Format.asprintf " property=\"%s\"" n)
    (match cpd.approx with None -> "" | Some b -> Format.asprintf " approximate=\"%b\"" b) ;
  (
    match cpd.time with
    | None -> ()
    | Some f -> Format.fprintf fmt "<Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@ " f
  ) ;
  ScMap.iter print_node cpd.elements ;
  (
    match cpd.counterexample, cpd.property with
    | Some cex, Some p ->
      Format.fprintf fmt "@ " ;
      print_mcs_counterexample in_sys param sys `XML fmt (p, cex)
    | _, _ -> ()
  ) ;
  Format.fprintf fmt "@]@.</%s>@." tag

let [@ocaml.warning "-27"] pp_print_no_solution sys clas ~unknown fmt prop =
  Format.fprintf fmt "%s for property @{<blue_b>%s@}.@.@."
    (if unknown then "Unknown result" else "No solution") (prop.Property.prop_name)

let [@ocaml.warning "-27"] pp_print_no_solution_json sys clas ~unknown fmt prop =
  let assoc = [
    ("objectType", `String "noModelElementSet") ;
    ("class", `String clas) ;
    ("property", `String prop.Property.prop_name) ;
    ("answer", `String (if unknown then "unknown" else "noSolution")) ;
    ("runtime", `Assoc [("unit", `String "sec") ; ("value", `Float (Stat.get_float Stat.analysis_time)) ; ("timeout", `Bool unknown)])
  ] in
  pp_print_json fmt (`Assoc assoc)

let [@ocaml.warning "-27"] pp_print_no_solution_xml sys clas ~unknown fmt prop =
  Format.fprintf fmt "<NoModelElementSet class=\"%s\" property=\"%s\">@.  @[<v>" clas prop.Property.prop_name ;
  Format.fprintf fmt "<Answer>%s</Answer>@ "
    (if unknown then "unknown" else "no_solution") ;
  Format.fprintf fmt "<Runtime unit=\"sec\" timeout=\"%s\">%.3f</Runtime>@ "
    (if unknown then "true" else "false") (Stat.get_float Stat.analysis_time) ;
  Format.fprintf fmt "@]@.</NoModelElementSet>@."

let name_of_wa_cat = function
  | ContractItem (_, svar, LustreNode.WeakAssumption) ->
    Some (LustreContract.prop_name_of_svar svar "weakly_assume" "")
  | ContractItem (_, svar, LustreNode.WeakGuarantee) ->
    Some (LustreContract.prop_name_of_svar svar "weakly_guarantee" "")
  | _ -> None

let all_wa_names_of_loc_core core =
  ScMap.fold
  (fun _ lst acc ->
    List.fold_left (fun acc (_,_,cat) ->
      match name_of_wa_cat cat with
      | None -> acc
      | Some str -> str::acc
    ) acc lst
  )
  core []

(* ---------- CORES ---------- *)

let actsvs_counter =
  let last = ref 0 in
  (fun () -> last := !last + 1 ; !last)

let fresh_actsv_name () =
  Printf.sprintf "__model_elt_%i" (actsvs_counter ())

let term_of_ts_eq ~init ~closed eq =
  if init && closed then eq.init_closed
  else if init then eq.init_opened
  else if closed then eq.trans_closed
  else eq.trans_opened

let empty_core = (ScMap.empty, SyMap.empty)

let get_actlits_of_scope (scmap, _) scope =
  try ScMap.find scope scmap with Not_found -> []

let get_ts_equation_of_actlit (_, mapping) actlit =
  SyMap.find actlit mapping |> fst

let get_sv_of_actlit (_, mapping) actlit =
  SyMap.find actlit mapping |> snd


let eq_of_actlit_sv core ?(with_act=false) actlit =
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


let eq_of_actlit_uf core ?(with_act=false) a =
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


let core_size (scmap, _) = scmap_size scmap

let scopes_of_core (scmap, _) =
  ScMap.bindings scmap |> List.map fst

let pick_element_of_core (scmap, mapping) =
  let scmap = ScMap.filter (fun _ lst -> lst <> []) scmap in
  match ScMap.bindings scmap with
  | [] -> None
  | (scope, lst)::_ ->
    Some (scope, List.hd lst, (ScMap.add scope (List.tl lst) scmap, mapping))

let add_new_ts_equation_to_core scope eq ((scmap, mapping) as core) =
  let actlit = Actlit.fresh_actlit () in
  let actlits = actlit::(get_actlits_of_scope core scope) in
  let sv = StateVar.mk_state_var ~is_input:false ~is_const:true
        (fresh_actsv_name ()) [] (Type.mk_bool ()) in
  (ScMap.add scope actlits scmap, SyMap.add actlit (eq, sv) mapping)

let add_from_other_core
  (_, src_mapping) scope actlit ((scmap, mapping) as core) =
  let actlits = get_actlits_of_scope core scope in
  if List.exists (fun a -> UfSymbol.equal_uf_symbols a actlit) actlits
  then core
  else (
    let mapping = SyMap.add actlit (SyMap.find actlit src_mapping) mapping in
    ScMap.add scope (actlit::actlits) scmap, mapping
  )

let sy_union sy1 sy2 =
  SySet.union (SySet.of_list sy1) (SySet.of_list sy2)
  |> SySet.elements

let sy_inter sy1 sy2 =
  SySet.inter (SySet.of_list sy1) (SySet.of_list sy2)
  |> SySet.elements

let sy_diff sy1 sy2 =
  SySet.diff (SySet.of_list sy1) (SySet.of_list sy2)
  |> SySet.elements

let remove_from_core actlit (scmap, mapping) =
  (ScMap.map (fun actlits -> sy_diff actlits [actlit]) scmap, mapping)

let filter_core actlits (scmap, mapping) =
  (ScMap.map (fun actlits' -> sy_inter actlits actlits') scmap, mapping)

let filter_core_svs state_vars ((scmap, mapping) as core) =
  let svs = SVSet.of_list state_vars in
  let aux actlits =
    List.filter
      (fun a -> SVSet.mem (get_sv_of_actlit core a) svs)
      actlits
  in
  (ScMap.map aux scmap, mapping)

let core_union (scmap1, mapping1) (scmap2, mapping2) =
  let merge _ eq1 eq2 = match eq1, eq2 with
  | None, None -> None
  | Some e, _ | None, Some e -> Some e
  in
  let mapping = SyMap.merge merge mapping1 mapping2 in
  let merge _ lst1 lst2 = match lst1, lst2 with
  | None, None -> None
  | Some lst, None | None, Some lst -> Some lst
  | Some lst1, Some lst2 -> Some (sy_union lst1 lst2)
  in
  let scmap = ScMap.merge merge scmap1 scmap2 in
  (scmap, mapping)

let core_diff (scmap1, mapping) (scmap2, _) =
  let merge _ lst1 lst2 = match lst1, lst2 with
  | None, _ -> None
  | Some lst, None -> Some lst
  | Some lst1, Some lst2 -> Some (sy_diff lst1 lst2)
  in
  let scmap = ScMap.merge merge scmap1 scmap2 in
  (scmap, mapping)


let core_to_eqmap (scmap, mapping) =
  ScMap.map (List.map (fun a -> SyMap.find a mapping |> fst)) scmap

(* ---------- MAPPING BACK ---------- *)

(* The first item contains the transition-system terms corresponding to the model element,
   the second item contains a list of position in the Lustre model that defines this model element,
   and the third item corresponds to the category of the model element
   (node call, lustre equation, assumption, guarantee, etc.).
*)
type model_element = ts_equation * (loc list) * term_cat

(* A [loc_core] is just a map from scopes to the corresponding list of model elements. *)
type loc_core = model_element list ScMap.t

let equal_model_elements (eq1, _, _) (eq2, _, _) =
  Equation.equal eq1 eq2

let get_model_elements_of_scope core scope =
  try ScMap.find scope core with Not_found -> []

let loc_core_size = scmap_size

let scopes_of_loc_core core =
  ScMap.bindings core |> List.map fst

let normalize_positions lst =
  List.sort_uniq Lib.compare_pos lst

let get_positions_of_model_element (_,locs,_) =
  List.map (fun loc -> loc.pos) locs |> normalize_positions

let locs_of_node_call in_sys output_svs =
  output_svs
  |> SVSet.elements
  |> List.map (fun sv ->
      InputSystem.lustre_definitions_of_state_var in_sys sv
      |> List.filter (function LustreNode.CallOutput _ -> true | _ -> false)
      |> List.map
        (fun d -> { pos=LustreNode.pos_of_state_var_def d ;
                    index=[](*LustreNode.index_of_state_var_def d*) })
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
  let node =
    match InputSystem.get_lustre_node in_sys (Scope.mk_scope [Ident.of_string name]) with
    | Some node -> node
    | None -> assert false
  in
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

let sv_of_term t =
  find_vars t |> List.hd |> Var.state_var_of_state_var_instance

let locs_of_eq_term in_sys t =
  try
    let contract_typ = ref LustreNode.Assumption in
    let contract_items = ref None in
    let set_contract_item svar = contract_items := Some svar in
    let has_asserts = ref false in
    let sv = sv_of_term t in
    InputSystem.lustre_definitions_of_state_var in_sys sv
    |> List.filter (function LustreNode.CallOutput _ -> false | _ -> true)
    |> List.map (fun def ->
      ( match def with
        | LustreNode.Assertion _ -> has_asserts := true
        | LustreNode.ContractItem (_, svar, typ) -> contract_typ := typ ; set_contract_item svar
        | _ -> ()
      );
      let p = LustreNode.pos_of_state_var_def def in
      let i = LustreNode.index_of_state_var_def def in
      { pos=p ; index=i }
    )
    |> (fun locs ->
      match !contract_items with
      | Some svar -> (ContractItem (sv, svar, !contract_typ), locs)
      | None ->
        if !has_asserts then (Assertion sv, locs)
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

let ts_equation_to_model_element = add_loc

let core_to_loc_core in_sys core =
  core_to_eqmap core
  |> ScMap.map (List.map (add_loc in_sys))

let loc_core_to_new_core loc_core =
  let add_eqs_of_scope scope lst acc =
    List.fold_left
      (fun acc (eq, _, _) -> add_new_ts_equation_to_core scope eq acc)
      acc lst
  in
  ScMap.fold add_eqs_of_scope loc_core empty_core

let loc_core_to_filtered_core loc_core ((scmap, mapping) as core) =
  let aux scope actlits =
    let eqs = get_model_elements_of_scope loc_core scope
    |> List.map (fun (a,_,_) -> a)
    |> EqSet.of_list in
    List.filter
      (fun a -> EqSet.mem (get_ts_equation_of_actlit core a) eqs)
      actlits
  in
  (ScMap.mapi aux scmap, mapping)

let empty_loc_core = ScMap.empty

let add_to_loc_core ?(check_already_exists=false) scope elt core =
  let elts = get_model_elements_of_scope core scope in
  if check_already_exists && List.exists (fun e -> equal_model_elements e elt) elts
  then core
  else ScMap.add scope (elt::elts) core

let remove_from_loc_core scope elt core =
  let elts = get_model_elements_of_scope core scope in
  let elts = List.filter (fun e -> equal_model_elements e elt |> not) elts in
  ScMap.add scope elts core

let loc_core_diff core1 core2 =
  ScMap.mapi (fun scope elts ->
    List.filter (fun elt ->
        get_model_elements_of_scope core2 scope
        |> List.exists (fun e -> equal_model_elements e elt)
        |> not
      ) elts
  ) core1

type category = [ `NODE_CALL | `CONTRACT_ITEM | `EQUATION | `ASSERTION | `ANNOTATIONS ]

let is_model_element_in_categories (_,_,cat) is_main_node cats =
  let cat = match cat with
  | NodeCall _ -> [`NODE_CALL]
  | ContractItem (_, _, LustreNode.WeakAssumption) when is_main_node
  -> [`ANNOTATIONS ; `CONTRACT_ITEM]
  | ContractItem (_, _, LustreNode.WeakGuarantee) when not is_main_node
  -> [`ANNOTATIONS ; `CONTRACT_ITEM]
  | ContractItem (_, _, LustreNode.Assumption) when is_main_node
  -> [`CONTRACT_ITEM]
  | ContractItem (_, _, LustreNode.Guarantee) when not is_main_node
  -> [`CONTRACT_ITEM]
  | ContractItem (_, _, LustreNode.Require) when not is_main_node
  -> [`CONTRACT_ITEM]
  | ContractItem (_, _, LustreNode.Ensure) when not is_main_node
  -> [`CONTRACT_ITEM]
  | ContractItem (_, _, _) -> []
  | Equation _ -> [`EQUATION]
  | Assertion _ -> [`ASSERTION]
  | Unknown -> [(*`UNKNOWN*)]
  in
  List.exists (fun cat -> List.mem cat cats) cat


(* Identify the provenance of a term.
   A 'trans' term and its corresponding 'init' term should have the same TermId. *)
type term_id = SVSet.t * bool (* Is node call *)
module TermId = struct
  type t = term_id
  let is_empty (k,_) = SVSet.is_empty k
  let compare (a,b) (a',b') =
    match compare b b' with
    | 0 -> SVSet.compare a a'
    | n -> n
end
module TIdMap = Map.Make(TermId)

let id_of_term in_sys t =
  match Term.destruct t with
  | Term.T.App (s, ts) when
    (match (Symbol.node_of_symbol s) with `UF _ -> true | _ -> false)
    -> (* Case of a node call *)
    let (_, svs) = name_and_svs_of_node_call in_sys s ts in
    (svs, true)
  | _ ->
    try (SVSet.singleton (sv_of_term t), false)
    with _ -> (SVSet.empty, false)


let rec deconstruct_conj t =
  match Term.destruct t with
  | Term.T.App (s_and, ts) when Symbol.equal_symbols s_and Symbol.s_and ->
    List.map deconstruct_conj ts |> List.flatten
  | _ -> [t]

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
    let tid = id_of_term in_sys c in
    if TermId.is_empty tid then acc
    else
      let (o,c) =
        try
          let (o',c') = TIdMap.find tid acc in
          (Term.mk_and [o;o'], Term.mk_and [c;c'])
        with Not_found -> (o,c) in
      TIdMap.add tid (o,c) acc
  ) TIdMap.empty
  in
  let init_map = mk_map init in
  let trans_map = mk_map trans in
  TIdMap.merge
    (fun _ i t ->
      match i, t with
      | Some (oi,ci), Some (ot,ct) -> (
        let eq =
          { init_opened=oi ; init_closed=ci ;
            trans_opened=ot ; trans_closed=ct }
        in
        Some eq
      )
      | Some (oi,ci), None -> (
        let eq =
          { init_opened=oi ; init_closed=ci ;
            trans_opened=Term.t_true ; trans_closed=Term.t_true }
        in
        Some eq
      )
      | None, Some (ot,ct) -> (
        let eq =
          { init_opened=Term.t_true ; init_closed=Term.t_true ;
            trans_opened=ot ; trans_closed=ct }
        in
        Some eq
      )
      | None, None -> assert false
    )
    init_map
    trans_map
  |> TIdMap.bindings |> List.map snd


let full_loc_core_for_sys in_sys sys ~only_top_level =
  let treat_subnode acc sys =
    let scope = TS.scope_of_trans_sys sys in
    extract_toplevel_equations in_sys sys
    |> List.map (ts_equation_to_model_element in_sys)
    |> List.fold_left (fun acc elt -> add_to_loc_core scope elt acc) acc
  in
  let res = treat_subnode empty_loc_core sys in
  if only_top_level then res
  else TS.fold_subsystems ~include_top:false treat_subnode res sys

let filter_loc_core_by_categories main_scope cats loc_core =
  let ok =
    ScMap.mapi (fun scope elts ->
      let main = Scope.equal scope main_scope in
      List.filter
        (fun elt -> is_model_element_in_categories elt main cats)
        elts
    ) loc_core in
  let not_ok =
    ScMap.mapi (fun scope elts ->
      let main = Scope.equal scope main_scope in
      List.filter
        (fun elt -> is_model_element_in_categories elt main cats |> not)
        elts
    ) loc_core in
  (ok, not_ok)

let partition_loc_core_elts_by_guarantees loc_core =
  let f = function
    | ContractItem (_, _, LustreNode.WeakGuarantee)
    | ContractItem (_, _, LustreNode.Guarantee) -> true
    | _ -> false
  in
  ScMap.fold
    (fun scope elts (lc_t, lc_f) ->
      let elts_t, elts_f =
        elts |> List.partition (fun (_,_,cat) -> f cat)
      in
      ScMap.add scope elts_t lc_t, ScMap.add scope elts_f lc_f
    )
    loc_core
    (ScMap.empty, ScMap.empty)