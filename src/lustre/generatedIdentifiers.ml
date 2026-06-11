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

(**
  @author Andrew Marmaduke 
  *)    

module StringMap = HString.HStringMap

module StringSet = HString.HStringSet

type source = Local | Input | Output | Ghost

type t = {
  node_args : (HString.t (* abstracted variable name *)
    * bool (* whether the variable is constant *)
    * LustreAst.lustre_type
    * LustreAst.expr)
    list;
  locals : 
  (LustreAst.lustre_type)
    StringMap.t;
  free_constants: (HString.t * LustreAst.lustre_type) list;
  contract_calls :
    (Lib.position
    * (Lib.position * NodeId.t) list (* contract scope *)
    * LustreAst.contract_node_equation list)
    StringMap.t;
  oracles : (HString.t * LustreAst.lustre_type * LustreAst.expr) list;
  ib_oracles : (HString.t * LustreAst.lustre_type) list;
  calls : (Lib.position (* node call position *)
    * HString.t (* abstracted output *)
    * LustreAst.expr (* condition expression *)
    * LustreAst.expr (* restart expression *)
    * HString.t option (* boolean variable representing call context *)
    * NodeId.t (* node name *)
    * (LustreAst.expr list) (* node arguments *)
    * (LustreAst.expr list option) (* node argument defaults *)
    * bool) (* Was call inlined? *)
    list;
  refinement_type_constraints: (source
    * Lib.position
    * HString.t (* Generated name for refinement type constraint *)
    * LustreAst.expr
    * NodeId.t option) (* Node ID for type ascription substitution *)
  list;
  empty_maps: (HString.t * LustreAst.lustre_type * LustreAst.lustre_type) list;
  empty_sets: (HString.t * LustreAst.lustre_type) list;
  map_element_updates: (HString.t * 
    LustreAst.expr * 
    LustreAst.expr * 
    LustreAst.expr * 
    HString.t *
    LustreAst.lustre_type * 
    LustreAst.lustre_type) list;
  map_subtractions: (HString.t *
    LustreAst.expr *
    LustreAst.expr *
    HString.t *
    LustreAst.lustre_type *
    LustreAst.lustre_type) list;
  set_insertions: (HString.t *
    LustreAst.expr * 
    LustreAst.expr * 
    HString.t *
    LustreAst.lustre_type) list;
  set_binops: (HString.t * 
    LustreAst.expr * 
    LustreAst.expr * 
    HString.t *
    LustreAst.binary_operator * 
    LustreAst.lustre_type) list;
  expanded_variables : StringSet.t;
  equations :
    (LustreAst.typed_ident list (* quantified variables *)
    * (Lib.position * NodeId.t) list (* contract scope  *)
    * LustreAst.eq_lhs
    * LustreAst.expr
    * source option) (* Record the source of the equation if generated before normalization step *)
    list;
  nonvacuity_props: StringSet.t;
  array_literal_vars: StringSet.t;
  expr_source_map: LustreAst.expr StringMap.t;
  type_ascription_exprs: LustreAst.expr NodeId.Map.t;
  history_vars: HString.t StringMap.t;
}

(* String constant used in lustreDesugarIfBlocks.ml and lustreDesugarFrameBlocks.ml
   that is used for if block oracle variable names. *)
let iboracle =  "iboracle"

(* String constant used for counter variables generated for instrumentation
   of reachability queries with timestep bounds. *)
let ctr_id = HString.mk_hstring "*counter"

(* Checks if a variable name corresponds to an iboracle *)
let var_is_iboracle var = 
  let 
    var = String.split_on_char '_' (HString.string_of_hstring var) |>
    List.rev |> List.hd
  in
  (var = iboracle)

let union_keys key id1 id2 = match key, id1, id2 with
  | _, None, None -> None
  | _, (Some v), None -> Some v
  | _, None, (Some v) -> Some v
  (* Identifiers are guaranteed to be unique making this branch impossible *)
  | _, (Some _), (Some _) -> assert false


let union ids1 ids2 = {
    locals = StringMap.merge union_keys ids1.locals ids2.locals;
    free_constants = ids1.free_constants @ ids2.free_constants;
    node_args = ids1.node_args @ ids2.node_args;
    oracles = ids1.oracles @ ids2.oracles;
    ib_oracles = ids1.ib_oracles @ ids2.ib_oracles;
    calls = ids1.calls @ ids2.calls;
    contract_calls = StringMap.merge union_keys
      ids1.contract_calls ids2.contract_calls;
    refinement_type_constraints = ids1.refinement_type_constraints @ ids2.refinement_type_constraints;
    empty_maps = ids1.empty_maps @ ids2.empty_maps;
    empty_sets = ids1.empty_sets @ ids2.empty_sets;
    map_element_updates = ids1.map_element_updates @ ids2.map_element_updates;
    map_subtractions = ids1.map_subtractions @ ids2.map_subtractions;
    set_binops = ids1.set_binops @ ids2.set_binops;
    set_insertions = ids1.set_insertions @ ids2.set_insertions;
    expanded_variables = StringSet.union ids1.expanded_variables ids2.expanded_variables;
    equations = ids1.equations @ ids2.equations;
    nonvacuity_props = StringSet.union ids1.nonvacuity_props ids2.nonvacuity_props;
    array_literal_vars = StringSet.union ids1.array_literal_vars ids2.array_literal_vars;
    expr_source_map = StringMap.union (fun _ src _ -> Some src) ids1.expr_source_map ids2.expr_source_map;
    type_ascription_exprs = NodeId.Map.union (fun _ expr _ -> Some expr) ids1.type_ascription_exprs ids2.type_ascription_exprs;
    history_vars = StringMap.union (fun _ h_sv _ -> Some h_sv) ids1.history_vars ids2.history_vars
  }

(* Same as union_keys, but we don't assume that identifiers are unique *)
let union_keys2 key id1 id2 = match key, id1, id2 with
  | _, None, None -> None
  | _, (Some v), None -> Some v
  | _, None, (Some v) -> Some v
  | _, (Some a), (Some b) -> Some (union a b)
  
let empty () = {
  locals = StringMap.empty;
  free_constants = [];
  node_args = [];
  oracles = [];
  ib_oracles = [];
  calls = [];
  contract_calls = StringMap.empty;
  refinement_type_constraints = [];
  empty_maps = [];
  empty_sets = [];
  map_element_updates = [];
  map_subtractions = [];
  set_binops = [];
  set_insertions = [];
  expanded_variables = StringSet.empty;
  equations = [];
  nonvacuity_props = StringSet.empty;
  array_literal_vars = StringSet.empty;
  expr_source_map = StringMap.empty;
  type_ascription_exprs = NodeId.Map.empty;
  history_vars = StringMap.empty;
}
