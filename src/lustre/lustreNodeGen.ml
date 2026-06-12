(* This file is part of the Kind 2 model checker.

   Copyright (c) 2021 by the Board of Trustees of the University of Iowa

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

(** Translation of type checked AST to intermediate node model
  
  @author Andrew Marmaduke *)

open Lib
open LustreReporting

module A = LustreAst
module AH = LustreAstHelpers
module AN = LustreAstNormalizer
module GI = GeneratedIdentifiers
module G = LustreGlobals
module N = LustreNode
module C = LustreContract
module I = LustreIdent
module X = LustreIndex
module H = LustreIdent.Hashtbl
module E = LustreExpr
module LDF = LustreDesugarFrameBlocks
module LDI = LustreDesugarIfBlocks
module NI = NodeId

module SVM = StateVar.StateVarMap
module SVT = StateVar.StateVarHashtbl
module SVS = StateVar.StateVarSet
module TM = Type.TypeMap

module Ctx = TypeCheckerContext

module StringMap = HString.HStringMap

type identifier_maps = {
  state_var : StateVar.t LustreIdent.Hashtbl.t;
  usr_state_var : StateVar.t LustreIndex.t LustreIdent.Hashtbl.t;
  res_state_var : StateVar.t LustreIndex.t LustreIdent.Hashtbl.t;
  expr : LustreExpr.t LustreIndex.t LustreIdent.Hashtbl.t; 
  array_literal_index : LustreExpr.t LustreIndex.t LustreIdent.Hashtbl.t;
  source : LustreNode.state_var_source StateVar.StateVarHashtbl.t;
  bounds : (LustreExpr.expr LustreExpr.bound_or_fixed list)
    StateVar.StateVarHashtbl.t;
  array_index : LustreExpr.t LustreIndex.t LustreIdent.Hashtbl.t;
  quant_vars : LustreExpr.t LustreIndex.t LustreIdent.Hashtbl.t;
  modes : LustreContract.mode list;
  contract_scope : (Lib.position * HString.t) list;
  node_name : HString.t option;
  assume_count : int;
  guarantee_count : int;
  poracle_count : int;
  call_count : int;
}

type compiler_state = {
  nodes : LustreNode.t list;
  node_io : (StateVar.t X.t * StateVar.t X.t * identifier_maps) NI.Map.t;
  type_alias : Type.t LustreIndex.t StringMap.t;
  free_constants : (HString.t option * HString.t * Var.t LustreIndex.t * bool) list;
  local_constants : LustreAst.expr StringMap.t;
  other_constants : LustreAst.expr StringMap.t;
  state_var_bounds : (LustreExpr.expr LustreExpr.bound_or_fixed list)
    StateVar.StateVarHashtbl.t;
  global_constraints: LustreExpr.t list;
}

(*
let pp_print_identifier_maps ppf maps =
  let table_to_list h = H.fold (fun k v acc -> (k, v) :: acc) h []
  in let map_to_list m = SVT.fold (fun k v acc -> (k, v) :: acc) m []
  in Format.fprintf ppf "{ state_var:%a;\n\n
    expr: %a;\n\n
    source:%a\n\n;
    array_index:%a\n\n }\n\n"
    (pp_print_list
      (pp_print_pair
        (I.pp_print_ident true)
        StateVar.pp_print_state_var
        "=") ",\n")
    (table_to_list maps.state_var)
    (pp_print_list
      (pp_print_pair
        (I.pp_print_ident true)
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true))
        "=") ",\n")
    (table_to_list maps.expr)
    (pp_print_list
      (pp_print_pair
        (StateVar.pp_print_state_var)
        (N.pp_print_state_var_source)
        "=") ",\n")
    (map_to_list maps.source)
    (pp_print_list
      (pp_print_pair
        (I.pp_print_ident true)
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true))
        "=") ",\n")
    (table_to_list maps.array_index)
*)

let empty_identifier_maps node_name = {
  state_var = H.create 7;
  usr_state_var = H.create 7;
  res_state_var = H.create 7;
  expr = H.create 7;
  array_literal_index = H.create 7;
  source = SVT.create 7;
  bounds = SVT.create 7;
  array_index = H.create 7;
  quant_vars = H.create 7;
  modes = [];
  contract_scope = [];
  node_name = node_name;
  assume_count = 0;
  guarantee_count = 0;
  poracle_count = 1;
  call_count = 1;
}

let empty_compiler_state () = { 
  nodes = [];
  node_io = NI.Map.empty;
  type_alias = StringMap.empty;
  free_constants = [];
  local_constants = StringMap.empty;
  other_constants = StringMap.empty;
  state_var_bounds = SVT.create 7;
  global_constraints = [];
}

(*
let array_select_of_bounds_term bounds e =
  let (_, e) = List.fold_left (fun (i, t) -> function
    | E.Bound _ ->
        succ i, Term.mk_select t (Term.mk_var @@ E.var_of_expr @@ E.mk_index_var i)
    | E.Unbound v ->
        i, Term.mk_select t (E.unsafe_term_of_expr v)
    | _ -> assert false)
      (0, e) bounds
  in e
*)

let array_select_of_indexes_expr indexes e =
  List.fold_left (fun e i -> 
    E.mk_select_and_push e (E.mk_array_index_var i Type.t_int)
  ) e indexes

(* Try to make the types of two expressions line up.
  * If one expression is an array but the other is not, then insert a 'select'
  * around the array expression so that the two expressions both have similar types.
  * This is used by mk_arrow and mk_ite for array expressions. *)
let coalesce_array2 e1 e2 =
  let t1 = E.type_of_lustre_expr e1
  and t2 = E.type_of_lustre_expr e2 in
  let i1 = List.length (Type.all_index_types_of_array t1)
  and i2 = List.length (Type.all_index_types_of_array t2) in
  if i1 > i2 then 
    array_select_of_indexes_expr (List.init (i1 - i2) (fun x -> x)) e1, e2
  else if i2 > i1 then 
    e1, array_select_of_indexes_expr (List.init (i2 - i1) (fun x -> x)) e2
  else
    e1, e2

(* For some reason this works, but E.state_var_of_expr does not,
  but one would expect them to be equivalent when an expression contains
  only one state variable *)
let state_var_of_expr expr = expr |> E.state_vars_of_expr |> SVS.choose

let mk_state_var_name ident index = Format.asprintf "%a%a"
  (I.pp_print_ident true) ident
  (X.pp_print_index true) 
  (* Filter out array indexes *)
  (X.filter_array_indices index)

let bounds_of_index index =
  List.fold_left (fun acc -> function
      | X.ArrayVarIndex b -> E.Bound b :: acc
      | X.SetMapIndex b -> E.Unbound (Some b) :: acc
      | X.ArrayIntIndex i ->
        E.Fixed (E.mk_int_expr (Numeral.of_int (i + 1))) :: acc
      | _ -> acc
    ) [] index


let update_array_literal_index map scope sv_ident index =
  let compute_expr expr =
    try
      let t = H.find !map.array_literal_index sv_ident in
      X.add index expr t
    with Not_found -> X.singleton index expr
  in
  let state_var_name = mk_state_var_name sv_ident index in
  let flatten_scopes = X.mk_scope_for_index index in
  try
    let state_var = StateVar.state_var_of_string
      (state_var_name,
      (List.map Ident.to_string (scope @ flatten_scopes)))
    in
    H.replace !map.array_literal_index sv_ident (compute_expr (E.mk_var state_var))
  with Not_found ->
    assert false

(* Create a state variable for from an indexed state variable in a
  scope *)
let mk_state_var
    ?is_input
    ?is_const
    ?for_inv_gen
    ?expr_ident
    ?(force_return = false)
    map
    scope
    sv_ident 
    index 
    state_var_type
    source = 
  let expr_ident = match expr_ident with
    | Some id -> id
    | None -> sv_ident
  in
  (* Concatenate identifier and indexes *)
  let state_var_name = mk_state_var_name sv_ident index in
  (* For each index add a scope to the identifier to distinguish the
    flattened indexed identifier from unindexed identifiers

    The scopes indicate the positions from the back of the string in
    the flattened identifier where a new index begins.

    The following indexed identifiers are all flattened to x_y_z, but
    we can distinguish them by their scopes:
    x_y_z  [] 
    x.y.z  [2;2]
    x.y_z  [4]
    x_y.z  [2]
  *)
  let flatten_scopes = X.mk_scope_for_index index in
  let compute_expr expr =
    try
      let t = H.find !map.expr expr_ident in
      X.add index expr t
    with Not_found -> X.singleton index expr
  in
  
  (* Create or retrieve state variable *)
  let state_var, fresh = (try
    let state_var = StateVar.state_var_of_string
      (state_var_name,
      (List.map Ident.to_string (scope @ flatten_scopes)))
    in
    state_var, false
  with Not_found ->
    let state_var = StateVar.mk_state_var
      ?is_input
      ?is_const
      ?for_inv_gen 
      state_var_name
      (scope @ flatten_scopes)
      state_var_type
    in
    state_var, true)
  in
  SVT.replace !map.bounds state_var (bounds_of_index index);
  H.replace !map.expr expr_ident (compute_expr (E.mk_var state_var));
  H.replace !map.state_var expr_ident state_var;
  (match source with
    | Some source -> SVT.replace !map.source state_var source;
    | None -> ());
  if fresh || force_return then Some(state_var) else None

let mk_ident id =
  let id = HString.string_of_hstring id in
  match String.split_on_char '_' id with
  | i :: id' -> (match int_of_string_opt i with
    | Some i -> 
      let id' = String.concat "_" id' in
      I.push_index (I.mk_string_ident id') i
    | None -> I.mk_string_ident id)
  | _ -> I.mk_string_ident id

(* The LustreAstNormalizer is expected to normalize specific expression
  positions to an identifier (or leave it be if it is a constnat).
  That assumption is made explicit by calling this function. *)
let extract_normalized = function
  | A.Ident (_, ident) -> mk_ident ident
  | A.IndexAccess (_, A.Ident (_, ident), _, _) -> mk_ident ident
  | _ -> assert false

module XMap = Map.Make(struct
  type t = X.index
  let compare = X.compare_indexes
end)

let flatten_list_indexes (e:'a X.t) =
  let top_is_list =
    try X.top_max_index e >= 0
    with Invalid_argument _ -> false
  in
  if not top_is_list then e
  else
    let rec extract_list_prefix acc = function
      | (X.ListIndex i) :: tl ->
        extract_list_prefix ((X.ListIndex i) :: acc) tl
      | rest -> (List.rev acc), rest
    in
    let m =
      List.fold_left (fun acc (indices, e) ->
        let prefix, other = extract_list_prefix [] indices in
        XMap.update
          prefix
          (function
          | None -> Some [(other, e)]
          | Some l -> Some ((other, e) :: l)
          )
          acc
      )
      XMap.empty
      (X.bindings e)
    in
    XMap.fold
      (fun _ l (acc, i) ->
        let acc =
          List.fold_left
            (fun acc (indices, e) ->
              X.add ((X.ListIndex i) :: indices) e acc
            )
            acc
            l
        in
        acc, i + 1
      )
      m
      (X.empty, 0)
    |> fst

(* Match bindings from a trie of state variables and bindings for a
   trie of expressions and produce a list of equations *)
let rec expand_tuple' pos accum bounds lhs rhs = 
  (*Format.eprintf "lhs: %a\n"
    (pp_print_list
      (pp_print_pair
        (pp_print_list (X.pp_print_one_index true) " , ")
        (StateVar.pp_print_state_var)
        " : ")
      " ; ") lhs;
  Format.eprintf "rhs: %a\n"
    (pp_print_list
      (pp_print_pair
        (pp_print_list (X.pp_print_one_index true) " , ")
        (E.pp_print_lustre_expr true)
        " : ")
      " ; ") rhs;*)
  match lhs, rhs with 
  (* No more equations, return in original order *)
  | [], [] -> accum
  (* Indexes are not of equal length *)
  | _, []
  | [], _ ->
    internal_error pos "Type mismatch in equation: indexes not of equal length";
    assert false
    (* All indexes consumed *)
  | ([], state_var) :: lhs_tl, 
    ([], expr) :: rhs_tl -> 
    expand_tuple' pos
      (((state_var, List.rev bounds), expr) :: accum)
      [] lhs_tl rhs_tl
  (* Only array indexes may be left at head of indexes *)
  | (X.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    ([], expr) :: rhs_tl ->
    expand_tuple' pos accum (E.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      (([], expr) :: rhs_tl)
  | (X.SetMapIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    ([], expr) :: rhs_tl ->
    expand_tuple' pos accum (E.Unbound (Some b) :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      (([], expr) :: rhs_tl)
  | (X.ArrayIntIndex idx :: lhs_index_tl, state_var) :: lhs_tl,
    ([], expr) :: rhs_tl ->
    let expr_type = E.type_of_lustre_expr expr in
    if Type.is_array expr_type then
      let index_type = Type.index_type_of_array expr_type in
      let index_arg = E.mk_of_expr ~as_type:index_type (E.mk_int_expr (Numeral.of_int idx)) in
      let indexed_expr = E.mk_select_and_push expr index_arg in
      let accum = expand_tuple' pos accum bounds
        [(lhs_index_tl, state_var)]
        [([], indexed_expr)]
      in
      if List.length lhs_tl == 0 then accum
      else expand_tuple' pos accum bounds lhs_tl (([], expr) :: rhs_tl)
    else
      let state_var_type = StateVar.type_of_state_var state_var in
      let rec mk_bounds ty acc =
        if Type.is_array ty then
          let index_type = Type.index_type_of_array ty in
          let u = match Type.bounds_of_int_range index_type with 
            | _, Some u -> u 
            | _, None -> assert false 
          in
          let uexpr = E.mk_int_expr u in
          let acc = E.Bound uexpr :: acc in
          mk_bounds (Type.elem_type_of_array ty) acc
        else acc
      in
      let bounds' = List.rev (mk_bounds state_var_type []) in
      expand_tuple' pos accum (bounds' @ bounds)
        (([], state_var) :: lhs_tl)
        (([], expr) :: rhs_tl)
  (* Array variable on left-hand side, fixed index on right-hand side *)
  | (X.ArrayVarIndex _ :: lhs_index_tl, state_var) :: _,
    (X.ArrayIntIndex i :: rhs_index_tl, expr) :: rhs_tl -> 
    (* Recurse to produce equations with this index *)
    let accum' = 
      expand_tuple' pos accum
        (E.Fixed (E.mk_int_expr (Numeral.of_int i)) :: bounds)
        [(lhs_index_tl, state_var)]
        [(rhs_index_tl, expr)]
    in
    (* Return of no fixed indexes on right-hand side left *)
    if rhs_tl = [] then accum' else
      (* Continue with next fixed index on right-hand side and
        variable index on left-hand side *)
      expand_tuple' pos accum' bounds lhs rhs_tl
  (* Array index on left-hand and right-hand side *)
  | (X.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ArrayVarIndex br :: rhs_index_tl, expr) :: rhs_tl -> 

    (* We cannot compare expressions for array bounds syntactically,
      because that may give too many false negatives. Evaluating both
      bounds to find if they are equal would be too complicated,
      therefore accept some false positives here. *)

    (* Take the smaller bound when it is known statically otherwise keep the
      one from the left-hand side *)
    let b = if E.is_numeral b && E.is_numeral br
      && Numeral.(E.(numeral_of_expr b > numeral_of_expr br))
      then br
      else b
    in
    let expr_type = expr.E.expr_type in
    let array_index_types = Type.all_index_types_of_array expr_type in
    let over_index_types (e, i, j) _ =
      let ty = 
        let idx = List.nth (List.rev (X.ArrayVarIndex b :: rhs_index_tl)) j in 
        match idx with 
        | X.SetMapIndex b
        | X.ArrayVarIndex b -> 
          E.type_of_expr b 
        | X.ArrayIntIndex _ -> Type.t_int
        | _ -> assert false 
      in
      E.mk_select_and_push e (E.mk_array_index_var i ty), succ i, succ j
    in
    let start = (List.length lhs_index_tl + 1) - List.length array_index_types in
    let expr, _, _ = List.fold_left over_index_types (expr, start, 0) array_index_types in
    expand_tuple' pos accum (E.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      ((rhs_index_tl, expr) :: rhs_tl)
  (* Map index on right and left side *)
  | (X.SetMapIndex _ :: lhs_index_tl, state_var) :: lhs_tl,
    (X.SetMapIndex b :: rhs_index_tl, expr) :: rhs_tl -> 
    let expr_type = expr.E.expr_type in
    let array_index_types = Type.all_index_types_of_array expr_type in
    let over_index_types (e, i, j) _ =
      let ty = 
        let idx = List.nth (List.rev (X.SetMapIndex b :: rhs_index_tl)) j in 
        match idx with 
        | X.ArrayVarIndex b
        | X.SetMapIndex b -> 
          E.type_of_expr b 
        | X.ArrayIntIndex _ -> Type.t_int
        | _ -> assert false 
      in
      E.mk_select_and_push e (E.mk_array_index_var i ty), succ i, succ j
    in
    let start = (List.length lhs_index_tl + 1) - List.length array_index_types in
    let expr, _, _ = List.fold_left over_index_types (expr, start, 0) array_index_types in
    expand_tuple' pos accum (E.Unbound (Some b) :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      ((rhs_index_tl, expr) :: rhs_tl)
  (* Tuple index on left-hand and right-hand side *)
  | ((X.TupleIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.TupleIndex j :: rhs_index_tl, expr) :: rhs_tl) 
  | ((X.ListIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ListIndex j :: rhs_index_tl, expr) :: rhs_tl) ->
    (* Indexes are sorted, must match *)
    if i = j then (match lhs_tl with
      | (X.ListIndex j' :: X.ArrayIntIndex _ :: _, _) :: _ ->
        if j = j' then
          let accum = expand_tuple' pos accum bounds
            [(lhs_index_tl, state_var)]
            [(rhs_index_tl, expr)]
          in
          expand_tuple' pos accum bounds
            lhs_tl
            ((X.ListIndex j :: rhs_index_tl, expr) :: rhs_tl)
        else expand_tuple' pos accum bounds
          ((lhs_index_tl, state_var) :: lhs_tl)
          ((rhs_index_tl, expr) :: rhs_tl)
      | _ -> expand_tuple' pos accum bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl))
    else (
      internal_error pos "Type mismatch in equation: indexes do not match";
      assert false)
  | ((X.ArrayIntIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ArrayIntIndex j :: rhs_index_tl, expr) :: rhs_tl) ->
    (* Indexes are sorted, must match *)
    let expr_type = E.type_of_lustre_expr expr in
    if Type.is_array expr_type then
      expand_tuple' pos accum bounds
        [([], state_var)]
        [([], expr)]
    else if i = j then 
      let n = (i |> Numeral.of_int |> E.mk_int).expr_init in
      expand_tuple' pos accum (E.Fixed n :: bounds)
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl)
    else (internal_error pos "Type mismatch in equation: indexes do not match";
          assert false)
  (* Tuple index on left-hand and array index on right-hand side *)
  | ((X.TupleIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ArrayIntIndex j :: _, expr) :: rhs_tl) ->
    (* Indexes are sorted, must match *)
    if i = j then 
      (* Use tuple index instead of array index on right-hand side *)
      expand_tuple' pos accum bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((lhs_index_tl, expr) :: rhs_tl)
    else (internal_error pos "Type mismatch in equation: indexes do not match";
          assert false)
  (* Record index on left-hand and right-hand side *)
  | (X.RecordIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.RecordIndex j :: rhs_index_tl, expr) :: rhs_tl
  (* Abstract type index works like record except program cannot project field *)
  | (X.AbstractTypeIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.AbstractTypeIndex j :: rhs_index_tl, expr) :: rhs_tl -> 
    (* Indexes are sorted, must match *)
    if i = j then 
      expand_tuple' pos accum bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl)
    else (internal_error pos "Type mismatch in equation: record indexes do not match";
          assert false)
  (* Mismatched indexes on left-hand and right-hand sides *)
  | (X.RecordIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.RecordIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.RecordIndex _ :: _, _) :: _, (X.ArrayIntIndex _ :: _, _) :: _
  | (X.RecordIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.RecordIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _
  | (X.RecordIndex _ :: _, _) :: _, (X.SetMapIndex _ :: _, _) :: _

  | (X.TupleIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.TupleIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.TupleIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.TupleIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _
  | (X.TupleIndex _ :: _, _) :: _, (X.SetMapIndex _ :: _, _) :: _

  | (X.ListIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.ArrayIntIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.SetMapIndex _ :: _, _) :: _

  | (X.ArrayIntIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.SetMapIndex _ :: _, _) :: _

  | (X.ArrayVarIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.ArrayVarIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.ArrayVarIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.ArrayVarIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _
  | (X.ArrayVarIndex _::_, _)::_, (SetMapIndex _ :: _, _)::_

  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.ArrayIntIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.SetMapIndex _ :: _, _) :: _

  | (X.SetMapIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.SetMapIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.SetMapIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.SetMapIndex _ :: _, _) :: _, (X.ArrayIntIndex _ :: _, _) :: _
  | (X.SetMapIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.SetMapIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _

  | (_ :: _, _) :: _, ([], _) :: _ 
  | ([], _) :: _, (_ :: _, _) :: _ ->
    (internal_error pos "Type mismatch in equation: head indexes do not match";
      assert false)

(* Return a list of equations from a trie of state variables and a
  trie of expressions *)
let expand_tuple pos lhs rhs = 
  (*Format.eprintf "lhs: %a\n\n rhs: %a\n\n"
    (X.pp_print_index_trie true StateVar.pp_print_state_var) lhs
    (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) rhs; *)
  (* Format.eprintf "expand_tuple: \n"; *)
  expand_tuple' pos [] []
    (X.bindings lhs) (X.bindings rhs)

let compile_contract_item gids map count scope kind pos name expr =
    let scope = List.map (fun (i, s) -> i, HString.string_of_hstring s) scope in
    let ident = extract_normalized expr in
    let state_var = H.find !map.state_var ident in
    let name = match name with
      | Some name -> Some (HString.string_of_hstring name)
      | None -> None
    in
    let sexpr =
      let key = HString.mk_hstring (LustreAst.string_of_expr expr) in
      try LustreAst.string_of_expr (GI.StringMap.find key gids.GI.expr_source_map)
      with Not_found -> LustreAst.string_of_expr expr
    in
    let contract_sv = C.mk_svar pos count name state_var scope sexpr in
    N.add_state_var_def state_var (N.ContractItem (pos, contract_sv, kind));
    contract_sv

let create_uf_symbols node_id inputs outputs =
  let type_of = StateVar.type_of_state_var in
  let input_types = List.map type_of (X.values inputs) in

  X.values outputs
  |> List.fold_left (
    fun uf_symbols output ->
      let uf_name =
        Format.asprintf "%a.%s.%s"
        HString.pp_print_hstring (NI.get_internal_name node_id)
          (StateVar.name_of_state_var output)
          Lib.ReservedIds.function_of_inputs
      in
      let uf =
        UfSymbol.mk_uf_symbol
          uf_name input_types (type_of output)
      in
      SVM.add output uf uf_symbols
  ) SVM.empty

let rec compile ctx gids scc_map decls =
  let over_decls_1 cstate decl = compile_declaration_phase1 cstate ctx decl in
  let output = List.fold_left over_decls_1 (empty_compiler_state ()) decls in
  let over_decls_2 cstate decl = compile_declaration_phase2 cstate gids ctx scc_map decl in
  let output = List.fold_left over_decls_2 output decls in
  let free_constants = output.free_constants
    |> List.map (fun (_, id, v, is_generated) -> mk_ident id, v, is_generated)
  in
  output.nodes,
    { G.free_constants = free_constants;
      G.state_var_bounds = output.state_var_bounds;
      G.global_constraints = output.global_constraints }

and compile_ast_type
  ?(expand=false)
  (cstate:compiler_state)
  (ctx:Ctx.tc_context)
  map
  = function
  | A.Bool _ -> X.singleton X.empty_index Type.t_bool
  | A.Int _ -> X.singleton X.empty_index Type.t_int
  | A.SBitVector (_, s) -> X.singleton X.empty_index (Type.t_bv s)
  | A.UBitVector (_, s) -> X.singleton X.empty_index (Type.t_ubv s)
  | A.Real _ -> X.singleton X.empty_index Type.t_real
  | A.EnumType (_, enum_name, enum_elements) ->
      let enum_name = HString.string_of_hstring enum_name in
      let enum_elements = List.map HString.string_of_hstring enum_elements in
      let ty = Type.mk_enum enum_name enum_elements in
      X.singleton X.empty_index ty
  | A.UserType (_, _, ident) ->
    StringMap.find ident cstate.type_alias 
  | A.AbstractType (_, ident) ->
    let ident = HString.string_of_hstring ident in
    X.singleton X.empty_index (Type.mk_abstr ident)
  | A.RecordType (_, _, record_fields) ->
    let over_fields = fun a (_, i, t) ->
      let i = HString.string_of_hstring i in
      let over_indices = fun j t a -> X.add (X.RecordIndex i :: j) t a in
      let compiled_record_field_ty = compile_ast_type cstate ctx map t in
      X.fold over_indices compiled_record_field_ty a
    in
    List.fold_left over_fields X.empty record_fields
  | A.TupleType (_, tuple_fields) ->
    let over_fields = fun (i, a) t ->
      let over_indices = fun j t a -> X.add (X.TupleIndex i :: j) t a in
      let compiled_tuple_field_ty = compile_ast_type cstate ctx map t in
      succ i, X.fold over_indices compiled_tuple_field_ty a
    in
    List.fold_left over_fields (0, X.empty) tuple_fields |> snd
  | A.GroupType (_, types) -> 
    let over_types (i, a) t =
      let over_indices j t a = X.add (X.ListIndex i :: j) t a in
      let compiled_type = compile_ast_type cstate ctx map t in
      succ i, X.fold over_indices compiled_type a
    in 
    List.fold_left over_types (0, X.empty) types |> snd
  | A.Set (_, ty1) -> 
    let index_type = compile_ast_type cstate ctx map ty1 in
    let types = List.rev (X.values index_type) in
    let last_type = List.hd types in
    let ty2' = A.Bool Lib.dummy_pos in
    let element_type = compile_ast_type cstate ctx map ty2' in
    let over_element_type ty j t a = 
      let dummy = (E.mk_free_var (Var.mk_fresh_var ty)).E.expr_init in
      X.add
      (j @ [X.SetMapIndex dummy])
      (Type.mk_array t ty)
      a
    in
    let base_map_type =
      X.fold (over_element_type last_type) element_type X.empty
    in
    List.fold_left
      (fun acc ty ->
         X.fold (over_element_type ty) acc X.empty
      )
      base_map_type
      (List.tl types)
  | A.Map (_, ty1, ty2) -> 
    let index_type = compile_ast_type cstate ctx map ty1 in
    let types = List.rev (X.values index_type) in
    let last_type = List.hd types in
    let ty2' =
      A.TupleType (Lib.dummy_pos, [A.Bool Lib.dummy_pos; ty2])
    in
    let element_type = compile_ast_type cstate ctx map ty2' in
    let over_element_type ty j t a = 
      let dummy = (E.mk_free_var (Var.mk_fresh_var ty)).E.expr_init in
      X.add
      (j @ [X.SetMapIndex dummy])
      (Type.mk_array t ty)
      a
    in
    let base_map_type =
      X.fold (over_element_type last_type) element_type X.empty
    in
    List.fold_left
      (fun acc ty ->
         X.fold (over_element_type ty) acc X.empty
      )
      base_map_type
      (List.tl types)
  | A.ArrayType (_, (type_expr, size_expr)) ->
    (* TODO: Should we check that array size is constant here or later?
      If the var_size flag is set, variable sized arrays are allowed
      otherwise we should fail and make sure they are constant *)
    let element_type = compile_ast_type cstate ctx map type_expr in
    let array_size' = compile_ast_expr cstate ctx [] map size_expr in
    let array_size = (List.hd (X.values array_size')).expr_init in
    if expand then
      let upper = Numeral.(max zero (E.numeral_of_expr array_size)) in
      let result = ref X.empty in
      for ix = 0 to (Numeral.to_int upper - 1) do
        result := X.fold
          (fun j t a -> 
            X.add (j @ [X.ArrayIntIndex ix])
            (Type.mk_array t
              (Type.mk_int_range (Some Numeral.zero) (Some upper)))
            a)
          element_type
          !result
      done;
      !result
    else
      let over_element_type j t a = X.add
        (j @ [X.ArrayVarIndex array_size])
        (Type.mk_array t (
          if E.is_numeral array_size
          then
            let array_size = Numeral.(max zero (E.numeral_of_expr array_size)) in
            Type.mk_int_range (Some Numeral.zero) (Some array_size)
          else Type.t_int))
        a
      in
      X.fold over_element_type element_type X.empty
  | A.History _
  | A.TArr _ -> assert false
  | A.RefinementType (_, (_, _, ty), _) -> compile_ast_type cstate ctx map ty
      (* Lib.todo "Trying to flatten function type. This should not happen" *)

and vars_of_quant cstate ctx map avars =
  let avars = List.map (fun (p, s, ty) -> p, HString.string_of_hstring s, ty) avars in
  let quant_vars = H.create 7 in
  let var_of_quant vars (_, v, ast_type) = 
    let index_types = compile_ast_type cstate ctx map ast_type in
    let vars, d = X.fold
      (fun index index_type (vars, d) ->
        let name = Format.sprintf "%s%s" v (X.string_of_index true index) in
        let var = Var.mk_free_var (HString.mk_hstring name) index_type in
        let ev = E.mk_free_var var in
        var :: vars, X.add index ev d)
      index_types
      (vars, X.empty)
    in
    let v = HString.mk_hstring v in
    H.replace quant_vars (mk_ident v) d;
    vars
  in
  List.fold_left var_of_quant [] avars, quant_vars

and compile_binary' mk expr1 expr2 =
  (*Format.printf "expr1: %a, expr2: %a\n" 
    (X.pp_print_trie_expr true) expr1 
    (X.pp_print_trie_expr true) expr2;*)
  (* TODO: Old code does three error checks here doublecheck *)
  X.map2 (fun _ -> mk) expr1 expr2

and compile_ast_expr
  (cstate:compiler_state)
  (ctx:Ctx.tc_context)
  (bounds:E.expr E.bound_or_fixed list)
  map
  expr
  : LustreExpr.t LustreIndex.t = 

  let rec compile_id_string bounds id_str =
    let ident = mk_ident id_str in
    try
      H.find !map.quant_vars ident
    with Not_found ->
    try
      H.find !map.array_index ident
    with Not_found ->
    try
      let (_, _, var, _) = List.find (fun (n, i, _, _) -> match (n, !map.node_name) with
        | Some n, Some n' -> n = n' && i = id_str
        | None, _ -> i = id_str
        | _ -> false)
        cstate.free_constants
      in
      X.map E.mk_free_var var
    with Not_found -> (* Local constants *)
    try
      let expr = StringMap.find id_str cstate.local_constants in
      compile_ast_expr cstate ctx bounds map expr
    with Not_found -> (* Global constants *)
    try
      let expr = StringMap.find id_str cstate.other_constants in
      compile_ast_expr cstate ctx bounds map expr
    with Not_found ->
    try 
      let id_str = HString.string_of_hstring id_str in
      let ty = Type.enum_of_constr id_str in
      X.singleton X.empty_index (E.mk_constr id_str ty)
    with Not_found ->
      let id_str = HString.string_of_hstring id_str in
      (match String.split_on_char '_' id_str with
      | proj :: id :: name :: [] -> (try
        let len = String.length proj in
        let proj = String.sub proj 0 (len - 4) in
        let proj = int_of_string proj in
        let id_str = HString.mk_hstring (id ^ "_" ^ name) in
        let ident = mk_ident id_str in
        let e = H.find !map.expr ident in
        let e = X.find [X.ListIndex proj] e in
        X.singleton X.empty_index e
        with _ -> H.find !map.expr ident)
      | _ -> H.find !map.expr ident)

  and compile_mode_reference path' =
    let path' = List.map HString.string_of_hstring path' in
    let path2 = List.map
      (fun (_, s) -> HString.string_of_hstring s)
      !map.contract_scope
    in
    let path' = path2 @ path' in
    let rec find_mode = function
      | { C.path ; C.requires } :: tail ->
        if path = path' then
          requires
          |> List.map (fun { C.svar } -> E.mk_var svar)
          |> E.mk_and_n
          |> X.singleton X.empty_index
        else find_mode tail
      | [] -> assert false
    in find_mode !map.modes

  and compile_unary bounds mk expr =
    (* TODO: Old code does a type check here *)
    X.map mk (compile_ast_expr cstate ctx bounds map expr)

  and compile_binary bounds mk expr1 expr2 =
    let expr1 = compile_ast_expr cstate ctx bounds map expr1 in
    let expr2 = compile_ast_expr cstate ctx bounds map expr2 in
    (*Format.printf "expr1: %a, expr2: %a\n" 
      (X.pp_print_trie_expr true) expr1 
      (X.pp_print_trie_expr true) expr2;*)
    (* TODO: Old code does three error checks here doublecheck *)
    X.map2 (fun _ -> mk) expr1 expr2

  and compile_bvextract bounds mk expr ub lb =
    (* TODO: Old code does a type check here *)
    X.map (mk ub lb) (compile_ast_expr cstate ctx bounds map expr)

  and compile_quantifier bounds mk avars expr =
    let vars, quant_var_map = vars_of_quant cstate ctx map avars in
    let bounds = bounds @
      List.map (fun v -> E.Unbound (Some (E.unsafe_expr_of_term (Term.mk_var v))))
        vars in
    let quant_vars = H.to_seq quant_var_map in
    H.add_seq !map.quant_vars quant_vars;
    let result = compile_unary bounds (mk vars) expr in
    Seq.iter (fun (id, _) -> H.remove !map.quant_vars id) quant_vars;
    result

  and compile_equality bounds polarity expr1 expr2 =
    let (mk_binary, mk_seq, const_expr, mk_quant, mk_comb) = match polarity with
      | true -> (E.mk_eq, E.mk_and, E.t_true, E.mk_forall, E.mk_impl)
      | false -> (E.mk_neq, E.mk_or, E.t_false, E.mk_exists, E.mk_and) in
    let expr1 = compile_ast_expr cstate ctx bounds map expr1 in
    let expr2 = compile_ast_expr cstate ctx bounds map expr2 in
    let eqs = X.map2 (fun _ e1 e2 -> (e1, e2)) expr1 expr2 in
    (* Compile the equality for each pair of `eqs` *)
    let over_indices = fun i (e1, e2) (fst_flag, acc_guard, acc) ->  
      match E.type_of_lustre_expr e1 with 
      (* For LustreNode array types (LustreAst arrays, maps, and sets) we need quantification 
         for structural equality *)
      | ty when Type.is_array ty ->
        let sv = state_var_of_expr e1 in
        let bounds = SVT.find !map.bounds sv in
        let idx_tys = Type.all_index_types_of_array ty in
        assert (List.length bounds = List.length idx_tys);
        let idx_vars = List.map (Var.mk_fresh_var) idx_tys in
        let arr_is = List.map E.mk_free_var idx_vars in
        let e1' = List.fold_left (fun acc arr_i -> 
          E.mk_select_and_push acc arr_i
        ) e1 arr_is in
        let e2' = List.fold_left (fun acc arr_i -> 
          E.mk_select_and_push acc arr_i
        ) e2 arr_is in
        let guard = List.fold_left (fun acc (idx_var, bound) -> 
          match bound with 
          (* For arrays we only consider indices that are in bounds *)
          | E.Bound n
          | E.Fixed n -> 
            let n = E.mk_of_expr n in
            let idx_var = E.mk_free_var idx_var in
            let cond = E.mk_and 
              (E.mk_lte (E.mk_int (Numeral.of_int 0)) idx_var) 
              (E.mk_lt idx_var n) 
            in
            E.mk_and cond acc 
          | E.Unbound _ -> 
            acc
        ) E.t_true (List.combine idx_vars bounds) in
        (* For map value equality we only consider m1[k] = m2[k] for k in the maps. 
           `acc_guard` collects the constraints that k is in the map (if the equality is over maps) *)
        let acc_guard' = List.fold_left (fun acc e -> 
          let e = List.fold_left (fun acc arr_i -> 
            E.mk_select_and_push acc arr_i
          ) e arr_is in
          E.mk_and acc e 
        ) E.t_true acc_guard in
        (* For equality:    forall (x: K) conditions =>  arr1[x]  = arr2[x] 
           For disequality: exists (x: K) conditions and arr1[x] <> arr2[x]. 
           For arrays, `conditions` are that the index is in range. 
           For maps, `conditions` are that the key is in the map (only for arr1 and arr2 representing map values) *)
        let e = mk_quant idx_vars (mk_comb (E.mk_and acc_guard' guard) (mk_binary e1' e2')) in 
        let acc_guard = match fst_flag, bounds with 
        (* Remember `e1` for `acc_guard` if it represents the Boolean presence/absence array *)
        | true, E.Unbound _ :: _ -> e1 :: acc_guard 
        | _ -> acc_guard 
        in
        false, acc_guard, X.add i e acc 
      (* For non-array types, straightforward equality (no quantification) *)
      | _ ->
        false, acc_guard, X.add i (mk_binary e1 e2) acc 
    in
    let _, _, expr = X.fold over_indices eqs (true, [], X.empty) in 
    X.singleton X.empty_index (List.fold_left mk_seq const_expr (X.values expr))

  and compile_ite bounds expr1 expr2 expr3 =
    (* TODO: Old code checks that expr1 is a non-indexed boolean *)
    let expr1 = compile_ast_expr cstate ctx bounds map expr1 in
    let expr1 = match X.bindings expr1 with
      | [_, expr] -> expr
      | _ -> assert false
    in
    let mk e1 e2 =
      let e1', e2' = coalesce_array2 e1 e2 in
      E.mk_ite expr1 e1' e2'
    in
    compile_binary bounds mk expr2 expr3

  and compile_pre bounds expr =
    let cexpr = compile_ast_expr cstate ctx bounds map expr in
    let ident = extract_normalized expr in
    let sv_opt = H.find_opt !map.state_var ident in
    let over_indices index expr' accum =
      let expr' = E.mk_pre expr' in
      let pos = AH.pos_of_expr expr in
      (match sv_opt with
        | Some sv ->
          let source = SVT.find_opt !map.source sv in
          if not (StateVar.is_input sv) && source == None then
            N.add_state_var_def ~is_dep:true sv (N.GeneratedEq (pos, index));
        | None -> ());
      X.add index expr' accum
    in X.fold over_indices cexpr X.empty

  and compile_merge bounds clock_ident merge_cases =
    let merge_cases = List.map (fun (s, e) -> HString.string_of_hstring s, e) merge_cases in
    let clock_expr = compile_id_string bounds clock_ident |> X.values |> List.hd in
    let clock_type = E.type_of_lustre_expr clock_expr in
    let cond_expr_clock_value clock_value = match clock_value with
      | "true" -> clock_expr
      | "false" -> E.mk_not clock_expr
      | _ -> E.mk_eq clock_expr (E.mk_constr clock_value clock_type)
    in
    let compile_merge_case = function
      | A.When (_, expr, _) ->
        compile_ast_expr cstate ctx bounds map expr
      | expr -> compile_ast_expr cstate ctx bounds map expr
    in
    let merge_cases_r =
      let over_cases = fun acc (case_value, e) ->
        let e = compile_merge_case e in
        (cond_expr_clock_value case_value, e) :: acc
      in List.fold_left over_cases [] merge_cases
    in
    let default_case, other_cases_r = match merge_cases_r with
      | (_, d) :: l -> d, l
      | _ -> assert false
    in
    let over_other_cases = fun acc (cond, e) ->
      X.map2 (fun _ -> E.mk_ite cond) e acc
    in
    List.fold_left over_other_cases default_case other_cases_r

  and compile_projection bounds expr = function
    | X.RecordIndex _
    | X.TupleIndex _
    | X.ArrayIntIndex _ as index ->
      let expr = compile_ast_expr cstate ctx bounds map expr in
      X.find_prefix [index] expr
    | _ -> assert false
  
  and compile_group_expr bounds mk expr_list =
    let over_exprs = fun (i, accum) expr ->
      let compiled_expr = compile_ast_expr cstate ctx bounds map expr in
      let over_expr = fun j e a -> X.add (mk j i) e a in
      (succ i, X.fold over_expr compiled_expr accum)
    in
    List.fold_left over_exprs (0, X.empty) expr_list |> snd
  
  and compile_record_expr bounds expr_list =
    let expr_list = List.map (fun (s, e) -> HString.string_of_hstring s, e) expr_list in
    let over_exprs = fun accum (i, expr) ->
      let compiled_expr = compile_ast_expr cstate ctx bounds map expr in
      let over_expr = fun j e t -> X.add (X.RecordIndex i :: j) e t in
      X.fold over_expr compiled_expr accum
    in
    List.fold_left over_exprs X.empty expr_list

  and compile_struct_update expr1 index expr2 =
    let cexpr1 = compile_ast_expr cstate ctx bounds map expr1 in
    let cexpr2 = compile_ast_expr cstate ctx bounds map expr2 in
    let rec aux accum = function
      | [] -> List.rev accum
      | A.MapIndex _ :: _ -> assert false 
      | A.SetIndex _ :: _ -> assert false
      | A.Label (_, index) :: tl ->
        let index = HString.string_of_hstring index in
        let accum' = X.RecordIndex index :: accum in
        if X.mem_prefix (List.rev accum') cexpr1 then
          aux accum' tl
        else assert false (* guaranteed by type checker *)
      | A.Index (_, index_expr) :: tl ->
        let index_cexpr = compile_ast_expr cstate ctx bounds map index_expr in
        let index = (index_cexpr |> X.values |> List.hd).expr_init in
        let cexpr_sub = X.find_prefix accum cexpr1 in
        let index_term = (index : E.expr :> Term.t ) in
        let value = Term.numeral_of_term index_term |> Numeral.to_int in
        let i = if Term.is_numeral index_term then
            (match X.choose cexpr_sub with
              | X.ArrayVarIndex _ :: _, _
              | X.ArrayIntIndex _ :: _, _ -> X.ArrayIntIndex value
              | X.TupleIndex _ :: _,_ -> X.TupleIndex value
              | _ -> assert false (* guaranteed by type checker *))
          else (match X.choose cexpr_sub with
            | X.ArrayVarIndex _ :: _, _ -> X.ArrayVarIndex index
            | _ -> assert false (* guaranteed by type checker *) )
        in aux (i :: accum) tl
      | A.GenericIndex _ :: _ -> assert false (* converted to another index in the normalizer *)
    in
    let rec mk_cond_indexes (acc, cpt) li ri =
      match li, ri with
      | X.ArrayVarIndex b :: li', X.ArrayIntIndex vi :: ri' ->
        let rhs = (E.mk_int (Numeral.of_int vi)) in
        let acc = E.mk_eq (E.mk_array_index_var cpt (E.type_of_expr b)) rhs :: acc in
        mk_cond_indexes (acc, cpt+1) li' ri'
      | X.ArrayVarIndex b :: li', X.ArrayVarIndex vi :: ri' ->
        let rhs = (E.mk_of_expr vi) in
        let acc = E.mk_eq (E.mk_array_index_var cpt (E.type_of_expr b)) rhs :: acc in
        mk_cond_indexes (acc, cpt+1) li' ri'
      | _ :: li', _ :: ri' -> mk_cond_indexes (acc, cpt) li' ri'
      | [], _ | _, [] -> if acc = [] then raise Not_found;
        List.rev acc |> E.mk_and_n
    in
    let rec mk_store acc a ri x = match ri with
      | X.ArrayIntIndex vi :: ri' ->
        let i = E.mk_int (Numeral.of_int vi) in
        let a' = List.fold_left E.mk_select_and_push a acc in
        let x = mk_store [i] a' ri' x in
        E.mk_store a i x
      | X.ArrayVarIndex vi :: ri' ->
        let i = E.mk_of_expr vi in
        let a' = List.fold_left E.mk_select_and_push a acc in
        let x = mk_store [i] a' ri' x in
        E.mk_store a i x
      | _ :: ri' -> mk_store acc a ri' x
      | [] -> x
    in
    let cindex = aux X.empty_index index in
    let cexpr2' = X.fold (fun i v a -> X.add (cindex @ i) v a) cexpr2 X.empty in
    let over_indices = fun i v a ->
      try let v' = X.find i cexpr2' in X.add i v' a
      with Not_found -> try
        (match i with
          | X.ArrayIntIndex _ :: _ | X.ArrayVarIndex _ :: _ -> ()
          | _ -> raise Not_found);
        let old_v = List.fold_left (fun (acc, cpt) i ->
          let kt = match i with 
          | X.ArrayIntIndex _ -> Type.t_int 
          | X.ArrayVarIndex b -> E.type_of_expr b 
          | _ -> assert false 
          in
          E.mk_select_and_push acc (E.mk_array_index_var cpt kt), cpt + 1
        ) (v, 0) i |> fst
        in let new_v = X.find cindex cexpr2' in
        if Flags.Arrays.smt () then
          let v' = mk_store [] v cindex new_v in X.add [] v' a
        else
          let v' = E.mk_ite (mk_cond_indexes ([], 0) i cindex) new_v old_v in
          X.add [] v' a
        with Not_found -> X.add i v a
    in
    X.fold over_indices cexpr1 X.empty

  and compile_array_ctor bounds expr size_expr =
    let array_size' = compile_ast_expr cstate ctx bounds map size_expr in
    let array_size = (array_size' |> X.values |> List.hd).expr_init in
    let cexpr = compile_ast_expr cstate ctx bounds map expr in
(*     let size_is_numeral = Term.is_numeral (E.unsafe_term_of_expr array_size) in
    if size_is_numeral then
      let l_expr = array_size
        |> E.unsafe_term_of_expr
        |> Term.numeral_of_term
        |> Numeral.to_int
        |> (flip List.init) (fun _ -> expr)
      in let gexpr = A.GroupExpr (pos, A.ArrayExpr, l_expr) in
      let result = compile_ast_expr cstate ctx bounds map gexpr in
      result
    else *)
      let over_indices = fun j (e:LustreExpr.t) a -> 
        let e' = state_var_of_expr e |> E.mk_var
        in X.add (j @ [X.ArrayVarIndex array_size]) e' a
      in let result = X.fold over_indices cexpr X.empty in
      result

  and compile_map_index bounds expr k =
    let compiled_k = compile_ast_expr cstate ctx bounds map k in
    let index_exprs = X.values compiled_k in
    let compiled_expr = compile_ast_expr cstate ctx bounds map expr in
    List.fold_left
      (fun acc index ->
        compile_array_index' acc index
      )
      compiled_expr
      index_exprs

  and compile_array_index bounds expr i =
    let compiled_i = compile_ast_expr cstate ctx bounds map i in
    let index_e = compiled_i |> X.values |> List.hd in
    let as_type = index_e.expr_type in 
    let index = E.mk_of_expr ~as_type index_e.E.expr_init in
    let bounds =
      try
        let index_nb = E.int_of_index_var index in
        let _, bounds = Lib.list_extract_nth bounds index_nb in
        bounds
      with Invalid_argument _ | Failure _ -> bounds
    in
    let compiled_expr = compile_ast_expr cstate ctx bounds map expr in
    compile_array_index' compiled_expr index

  and compile_array_index' compiled_expr index =
    let rec push expr = match X.choose expr with
      | X.SetMapIndex _ :: _, v
      | X.ArrayVarIndex _ :: _, v
      | X.ArrayIntIndex _ :: _, v -> 
        let over_expr = fun k v acc -> 
          match (List.rev k) with 
          | X.SetMapIndex _ :: tl
          | X.ArrayVarIndex _ :: tl
          | X.ArrayIntIndex _ :: tl -> X.add (List.rev tl) v acc
          | _ -> assert false in
        let expr = X.fold over_expr expr X.empty in
        if E.type_of_lustre_expr v |> Type.is_array then
          X.map (fun e -> E.mk_select_and_push e index) expr
        else expr
(*       | X.ArrayIntIndex _ :: _, _ ->
        let over_expr = fun j v vals -> match j with
          | X.ArrayIntIndex i :: [] -> (i, v) :: vals
          | _ -> assert false
        in let vals = X.fold over_expr expr [] in
        (* TODO: Old code type checks length when it is statically known *)
        let last, vals = match vals with
          | (_, x) :: r -> x, r
          | _ -> assert false
        in let v =
          let over_vals = fun acc (i ,v) ->
            E.mk_ite (E.mk_eq index (E.mk_int (Numeral.of_int i))) v acc
          in List.fold_left over_vals last vals
        in X.add [] v X.empty *)
      | X.TupleIndex _ :: _, _
      | X.RecordIndex _ :: _, _
      | X.ListIndex _ :: _, _
      | X.AbstractTypeIndex _ :: _, _ ->
        let over_expr = fun indexes v acc -> match indexes with
          | top :: tl ->
            let r = X.add tl v X.empty in
            let e = push r in
            X.fold (fun j -> X.add (top :: j)) e acc
          | _ -> assert false
        in X.fold over_expr expr X.empty
      | [], e -> X.singleton X.empty_index (E.mk_select_and_push e index)
    in push compiled_expr

  in
  (* Format.eprintf "%a@." A.pp_print_expr expr; *)
  match expr with
  (* ****************************************************************** *)
  (* Identifiers                                                        *)
  (* ****************************************************************** *)
  | A.Ident (_, ident) -> compile_id_string bounds ident
  | A.ModeRef (_, path) -> compile_mode_reference path
  (* ****************************************************************** *)
  (* Constants                                                          *)
  (* ****************************************************************** *)
  | A.Const (_, A.True) -> X.singleton X.empty_index E.t_true
  | A.Const (_, A.False) -> X.singleton X.empty_index E.t_false
  | A.Const (_, A.Num d) ->
    let d = HString.string_of_hstring d in
    X.singleton X.empty_index (E.mk_int (Numeral.of_string d))
  | A.Const (_, A.Dec f) ->
    let f = HString.string_of_hstring f in
    X.singleton X.empty_index (E.mk_real (Decimal.of_string f))
  (* ****************************************************************** *)
  (* Unary Operators                                                    *)
  (* ****************************************************************** *)
  | A.ConvOp (_, A.ToInt, expr) -> compile_unary bounds E.mk_to_int expr 
  | A.ConvOp (_, A.ToUBV n, expr) -> compile_unary bounds (E.mk_to_ubv n) expr
  | A.ConvOp (_, A.ToBV n, expr) -> compile_unary bounds (E.mk_to_bv n) expr
  | A.ConvOp (_, A.ToReal, expr) -> compile_unary bounds E.mk_to_real expr
  | A.UnaryOp (_, A.Not, expr) -> compile_unary bounds E.mk_not expr 
  | A.UnaryOp (_, A.Uminus, expr) -> compile_unary bounds E.mk_uminus expr 
  | A.UnaryOp (_, A.BVNot, expr) -> compile_unary bounds E.mk_bvnot expr
  (* ****************************************************************** *)
  (* Binary Operators                                                   *)
  (* ****************************************************************** *)
  | A.BinaryOp (_, A.And, expr1, expr2) ->
    compile_binary bounds E.mk_and expr1 expr2
  | A.BinaryOp (_, A.AndThen, _, _) -> assert false
  | A.BinaryOp (_, A.Or, expr1, expr2) ->
    compile_binary bounds E.mk_or expr1 expr2 
  | A.BinaryOp (_, A.OrElse, _, _) -> assert false
  | A.BinaryOp (_, A.Xor, expr1, expr2) ->
    compile_binary bounds E.mk_xor expr1 expr2 
  | A.BinaryOp (_, A.Impl, expr1, expr2) ->
    compile_binary bounds E.mk_impl expr1 expr2
  | A.BinaryOp (_, A.LazyImpl, _, _) -> assert false
  | A.BinaryOp (_, A.In Set, k, map_expr) ->
    compile_map_index bounds map_expr k
  | A.BinaryOp (_, A.In Map, k, map_expr) ->
    let map_expr = compile_map_index bounds map_expr k in
    X.find_prefix [(X.TupleIndex 0)] map_expr
  | A.BinaryOp (_, A.In Unknown, _, _) -> assert false
  | A.BinaryOp (_, A.Mod, expr1, expr2) ->
    compile_binary bounds E.mk_mod expr1 expr2 
  | A.BinaryOp (_, A.Minus, expr1, expr2) ->
    compile_binary bounds E.mk_minus expr1 expr2
  | A.BinaryOp (_, A.Plus, expr1, expr2) ->
    compile_binary bounds E.mk_plus expr1 expr2
  | A.BinaryOp (_, A.Union, _, _) 
  | A.BinaryOp (_, A.Intersection, _, _)
  | A.BinaryOp (_, A.Difference, _, _) ->
    assert false (* abstracted during normalization *)
  | A.BinaryOp (_, A.Div, expr1, expr2) ->
    compile_binary bounds E.mk_div expr1 expr2 
  | A.BinaryOp (_, A.Times, expr1, expr2) ->
    compile_binary bounds E.mk_times expr1 expr2 
  | A.BinaryOp (_, A.IntDiv, expr1, expr2) ->
    compile_binary bounds E.mk_intdiv expr1 expr2 
  | A.BinaryOp (_, A.BVAnd, expr1, expr2) ->
    compile_binary bounds E.mk_bvand expr1 expr2
  | A.BinaryOp (_, A.BVOr, expr1, expr2) ->
    compile_binary bounds E.mk_bvor expr1 expr2
  | A.BinaryOp (_, A.BVShiftL, expr1, expr2) ->
    compile_binary bounds E.mk_bvshl expr1 expr2
  | A.BinaryOp (_, A.BVShiftR, expr1, expr2) ->
    compile_binary bounds E.mk_bvshr expr1 expr2
  | A.BinaryOp (_, A.BVConcat, expr1, expr2) -> 
    compile_binary bounds E.mk_bvconcat expr1 expr2
  | A.CompOp (_, A.Lte, expr1, expr2) ->
    compile_binary bounds E.mk_lte expr1 expr2 
  | A.CompOp (_, A.Lt, expr1, expr2) ->
    compile_binary bounds E.mk_lt expr1 expr2 
  | A.CompOp (_, A.Gte, expr1, expr2) ->
    compile_binary bounds E.mk_gte expr1 expr2 
  | A.CompOp (_, A.Gt, expr1, expr2) ->
    compile_binary bounds E.mk_gt expr1 expr2 
  | A.Arrow (_, expr1, expr2) ->
    let mk e1 e2 = let e1', e2' = coalesce_array2 e1 e2 in E.mk_arrow e1' e2' in
    compile_binary bounds mk expr1 expr2
  (* ****************************************************************** *)
  (* Quantifiers                                                        *)
  (* ****************************************************************** *)
  | A.Quantifier (_, A.Forall, avars, expr) ->
    compile_quantifier bounds E.mk_forall avars expr
  | A.Quantifier (_, A.Exists, avars, expr) ->
    compile_quantifier bounds E.mk_exists avars expr
  (* ****************************************************************** *)
  (* Other Operators                                                    *)
  (* ****************************************************************** *)
  | A.CompOp (_, A.Eq, expr1, expr2) ->
    compile_equality bounds true expr1 expr2
  | A.CompOp (_, A.Neq, expr1, expr2) ->
    compile_equality bounds false expr1 expr2
  | A.TernaryOp (_, A.Ite, expr1, expr2, expr3)
  | A.TernaryOp (_, A.LazyIte, expr1, expr2, expr3) ->
    compile_ite bounds expr1 expr2 expr3
  | A.Pre (_, expr) -> compile_pre bounds expr
  | A.Merge (_, clock_ident, merge_cases) ->
    compile_merge bounds clock_ident merge_cases
  | A.Extract (_, expr, ub, lb) -> 
    compile_bvextract bounds E.mk_bvextract expr ub lb
  | A.AnyOp _ -> assert false (* already desugared in lustreDesugarAnyChooseOps *)
  | A.ChooseOp _ -> assert false (* already desugared in lustreDesugarAnyChooseOps *)
  | A.TypeAscription _ -> assert false (* already desugared in lustreDesugarTypeAscriptions *)
  (* ****************************************************************** *)
  (* Tuple and Record Operators                                         *)
  (* ****************************************************************** *)
  | A.RecordProject (_, expr, field) ->
    let field = HString.string_of_hstring field in
    compile_projection bounds expr (X.RecordIndex field)
  | A.IndexAccess (_, expr, field, A.Tuple) ->
    let field = match field with 
    | A.Const (_, A.Num n) -> n |> HString.string_of_hstring |> int_of_string  
    | _ -> assert false in (* Tuple accesses are guaranteed concrete integers in type checking *)
    compile_projection bounds expr (X.TupleIndex field)
  | A.GroupExpr (_, A.ExprList, expr_list) ->
    let rec flatten_expr_list accum = function
      | [] -> List.rev accum
      | A.GroupExpr (_, A.ExprList, expr_list) :: tl -> 
        flatten_expr_list accum (expr_list @ tl)
      | expr :: tl -> flatten_expr_list (expr :: accum) tl
    in let expr_list = flatten_expr_list [] expr_list in
    compile_group_expr bounds (fun j i -> X.ListIndex i :: j) expr_list
  | A.GroupExpr (_, A.TupleExpr, expr_list) ->
    compile_group_expr bounds (fun j i -> X.TupleIndex i :: j) expr_list
  | A.RecordExpr (_, _, _, expr_list) ->
    compile_record_expr bounds expr_list
  | A.StructUpdate (_, _, _, None)  (* SetIndex case *)
  | A.StructUpdate (_, _, [A.MapIndex _], _) -> 
    assert false (* handled during normalization *)
  | A.StructUpdate (_, expr1, index, Some expr2) ->
    compile_struct_update expr1 index expr2
  (* ****************************************************************** *)
  (* Node Calls                                                         *)
  (* ****************************************************************** *)
  (* Node calls are abstracted to identifiers or group expressions by 
    the normalizer, making these expressions impossible at this stage *)
  | A.Condact _ -> assert false
  | A.Call _ -> assert false
  | A.RestartEvery _ -> assert false
  (* ****************************************************************** *)
  (* Array Operators                                                    *)
  (* ****************************************************************** *)
  | A.GroupExpr (_, A.ArrayExpr, expr_list) ->
    compile_group_expr bounds (fun j i -> j @[X.ArrayIntIndex i]) expr_list
  | A.ArrayConstr (_, expr, size_expr) ->
    compile_array_ctor bounds expr size_expr
  | A.IndexAccess (_, expr, i, Array) -> compile_array_index bounds expr i
  | A.IndexAccess (_, expr, k, Map) ->
    let expr = compile_map_index bounds expr k in
    X.find_prefix [(X.TupleIndex 1)] expr
  | A.IndexAccess (_, _, _, Unknown) -> assert false
  (* ****************************************************************** *)
  (* Not Implemented                                                    *)
  (* ****************************************************************** *)
  (* Abstracted away in normalization; handled in generated identifiers *)
  | A.EmptyMap _ -> assert false
  | A.EmptySet _ -> assert false
  (* LustreSyntaxChecks handles these expressions on the first pass,
    making these expressions impossible at this stage *)
  | A.When _ -> assert false
  | A.Activate _ -> assert false

and compile_node_call node_scope pos ctx cstate map outputs cond restart call_ctx node_id args defaults inlined =
  let ident = NI.get_internal_name node_id |> I.of_hstring in
  let called_node_oracles =
    try
      let called_node = N.node_of_node_id node_id cstate.nodes in
      called_node.oracles
    with Not_found ->
      (* This should only happen for recursive calls.
         Recursive functions do not have oracles *)
      []
  in
  let po_ct = !map.poracle_count in
  map := {!map with poracle_count = po_ct + (List.length called_node_oracles) };
  let oracles =
    called_node_oracles
    |> List.mapi (fun i sv ->
      let propagated_oracle =
        let sv' = mk_state_var
          ~is_const:true
          map
          (node_scope @ I.reserved_scope)
          (I.mk_string_ident (Format.sprintf "poracle_%d" (po_ct+i) ))
          X.empty_index (* Use dummy value here, replace it below *)
          (StateVar.type_of_state_var sv)
          (Some N.Oracle)
        in
        match sv' with
        | Some sv' -> (
          (* Use the bounds computed for the original oracle *)
          SVT.add !map.bounds sv' (SVT.find cstate.state_var_bounds sv);
          sv'
        )
        | None -> assert false
      in
      N.set_state_var_instance propagated_oracle pos ident sv;
      propagated_oracle
    )
  in
  let node_inputs_of_exprs inputs ast =
    let ast_group_expr = A.GroupExpr (dummy_pos, A.ExprList, ast) in
    let cexpr = compile_ast_expr cstate ctx [] map ast_group_expr in
    let cexpr = flatten_list_indexes cexpr in
    let over_indices i input_sv expr accum =
      let sv = state_var_of_expr expr in
      N.set_state_var_instance sv pos ident input_sv;
      let i' = match i with
        | (X.ListIndex _)::idx -> idx
        | idx -> idx
      in 
      if not (StateVar.is_input sv) then
        N.add_state_var_def ~is_dep:true sv (N.GeneratedEq (pos, i'));
      X.add i sv accum
    in
    let result = X.fold2 over_indices inputs cexpr X.empty in
    result
  in
  let node_act_cond_of_expr cond defaults =
    let cond_test = match cond with
      | A.Const (_, A.True) -> true
      | _ -> false
    in if cond_test then None, None
    else
      let state_var = cond |> extract_normalized |> H.find !map.state_var in
      let defaults' = match defaults with
        | Some [d] -> Some (compile_ast_expr cstate ctx [] map d)
        | Some d -> Some (compile_ast_expr cstate ctx [] map
          (A.GroupExpr (dummy_pos, A.ExprList, d)))
        | None -> None
      in Some state_var, defaults'
  in
  let restart_cond_of_expr restart =
    let restart_test = match restart with
      | A.Const (_, A.False) -> true
      | _ -> false
    in if restart_test then None
    else let state_var = restart |> extract_normalized |> H.find !map.state_var
    in Some state_var
  in
  let (called_node_inputs, _, _) = NI.Map.find node_id cstate.node_io in
  let input_state_vars = node_inputs_of_exprs called_node_inputs args in
  let act_state_var, defaults = node_act_cond_of_expr cond defaults in
  let restart_state_var = restart_cond_of_expr restart in
  let cond_state_var = match act_state_var, restart_state_var with
    | None, None -> []
    | Some c, None -> [N.CActivate c]
    | None, Some r -> [N.CRestart r]
    | Some c, Some r -> [N.CActivate c; N.CRestart r]
  in
  let call_ctx =
    match call_ctx with
    | Some id -> Some (mk_ident id |> H.find !map.state_var)
    | None -> None
  in
  let call_id = !map.call_count in
  map := {!map with call_count = call_id + 1 };
  let node_call = {
    N.call_id = call_id;
    N.call_pos = pos;
    N.call_node_id = node_id;
    N.call_cond = cond_state_var;
    N.call_context = call_ctx;
    N.call_inputs = input_state_vars;
    N.call_oracles = oracles;
    N.call_outputs = outputs;
    N.call_defaults = defaults;
    N.call_inlined = inlined;
  }
  in node_call

and compile_contract_variables cstate gids ctx map contract_scope node_scope contract =
  (* let contract_scope = List.map HString.string_of_hstring contract_scope in *)
  (* ****************************************************************** *)
  (* Split contracts into relevant categories                           *)
  (* ****************************************************************** *)
  let gconsts, gvars, modes, contract_calls =
    let over_items (consts, vars, modes, calls) = function
      | A.GhostConst c -> c :: consts, vars, modes, calls
      | A.GhostVars v -> consts, v :: vars, modes, calls 
      | A.Assume _ -> consts, vars, modes, calls
      | A.Guarantee _ -> consts, vars, modes, calls
      | A.Decreases _ -> consts, vars, modes, calls
      | A.Mode m -> consts, vars, m :: modes, calls
      | A.ContractCall c -> consts, vars, modes, c :: calls
      | A.AssumptionVars _ -> consts, vars, modes, calls
    in List.fold_left over_items ([], [], [], []) contract in
  (* ****************************************************************** *)
  (* Ghost Constants and Variables                                      *)
  (* ****************************************************************** *)
  let cstate =
    List.fold_left
      (fun cstate g ->
        compile_const_decl cstate ctx map true (node_scope @ ["contract"]) g
      )
      cstate
      gconsts
  in

  let ghost_locals, ghost_equations =
    let extract_namespace name =
      let name = HString.string_of_hstring name in
      let parts = String.split_on_char '_' name in
      match parts with
      | ref :: prefix :: tail ->
        let id = String.concat "_" tail in
        (id |> HString.mk_hstring |> mk_ident, [prefix; ref])
      | _ -> assert false
    in
    let over_vars (gvar_accum, eq_accum) = fun (pos, (A.GhostVarDec (_, tis)), expr) ->
        let extract_local ((_, id, ty)) = (
          let expr_ident = mk_ident id in
          let (ident, contract_namespace) = extract_namespace id in
          let index_types = compile_ast_type cstate ctx map ty in
          let over_indices = fun index index_type accum -> (
            let possible_state_var = (
              mk_state_var
                ~is_input:false
                ~expr_ident:expr_ident
                map
                (node_scope @ contract_namespace @ I.user_scope)
                ident
                index
                index_type
                (Some N.Ghost)
              )
            in
            match possible_state_var with
            | Some state_var -> X.add index state_var accum
            | None -> accum
          )
          in
          let indexed_state_var =
            X.fold over_indices index_types X.empty
          in
          H.replace !map.usr_state_var ident indexed_state_var ;
          indexed_state_var
        ) in
        
        (* Patch up eq_rhs and ghost_local *)
        let struct_items = List.map (fun (pos, id, _) -> A.SingleIdent(pos, id)) tis in
        let eq_lhs = A.StructDef (pos, struct_items) in
        let eq_rhs = expr in
        (List.map extract_local tis) @ gvar_accum, (pos, eq_lhs, eq_rhs) :: eq_accum
    in List.fold_left over_vars ([], []) gvars
  (* ****************************************************************** *)
  (* Contract Modes                                                     *)
  (* ****************************************************************** *)
  in let modes =
    let over_modes (pos, id, reqs, enss) =
      let id' = HString.string_of_hstring id in
      let reqs = List.mapi
        (fun i (p, n, e) -> 
          compile_contract_item gids map (i + 1) contract_scope N.Require p n e)
        reqs in
      let enss = List.mapi
        (fun i (p, n, e) -> 
          compile_contract_item gids map (i + 1) contract_scope N.Ensure p n e)
        enss in
      let contract_scope =
        List.map (fun (_, i) -> HString.string_of_hstring i) contract_scope
      in
      let path = contract_scope @ [id'] in
      let mode = C.mk_mode (mk_ident id) pos path reqs enss false in
      map := { !map with modes = mode :: !map.modes };
      mode
    in List.map over_modes modes
  (* ****************************************************************** *)
  (* Contract Calls                                                     *)
  (* ****************************************************************** *)
  in let (cstate, ghost_locals2, ghost_equations2, modes2) =
    let over_calls (cstate, gls, ges, ms) (_, node_id, _, _, _) =
      let cref = NI.get_name node_id in
      let (_, sc, _) = StringMap.find cref gids.GI.contract_calls in
      let cname = sc |> List.rev |> List.hd |> snd in
      (* Update cstate with uninstantiated params *)
      let params = match Ctx.lookup_contract_ty_vars ctx cname with 
      | None -> [] 
      | Some params -> params 
      in
      let cstate = List.fold_left (fun acc param -> 
        let empty_map = ref (empty_identifier_maps None) in
        let t = compile_ast_type cstate ctx empty_map (A.AbstractType (Lib.dummy_pos, param)) in
        let type_alias = StringMap.add param t acc.type_alias in
        { acc with type_alias } 
      ) cstate params in
      (* Instantiate polymorphic types in imported contract *)
      let (_, contract_scope, contract_eqns) =
        (GI.StringMap.find cref gids.GI.contract_calls)
      in
      let contract_scope = List.map (fun (pos, node_id) -> 
        pos, NI.get_internal_name node_id
      ) contract_scope in
      map := { !map with contract_scope };
      let (cstate, gl, ge, m) = compile_contract_variables cstate gids ctx map contract_scope node_scope contract_eqns
      in cstate, gl @ gls, ge @ ges, m @ ms
    in List.fold_left over_calls (cstate, [], [], []) contract_calls
  in cstate, ghost_locals @ ghost_locals2, ghost_equations @ ghost_equations2, modes @ modes2

and compile_contract cstate gids ctx map contract_scope node_scope contract =
  (* ****************************************************************** *)
  (* Split contracts into relevant categories                           *)
  (* ****************************************************************** *)
  let assumes, guarantees, contract_calls =
    let over_items (assumes, guarantees, calls) = function
      | A.GhostConst _ -> assumes, guarantees, calls
      | A.GhostVars _ -> assumes, guarantees, calls
      | A.Assume a -> a :: assumes, guarantees, calls
      | A.Guarantee g -> assumes, g :: guarantees, calls
      | A.Mode _ -> assumes, guarantees, calls
      | A.ContractCall c -> assumes, guarantees, c :: calls
      | A.AssumptionVars _ -> assumes, guarantees, calls
      | A.Decreases _ -> assumes, guarantees, calls
    in List.fold_left over_items ([], [], []) contract
  (* ****************************************************************** *)
  (* Contract Calls                                                     *)
  (* ****************************************************************** *)
  in let (assumes2, guarantees2) =
    let over_calls (ams, gs) (_, node_id, _, _, _) =
      let id = NI.get_internal_name node_id in
      let (_, scope, contract_eqns) =
        GI.StringMap.find id gids.GI.contract_calls
      in
      let scope = List.map (fun (pos, name) -> 
        pos, NI.get_internal_name name
      ) scope in
      map := { !map with contract_scope=scope };
      let (a, g) = compile_contract cstate gids ctx map scope node_scope contract_eqns
      in a @ ams, g @ gs
    in List.fold_left over_calls ([], []) contract_calls
  (* ****************************************************************** *)
  (* Contract Assumptions and Guarantees                                *)
  (* ****************************************************************** *)
  in
  let assumes =
    let over_assumes (pos, name, soft, expr) =
      let i = !map.assume_count in
      map := {!map with assume_count = i + 1 };
      let kind = if soft then N.WeakAssumption else N.Assumption in
      compile_contract_item gids map (i + 1) contract_scope kind pos name expr
    in List.map over_assumes assumes
  in
  let guarantees = 
    let over_guarantees (pos, name, soft, expr) =
      let i = !map.guarantee_count in
      map := {!map with guarantee_count = i + 1 };
      let kind = if soft then N.WeakGuarantee else N.Guarantee in
      compile_contract_item gids map (i + 1) contract_scope kind pos name expr
    in List.map over_guarantees guarantees
      |> List.map (fun g -> g, false)
  in assumes @ assumes2,
    guarantees @ guarantees2

and add_uninstantiated_cstate ctx cstate params =
  List.fold_left (fun acc param -> 
    let empty_map = ref (empty_identifier_maps None) in
    let t = compile_ast_type cstate ctx empty_map (A.AbstractType (Lib.dummy_pos, param)) in
    let type_alias = StringMap.add param t acc.type_alias in
    { acc with type_alias } 
  ) cstate params 

and process_node_inputs cstate ctx map node_scope inputs =
  (* TODO: The documentation on lustreNode says that a single argument
  node should have a non-list index (a singleton index), but the old
  node generation code does not seem to honor that *)
  let over_inputs = fun compiled_input (_pos, i, ast_type, clock, is_const) ->
    let indexed_state_var = X.empty in
    match clock with
    | A.ClockTrue ->
      let n = X.top_max_index compiled_input |> succ in
      let ident = mk_ident i in
      let index_types = compile_ast_type cstate ctx map ast_type in
      let over_indices = fun index index_type (accum1, accum2) ->
        let possible_state_var = mk_state_var
          ~is_input:true
          ~is_const
          map
          (node_scope @ I.user_scope)
          ident
          index
          index_type
          (Some N.Input)
        in
        match possible_state_var with
        | Some state_var ->
          X.add (X.ListIndex n :: index) state_var accum1,
          X.add index state_var accum2
        | None -> accum1, accum2
      in
      let compiled_input, indexed_state_var =
        X.fold over_indices index_types (compiled_input, indexed_state_var)
      in
      H.replace !map.usr_state_var ident indexed_state_var ;
      compiled_input
    | _ -> assert false (* Guaranteed by LustreSyntaxChecks *)
  in List.fold_left over_inputs X.empty inputs


and process_node_outputs cstate ctx map node_scope outputs =
  (* TODO: The documentation on lustreNode does not state anything about
  the requirements for indices of outputs, yet the old code makes it
  a singleton index in the event there is only one index *)
  let over_outputs = fun (is_single) compiled_output (_, i, ast_type, clock) ->
    let indexed_state_var = X.empty in
    match clock with
    | A.ClockTrue ->
      let n = X.top_max_index compiled_output |> succ in
      let ident = mk_ident i in
      let index_types = compile_ast_type cstate ctx map ast_type in
      let over_indices = fun index index_type (accum1, accum2) ->
        let possible_state_var = mk_state_var
          ~is_input:false
          map
          (node_scope @ I.user_scope)
          ident
          index
          index_type
          (Some N.Output)
        in
        let index' = if is_single then index
          else X.ListIndex n :: index
        in 
        match possible_state_var with
        | Some state_var ->
          X.add index' state_var accum1,
          X.add index state_var accum2
        | None -> accum1, accum2
      in
      let compiled_output, indexed_state_var =
        X.fold over_indices index_types (compiled_output, indexed_state_var)
      in
      H.replace !map.usr_state_var ident indexed_state_var ;
      compiled_output
    | _ -> assert false (* Guaranteed by LustreSyntaxChecks *)
  and is_single = List.length outputs = 1
  in List.fold_left (over_outputs is_single) X.empty outputs

and compile_node_io cstate ctx node_id params inputs outputs =
  let internal_node_name_hstring = NI.get_internal_name node_id in 
  let internal_node_name = mk_ident internal_node_name_hstring in
  let node_scope = internal_node_name |> I.to_scope in
  let map = ref (empty_identifier_maps (Some internal_node_name_hstring)) in
  let cstate = add_uninstantiated_cstate ctx cstate params in
  let inputs = process_node_inputs cstate ctx map node_scope inputs in
  let outputs = process_node_outputs cstate ctx map node_scope outputs in
  { cstate with
    node_io = NI.Map.add node_id (inputs, outputs, !map) cstate.node_io }

and compile_node_decl scc_map gids_map is_function is_rec opac cstate ctx node_id ext params locals items contract =
  let gids = NI.Map.find node_id gids_map in
  let internal_node_name_hstring = NI.get_internal_name node_id in 
  let internal_node_name = mk_ident internal_node_name_hstring in
  let node_scope = internal_node_name |> I.to_scope in
  let is_extern = ext in
  let opacity =
    match opac with
    | A.Opaque -> Opacity.Opaque
    | A.Transparent -> Opacity.Transparent
    | A.Default -> Opacity.Translucent
  in
  let instance =
    StateVar.mk_state_var
      ~is_const:true
      (I.instance_ident |> I.string_of_ident false)
      (I.to_scope internal_node_name @ I.reserved_scope)
      Type.t_int
  in
  let init_flag = 
    StateVar.mk_state_var
      (I.init_flag_ident |> I.string_of_ident false)
      (I.to_scope internal_node_name @ I.reserved_scope)
      Type.t_bool
  in
  let state_var_expr_map = SVT.create 7 in
  (* Update cstate with uninstantiated params *)
  let cstate = add_uninstantiated_cstate ctx cstate params in
  (* ****************************************************************** *)
  (* Node Inputs and Outputs                                            *)
  (* ****************************************************************** *)
  let inputs, outputs, init_map =
    NI.Map.find node_id cstate.node_io
  in
  let map = ref init_map in
  (* ****************************************************************** *)
  (* Type of component                                                  *)
  (* ****************************************************************** *)
  let comp_type =
    if is_function then
      let rec_info =
        if is_rec then
          match StringMap.find_opt internal_node_name_hstring scc_map with
          | Some scc_id -> (
            let decreases_expr = 
              match get_decreases_expr contract with
              | Some expr -> (
                let nexpr = compile_ast_expr cstate ctx [] map expr in
                match X.bindings nexpr with
                | [_, expr] -> E.init_expr expr
                | _ -> assert false
              )
              | None -> assert false
            in
            Some (scc_id, decreases_expr)
          )
          | None -> None
        else
          None
      in
      N.Function { 
        uf_symbols = create_uf_symbols node_id inputs outputs;
        rec_info
      }
    else
      N.Node
  in
  (* ****************************************************************** *)
  (* User Locals                                                        *)
  (* ****************************************************************** *)
  let locals, cstate =
    let over_locals = fun (locals, cstate) local ->
      match local with
      | A.NodeVarDecl (_, (_, i, ast_type, A.ClockTrue)) ->
        let ident = mk_ident i
        and index_types = compile_ast_type cstate ctx map ast_type in
        let over_indices = fun index index_type accum ->
          let possible_state_var = mk_state_var
            ~is_input:false
            map
            (node_scope @ "impl" :: I.user_scope)
            ident
            index
            index_type
            (Some N.Local)
          in
          match possible_state_var with
          | Some state_var -> X.add index state_var accum
          | None -> accum
        in
        let indexed_state_var =
          X.fold over_indices index_types X.empty
        in
        H.replace !map.usr_state_var ident indexed_state_var ;
        indexed_state_var :: locals, cstate
      | A.NodeConstDecl (_, decl) ->
        locals, compile_const_decl cstate ctx map true (node_scope @ ["impl"]) decl
      | A.NodeVarDecl _ -> assert false (* guaranteed by LustreSyntaxChecks *)
    in
    List.fold_left over_locals ([], cstate) locals
  (* ****************************************************************** *)
  (* Generated Free Constants                                           *)
  (* ****************************************************************** *)
  in let cstate =
    List.fold_left
      (fun cstate (id, ty) ->
        let g = A.FreeConst (dummy_pos, id, ty) in
        compile_const_decl ~is_generated:true cstate ctx map true (node_scope @ ["res"]) g
      )
      cstate
      gids.GI.free_constants
  (* ****************************************************************** *)
  (* (State Variables for) Generated Locals                             *)
  (* ****************************************************************** *)
  in let glocals =
    let locals_list = GI.StringMap.bindings gids.GI.locals in
    let over_generated_locals glocals (id, expr_type) =
      let ident = mk_ident id in
      let index_types = compile_ast_type cstate ctx map expr_type in
      let over_indices = fun index index_type accum ->
        let possible_state_var = mk_state_var
          map
          (node_scope @ I.reserved_scope)
          ident
          index 
          (* (if Type.is_array index_type then index else X.empty_index) *)
          index_type
          (Some N.Generated)
        in
        match possible_state_var with
        | Some state_var -> X.add index state_var accum
        | None -> accum
      in
      let result = X.fold over_indices index_types X.empty in
      H.replace !map.res_state_var ident result ;
      if GI.StringSet.mem id gids.GI.array_literal_vars then (
        (* Store expanded type index *)
        let index_types' = compile_ast_type ~expand:true cstate ctx map expr_type in
        X.iter
          (fun index _ ->
            update_array_literal_index map (node_scope @ I.reserved_scope)
            ident
            index
          )
          index_types'
      ) ;
      result :: glocals
    in List.fold_left over_generated_locals [] locals_list
  (* ****************************************************************** *)
  (* (State Variables for) Generated Refinement Type Constraints        *)
  (* ****************************************************************** *)
  in let glocals =
    let over_generated_locals glocals (_, _, id, _, _) =
      let ident = mk_ident id in
      let index_types = compile_ast_type cstate ctx map (A.Bool dummy_pos) in
      let over_indices = fun index index_type accum ->
        let possible_state_var = mk_state_var
          map
          (node_scope @ I.reserved_scope)
          ident
          index
          index_type
          (Some N.Generated)
        in
        match possible_state_var with
        | Some state_var -> X.add index state_var accum
        | None -> accum
      in let result = X.fold over_indices index_types X.empty in
      result :: glocals
    in List.fold_left over_generated_locals glocals gids.GI.refinement_type_constraints
  (* ****************************************************************** *)
  (* (State Variables for) Generated Locals for Node Arguments          *)
  (* ****************************************************************** *)
  in let glocals =
    let over_generated_locals glocals (id, is_const, expr_type, _) =
      let ident = mk_ident id in
      let index_types = compile_ast_type cstate ctx map expr_type in
      let over_indices = fun index index_type accum ->
        let possible_state_var = mk_state_var
          ~is_const
          map
          (node_scope @ I.reserved_scope)
          ident
          index
          index_type
          (Some N.Generated)
        in
        match possible_state_var with
        | Some state_var -> X.add index state_var accum
        | None -> accum
      in let result = X.fold over_indices index_types X.empty in
      result :: glocals
    in List.fold_left over_generated_locals glocals gids.GI.node_args
  (* ****************************************************************** *)
  (* (State Variables for) Node Calls, to put in the map for oracles    *)
  (* ****************************************************************** *)
  in
  let () =
    let over_calls = fun () ((_, var, _, _, _, node_id, _, _, _)) ->
      let (_, called_node_outputs, _) =
        NI.Map.find node_id cstate.node_io
      in
      let _outputs =
        let over_vars = fun index sv compiled_vars ->
          let var_id = mk_ident var in
          let possible_state_var = mk_state_var
            ~is_input:false
            map
            (node_scope @ I.reserved_scope)
            var_id
            index
            (StateVar.type_of_state_var sv)
            (Some N.Call)
          in
          match possible_state_var with
          | Some state_var -> X.add index state_var compiled_vars
          | None -> compiled_vars
        in
        X.fold over_vars called_node_outputs X.empty
      in
      ()
    in
    List.fold_left over_calls () gids.calls
  in 
  (* ****************************************************************** *)
  (* Contract State Variables                                           *)
  (* ****************************************************************** *)
  let (cstate, ghost_locals, ghost_equations, modes) =
    match contract with
    | Some (_, contract) -> 
      compile_contract_variables cstate gids ctx map [] node_scope contract
    | None -> cstate, [], [], []
  (* ****************************************************************** *)
  (* Oracles                                                            *)
  (* ****************************************************************** *)
  in
  let (oracles, oracle_state_var_map) =
    let over_oracles (oracles, osvm) (id, expr_type, expr) =
      let oracle_ident = mk_ident id in
      let closed_sv = match expr with
        | A.Ident (_, id')
        | A.IndexAccess (_, A.Ident (_, id'), _, _) ->
          let ident = mk_ident id' in
          let closed_sv = H.find !map.state_var ident in
          Some closed_sv
        | A.Const (_, _) -> None
        | _ -> assert false
      in
      let index_types = compile_ast_type cstate ctx map expr_type in
      let over_indices = fun index index_type accum ->
        let possible_state_var = mk_state_var
          ~is_const:true
          map
          (node_scope @ I.reserved_scope)
          oracle_ident
          index
          index_type
          (Some N.Oracle)
        in
        match possible_state_var with
        | Some(state_var) ->
          (match closed_sv with
          | Some sv -> SVT.add osvm state_var sv
          | None -> ());
          X.add index state_var accum
        | None -> accum
      in
      let result = X.fold over_indices index_types X.empty in
      (X.values result) @ oracles, osvm
    in
    List.fold_left over_oracles ([], SVT.create 7) gids.GI.oracles in
  let ib_oracles =
    let over_ib_oracles  ib_oracles (id, expr_type) = (
      let oracle_ident = mk_ident id in
      let index_types = compile_ast_type cstate ctx map expr_type in
      let over_indices = ( fun index index_type accum ->
        let possible_state_var = mk_state_var
          ~is_const:false
          map
          (node_scope @ I.reserved_scope)
          oracle_ident
          index
          index_type
          (Some N.Oracle)
        in
        match possible_state_var with
          | Some state_var -> X.add index state_var accum
          | None -> accum
      ) in 
      (X.fold over_indices index_types X.empty) :: ib_oracles
    ) in
    List.fold_left over_ib_oracles [] gids.GI.ib_oracles
  (* ****************************************************************** *)
  (* Node Calls                                                         *)
  (* ****************************************************************** *)
  in
  let (calls, glocals) =
    let seen_calls = ref SVS.empty in
    let over_calls =
      fun (calls, glocals) (pos, var, cond, restart, call_ctx, node_id, args, defaults, inlined)
    ->
      (* let internal_node_name_hstring = NI.get_internal_name node_id |> HString.mk_hstring in *)
      let internal_node_name = NI.get_internal_name node_id |> I.of_hstring in
      let (_, called_node_outputs, _) =
        NI.Map.find node_id cstate.node_io
      in
(*       let output_ast_types = (match Ctx.lookup_node_ty ctx ident with
        | Some (A.TArr (_, _, output_types)) ->
            (match output_types with
            | A.GroupType (_, types) -> types
            | t -> [t])
        | _ -> assert false)
      in *)
      let local_map = H.create 7 in
      let outputs =
        let over_vars = fun index sv compiled_vars ->
          let var_id = mk_ident var in
          let possible_state_var = mk_state_var
            ~force_return:true
            ~is_input:false
            map
            (node_scope @ I.reserved_scope)
            var_id
            index
            (StateVar.type_of_state_var sv)
            (Some N.Call)
          in
          match possible_state_var with
          | Some state_var ->
            let result = if SVS.mem state_var !seen_calls then
              compiled_vars
            else (
              H.add local_map var_id state_var;
              N.add_state_var_def state_var (N.CallOutput (pos, index));
              N.set_state_var_instance state_var pos internal_node_name sv;
              X.add index state_var compiled_vars)
            in
            seen_calls := SVS.add state_var !seen_calls;
            result
          | None -> compiled_vars
        in
        X.fold over_vars called_node_outputs X.empty
      in
      let node_call = compile_node_call
        node_scope pos ctx cstate map outputs cond restart call_ctx node_id args defaults inlined
      in
      let glocals' = H.fold (fun _ v a -> (X.singleton X.empty_index v) :: a) local_map [] in 
      node_call :: calls, glocals' @ glocals
    in
    List.fold_left over_calls ([], glocals) gids.calls
  (* ****************************************************************** *)
  (* Add Propagated Oracles                                             *)
  (* ****************************************************************** *)
  in let oracles =
    List.fold_left
      (fun acc { N.call_oracles } -> call_oracles @ acc)
      oracles
      calls
  (* ****************************************************************** *)
  (* Split node items into relevant categories                          *)
  (* ****************************************************************** *)
  in let (node_props, node_eqs, node_asserts, is_main) = 
    let over_items = fun (props, eqs, asserts, is_main) (item) ->
      match item with
      | A.Body e -> (match e with
        | A.Assert (p, e) -> (props, eqs, (p, e) :: asserts, is_main)
        | A.Equation (p, l, e) -> (props, (p, l, e) :: eqs, asserts, is_main))
      | A.AnnotMain (_, flag) -> (props, eqs, asserts, flag || is_main)
      | A.AnnotProperty (p, n, e, k) -> ((p, n, e, k) :: props, eqs, asserts, is_main) 
      | A.IfBlock _ 
      | A.WhenBlock _
      | A.FrameBlock _ -> 
        (* IfBlock and FrameBlock desugaring already occurred earlier in pipeline
           (in lustreRemoveMultAssign.ml, lustreDesugarIfBlocks.ml, and 
           lustreDesugarFrameBlocks.ml), so there are no If/FrameBlocks left. *)
        (props, eqs, asserts, is_main) 
    in List.fold_left over_items ([], [], [], false) items
  (* ****************************************************************** *)
  (* Properties and Assertions                                          *)
  (* ****************************************************************** *)
  in let props =
    let op (pos, name_opt, expr, kind) =
      let id_str = match expr with
        | A.Ident (_, id_str) -> id_str
        | A.IndexAccess (_, A.Ident (_, id_str), _, _) -> id_str
        | _ -> assert false (* must be abstracted *)
      in let id = mk_ident id_str in
      let sv = H.find !map.state_var id in
      let src_expr =
        let key = HString.mk_hstring (LustreAst.string_of_expr expr) in
        try GI.StringMap.find key gids.GI.expr_source_map with Not_found -> expr
      in
      let name, src =
        match name_opt with
        | None -> assert false (* Prop named in LustreAstNormalizer *)
        | Some n ->
          HString.string_of_hstring n,
          if GI.StringSet.mem n gids.GI.nonvacuity_props then
            Property.NonVacuityCheck (pos, node_scope)
          else
            Property.PropAnnot pos
      in
      let kind = match kind with
        | A.Invariant -> Property.Invariant
        | A.Reachable Some (FromWithin (ts1, ts2)) -> Property.Reachable (Some (FromWithin (ts1, ts2)))
        | A.Reachable Some (At ts) -> Property.Reachable (Some (At ts))
        | A.Reachable Some (From ts) -> Property.Reachable (Some (From ts))
        | A.Reachable Some (Within ts) -> Property.Reachable (Some (Within ts))
        | A.Reachable None -> Property.Reachable None
        | A.Provided _ -> assert false (* Should be desugared into one invariant and one reachable property *)
      in
      sv, name, src, kind, src_expr
    in List.map op node_props

  in let asserts =
    let op (pos, expr) =
      let id = extract_normalized expr in
      let sv = H.find !map.state_var id in
      N.add_state_var_def sv (N.Assertion pos);
      (pos, sv)
    in List.map op node_asserts
  in
  (* ****************************************************************** *)
  (* Helpers for generated and user equations                           *)
  (* ****************************************************************** *)
  let compile_map_or_set_def i idx is_set = 
    let ident = mk_ident i in
    let expr = H.find !map.expr ident in
    let result = X.map state_var_of_expr expr in
    (* TODO: Old code checks that array lengths between l and result match *)
    (* TODO: Old code checks that result must have at least one element *)
    (* TODO: Old code suggests that shadowing can occur here *)

    let num_is = List.fold_left (fun acc i -> 
    (* In the list of indices `i`, multiple SetMapIndexes are ambiguous: 
       they can represent either multiple components of a single structured key, or 
       separate keys of nested maps.
       But, if it is structured key with N elements, we will always get at least N SetMapIndexes in a row 
       before encountering the TupleIndex representing the membership/value arrays. 
       So, we can compute the number of SetMapIndexes associated with the outer map's key type 
       by finding the minimal number of SetMapIndexes before the first TupleIndex. 

       Note that this only suffices to find the number of SetMapIndexes for the key type of the outermost map; 
       hence, this function (compile_map_or_set_def) currently can handle only a single input 
       index variable `idx` (as opposed to a list of indices, which is supported by compile_array_def) *)
      let _, count = List.fold_left (fun (acc_b, acc_c) i -> 
        if acc_b then match i with 
        | X.SetMapIndex _ -> acc_b, acc_c + 1 
        | _ -> false, acc_c
        else acc_b, acc_c
      ) (true, 0) i in 
      if count < acc then count else acc
    ) max_int (X.keys expr |> List.map List.rev) in 

    let ident = mk_ident idx in
    (* Add index types to kt trie *)
    let kt = X.fold (fun k _ acc -> 
        List.fold_left (fun (acc, acc_is, acc_i, num_is) idx -> 
      match idx with 
      | X.SetMapIndex b -> 
        if is_set && num_is > 0 then 
          X.add acc_is (E.type_of_expr b) acc, acc_is, acc_i + 1, num_is - 1 
        else if num_is > 0 then  
          X.add (acc_is @ [X.TupleIndex acc_i]) (E.type_of_expr b) acc, acc_is, acc_i + 1, num_is - 1 
        else 
          acc, acc_is, acc_i, num_is 
      | _ -> acc, acc_is, acc_i, num_is  
      ) (acc, [], 0, num_is) (List.rev k) |> (fun (x, _, _, _) -> x) 
    ) expr X.empty in

    let over_indices j t (i, a) = 
      let expr = E.mk_array_index_var i t in
      i + 1, X.add j expr a 
    in
    let _, index = X.fold over_indices kt (0, X.empty) in
    H.add !map.array_index ident index;
  result

  in let compile_array_def i l =
    let ident = mk_ident i in
    let expr = H.find !map.expr ident in
    let result = X.map state_var_of_expr expr in
    (* TODO: Old code checks that array lengths between l and result match *)
    (* TODO: Old code checks that result must have at least one element *)
    (* TODO: Old code suggets that shadowing can occur here *)
    let indexes = List.length l in

    List.iteri (fun i v -> 
      let ident = mk_ident v in
      let indices = X.bindings expr |> List.hd |> fst |> List.rev  in
      let index = List.nth indices i in 
      let ty = match index with 
      | ArrayVarIndex b -> E.type_of_expr b 
      | _ -> assert false 
      in
      let expr = E.mk_array_index_var i ty in
      let index = X.singleton X.empty_index expr in
      H.add !map.array_index ident index
    ) l;

    result, indexes

  in let compile_struct_item struct_item = match struct_item with
    | A.SingleIdent (_, i) ->
      let ident = mk_ident i in
      let expr = H.find !map.expr ident in
      let result = X.map state_var_of_expr expr in
      result, 0
    | A.ArrayDef (_, i, l) -> 
      compile_array_def i l 
    | A.TupleStructItem _
    | A.TupleSelection _
    | A.FieldSelection _
    | A.ArraySliceStructItem _ ->
      assert false (* guaranteed by LustreSyntaxChecks *)

  in let rm_array_var_index lst =
      List.filter (function
      | X.ArrayVarIndex _ -> false
      | _ -> true
      ) lst

  in let gen_lhs_bounds pos is_generated eq_lhs indexes =
    List.fold_left (fun acc (i, sv) ->
      let result = List.fold_left (fun (acc, cpt) -> function
        | X.ArrayVarIndex b -> if cpt < indexes
          then E.Bound b :: acc, succ cpt
          else acc, cpt
        | X.SetMapIndex b -> if cpt < indexes 
          then E.Unbound (Some b) :: acc, succ cpt
          else acc, cpt
        | X.ArrayIntIndex x -> 
          let expr = (E.mk_int (Numeral.of_int x)).expr_init in
          E.Fixed expr :: acc, succ cpt
        | _ -> acc, cpt)
        (acc, 0) i |> fst
      in
      if not is_generated then
        N.add_state_var_def sv ~is_dep:false
          (N.ProperEq (pos, rm_array_var_index i));
      result
    ) [] (X.bindings eq_lhs)
  (* ****************************************************************** *)
  (* Generated Equations                                                *)
  (* ****************************************************************** *)
  in let gequations =
    let over_equations = fun eqns (qvars, contract_scope, lhs, ast_expr, _) ->
      let contract_scope = List.map (fun (pos, name) -> 
        pos, NI.get_internal_name name
      ) contract_scope in 
      map := { !map with contract_scope };
      let eq_lhs, indexes = match lhs with
        | A.StructDef (_, []) -> X.empty, 0
        | A.StructDef (_, [A.SingleIdent (_, i)]) when (GI.StringSet.mem i gids.GI.array_literal_vars) -> (
          (* Use expanded version of the equation *)
          let ident = mk_ident i in
          let idx = H.find !map.array_literal_index ident in
          let result = X.map (fun e -> state_var_of_expr e) idx in
          result, 0
        )
        | A.StructDef (_, [e]) -> (compile_struct_item e)
        | A.StructDef (_, l) ->
          let construct_index i j e a = X.add (X.ListIndex i :: j) e a in
          let over_items = fun (i, accum) e -> 
            let t, _ = compile_struct_item e in
              i + 1, X.fold (construct_index i) t accum
          in
          let _, res = List.fold_left over_items (0, X.empty) l
          in res, 0
      in
      let lhs_bounds = gen_lhs_bounds (AH.pos_of_expr ast_expr) true eq_lhs indexes in
      let vars, quant_var_map = vars_of_quant cstate ctx map qvars in
      let bounds = lhs_bounds @
        List.map (fun v -> E.Unbound (Some (E.unsafe_expr_of_term (Term.mk_var v))))
          vars in
      H.add_seq !map.quant_vars (H.to_seq quant_var_map);
      let eq_rhs = compile_ast_expr cstate ctx bounds map ast_expr in
      let eq_lhs = flatten_list_indexes eq_lhs in
      let eq_rhs = flatten_list_indexes eq_rhs in
      (* Format.eprintf "lhs: %a\n\n rhs: %a\n\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
      
      let equations = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in 
      List.iter (fun ((sv, _), e) -> SVT.add state_var_expr_map sv e) equations;
      H.clear !map.array_index;
      H.clear !map.quant_vars;
      equations @ eqns
    in List.fold_left over_equations [] gids.GI.equations in
  (* ****************************************************************** *)
  (* Maps                                                               *)
  (* ****************************************************************** *)
  let empty_map_eqs = 
    let over_empty_maps acc (id, _, _) =
      let eq_lhs, _ = compile_struct_item (A.SingleIdent (Lib.dummy_pos, id)) in 
      let eq_lhs = flatten_list_indexes eq_lhs in
      (* extract index for boolean flag denoting presence or absence of map item *)
      let eq_lhs = X.fold (fun k sv acc -> match k with 
      | X.TupleIndex 0 :: _ -> X.add k sv acc 
      | _ -> acc 
      ) eq_lhs X.empty 
      in
      (* Set boolean flag to false *)
      let eq_rhs = X.fold (fun k _ acc -> 
        X.add k E.t_false acc
      ) eq_lhs X.empty in
      (*Format.fprintf Format.std_formatter "lhs: %a@.rhs: %a@.@.\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs;*)
      let empty_map_eqs = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in
      empty_map_eqs @ acc
    in 
    List.fold_left over_empty_maps [] gids.GI.empty_maps 
  in 
  let gequations = gequations @ empty_map_eqs in
  let map_element_update_eqs = 
    let over_map_element_updates acc (id, nexpr1, nexpr2, nexpr3, fresh_idx_name, _, _) =
      let fresh_idx = A.Ident (dummy_pos, fresh_idx_name) in 
      let eq_lhs = compile_map_or_set_def id fresh_idx_name false in 
      let lhs_bounds = gen_lhs_bounds (AH.pos_of_expr nexpr1) true eq_lhs 1 in 
      let nexpr2 = compile_ast_expr cstate ctx lhs_bounds map nexpr2 in 
      let fresh_idx_e = compile_ast_expr cstate ctx lhs_bounds map fresh_idx in 
      let nexpr2 = 
        let nexpr2 = X.values nexpr2 in 
        List.fold_left (fun (acc, acc_i) e -> 
          X.add [X.TupleIndex acc_i] e acc, acc_i + 1
        ) (X.empty, 0) nexpr2 |> fst 
      in
      let expr = compile_binary' E.mk_eq nexpr2 fresh_idx_e in
      let cond_expr = 
        X.singleton X.empty_index (List.fold_left E.mk_and E.t_true (X.values expr)) 
      in
      let then_expr = A.GroupExpr (dummy_pos, TupleExpr, [Const (dummy_pos, True); nexpr3]) in 
      let else_expr = 
        A.GroupExpr (dummy_pos, TupleExpr, [A.BinaryOp (dummy_pos, In Map, fresh_idx, nexpr1); 
                                            A.IndexAccess (dummy_pos, nexpr1, fresh_idx, Map)]) 
      in 
      let then_expr = compile_ast_expr cstate ctx lhs_bounds map then_expr in 
      let else_expr = compile_ast_expr cstate ctx lhs_bounds map else_expr in 
      let cond_expr = match X.bindings cond_expr with
      | [_, expr] -> expr
      | _ -> assert false
      in
      let mk e1 e2 =
        let e1', e2' = coalesce_array2 e1 e2 in
        E.mk_ite cond_expr e1' e2'
      in
      let eq_rhs = compile_binary' mk then_expr else_expr in 
      (* Format.fprintf Format.std_formatter "lhs: %a@.rhs: %a@.@.\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
      let map_element_update_eqs = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in
      map_element_update_eqs @ acc
    in 
    List.fold_left over_map_element_updates [] gids.GI.map_element_updates
  in
  let gequations = gequations @ map_element_update_eqs in
  let map_subtraction_eqs =
    let over_map_subtractions acc (id, nexpr1, nexpr2, fresh_idx_name, _, _) =
      (* Desugar to lhs[i] = (i in nexpr1 and not (i in nexpr2), nexpr1[i]),
         i.e. a key is kept iff it is in the map and not in the subtracted set *)
      let fresh_idx = A.Ident (dummy_pos, fresh_idx_name) in
      let eq_lhs = compile_map_or_set_def id fresh_idx_name false in
      let lhs_bounds = gen_lhs_bounds (AH.pos_of_expr nexpr1) true eq_lhs 1 in
      let present_expr =
        A.BinaryOp (dummy_pos, A.And,
          A.BinaryOp (dummy_pos, In Map, fresh_idx, nexpr1),
          A.UnaryOp (dummy_pos, A.Not,
            A.BinaryOp (dummy_pos, In Set, fresh_idx, nexpr2)))
      in
      let value_expr = A.IndexAccess (dummy_pos, nexpr1, fresh_idx, Map) in
      let expr = A.GroupExpr (dummy_pos, TupleExpr, [present_expr; value_expr]) in
      let eq_rhs = compile_ast_expr cstate ctx lhs_bounds map expr in
      (* Format.fprintf Format.std_formatter "lhs: %a@.rhs: %a@.@.\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
      let map_subtraction_eqs = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in
      map_subtraction_eqs @ acc
    in
    List.fold_left over_map_subtractions [] gids.GI.map_subtractions
  in
  let gequations = gequations @ map_subtraction_eqs in
  (* ****************************************************************** *)
  (* Sets                                                               *)
  (* ****************************************************************** *)
  let empty_set_eqs = 
    let over_empty_sets acc (id, _) =
      let eq_lhs, _ = compile_struct_item (A.SingleIdent (Lib.dummy_pos, id)) in 
      let eq_lhs = flatten_list_indexes eq_lhs in
      (* Set boolean flag to false *)
      let eq_rhs = X.fold (fun k _ acc -> 
        X.add k E.t_false acc
      ) eq_lhs X.empty in
      (*Format.fprintf Format.std_formatter "lhs: %a@.rhs: %a@.@.\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs;*)
      let empty_set_eqs = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in
      empty_set_eqs @ acc
    in 
    List.fold_left over_empty_sets [] gids.GI.empty_sets 
  in 
  let gequations = gequations @ empty_set_eqs in
  let set_insertions_eqs = 
    let over_set_insertions acc (id, nexpr1, nexpr2, fresh_idx_name, _) =
      (* Desugar to lhs[i] = if i = nexpr2 then true else i in nexpr1 *)
      let fresh_idx = A.Ident (dummy_pos, fresh_idx_name) in 
      let eq_lhs = compile_map_or_set_def id fresh_idx_name false in 
      let lhs_bounds = gen_lhs_bounds (AH.pos_of_expr nexpr1) true eq_lhs 1 in
      let nexpr2 = compile_ast_expr cstate ctx lhs_bounds map nexpr2 in 
      let fresh_idx_e = compile_ast_expr cstate ctx lhs_bounds map fresh_idx in 
      (* Flatten nexpr2 to make the indices align (the compilation of map types in 
         compile_ast_type flattens indices, so we need to do a corresponding flattening 
         of nexpr2 to compile the equality between nexpr2 and fresh_idx_e) *)
      let nexpr2 =
        let nexpr2 = X.values nexpr2 in 
        List.fold_left (fun (acc, acc_i) e -> 
          X.add [X.TupleIndex acc_i]  e acc, acc_i + 1
        ) (X.empty, 0) nexpr2 |> fst 
      in
      let expr = compile_binary' E.mk_eq nexpr2 fresh_idx_e in
      let cond_expr = 
        X.singleton X.empty_index (List.fold_left E.mk_and E.t_true (X.values expr)) 
      in
      let then_expr = A.Const (dummy_pos, True) in 
      let else_expr = A.BinaryOp (dummy_pos, In Set, fresh_idx, nexpr1) in 
      let then_expr = compile_ast_expr cstate ctx lhs_bounds map then_expr in 
      let else_expr = compile_ast_expr cstate ctx lhs_bounds map else_expr in 
      let cond_expr = match X.bindings cond_expr with
      | [_, expr] -> expr
      | _ -> assert false
      in
      let mk e1 e2 =
        let e1', e2' = coalesce_array2 e1 e2 in
        E.mk_ite cond_expr e1' e2'
      in
      let eq_rhs = compile_binary' mk then_expr else_expr in 
      (* Format.fprintf Format.std_formatter "lhs: %a@.rhs: %a@.@.\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
      let set_insertions_eqs = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in
      set_insertions_eqs @ acc
    in 
    List.fold_left over_set_insertions [] gids.GI.set_insertions
  in
  let gequations = gequations @ set_insertions_eqs in
  let set_binop_eqs = 
    let over_set_binops acc (id, nexpr1, nexpr2, fresh_idx_name, op, _) =
      (* Desugar to lhs[i] = i in nexpr1 <op> i in nexpr2 *)
      let fresh_idx = A.Ident (dummy_pos, fresh_idx_name) in 
      let eq_lhs = compile_map_or_set_def id fresh_idx_name false in 
      let lhs_bounds = gen_lhs_bounds (AH.pos_of_expr nexpr1) true eq_lhs 1 in
      let in_l = A.BinaryOp (dummy_pos, In Set, fresh_idx, nexpr1) in
      let in_r = A.BinaryOp (dummy_pos, In Set, fresh_idx, nexpr2) in
      let expr = 
        match op with
        | A.Union -> A.BinaryOp (dummy_pos, A.Or, in_l, in_r)
        | A.Intersection -> A.BinaryOp (dummy_pos, And, in_l, in_r)
        | A.Difference -> A.BinaryOp (dummy_pos, And, in_l, A.UnaryOp (dummy_pos, A.Not, in_r))
        | _ -> assert false
      in
      let eq_rhs = compile_ast_expr cstate ctx lhs_bounds map expr in
      (* Format.fprintf Format.std_formatter "lhs: %a@.rhs: %a@.@.\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
      let set_binop_eqs = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in
      set_binop_eqs @ acc
    in 
    List.fold_left over_set_binops [] gids.GI.set_binops
  in
  let gequations = gequations @ set_binop_eqs in
  (* ****************************************************************** *)
  (* Node Equations                                                     *)
  (* ****************************************************************** *)
(*   Format.eprintf "map:\n\n%a\n\n" pp_print_identifier_maps !map; *)
  let equations =
    let over_equations = fun eqns (pos, lhs, ast_expr) ->
      match lhs with
      | A.StructDef (_, []) -> eqns
      | _ -> (
        let (eq_lhs, indexes), is_generated = match lhs with
          | A.StructDef (_, []) -> assert false (* (X.empty, 0) *)
          | A.StructDef (_, [e]) as lhs1 -> 
            (* Detect if equation is result of desugaring a frame block *)
            let is_generated = match NI.Hashtbl.find_opt LDF.pos_list_map node_id with
              | None -> false
              | Some frame_infos -> (
                match List.find_opt (fun (_, lhs) -> match lhs with | LDF.FCond lhs2 -> lhs1 = lhs2 | _ -> false) 
                                    frame_infos with
                  | None -> false
                  | Some _ -> true
              ) in
            compile_struct_item e, is_generated
          | A.StructDef (_, l) ->
            let construct_index =
              fun i j e a -> X.add (X.ListIndex i :: j) e a
            in
            let over_items = fun (i, accum) e ->
              let t, _ = compile_struct_item e in
                i + 1, X.fold (construct_index i) t accum
            in
            let _, res = List.fold_left over_items (0, X.empty) l
            in (res, 0), false
        in
        let lhs_bounds = gen_lhs_bounds (AH.pos_of_expr ast_expr) is_generated eq_lhs indexes in
        let eq_rhs = compile_ast_expr cstate ctx lhs_bounds map ast_expr in
        let eq_lhs = flatten_list_indexes eq_lhs in
        let eq_rhs = flatten_list_indexes eq_rhs in
        (*Format.eprintf "lhs: %a@.rhs: %a@.@."
          (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
          (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
        let equations = expand_tuple pos eq_lhs eq_rhs in
        (*
         Format.eprintf "\nequations: %a\n"
          (pp_print_list
            (pp_print_pair
              (pp_print_pair
                StateVar.pp_print_state_var
                (pp_print_list
                  E.pp_print_bound_or_fixed
                  " / ")
                " : ")
              (E.pp_print_lustre_expr true)
              " : ")
            " ; ")
          
          equations; *)
        H.clear !map.array_index;
        equations @ eqns
      )
    in 
    List.fold_left over_equations [] (ghost_equations @ node_eqs)
  (* ****************************************************************** *)
  (* Contract Assumptions and Guarantees                                *)
  (* ****************************************************************** *)
  in let (assumes, guarantees) =
    match contract with
    | Some (_, contract) -> compile_contract cstate gids ctx map [] node_scope contract
    | None -> [], []
  (* ****************************************************************** *)
  (* Collect Variables for Assumption Generation                        *)
  (* ****************************************************************** *)
  in let assumption_svars =
    match contract with
    | Some (_, contract) -> (
      contract |> List.fold_left (fun acc decl ->
        match decl with
        | A.AssumptionVars (_, vars) ->
          vars |> List.fold_left (fun acc' (_, id) ->
            let sv = H.find !map.state_var (mk_ident id) in
            SVS.add sv acc'
          )
          acc
        | _ -> acc
      ) 
      SVS.empty
    )
    | None -> SVS.empty
  (* ****************************************************************** *)
  (* Generate Contract Constraints for Refinement Type Constraints      *)
  (* ****************************************************************** *)
  in 
  (* Helper for refinement type expression substitution *)
  let find_type_ascription_expr nid = 
    NI.Map.fold (fun _ gds acc ->
      match acc with
      | Some _ -> acc
      | None -> NI.Map.find_opt nid gds.GI.type_ascription_exprs
      ) gids_map None
  in
  (* Several type constraints may be generated from a single source position
     (e.g. one per field of a record type). Since constraint names are derived
     from the position, this returns a function that disambiguates colliding
     names by appending a numeric suffix (_1, _2, ...), leaving unique names
     untouched. *)
  let make_uniquifier base_names =
    let counts = Hashtbl.create 7 in
    List.iter (fun n ->
      Hashtbl.replace counts n
        (1 + (try Hashtbl.find counts n with Not_found -> 0))
    ) base_names;
    let indices = Hashtbl.create 7 in
    fun name ->
      if (try Hashtbl.find counts name with Not_found -> 0) > 1 then (
        let idx = 1 + (try Hashtbl.find indices name with Not_found -> 0) in
        Hashtbl.replace indices name idx;
        Format.asprintf "%s_%d" name idx
      ) else name
  in let (assumes, guarantees, props) =
    let create_constraint_name_pos (pos : position)=
      Format.asprintf "@[<h>SubType%a@]" pp_print_line_and_column pos
    in
    let uniq_name =
      make_uniquifier
        (List.map (fun (_, pos, _, _, _) -> create_constraint_name_pos pos)
          gids.GI.refinement_type_constraints)
    in
    let create_constraint_name_pos pos =
      uniq_name (create_constraint_name_pos pos)
    in
    let over_ref_type_constraints (a, ac, g, gc, p) (source, pos, id, rexpr, node_id_opt) =
      let sv = H.find !map.state_var (mk_ident id) in
      let constraint_kind, generated_source = match source with
      | GI.Input -> Some N.Assumption, None
      | Local -> None, Some Property.Body
      | Output -> Some N.Guarantee, None
      | Ghost -> if is_extern then None, Some Property.Contract else Some N.Guarantee, None
    in
    let name = create_constraint_name_pos pos in
    let replace_expr = match node_id_opt with
    | Some nid -> find_type_ascription_expr nid
    | None -> None
    in

    let rexpr = match replace_expr with
      | Some expr -> LustreAstHelpers.substitute_naive (HString.mk_hstring ".inp") expr rexpr
      | None -> rexpr
      in
      let srexpr = A.string_of_expr rexpr in
      match constraint_kind, generated_source with
        | Some N.Assumption, _ ->
          let contract_sv = C.mk_svar pos ac (Some name) sv [] srexpr in
          N.add_state_var_def sv (N.ContractItem (pos, contract_sv, N.Assumption));
          (contract_sv :: a, ac + 1, g, gc, p)
        | Some N.Guarantee, _ ->
          let contract_sv = C.mk_svar pos gc (Some name) sv [] srexpr in
          N.add_state_var_def sv (N.ContractItem (pos, contract_sv, N.Guarantee));
          (a, ac, (contract_sv, false) :: g, gc + 1, p)
        | None, Some gen_src ->
          let src = Property.Generated (Some pos, [sv], gen_src) in
          (a, ac, g, gc, (sv, name, src, Property.Invariant, rexpr) :: p)
        | _ -> assert false
    in
    let (assumes, _, guarantees, _, props) = 
      List.fold_left over_ref_type_constraints
      (assumes, List.length assumes, guarantees, List.length guarantees, props)
      gids.GI.refinement_type_constraints
    in
    (assumes, guarantees, props)
  (* ****************************************************************** *)
  (* Finalize Contracts and add Sofar assumption                        *)
  (* ****************************************************************** *)
  in let (contract, sofar_local, sofar_equation) =
    if assumes != [] || guarantees != [] || modes != [] then
      let assumes = List.sort
          (fun a b -> compare_pos (C.pos_of_svar a) (C.pos_of_svar b))
          assumes
        in
        let guarantees = List.sort
          (fun (a, _) (b, _) -> compare_pos (C.pos_of_svar a) (C.pos_of_svar b))
          guarantees
        in
        let modes = List.sort
          (fun {C.pos = a} {C.pos = b} -> compare_pos a b)
          modes
      in
      if is_function then
        let contract = C.mk assumes None guarantees modes in
        Some (contract), [], []
      else
        let sofar_assumption = get (mk_state_var
          ~is_input:false
          map
          (node_scope @ I.reserved_scope)
          (mk_ident (HString.mk_hstring "sofar"))
          X.empty_index
          Type.t_bool
          None)
        in
        let sofar_local = X.singleton X.empty_index sofar_assumption in
        let conj_of_assumes = assumes
          |> List.map (fun { C.svar } -> E.mk_var svar)
          |> E.mk_and_n
        in
        let pre_sofar = E.mk_pre (E.mk_var sofar_assumption) in
        let expr = E.mk_arrow conj_of_assumes (E.mk_and conj_of_assumes pre_sofar) in
        let equation = (sofar_assumption, []), expr in
        let contract = C.mk assumes (Some sofar_assumption) guarantees modes in
        Some (contract), [sofar_local], [equation]
    else None, [], []
  in
  (* ****************************************************************** *)
  (* Add state var definitions for frame and if blocks                  *)
  (* ****************************************************************** *)
  (* Add state var definitions for frame blocks *)
  (
    match NI.Hashtbl.find_opt LDF.pos_list_map node_id with
      | Some frame_infos ->
        (* Get state variables for frame block variables *)
          List.iter (fun (pos, def) -> 
            (match def with
              (* Adding state vars for frame block equations *)
              | LDF.Eq A.StructDef (_, [e]) -> 
                let lhs, _ = compile_struct_item e in
                List.iter (fun (i, sv) -> N.add_state_var_def sv (N.ProperEq (pos, rm_array_var_index i))) (X.bindings lhs);
              (* Adding state vars for frame block headers *)
              | FCond A.StructDef (_, [e]) ->
                let lhs, _ = compile_struct_item e in
                List.iter (fun (_, sv) -> N.add_state_var_def sv (N.FrameBlock pos)) (X.bindings lhs);
              | _ -> assert false) 
        ) frame_infos;  
      | None -> ()
  );

  (* Add state var definitions for if blocks *)
  (
    match NI.Hashtbl.find_opt LDI.pos_list_map node_id with
      | Some if_infos ->
        (* Add state var defs for if block equations *)
        List.iter (fun (pos, lhs) -> 
            let lhs, _ = (match lhs with
              | A.StructDef (_, [e]) -> compile_struct_item e
              | _ -> assert false) 
            in
            List.iter (fun (i, sv) -> N.add_state_var_def sv (N.ProperEq (pos, rm_array_var_index i))) (X.bindings lhs);
        ) if_infos;  
      | None -> ()
  );
  (* ****************************************************************** *)
  (* Finalize and build intermediate LustreNode                         *)
  (* ****************************************************************** *)    
  let locals = sofar_local @ ghost_locals @ glocals @ locals in
  let equations = sofar_equation @ equations @ gequations in
  let asserts = List.sort (fun (p1, _) (p2, _) -> compare_pos p1 p2) asserts in
  let state_var_source_map = SVT.fold
    (fun k v a -> SVM.add k v a)
    !map.source SVM.empty in
  let var_bounds = SVT.fold (fun k v a -> (k, v) :: a) !map.bounds [] in
  List.iter (fun (k, v) -> SVT.add cstate.state_var_bounds k v) var_bounds;

  let history_svars =
    List.fold_left
      (fun acc (id, h_id) ->
        let id = mk_ident id in
        let h_id = mk_ident h_id in
        let svars = H.find !map.usr_state_var id in
        let h_svars = H.find !map.res_state_var h_id in
        List.fold_left2
          (fun acc (_, sv) (_, h_sv) ->
            let ty = StateVar.type_of_state_var sv in
            match TM.find_opt ty acc with
            | None -> TM.add ty [(sv, h_sv)] acc
            | Some l -> TM.add ty ((sv, h_sv) :: l) acc
          )
          acc
          (X.bindings svars)
          (X.bindings h_svars)
      )
      TM.empty
      (StringMap.bindings gids.GI.history_vars)
  in

  let (node:N.t) = { node_id;
    is_extern;
    opacity;
    instance;
    init_flag;
    inputs;
    oracles;
    outputs;
    locals = ib_oracles @ locals;
    equations;
    calls;
    asserts;
    props;
    contract;
    is_main;
    comp_type;
    state_var_source_map;
    oracle_state_var_map;
    state_var_expr_map;
    assumption_svars;
    history_svars;
  } in { cstate with
    nodes = node :: cstate.nodes;
  }


and compile_const_decl ?(is_generated=false) cstate ctx map is_local scope = function
  | A.FreeConst (p, i, ty) -> (
    let ident = mk_ident i in
    let cty = compile_ast_type cstate ctx map ty in
    let over_index = fun i ty vt ->
      let possible_state_var = mk_state_var
        ?is_input:(Some false)
        ?is_const:(Some true)
        ?for_inv_gen:(Some true)
        map
        (scope @ I.user_scope)
        ident
        i
        ty
        None
      in
      match possible_state_var with
      | Some state_var ->
        X.add i (Var.mk_const_state_var state_var) vt
      | None -> vt
    in
    let vt = X.fold over_index cty X.empty in
    let var_bounds = SVT.fold (fun k v a -> (k, v) :: a) !map.bounds [] in
    List.iter (fun (k, v) -> SVT.add cstate.state_var_bounds k v) var_bounds;
    let global_constraints =
      let ty = Ctx.expand_type_syn ctx ty in
      let has_ref_type = Ctx.type_contains_ref ctx ty in
      if has_ref_type then (
        let ctx = Ctx.add_ty ctx i ty in
        let ref_type_exprs =
          if has_ref_type then
            AN.mk_ref_type_expr ctx None (A.Ident(p, i)) ty
          else []
        in
        List.map (fun expr ->
          let c_expr = compile_ast_expr cstate ctx [] map expr in
          X.max_binding c_expr |> snd
        ) ref_type_exprs @ cstate.global_constraints
      )
      else cstate.global_constraints
    in
    { cstate with
      free_constants = (!map.node_name, i, vt, is_generated) :: cstate.free_constants;
      global_constraints
    }
  )
  (* TODO: Old code does some subtyping checks for Typed constants
    Otherwise these other constants are used only for constant propagation *)
  | A.UntypedConst (_, id, expr)
  | A.TypedConst (_, id, expr, _) ->
    if is_local then ( 
      { cstate with
        local_constants = StringMap.add id expr cstate.local_constants })
    else 
      { cstate with
        other_constants = StringMap.add id expr cstate.other_constants }

and compile_type_decl pos ctx cstate = function
  | A.AliasType (_, ident, ps, ltype) ->
    let cstate = List.fold_left (fun acc p -> 
      compile_type_decl pos ctx acc (A.FreeType (Lib.dummy_pos, p))
    ) cstate ps in
    let empty_map = ref (empty_identifier_maps None) in
    let t = compile_ast_type cstate ctx empty_map ltype in
    let type_alias = StringMap.add ident t cstate.type_alias in
    { cstate with
      type_alias }
  | A.FreeType (_, ident) ->
    let empty_map = ref (empty_identifier_maps None) in
    let t = compile_ast_type cstate ctx empty_map (A.AbstractType (pos, ident)) in
    let type_alias = StringMap.add ident t cstate.type_alias in
    { cstate with
      type_alias }

and compile_declaration_phase1:
  compiler_state -> Ctx.tc_context -> A.declaration -> compiler_state
= fun cstate ctx decl ->
(*   Format.eprintf "decl: %a\n\n" A.pp_print_declaration decl; *)
  match decl with
  | A.TypeDecl ({A.start_pos = pos}, type_rhs) ->
    compile_type_decl pos ctx cstate type_rhs
  | A.ConstDecl (_, const_decl) ->
    let empty_map = ref (empty_identifier_maps None) in
    compile_const_decl cstate ctx empty_map false [] const_decl 
  | A.FuncDecl (_, (i, _, _, params, inputs, outputs, _, _, _), _) ->
    compile_node_io cstate ctx i params inputs outputs
  | A.NodeDecl (_, (i, _, _, params, inputs, outputs, _, _, _)) ->
    compile_node_io cstate ctx i params inputs outputs
  (* All contract node declarations are recorded and normalized in gids,
    this is necessary because each unique call to a contract node must be 
    normalized independently *)
  | A.ContractNodeDecl _ -> cstate
  | A.NodeParamInst _ -> assert false

and get_decreases_expr contract = 
  match contract with
  | Some (_, contract) -> (
    let over_decrease_clause = fun acc decl ->
      match decl with
      | A.Decreases (_, expr) -> Some expr
      | _ -> acc
    in
    List.fold_left over_decrease_clause None contract
  )
  | None -> None
  
and compile_declaration_phase2:
  compiler_state -> GI.t NI.Map.t -> Ctx.tc_context -> int StringMap.t -> A.declaration -> compiler_state
= fun cstate gids ctx scc_map decl ->
  (*   Format.eprintf "decl: %a\n\n" A.pp_print_declaration decl; *)
  match decl with
  | A.TypeDecl _ -> cstate
  | A.ConstDecl _ -> cstate
  | A.FuncDecl (_, (i, ext, opac, params, _, _, locals, items, contract), { is_rec }) -> (
    let cstate = compile_node_decl scc_map gids true is_rec opac cstate ctx i ext params locals items contract in
    { cstate with local_constants = StringMap.empty }
  )
  | A.NodeDecl (_, (i, ext, opac, params, _, _, locals, items, contract)) ->
    let cstate = compile_node_decl scc_map gids false false opac cstate ctx i ext params locals items contract in
    { cstate with local_constants = StringMap.empty }
  (* All contract node declarations are recorded and normalized in gids,
  this is necessary because each unique call to a contract node must be 
  normalized independently *)
  | A.ContractNodeDecl _ -> cstate
  | A.NodeParamInst _ -> assert false
