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
module LAN = LustreAstNormalizer
module G = LustreGlobals
module N = LustreNode
module C = LustreContract
module I = LustreIdent
module X = LustreIndex
module H = LustreIdent.Hashtbl
module E = LustreExpr

module SVM = StateVar.StateVarMap
module SVT = StateVar.StateVarHashtbl
module SVS = StateVar.StateVarSet

module Ctx = TypeCheckerContext

module StringMap = struct
  include Map.Make(struct
    type t = HString.t
    let compare i1 i2 = HString.compare i1 i2
  end)
end

type compiler_state = {
  nodes : LustreNode.t list;
  type_alias : Type.t LustreIndex.t StringMap.t;
  free_constants : Var.t LustreIndex.t StringMap.t;
  other_constants : LustreAst.expr StringMap.t;
  state_var_bounds : (LustreExpr.expr LustreExpr.bound_or_fixed list)
    StateVar.StateVarHashtbl.t;
}

type identifier_maps = {
  state_var : StateVar.t LustreIdent.Hashtbl.t;
  expr : LustreExpr.t LustreIndex.t LustreIdent.Hashtbl.t;
  source : LustreNode.state_var_source StateVar.StateVarHashtbl.t;
  bounds : (LustreExpr.expr LustreExpr.bound_or_fixed list)
    StateVar.StateVarHashtbl.t;
  array_index : LustreExpr.t LustreIndex.t LustreIdent.Hashtbl.t;
  quant_vars : LustreExpr.t LustreIndex.t LustreIdent.Hashtbl.t;
  modes : LustreContract.mode list;
  contract_scope : (Lib.position * HString.t) list;
  assume_count : int;
  guarantee_count : int;
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

let empty_identifier_maps () = {
  state_var = H.create 7;
  expr = H.create 7;
  source = SVT.create 7;
  bounds = SVT.create 7;
  array_index = H.create 7;
  quant_vars = H.create 7;
  modes = [];
  contract_scope = [];
  assume_count = 0;
  guarantee_count = 0;
}

let empty_compiler_state () = { 
  nodes = [];
  type_alias = StringMap.empty;
  free_constants = StringMap.empty;
  other_constants = StringMap.empty;
  state_var_bounds = SVT.create 7;
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
  List.fold_left (fun e i -> E.mk_select e (E.mk_index_var i)) e indexes

(* Try to make the types of two expressions line up.
 * If one expression is an array but the other is not, then insert a 'select'
 * around the array expression so that the two expressions both have similar types.
 * This is used by mk_arrow for array expressions. *)
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
  (List.filter (function 
      | X.ArrayVarIndex _ 
      | X.ArrayIntIndex _ -> false
      | X.RecordIndex _
      | X.TupleIndex _
      | X.ListIndex _
      | X.AbstractTypeIndex _ -> true)
    index)

let bounds_of_index index =
  List.fold_left (fun acc -> function
      | X.ArrayVarIndex b -> E.Bound b :: acc
      | X.ArrayIntIndex i ->
        E.Fixed (E.mk_int_expr (Numeral.of_int i)) :: acc
      | _ -> acc
    ) [] index

(* Create a state variable for from an indexed state variable in a
  scope *)
let mk_state_var
    ?is_input
    ?is_const
    ?for_inv_gen
    ?expr_ident
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
    if index = X.empty_index then
      X.singleton index expr
    else try
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
  if fresh then Some(state_var) else None

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
  | A.ArrayIndex (_, A.Ident (_, ident), _) -> mk_ident ident
  | _ -> assert false

let flatten_list_indexes (e:E.t X.t) =
  let over_indices k (indices, e) =
    let rec flatten = function
      | (X.ListIndex _) :: (ListIndex _) :: t -> flatten ((X.ListIndex k) :: t)
      | h :: t -> h :: t
      | [] -> []
    in
    (flatten indices, e)
  in
  let flattened = List.mapi over_indices (X.bindings e) in
  List.fold_left (fun acc (idx, e) -> X.add idx e acc) X.empty flattened

(* Match bindings from a trie of state variables and bindings for a
  trie of expressions and produce a list of equations *)
let rec expand_tuple' pos accum bounds lhs rhs = 
(*   Format.eprintf "lhs: %a\n"
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
      " ; ") rhs; *)
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
    let over_index_types (e, i) _ = E.mk_select e (E.mk_index_var i), succ i in
    let expr, _ = List.fold_left over_index_types (expr, 0) array_index_types in
    expand_tuple' pos accum (E.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      ((rhs_index_tl, expr) :: rhs_tl)
  (* Tuple index on left-hand and right-hand side *)
  | ((X.TupleIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.TupleIndex j :: rhs_index_tl, expr) :: rhs_tl) 
  | ((X.ListIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ListIndex j :: rhs_index_tl, expr) :: rhs_tl) ->
    (* Indexes are sorted, must match *)
    if i = j then 
      expand_tuple' pos accum bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl)
    else (
      internal_error pos "Type mismatch in equation: indexes do not match";
      assert false)
  | ((X.ArrayIntIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ArrayIntIndex j :: rhs_index_tl, expr) :: rhs_tl) -> 
    (* Indexes are sorted, must match *)
    if i = j then 
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

  | (X.TupleIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.TupleIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.TupleIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.TupleIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _

  | (X.ListIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.ArrayIntIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.ListIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _

  | (X.ArrayIntIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _
  | (X.ArrayIntIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _

  | (X.ArrayVarIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.ArrayVarIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.ArrayVarIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.ArrayVarIndex _ :: _, _) :: _, (X.AbstractTypeIndex _ :: _, _) :: _

  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.RecordIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.TupleIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.ListIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.ArrayIntIndex _ :: _, _) :: _
  | (X.AbstractTypeIndex _ :: _, _) :: _, (X.ArrayVarIndex _ :: _, _) :: _

  | (_ :: _, _) :: _, ([], _) :: _ 
  | ([], _) :: _, (_ :: _, _) :: _ ->
    (internal_error pos "Type mismatch in equation: head indexes do not match";
      assert false)

(* Return a list of equations from a trie of state variables and a
  trie of expressions *)
let expand_tuple pos lhs rhs = 
  (* Format.eprintf "expand_tuple: \n"; *)
  expand_tuple' pos [] []
    (List.map (fun (i, e) -> (i, e)) (X.bindings lhs))
    (List.map (fun (i, e) -> (i, e)) (X.bindings rhs))

let rec compile ctx gids decls =
  let over_decls cstate decl = compile_declaration cstate gids ctx decl in
  let output = List.fold_left over_decls (empty_compiler_state ()) decls in
  let free_constants = output.free_constants
    |> StringMap.bindings
    |> List.map (fun (id, v) -> mk_ident id, v)
  in output.nodes,
    { G.free_constants = free_constants;
      G.state_var_bounds = output.state_var_bounds}

and compile_ast_type
  ?(expand = false)
  (cstate:compiler_state)
  (ctx:Ctx.tc_context)
  map
  = function
  | A.TVar _ -> assert false
  | A.Bool _ -> X.singleton X.empty_index Type.t_bool
  | A.Int _ -> X.singleton X.empty_index Type.t_int
  | A.UInt8 _ -> X.singleton X.empty_index (Type.t_ubv 8)
  | A.UInt16 _ -> X.singleton X.empty_index (Type.t_ubv 16)
  | A.UInt32 _ -> X.singleton X.empty_index (Type.t_ubv 32)
  | A.UInt64 _ -> X.singleton X.empty_index (Type.t_ubv 64)
  | A.Int8 _ -> X.singleton X.empty_index (Type.t_bv 8)
  | A.Int16 _ -> X.singleton X.empty_index (Type.t_bv 16)
  | A.Int32 _ -> X.singleton X.empty_index (Type.t_bv 32)
  | A.Int64 _ -> X.singleton X.empty_index (Type.t_bv 64)
  | A.Real _ -> X.singleton X.empty_index Type.t_real
  | A.IntRange (_, lbound, ubound) -> 
    (* TODO: Old code does subtyping here, currently missing *)
    (* TODO: This type should only be well-formed if bounds are constants 
      This should be done in the type checker *)
    (* We assume that lbound and ubound are constant integers
      and that lbound < ubound *)
    let (lvalue, uvalue) = match (lbound, ubound) with
      | A.Const (_, Num x), A.Const (_, Num y) ->
        let x = HString.string_of_hstring x in
        let y = HString.string_of_hstring y in
        Numeral.of_string x, Numeral.of_string y
      | _ -> assert false
    in 
    X.singleton X.empty_index (Type.mk_int_range lvalue uvalue)
  | A.EnumType (_, enum_name, enum_elements) ->
      let enum_name = HString.string_of_hstring enum_name in
      let enum_elements = List.map HString.string_of_hstring enum_elements in
      let ty = Type.mk_enum enum_name enum_elements in
      X.singleton X.empty_index ty
  | A.UserType (_, ident) ->
    StringMap.find ident cstate.type_alias
  | A.AbstractType (_, ident) ->
    (match StringMap.find_opt ident cstate.type_alias with
      | Some candidate ->
        (* The typechecker transforms enum types to abstract types (not sure why) 
          here we check if the ident in fact names an enum type *)
        let ident = HString.string_of_hstring ident in
        let bindings = X.bindings candidate in
        let (head_index, ty) = List.hd bindings in
        if List.length bindings = 1 && head_index = X.empty_index && Type.is_enum ty then
          candidate
        else X.singleton [X.AbstractTypeIndex ident] Type.t_int
      | None ->
        let ident = HString.string_of_hstring ident in
        X.singleton [X.AbstractTypeIndex ident] Type.t_int)
  | A.RecordType (_, record_fields) ->
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
  | A.ArrayType (_, (type_expr, size_expr)) ->
    (* TODO: Should we check that array size is constant here or later?
      If the var_size flag is set, variable sized arrays are allowed
      otherwise we should fail and make sure they are constant *)
    let element_type = compile_ast_type cstate ctx map type_expr in
    let array_size' = compile_ast_expr cstate ctx [] map size_expr in
    let array_size = (List.hd (X.values array_size')).expr_init in
    (* Old code does flattening here, but that flattening is only ever used
      once! And it is for a check, in lustreDeclarations line 423 *)
    if AH.expr_is_const size_expr && expand then
      let upper = E.numeral_of_expr array_size in
      let result = ref X.empty in
      for ix = 0 to (Numeral.to_int upper - 1) do
        result := X.fold
          (fun j t a -> 
            X.add (j @ [X.ArrayIntIndex ix])
            (Type.mk_array t
              (Type.mk_int_range Numeral.zero upper))
            a)
          element_type
          !result
      done;
      !result
    else
      let over_element_type j t a = X.add
        (j @ [X.ArrayVarIndex array_size])
        (Type.mk_array t (if E.is_numeral array_size
          then Type.mk_int_range Numeral.zero (E.numeral_of_expr array_size)
          else Type.t_int))
        a
      in
      X.fold over_element_type element_type X.empty
  | A.TArr _ -> assert false
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
      let var = StringMap.find id_str cstate.free_constants in
      X.map E.mk_free_var var
    with Not_found ->
    try
      let expr = StringMap.find id_str cstate.other_constants in
      compile_ast_expr cstate ctx bounds map expr
    with Not_found ->
    try 
      let id_str = HString.string_of_hstring id_str in
      let ty = Type.enum_of_constr id_str in
      X.singleton X.empty_index (E.mk_constr id_str ty)
    with Not_found ->
    try
      H.find !map.quant_vars ident
    with Not_found ->
    try
      H.find !map.array_index ident
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
    let rpath = List.rev path' in
    let path1 = (rpath |> List.tl |> List.rev) in
    let path2 = List.map
      (fun (_, s) -> HString.string_of_hstring s)
      !map.contract_scope
    in
    let path3 = [(rpath |> List.hd)] in
    let path' = path2 @ path1 @ path3 in
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
    (* TODO: Old code does three error checks here doublecheck *)
    X.map2 (fun _ -> mk) expr1 expr2

  and compile_quantifier bounds mk avars expr =
    let vars, quant_var_map = vars_of_quant cstate ctx map avars in
    let bounds = bounds @
      List.map (fun v -> E.Unbound (E.unsafe_expr_of_term (Term.mk_var v)))
        vars in
    H.add_seq !map.quant_vars (H.to_seq quant_var_map);
    let result = compile_unary bounds (mk vars) expr in
    H.clear !map.quant_vars;
    result

  and compile_equality bounds polarity expr1 expr2 =
    let (mk_binary, mk_seq, const_expr) = match polarity with
      | true -> (E.mk_eq, E.mk_and, E.t_true)
      | false -> (E.mk_neq, E.mk_or, E.t_false) in
    let expr = compile_binary bounds mk_binary expr1 expr2 in
    X.singleton X.empty_index (List.fold_left mk_seq const_expr (X.values expr))

  and compile_ite bounds expr1 expr2 expr3 =
    (* TODO: Old code checks that expr1 is a non-indexed boolean *)
    let expr1 = compile_ast_expr cstate ctx bounds map expr1 in
    let expr1 = match X.bindings expr1 with
      | [_, expr] -> expr
      | _ -> assert false
    in compile_binary bounds (E.mk_ite expr1) expr2 expr3

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
            N.add_state_var_def sv (N.GeneratedEq (pos, index));
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
    in
    let rec mk_cond_indexes (acc, cpt) li ri =
      match li, ri with
      | X.ArrayVarIndex _ :: li', X.ArrayIntIndex vi :: ri' ->
        let rhs = (E.mk_int (Numeral.of_int vi)) in
        let acc = E.mk_eq (E.mk_index_var cpt) rhs :: acc in
        mk_cond_indexes (acc, cpt+1) li' ri'
      | X.ArrayVarIndex _ :: li', X.ArrayVarIndex vi :: ri' ->
        let rhs = (E.mk_of_expr vi) in
        let acc = E.mk_eq (E.mk_index_var cpt) rhs :: acc in
        mk_cond_indexes (acc, cpt+1) li' ri'
      | _ :: li', _ :: ri' -> mk_cond_indexes (acc, cpt) li' ri'
      | [], _ | _, [] -> if acc = [] then raise Not_found;
        List.rev acc |> E.mk_and_n
    in
    let rec mk_store acc a ri x = match ri with
      | X.ArrayIntIndex vi :: ri' ->
        let i = E.mk_int (Numeral.of_int vi) in
        let a' = List.fold_left E.mk_select a acc in
        let x = mk_store [i] a' ri' x in
        E.mk_store a i x
      | X.ArrayVarIndex vi :: ri' ->
        let i = E.mk_of_expr vi in
        let a' = List.fold_left E.mk_select a acc in
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
        let old_v = List.fold_left (fun (acc, cpt) _ ->
          E.mk_select acc (E.mk_index_var cpt), cpt + 1) (v, 0) i |> fst
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
        |> list_init (fun _ -> expr)
      in let gexpr = A.GroupExpr (pos, A.ArrayExpr, l_expr) in
      let result = compile_ast_expr cstate ctx bounds map gexpr in
      result
    else *)
      let over_indices = fun j (e:LustreExpr.t) a -> 
        let e' = state_var_of_expr e |> E.mk_var
        in X.add (X.ArrayVarIndex array_size :: j) e' a
      in let result = X.fold over_indices cexpr X.empty in
      result

  and compile_array_index bounds expr i =
    let compiled_i = compile_ast_expr cstate ctx bounds map i in
    let index_e = compiled_i |> X.values |> List.hd in
    let index = E.mk_of_expr index_e.expr_init in
    let bounds =
      try
        let index_nb = E.int_of_index_var index in
        let _, bounds = Lib.list_extract_nth bounds index_nb in
        bounds
      with Invalid_argument _ | Failure _ -> bounds
    in
    let compiled_expr = compile_ast_expr cstate ctx bounds map expr in
    let rec push expr = match X.choose expr with
      | X.ArrayVarIndex _ :: _, v
      | X.ArrayIntIndex _ :: _, v ->
        let over_expr = fun e -> match e with
          | X.ArrayVarIndex _ :: tl
          | X.ArrayIntIndex _ :: tl -> X.add tl
          | _ -> assert false
        in let expr = X.fold over_expr expr X.empty in
        if E.type_of_lustre_expr v |> Type.is_array then
          X.map (fun e -> E.mk_select e index) expr
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
      | _ -> assert false
    in push compiled_expr

  in
(*   Format.eprintf "%a\n" A.pp_print_expr expr; *)
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
  | A.ConvOp (_, A.ToUInt8, expr) -> compile_unary bounds E.mk_to_uint8 expr
  | A.ConvOp (_, A.ToUInt16, expr) -> compile_unary bounds E.mk_to_uint16 expr
  | A.ConvOp (_, A.ToUInt32, expr) -> compile_unary bounds E.mk_to_uint32 expr
  | A.ConvOp (_, A.ToUInt64, expr) -> compile_unary bounds E.mk_to_uint64 expr
  | A.ConvOp (_, A.ToInt8, expr) -> compile_unary bounds E.mk_to_int8 expr
  | A.ConvOp (_, A.ToInt16, expr) -> compile_unary bounds E.mk_to_int16 expr
  | A.ConvOp (_, A.ToInt32, expr) -> compile_unary bounds E.mk_to_int32 expr
  | A.ConvOp (_, A.ToInt64, expr) -> compile_unary bounds E.mk_to_int64 expr
  | A.ConvOp (_, A.ToReal, expr) -> compile_unary bounds E.mk_to_real expr
  | A.UnaryOp (_, A.Not, expr) -> compile_unary bounds E.mk_not expr 
  | A.UnaryOp (_, A.Uminus, expr) -> compile_unary bounds E.mk_uminus expr 
  | A.UnaryOp (_, A.BVNot, expr) -> compile_unary bounds E.mk_bvnot expr
  (* ****************************************************************** *)
  (* Binary Operators                                                   *)
  (* ****************************************************************** *)
  | A.BinaryOp (_, A.And, expr1, expr2) ->
    compile_binary bounds E.mk_and expr1 expr2
  | A.BinaryOp (_, A.Or, expr1, expr2) ->
    compile_binary bounds E.mk_or expr1 expr2 
  | A.BinaryOp (_, A.Xor, expr1, expr2) ->
    compile_binary bounds E.mk_xor expr1 expr2 
  | A.BinaryOp (_, A.Impl, expr1, expr2) ->
    compile_binary bounds E.mk_impl expr1 expr2 
  | A.BinaryOp (_, A.Mod, expr1, expr2) ->
    compile_binary bounds E.mk_mod expr1 expr2 
  | A.BinaryOp (_, A.Minus, expr1, expr2) ->
    compile_binary bounds E.mk_minus expr1 expr2
  | A.BinaryOp (_, A.Plus, expr1, expr2) ->
    compile_binary bounds E.mk_plus expr1 expr2
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
  | A.TernaryOp (_, A.Ite, expr1, expr2, expr3) ->
    compile_ite bounds expr1 expr2 expr3
  | A.Pre (_, expr) -> compile_pre bounds expr
  | A.Merge (_, clock_ident, merge_cases) ->
    compile_merge bounds clock_ident merge_cases
  (* ****************************************************************** *)
  (* Tuple and Record Operators                                         *)
  (* ****************************************************************** *)
  | A.RecordProject (_, expr, field) ->
    let field = HString.string_of_hstring field in
    compile_projection bounds expr (X.RecordIndex field)
  | A.TupleProject (_, expr, field) ->
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
  | A.RecordExpr (_, _, expr_list) -> 
    compile_record_expr bounds expr_list
  | A.StructUpdate (_, expr1, index, expr2) ->
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
  | A.ArrayIndex (_, expr, i) -> compile_array_index bounds expr i
  (* ****************************************************************** *)
  (* Not Implemented                                                    *)
  (* ****************************************************************** *)
  (* LustreSyntaxChecks handles these expressions on the first pass,
    making these expressions impossible at this stage *)
  | A.ArraySlice _ -> assert false
  | A.ArrayConcat _ -> assert false
  | A.Current _ -> assert false
  | A.NArityOp _ -> assert false
  | A.Fby _ -> assert false
  | A.When _ -> assert false
  | A.Activate _ -> assert false
  | A.TernaryOp _ -> assert false
  | A.CallParam _ -> assert false

and compile_node pos ctx cstate map oracles outputs cond restart ident args defaults =
  let called_node = N.node_of_name ident cstate.nodes in
  let oracles = oracles
    |> List.map (fun n -> H.find !map.state_var (mk_ident n))
    |> List.combine called_node.oracles
    |> List.map (fun (sv, sv') ->
      N.set_state_var_instance sv' pos ident sv;
      sv')
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
        N.add_state_var_def sv (N.GeneratedEq (pos, i'));
      X.add i sv accum
    in let result = X.fold2 over_indices inputs cexpr X.empty
    in result
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
  let input_state_vars = node_inputs_of_exprs called_node.inputs args in
  let act_state_var, defaults = node_act_cond_of_expr cond defaults in
  let restart_state_var = restart_cond_of_expr restart in
  let cond_state_var = match act_state_var, restart_state_var with
    | None, None -> []
    | Some c, None -> [N.CActivate c]
    | None, Some r -> [N.CRestart r]
    | Some c, Some r -> [N.CActivate c; N.CRestart r]
  in
  let node_call = {
    N.call_pos = pos;
    N.call_node_name = ident;
    N.call_cond = cond_state_var;
    N.call_inputs = input_state_vars;
    N.call_oracles = oracles;
    N.call_outputs = outputs;
    N.call_defaults = defaults
  }
  in node_call

and compile_contract_variables cstate gids ctx map contract_scope node_scope contract =
  (* let contract_scope = List.map HString.string_of_hstring contract_scope in *)
  let compile_contract_item count scope kind pos name expr =
    let ident = extract_normalized expr in
    let state_var = H.find !map.state_var ident in
    let name = match name with
      | Some name -> Some (HString.string_of_hstring name)
      | None -> None
    in
    let contract_sv = C.mk_svar pos count name state_var scope in
    N.add_state_var_def state_var (N.ContractItem (pos, contract_sv, kind));
    contract_sv
  (* ****************************************************************** *)
  (* Split contracts into relevant categories                           *)
  (* ****************************************************************** *)
  in let gconsts, gvars, modes, contract_calls =
    let over_items (consts, vars, modes, calls) = function
      | A.GhostConst c -> c :: consts, vars, modes, calls
      | A.GhostVar v -> consts, v :: vars, modes, calls
      | A.Assume _ -> consts, vars, modes, calls
      | A.Guarantee _ -> consts, vars, modes, calls
      | A.Mode m -> consts, vars, m :: modes, calls
      | A.ContractCall c -> consts, vars, modes, c :: calls
      | A.AssumptionVars _ -> consts, vars, modes, calls
    in List.fold_left over_items ([], [], [], []) contract in
  (* ****************************************************************** *)
  (* Ghost Constants and Variables                                      *)
  (* ****************************************************************** *)
  List.iter
    (fun g -> g |> compile_const_decl ~ghost:true cstate ctx map [] |> ignore)
    gconsts;

  let ghost_locals, ghost_equations =
    let extract_namespace name =
      let name = HString.string_of_hstring name in
      let parts = List.rev (String.split_on_char '_' name) in
      (parts |> List.hd |> HString.mk_hstring |> mk_ident, List.tl parts)
    in
    let over_vars (gvar_accum, eq_accum) = function
      | A.FreeConst (_, _, _) -> assert false
      | A.UntypedConst (_, id, expr) ->
        let expr_ident = mk_ident id in
        let (ident, contract_namespace) = extract_namespace id in
        let nexpr = compile_ast_expr cstate ctx [] map expr in
        let index_types = X.map (fun { E.expr_type } -> expr_type) nexpr in
        let over_indices = fun index index_type accum ->
          let possible_state_var = mk_state_var
            ~is_input:false
            ~expr_ident:expr_ident
            map
            (node_scope @ contract_namespace @ I.user_scope)
            ident
            index
            index_type
            (Some N.Ghost)
          in 
          match possible_state_var with
          | Some state_var -> X.add index state_var accum
          | None -> accum
        in let ghost_local = X.fold over_indices index_types X.empty in
        H.replace !map.expr expr_ident nexpr;
        ghost_local :: gvar_accum, eq_accum
      | A.TypedConst (pos, id, expr, expr_type) ->
        let expr_ident = mk_ident id in
        let (ident, contract_namespace) = extract_namespace id in
        let index_types = compile_ast_type cstate ctx map expr_type in
        let over_indices = fun index index_type accum ->
          let possible_state_var = mk_state_var
            ~is_input:false
            ~expr_ident:expr_ident
            map
            (node_scope @ contract_namespace @ I.user_scope)
            ident
            index
            index_type
            (Some N.Ghost)
          in
          match possible_state_var with
          | Some state_var -> X.add index state_var accum
          | None -> accum
        in let ghost_local = X.fold over_indices index_types X.empty in
        let eq_lhs = A.StructDef (pos, [A.SingleIdent (pos, id)]) in
        let eq_rhs = expr in
        ghost_local :: gvar_accum, (pos, eq_lhs, eq_rhs) :: eq_accum
    in List.fold_left over_vars ([], []) gvars
  (* ****************************************************************** *)
  (* Contract Modes                                                     *)
  (* ****************************************************************** *)
  in let modes =
    let over_modes (pos, id, reqs, enss) =
      let id' = HString.string_of_hstring id in
      let contract_scope = List.map
        (fun (p, s) -> (p, HString.string_of_hstring s))
        contract_scope
      in
      let reqs = List.mapi
        (fun i (p, n, e) -> compile_contract_item (i + 1) contract_scope N.Require p n e)
        reqs in
      let enss = List.mapi
        (fun i (p, n, e) -> compile_contract_item (i + 1) contract_scope N.Ensure p n e)
        enss in
      let contract_scope = List.map (fun (_, i) -> i) contract_scope in
      let path = contract_scope @ [id'] in
      let mode = C.mk_mode (mk_ident id) pos path reqs enss false in
      map := { !map with modes = mode :: !map.modes };
      mode
    in List.map over_modes modes
  (* ****************************************************************** *)
  (* Contract Calls                                                     *)
  (* ****************************************************************** *)
  in let (ghost_locals2, ghost_equations2, modes2) =
    let over_calls (gls, ges, ms) (_, id, _, _) =
      let (_, contract_scope, contract_eqns) =
        LAN.StringMap.find id gids.LAN.contract_calls
      in
      map := { !map with contract_scope };
      let (gl, ge, m) = compile_contract_variables cstate gids ctx map contract_scope node_scope contract_eqns
      in gl @ gls, ge @ ges, m @ ms
    in List.fold_left over_calls ([], [], []) contract_calls
  in ghost_locals @ ghost_locals2, ghost_equations @ ghost_equations2, modes @ modes2

and compile_contract cstate gids ctx map contract_scope node_scope contract =
  let compile_contract_item count scope kind pos name expr =
    let scope = List.map (fun (i, s) -> i, HString.string_of_hstring s) scope in
    let ident = extract_normalized expr in
    let state_var = H.find !map.state_var ident in
    let name = match name with
      | Some name -> Some (HString.string_of_hstring name)
      | None -> None
    in
    let contract_sv = C.mk_svar pos count name state_var scope in
    N.add_state_var_def state_var (N.ContractItem (pos, contract_sv, kind));
    contract_sv
  (* ****************************************************************** *)
  (* Split contracts into relevant categories                           *)
  (* ****************************************************************** *)
  in let assumes, guarantees, contract_calls =
    let over_items (assumes, guarantees, calls) = function
      | A.GhostConst _ -> assumes, guarantees, calls
      | A.GhostVar _ ->  assumes, guarantees, calls
      | A.Assume a -> a :: assumes, guarantees, calls
      | A.Guarantee g -> assumes, g :: guarantees, calls
      | A.Mode _ -> assumes, guarantees, calls
      | A.ContractCall c -> assumes, guarantees, c :: calls
      | A.AssumptionVars _ -> assumes, guarantees, calls
    in List.fold_left over_items ([], [], []) contract
  (* ****************************************************************** *)
  (* Contract Calls                                                     *)
  (* ****************************************************************** *)
  in let (assumes2, guarantees2) =
    let over_calls (ams, gs) (_, id, _, _) =
      let (_, scope, contract_eqns) =
        LAN.StringMap.find id gids.LAN.contract_calls
      in
      let contract_scope = (List.hd scope) :: contract_scope in
      map := { !map with contract_scope };
      let (a, g) = compile_contract cstate gids ctx map contract_scope node_scope contract_eqns
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
      compile_contract_item (i + 1) contract_scope kind pos name expr
    in List.map over_assumes assumes
  in
  let guarantees = 
    let over_guarantees (pos, name, soft, expr) =
      let i = !map.guarantee_count in
      map := {!map with guarantee_count = i + 1 };
      let kind = if soft then N.WeakGuarantee else N.Guarantee in
      compile_contract_item (i + 1) contract_scope kind pos name expr
    in List.map over_guarantees guarantees
      |> List.map (fun g -> g, false)
  in assumes @ assumes2,
    guarantees @ guarantees2

and compile_node_decl gids is_function cstate ctx i ext inputs outputs locals items contract =
  let name = mk_ident i in
  let node_scope = name |> I.to_scope in
  let is_extern = ext in
  let instance =
    StateVar.mk_state_var
      ~is_const:true
      (I.instance_ident |> I.string_of_ident false)
      (I.to_scope name @ I.reserved_scope)
      Type.t_int
  in
  let init_flag = 
    StateVar.mk_state_var
      (I.init_flag_ident |> I.string_of_ident false)
      (I.to_scope name @ I.reserved_scope)
      Type.t_bool
  in
  let map = ref (empty_identifier_maps ()) in
  let state_var_expr_map = SVT.create 7 in
  (* ****************************************************************** *)
  (* Node Inputs                                                        *)
  (* ****************************************************************** *)
  let inputs =
    (* TODO: The documentation on lustreNode says that a single argument
      node should have a non-list index (a singleton index), but the old
      node generation code does not seem to honor that *)
    let over_inputs = fun compiled_input (_pos, i, ast_type, clock, is_const) ->
      match clock with
      | A.ClockTrue ->
        let n = X.top_max_index compiled_input |> succ in
        let expand = LAN.StringSet.find_opt i gids.LAN.expanded_variables in
        let expand = match expand with | Some _ -> true | None -> false in
        let ident = mk_ident i in
        let index_types = compile_ast_type ~expand cstate ctx map ast_type in
        let over_indices = fun index index_type accum ->
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
          | Some state_var -> X.add (X.ListIndex n :: index) state_var accum
          | None -> accum
        in X.fold over_indices index_types compiled_input
      | _ -> assert false (* Guaranteed by LustreSyntaxChecks *)
    in List.fold_left over_inputs X.empty inputs
  (* ****************************************************************** *)
  (* Node Outputs                                                       *)
  (* ****************************************************************** *)
  in let outputs =
    (* TODO: The documentation on lustreNode does not state anything about
      the requirements for indices of outputs, yet the old code makes it
      a singleton index in the event there is only one index *)
    let over_outputs = fun (is_single) compiled_output (_, i, ast_type, clock) ->
      match clock with
      | A.ClockTrue ->
        let n = X.top_max_index compiled_output |> succ in
        let ident = mk_ident i in
        let index_types = compile_ast_type cstate ctx map ast_type in
        let over_indices = fun index index_type accum ->
          let possible_state_var = mk_state_var
            ~is_input:false
            map
            (node_scope @ I.user_scope)
            ident
            index
            index_type
            (Some N.Output)
          and index' = if is_single then index
            else X.ListIndex n :: index
          in 
          match possible_state_var with
          | Some state_var -> X.add index' state_var accum
          | None -> accum
        in X.fold over_indices index_types compiled_output
      | _ -> assert false (* Guaranteed by LustreSyntaxChecks *)
    and is_single = List.length outputs = 1
    in List.fold_left (over_outputs is_single) X.empty outputs
  (* ****************************************************************** *)
  (* User Locals                                                        *)
  (* ****************************************************************** *)
  in let locals, cstate =
    let over_locals = fun (locals, cstate) local ->
      match local with
      | A.NodeVarDecl (_, (_, i, ast_type, A.ClockTrue)) ->
        let expand = LAN.StringSet.find_opt i gids.LAN.expanded_variables in
        let expand = match expand with | Some _ -> true | None -> false in
        let ident = mk_ident i
        and index_types = compile_ast_type ~expand cstate ctx map ast_type in
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
        (X.fold over_indices index_types X.empty) :: locals, cstate
      | A.NodeConstDecl (_, decl) ->
        locals, compile_const_decl cstate ctx map (node_scope @ ["impl"]) decl
      | A.NodeVarDecl _ -> assert false (* guaranteed by LustreSyntaxChecks *)
    in
    List.fold_left over_locals ([], cstate) locals
  (* ****************************************************************** *)
  (* (State Variables for) Generated Locals                             *)
  (* ****************************************************************** *)
  in let glocals =
    let locals_list = LAN.StringMap.bindings gids.LAN.locals in
    let over_generated_locals glocals (id, (is_ghost, expr_type, _, _)) =
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
          (if is_ghost then Some N.KGhost else None)
        in
        match possible_state_var with
        | Some state_var -> X.add index state_var accum
        | None -> accum
      in let result = X.fold over_indices index_types X.empty in
      result :: glocals
    in List.fold_left over_generated_locals [] locals_list
  (* ****************************************************************** *)
  (* (State Variables for) Generated Subrange Constraints               *)
  (* ****************************************************************** *)
  in let glocals =
    let over_generated_locals glocals (_, _, _, id, _) =
      let ident = mk_ident id in
      let index_types = compile_ast_type cstate ctx map (A.Bool dummy_pos) in
      let over_indices = fun index index_type accum ->
        let possible_state_var = mk_state_var
          map
          (node_scope @ I.reserved_scope)
          ident
          index
          index_type
          (Some N.KGhost)
        in
        match possible_state_var with
        | Some state_var -> X.add index state_var accum
        | None -> accum
      in let result = X.fold over_indices index_types X.empty in
      result :: glocals
    in List.fold_left over_generated_locals glocals gids.LAN.subrange_constraints
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
          (Some N.KLocal)
        in
        match possible_state_var with
        | Some state_var -> X.add index state_var accum
        | None -> accum
      in let result = X.fold over_indices index_types X.empty in
      result :: glocals
    in List.fold_left over_generated_locals glocals gids.LAN.node_args
  (* ****************************************************************** *)
  (* (State Variables for) Generated Locals for Array Constructors      *)
  (* ****************************************************************** *)
  in let glocals =
    let array_ctor_list = LAN.StringMap.bindings gids.LAN.array_constructors in
    let over_generated_locals glocals (id, (expr_type, expr, size_expr)) =
      let pos = AH.pos_of_expr expr in
      let ident = mk_ident id in
      let index_types = compile_ast_type cstate ctx map expr_type in
      let nsize_expr = compile_ast_expr cstate ctx [] map size_expr in
      let size = (nsize_expr |> X.values |> List.hd).expr_init in
      let is_numeral = Term.is_numeral (E.unsafe_term_of_expr size) in
      let bound = if is_numeral then E.Fixed size else E.Bound size in
        let over_indices = fun index index_type accum ->
          let possible_state_var = mk_state_var 
            map
            (node_scope @ I.reserved_scope)
            ident
            index
            index_type
            None
          in
          match possible_state_var with
          | Some(state_var) ->
            if not (StateVar.is_input state_var)
              then N.add_state_var_def state_var (N.GeneratedEq (pos, index));
            SVT.add !map.bounds state_var [bound];
            X.add index state_var accum
          | None -> accum
      in let result = X.fold over_indices index_types X.empty in
      result :: glocals
    in List.fold_left over_generated_locals glocals array_ctor_list
  (* ****************************************************************** *)
  (* Contract State Variables                                           *)
  (* ****************************************************************** *)
  in let (ghost_locals, ghost_equations, modes) =
    match contract with
    | Some contract -> compile_contract_variables cstate gids ctx map [] node_scope contract
    | None -> [], [], []
  (* ****************************************************************** *)
  (* Oracles                                                            *)
  (* ****************************************************************** *)
  in let (oracles, oracle_state_var_map) =
    let over_oracles (oracles, osvm) (id, expr_type, expr) =
      let oracle_ident = mk_ident id in
      let closed_sv = match expr with
        | A.Ident (_, id') ->
          let ident = mk_ident id' in
          let closed_sv = H.find !map.state_var ident in
          Some closed_sv
        | A.Const (_, _) -> None
        | _ -> assert false
      in let index_types = compile_ast_type cstate ctx map expr_type in
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
      in let result = X.fold over_indices index_types X.empty in
      (X.values result) @ oracles, osvm
    in List.fold_left over_oracles ([], SVT.create 7) gids.LAN.oracles
  (* ****************************************************************** *)
  (* Propagated Oracles                                                 *)
  (* ****************************************************************** *)
  in let oracles =
    let existing_oracles = cstate.nodes
      |> List.map (fun n -> n.N.oracles) 
      |> List.flatten
    in let over_propagated_oracles oracles (name, orc) =
      let oracle_ident = mk_ident name in
      let orc_state_var = List.find (fun o ->
        let existing_oracle_name = StateVar.name_of_state_var o
        and current_oracle_name = mk_state_var_name (mk_ident orc) X.empty_index
        in existing_oracle_name = current_oracle_name)
        existing_oracles
      in let state_var_type = StateVar.type_of_state_var orc_state_var in
      let is_const = StateVar.is_const orc_state_var in
      let possible_state_var = mk_state_var
        ~is_input:true
        ~is_const
        map
        (node_scope @ I.reserved_scope)
        oracle_ident
        X.empty_index
        state_var_type
        (Some N.Oracle)
      in 
      match possible_state_var with
      | Some (state_var) -> state_var :: oracles
      | None -> oracles
    in List.fold_left over_propagated_oracles oracles gids.LAN.propagated_oracles
  (* ****************************************************************** *)
  (* Node Calls                                                         *)
  (* ****************************************************************** *)
  in let (calls, glocals) =
    let over_calls = fun (calls, glocals) (pos, oracles, var, cond, restart, ident, args, defaults) ->
      let node_id = mk_ident ident in
      let called_node = N.node_of_name node_id cstate.nodes in
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
            H.add local_map var_id state_var;
            N.add_state_var_def state_var (N.CallOutput (pos, index));
            N.set_state_var_instance state_var pos node_id sv;
            X.add index state_var compiled_vars
          | None -> compiled_vars
        in
        X.fold over_vars called_node.outputs X.empty
      in let node_call = compile_node
        pos ctx cstate map oracles outputs cond restart node_id args defaults
      in let glocals' = H.fold (fun _ v a -> (X.singleton X.empty_index v) :: a) local_map [] in 
      node_call :: calls, glocals' @ glocals
    in List.fold_left over_calls ([], glocals) gids.calls
  (* ****************************************************************** *)
  (* Split node items into relevant categories                          *)
  (* ****************************************************************** *)
  in let (node_props, node_eqs, node_asserts, is_main) = 
    let over_items = fun (props, eqs, asserts, is_main) (item) ->
      match item with
      | A.Body e -> (match e with
        | A.Assert (p, e) -> (props, eqs, (p, e) :: asserts, is_main)
        | A.Equation (p, l, e) -> (props, (p, l, e) :: eqs, asserts, is_main))
      | A.AnnotMain flag -> (props, eqs, asserts, flag || is_main)
      | A.AnnotProperty (p, n, e) -> ((p, n, e) :: props, eqs, asserts, is_main) 
    in List.fold_left over_items ([], [], [], false) items
  (* ****************************************************************** *)
  (* Properties and Assertions                                          *)
  (* ****************************************************************** *)
  in let props =
    let op (pos, name_opt, expr) =
      let name_opt = match name_opt with
        | Some name -> Some (HString.string_of_hstring name)
        | None -> None
      in
      let id_str = match expr with
        | A.Ident (_, id_str) -> id_str
        | A.ArrayIndex (_, A.Ident (_, id_str), _) -> id_str
        | _ -> assert false (* must be abstracted *)
      in let id = mk_ident id_str in
      let sv = H.find !map.state_var id in
      let name = match name_opt with
        | Some n -> n
        | None -> let abs = LAN.StringMap.find_opt id_str gids.LAN.locals in
          let name = match abs with | Some (_, _, _, e) -> e | None -> expr in
            Format.asprintf "@[<h>%a@]" A.pp_print_expr name
      in sv, name, (Property.PropAnnot pos)
    in List.map op node_props

  in let asserts =
    let op (pos, expr) =
      let id = extract_normalized expr in
      let sv = H.find !map.state_var id in
      N.add_state_var_def sv (N.Assertion pos);
      (pos, sv)
    in List.map op node_asserts
  (* ****************************************************************** *)
  (* Helpers for generated and user equations                           *)
  (* ****************************************************************** *)
  in let compile_struct_item struct_item = match struct_item with
    | A.SingleIdent (_, i) ->
      let ident = mk_ident i in
      let expr = H.find !map.expr ident in
      let result = X.map (fun e -> state_var_of_expr e) expr in
      result, 0
    | A.ArrayDef (_, i, l) ->
      let ident = mk_ident i in
      let expr = H.find !map.expr ident in
      let result = X.map (fun e -> state_var_of_expr e) expr in
      (* TODO: Old code checks that array lengths between l and result match *)
      (* TODO: Old code checks that result must have at least one element *)
      (* TODO: Old code suggets that shadowing can occur here *)
      let indexes = List.length l in
      List.iteri (fun i v -> 
        let ident = mk_ident v in
        let expr = E.mk_index_var i in
        let index = X.singleton X.empty_index expr in
        H.add !map.array_index ident index;)
        l;
      result, indexes
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

  in let gen_lhs_bounds is_generated eq_lhs expr indexes =
    List.fold_left (fun acc (i, sv) ->
      let result = List.fold_left (fun (acc, cpt) -> function
        | X.ArrayVarIndex b -> if cpt < indexes
          then E.Bound b :: acc, succ cpt
          else acc, cpt
        | X.ArrayIntIndex x -> 
          let expr = (E.mk_int (Numeral.of_int x)).expr_init in
          E.Fixed expr :: acc, succ cpt
        | _ -> acc, cpt)
        (acc, 0) i |> fst
      in
      if not is_generated then
        N.add_state_var_def sv
          (N.ProperEq (AH.pos_of_expr expr, rm_array_var_index i));
      result
    ) [] (X.bindings eq_lhs)
  (* ****************************************************************** *)
  (* Generated Equations                                                *)
  (* ****************************************************************** *)
  in let gequations =
    let over_equations = fun eqns (qvars, contract_scope, lhs, ast_expr) ->
      map := { !map with contract_scope };
      let eq_lhs, indexes = match lhs with
        | A.StructDef (_, []) -> (X.empty, 0)
        | A.StructDef (_, [e]) -> compile_struct_item e
        | A.StructDef (_, l) ->
          let construct_index i j e a = X.add (X.ListIndex i :: j) e a in
          let over_items = fun (i, accum) e -> 
            let t, _ = compile_struct_item e in
              i + 1, X.fold (construct_index i) t accum
          in
          let _, res = List.fold_left over_items (0, X.empty) l
          in res, 0
      in
      let lhs_bounds = gen_lhs_bounds true eq_lhs ast_expr indexes in
      let vars, quant_var_map = vars_of_quant cstate ctx map qvars in
      let bounds = lhs_bounds @
        List.map (fun v -> E.Unbound (E.unsafe_expr_of_term (Term.mk_var v)))
          vars in
      H.add_seq !map.quant_vars (H.to_seq quant_var_map);
      let eq_rhs = compile_ast_expr cstate ctx bounds map ast_expr in
      let eq_rhs = flatten_list_indexes eq_rhs in
(*       Format.eprintf "lhs: %a\n\n rhs: %a\n\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
      
      let equations = expand_tuple Lib.dummy_pos eq_lhs eq_rhs in 
      List.iter (fun ((sv, _), e) -> SVT.add state_var_expr_map sv e) equations;
      H.clear !map.array_index;
      H.clear !map.quant_vars;
      (* TODO: Old code tries to infer a more strict type here
        lustreContext 2040+ *)
      equations @ eqns
    in List.fold_left over_equations [] gids.LAN.equations
  (* ****************************************************************** *)
  (* Node Equations                                                     *)
  (* ****************************************************************** *)
  in 
(*   Format.eprintf "map:\n\n%a\n\n" pp_print_identifier_maps !map; *)
  let equations =
    let over_equations = fun eqns (pos, lhs, ast_expr) ->
      let eq_lhs, indexes = match lhs with
        | A.StructDef (_, []) -> (X.empty, 0)
        | A.StructDef (_, [e]) -> compile_struct_item e
        | A.StructDef (_, l) ->
          let construct_index = fun i j e a -> X.add (X.ListIndex i :: j) e a in
          let over_items = fun (i, accum) e -> 
            let t, _ = compile_struct_item e in
              i + 1, X.fold (construct_index i) t accum
          in
          let _, res = List.fold_left over_items (0, X.empty) l
          in res, 0
      in
      let lhs_bounds = gen_lhs_bounds false eq_lhs ast_expr indexes in
      let eq_rhs = compile_ast_expr cstate ctx lhs_bounds map ast_expr in
      let eq_rhs = flatten_list_indexes eq_rhs in
(*       Format.eprintf "lhs: %a\n\n rhs: %a\n\n"
        (X.pp_print_index_trie true StateVar.pp_print_state_var) eq_lhs
        (X.pp_print_index_trie true (E.pp_print_lustre_expr true)) eq_rhs; *)
      let equations = expand_tuple pos eq_lhs eq_rhs in
(*       Format.eprintf "\nequations: %a\n"
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
      (* TODO: Old code tries to infer a more strict type here
        lustreContext 2040+ *)
      equations @ eqns
    in List.fold_left over_equations [] (ghost_equations @ node_eqs)
  (* ****************************************************************** *)
  (* Contract Assumptions and Guarantees                                *)
  (* ****************************************************************** *)
  in let (assumes, guarantees) =
    match contract with
    | Some contract -> compile_contract cstate gids ctx map [] node_scope contract
    | None -> [], []
  (* ****************************************************************** *)
  (* Collect Variables for Assumption Generation                        *)
  (* ****************************************************************** *)
  in let assumption_svars =
    match contract with
    | Some contract -> (
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
  (* Generate Contract Constraints for Integer Subranges                *)
  (* ****************************************************************** *)
  in let (assumes, guarantees, props) =
    let create_constraint_name rexpr = 
      Format.asprintf "@[<h>%a@]" A.pp_print_expr rexpr
    in
    let over_subrange_constraints (a, ac, g, gc, p) (source, is_original, pos, id, rexpr) =
      let sv = H.find !map.state_var (mk_ident id) in
      let effective_contract = guarantees != [] || modes != [] in
      let constraint_kind = match source with
        | LAN.Input -> Some N.Assumption
        | Local -> None
        | Output -> if not ext && not effective_contract then
            None else Some N.Guarantee
        | Ghost -> Some N.Guarantee
      in
      if is_original then
        match constraint_kind with
        | Some N.Assumption ->
          let name = create_constraint_name rexpr in
          let contract_sv = C.mk_svar pos ac (Some name) sv [] in
          N.add_state_var_def sv (N.ContractItem (pos, contract_sv, N.Assumption));
          contract_sv :: a, ac + 1, g, gc, p
        | Some N.Guarantee ->
          let name = create_constraint_name rexpr in
          let contract_sv = C.mk_svar pos gc (Some name) sv [] in
          N.add_state_var_def sv (N.ContractItem (pos, contract_sv, N.Guarantee));
          a, ac, (contract_sv, false) :: g, gc + 1, p
        | None ->
          let name = create_constraint_name rexpr in
          let src = Property.Generated (Some pos, [sv]) in
          a, ac, g, gc, (sv, name, src) :: p
        | _ -> assert false
      else
        let name = create_constraint_name rexpr in
        let src = Property.Generated (Some pos, [sv]) in
        let src = Property.Candidate (Some src) in
        a, ac, g, gc, (sv, name, src) :: p
    in
    let (assumes, _, guarantees, _, props) = 
      List.fold_left over_subrange_constraints
      (assumes, List.length assumes, guarantees, List.length guarantees, props)
      gids.LAN.subrange_constraints
    in
    assumes, guarantees, props
  (* ****************************************************************** *)
  (* Finalize Contracts and add Sofar assumption                        *)
  (* ****************************************************************** *)
  in let (contract, sofar_local, sofar_equation) =
    if assumes != [] || guarantees != [] then
      let sofar_assumption = get (mk_state_var
        ~is_input:false
        map
        (node_scope @ I.reserved_scope)
        (mk_ident (HString.mk_hstring "sofar"))
        X.empty_index
        Type.t_bool
        None)
      in
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
      let sofar_local = X.singleton X.empty_index sofar_assumption in
      let conj_of_assumes = assumes
        |> List.map (fun { C.svar } -> E.mk_var svar)
        |> E.mk_and_n
      in
      let pre_sofar = E.mk_pre (E.mk_var sofar_assumption) in
      let expr = E.mk_arrow conj_of_assumes (E.mk_and conj_of_assumes pre_sofar) in
      let equation = (sofar_assumption, []), expr in
      let contract = C.mk assumes sofar_assumption guarantees modes in
      Some (contract), [sofar_local], [equation]
    else None, [], []
  (* ****************************************************************** *)
  (* Finalize and build intermediate LustreNode                         *)
  (* ****************************************************************** *)
  in let locals = sofar_local @ ghost_locals @ glocals @ locals in
  let calls = List.rev calls in
  let props = List.rev props in
  let equations = List.rev (sofar_equation @ equations @ gequations) in
  let asserts = List.sort (fun (p1, _) (p2, _) -> compare_pos p1 p2) asserts in
  let state_var_source_map = SVT.fold
    (fun k v a -> SVM.add k v a)
    !map.source SVM.empty in
  let var_bounds = SVT.fold (fun k v a -> (k, v) :: a) !map.bounds [] in
  List.iter (fun (k, v) -> SVT.add cstate.state_var_bounds k v) var_bounds;

  let (node:N.t) = { name;
    is_extern;
    instance;
    init_flag;
    inputs;
    oracles;
    outputs;
    locals;
    equations;
    calls;
    asserts;
    props;
    contract;
    is_main;
    is_function;
    state_var_source_map;
    oracle_state_var_map;
    state_var_expr_map;
    assumption_svars;
  } in { cstate with
    nodes = node :: cstate.nodes;
  }

and compile_const_decl ?(ghost = false) cstate ctx map scope = function
  | A.FreeConst (_, i, ty) ->
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
        let v = Var.mk_const_state_var state_var in X.add i v vt
      | None -> vt
    in
    let vt = X.fold over_index cty X.empty in
    if ghost then cstate
    else { cstate
      with free_constants = StringMap.add i vt cstate.free_constants }
  (* TODO: Old code does some subtyping checks for Typed constants
    Otherwise these other constants are used only for constant propagation *)
  | A.UntypedConst (_, id, expr)
  | A.TypedConst (_, id, expr, _) ->
    if ghost then
      let nexpr = compile_ast_expr cstate ctx [] map expr in
      H.replace !map.expr (mk_ident id) nexpr;
      cstate
    else { cstate with 
      other_constants = StringMap.add id expr cstate.other_constants }

and compile_type_decl pos ctx cstate = function
  | A.AliasType (_, ident, ltype) ->
    let empty_map = ref (empty_identifier_maps ()) in
    let t = compile_ast_type cstate ctx empty_map ltype in
    let type_alias = StringMap.add ident t cstate.type_alias in
    { cstate with
      type_alias }
  | A.FreeType (_, ident) ->
    let empty_map = ref (empty_identifier_maps ()) in
    let t = compile_ast_type cstate ctx empty_map (A.AbstractType (pos, ident)) in
    let type_alias = StringMap.add ident t cstate.type_alias in
    { cstate with
      type_alias }

and compile_declaration cstate gids ctx decl =
(*   Format.eprintf "decl: %a\n\n" A.pp_print_declaration decl; *)
  match decl with
  | A.TypeDecl ({A.start_pos = pos}, type_rhs) ->
    compile_type_decl pos ctx cstate type_rhs
  | A.ConstDecl (_, const_decl) ->
    let empty_map = ref (empty_identifier_maps ()) in
    compile_const_decl cstate ctx empty_map [] const_decl
  | A.FuncDecl (_, (i, ext, [], inputs, outputs, locals, items, contract)) ->
    let gids = LAN.StringMap.find i gids in
    compile_node_decl gids true cstate ctx i ext inputs outputs locals items contract
  | A.NodeDecl (_, (i, ext, [], inputs, outputs, locals, items, contract)) ->
    let gids = LAN.StringMap.find i gids in
    compile_node_decl gids false cstate ctx i ext inputs outputs locals items contract
  (* All contract node declarations are recorded and normalized in gids,
    this is necessary because each unique call to a contract node must be 
    normalized independently *)
  | A.ContractNodeDecl _ -> cstate
  (* guaranteed by LustreSyntaxChecks *)
  | A.NodeParamInst _ | A.NodeDecl _ | A.FuncDecl _ -> assert false
