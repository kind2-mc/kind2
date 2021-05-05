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
module I = LustreIdent
module X = LustreIndex
module H = LustreIdent.Hashtbl
module E = LustreExpr

module SVM = StateVar.StateVarMap
module SVT = StateVar.StateVarHashtbl

module C = TypeCheckerContext

module StringMap = struct
  include Map.Make(struct
    type t = string
    let compare i1 i2 = String.compare i1 i2
  end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end

type compiler_state = {
  nodes : LustreNode.t list;
  type_alias : Type.t LustreIndex.t StringMap.t;
  free_constants : (LustreIdent.t * Var.t LustreIndex.t) list;
  state_var_bounds : (E.expr E.bound_or_fixed list) StateVar.StateVarHashtbl.t;
}

let empty_compiler_state = { 
  nodes = [];
  type_alias = StringMap.empty;
  free_constants = [];
  state_var_bounds = SVT.create 7;
}

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

(* Create a state variable for from an indexed state variable in a
  scope *)
let mk_state_var
    ?is_input
    ?is_const
    ?for_inv_gen 
    ?(shadow = false)
    scope
    ident 
    index 
    state_var_type
    source
    state_var_source_map = 
  (* Concatenate identifier and indexes *)
  let state_var_name = mk_state_var_name ident index in
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
  (* Create or retrieve state variable *)
  let state_var =
  (* TODO check this *)
    try
      StateVar.state_var_of_string
        (state_var_name,
        (List.map Ident.to_string (scope @ flatten_scopes)))
    with Not_found ->
      StateVar.mk_state_var
        ?is_input
        ?is_const
        ?for_inv_gen 
        state_var_name
        (scope @ flatten_scopes)
        state_var_type 
  in let state_var_source_map' = match source with
    | Some s -> SVM.add state_var s state_var_source_map
    | None -> state_var_source_map
  in
  state_var, state_var_source_map'

let mk_ident id = match String.split_on_char '_' id with
  | i :: id' :: [] -> (match int_of_string_opt i with
    | Some i -> I.push_index (I.mk_string_ident id') i
    | None -> I.mk_string_ident id)
  | list -> I.mk_string_ident id

(* The LustreAstNormalizer is expected to normalize specific expression
  positions to an identifier (or leave it be if it is a constnat).
  That assumption is made explicit by calling this function. *)
let extract_normalized = function
  | A.Ident (pos, ident) -> mk_ident ident
  | _ -> assert false

let add_state_var_bounds cstate sv bounds =
  SVT.add cstate.state_var_bounds sv bounds
  

(* Match bindings from a trie of state variables and bindings for a
  trie of expressions and produce a list of equations *)
let rec expand_tuple' pos accum bounds lhs rhs = match lhs, rhs with 
  (* No more equations, return in original order *)
  | [], [] -> accum
  (* Indexes are not of equal length *)
  | _, []
  | [], _ -> fail_at_position pos
    "Type mismatch in equation: indexes not of equal length"
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
  | (X.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
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
    in expand_tuple' pos accum (E.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      ((rhs_index_tl, expr) :: rhs_tl)
  (* Tuple index on left-hand and right-hand side *)
  | ((X.TupleIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.TupleIndex j :: rhs_index_tl, expr) :: rhs_tl) 
  | ((X.ListIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ListIndex j :: rhs_index_tl, expr) :: rhs_tl) 
  | ((X.ArrayIntIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ArrayIntIndex j :: rhs_index_tl, expr) :: rhs_tl) -> 
    (* Indexes are sorted, must match *)
    if i = j then 
      expand_tuple' pos accum bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl)
    else fail_at_position pos
      "Type mismatch in equation: indexes do not match"
  (* Tuple index on left-hand and array index on right-hand side *)
  | ((X.TupleIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (X.ArrayIntIndex j :: rhs_index_tl, expr) :: rhs_tl) ->
    (* Indexes are sorted, must match *)
    if i = j then 
      (* Use tuple index instead of array index on right-hand side *)
      expand_tuple' pos accum bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((lhs_index_tl, expr) :: rhs_tl)
    else fail_at_position pos
      "Type mismatch in equation: indexes do not match"
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
    else
      fail_at_position pos
        "Type mismatch in equation: record indexes do not match"
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
  | ([], _) :: _, (_ :: _, _) :: _ -> fail_at_position pos
    "Type mismatch in equation: head indexes do not match"

(* Return a list of equations from a trie of state variables and a
  trie of expressions *)
let expand_tuple pos lhs rhs = 
  expand_tuple' pos [] []
    (List.map (fun (i, e) -> (i, e)) (X.bindings lhs))
    (List.map (fun (i, e) -> (i, e)) (X.bindings rhs))


let rec compile ctx (gids:LAN.generated_identifiers LAN.StringMap.t) (decls:LustreAst.declaration list) =
  let over_decls cstate decl = compile_declaration cstate gids ctx decl in
  let output = List.fold_left over_decls empty_compiler_state decls in
  output.nodes,
    { G.free_constants = output.free_constants;
      G.state_var_bounds = output.state_var_bounds}

and compile_ast_type (ctx:C.tc_context) cstate = function
  | A.TVar _ -> Lib.todo __LOC__
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
  | A.IntRange (pos, lbound, ubound) -> 
    (* TODO: Old code does subtyping here, currently missing *)
    (* TODO: This type should only be well-formed if bounds are constants 
      This should be done in the type checker *)
    Lib.todo __LOC__
  | A.EnumType (pos, enum_name, enum_elements) ->
      let ty = Type.mk_enum enum_name enum_elements in
      X.singleton X.empty_index ty
  | A.UserType (pos, ident) ->
    StringMap.find ident cstate.type_alias
  | A.AbstractType (pos, ident) ->
    X.singleton [X.AbstractTypeIndex ident] Type.t_int
  | A.RecordType (pos, record_fields) ->
    let over_fields = fun a (_, i, t) ->
      let over_indices = fun j t a -> X.add (X.RecordIndex i :: j) t a in
      let compiled_record_field_ty = compile_ast_type ctx cstate t in
      X.fold over_indices compiled_record_field_ty a
    in
    List.fold_left over_fields X.empty record_fields
  | A.TupleType (pos, tuple_fields) ->
    let over_fields = fun (i, a) t ->
      let over_indices = fun j t a -> X.add (X.TupleIndex i :: j) t a in
      let compiled_tuple_field_ty = compile_ast_type ctx cstate t in
      succ i, X.fold over_indices compiled_tuple_field_ty a
    in
    List.fold_left over_fields (0, X.empty) tuple_fields |> snd
  | A.GroupType _ -> assert false
      (* Lib.todo "Trying to flatten group type. Should not happen" *)
  | A.ArrayType (pos, (type_expr, size_expr)) ->
    (* TODO: Should we check that array size is constant here or later?
      If the var_size flag is set, variable sized arrays are allowed
      otherwise we should fail and make sure they are constant *)
    Lib.todo __LOC__
  | A.TArr _ -> assert false
      (* Lib.todo "Trying to flatten function type. This should not happen" *)


and compile_ast_expr
  (cstate:compiler_state)
  (ctx:C.tc_context)
  (bounds:E.expr E.bound_or_fixed list)
  (map:(StateVar.t * N.state_var_source option) LustreIdent.Hashtbl.t)
  expr = 
  
  let rec compile_id_string id_str =
    let ident = mk_ident id_str in
    try
      let _, var = List.find (fun (i, _) -> i = ident) cstate.free_constants in
      X.map E.mk_free_var var
    with Not_found ->
    try 
      let ty = Type.enum_of_constr id_str in
      X.singleton X.empty_index (E.mk_constr id_str ty)
    with Not_found ->
      let (sv, _) = H.find map ident in
      X.singleton X.empty_index (E.mk_var sv)

  and compile_mode_reference bounds path' =
    Lib.todo __LOC__

  and compile_unary bounds mk expr =
    (* TODO: Old code does a type check here *)
    X.map mk (compile_ast_expr cstate ctx bounds map expr)

  and compile_binary bounds mk expr1 expr2 =
    let expr1 = compile_ast_expr cstate ctx bounds map expr1 in
    let expr2 = compile_ast_expr cstate ctx bounds map expr2 in
    (* TODO: Old code does three error checks here doublecheck *)
    X.map2 (fun _ -> mk) expr1 expr2

  and compile_quantifier bounds mk avars expr =
    let vars_of_quant ctx avars = Lib.todo __LOC__ in
    let ctx, vars = vars_of_quant ctx avars in
    let bounds = bounds @
      List.map (fun v -> E.Unbound (E.unsafe_expr_of_term (Term.mk_var v)))
        vars in
    compile_unary bounds (E.mk_forall vars) expr

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
    let (sv, source) = H.find map ident in
    let over_indices index expr' accum =
      let expr' = E.mk_pre expr' in
      let pos = AH.pos_of_expr expr in
      if not (StateVar.is_input sv) && source == None then
        N.add_state_var_def sv (N.GeneratedEq (pos, index));
      X.add index expr' accum
    in X.fold over_indices cexpr X.empty

  and compile_merge bounds pos clock_ident merge_cases =
    Lib.todo __LOC__

  and compile_projection bounds expr x =
    Lib.todo __LOC__
  
  and compile_group_expr bounds mk expr_list =
    let over_exprs = fun (i, accum) expr ->
      let compiled_expr = compile_ast_expr cstate ctx bounds map expr in
      let over_expr = fun j e a -> X.add (mk j i) e a in
      (succ i, X.fold over_expr compiled_expr accum)
    in List.fold_left over_exprs (0, X.empty) expr_list |> snd
  
  and compile_record_expr bounds expr_list =
    Lib.todo __LOC__

  and compile_struct_update expr1 index expr2 =
    Lib.todo __LOC__

  and compile_array_ctor bounds expr size_expr =
    Lib.todo __LOC__

  and compile_array_index bounds expr i =
    Lib.todo __LOC__

  in
  (* Format.eprintf "%a\n" A.pp_print_expr expr; *)
  match expr with
  (* ****************************************************************** *)
  (* Identifiers                                                        *)
  (* ****************************************************************** *)
  | A.Ident (pos, ident) -> compile_id_string ident
  | A.ModeRef (pos, path) -> compile_mode_reference bounds path
  (* ****************************************************************** *)
  (* Constants                                                          *)
  (* ****************************************************************** *)
  | A.Const (pos, A.True) -> X.singleton X.empty_index E.t_true
  | A.Const (pos, A.False) -> X.singleton X.empty_index E.t_false
  | A.Const (pos, A.Num d) ->
    X.singleton X.empty_index (E.mk_int (Numeral.of_string d))
  | A.Const (pos, A.Dec f) ->
    X.singleton X.empty_index (E.mk_real (Decimal.of_string f))
  (* ****************************************************************** *)
  (* Unary Operators                                                    *)
  (* ****************************************************************** *)
  | A.ConvOp (pos, A.ToInt, expr) -> compile_unary bounds E.mk_to_int expr 
  | A.ConvOp (pos, A.ToUInt8, expr) -> compile_unary bounds E.mk_to_uint8 expr
  | A.ConvOp (pos, A.ToUInt16, expr) -> compile_unary bounds E.mk_to_uint16 expr
  | A.ConvOp (pos, A.ToUInt32, expr) -> compile_unary bounds E.mk_to_uint32 expr
  | A.ConvOp (pos, A.ToUInt64, expr) -> compile_unary bounds E.mk_to_uint64 expr
  | A.ConvOp (pos, A.ToInt8, expr) -> compile_unary bounds E.mk_to_int8 expr
  | A.ConvOp (pos, A.ToInt16, expr) -> compile_unary bounds E.mk_to_int16 expr
  | A.ConvOp (pos, A.ToInt32, expr) -> compile_unary bounds E.mk_to_int32 expr
  | A.ConvOp (pos, A.ToInt64, expr) -> compile_unary bounds E.mk_to_int64 expr
  | A.ConvOp (pos, A.ToReal, expr) -> compile_unary bounds E.mk_to_real expr
  | A.UnaryOp (pos, A.Not, expr) -> compile_unary bounds E.mk_not expr 
  | A.UnaryOp (pos, A.Uminus, expr) -> compile_unary bounds E.mk_uminus expr 
  | A.UnaryOp (pos, A.BVNot, expr) -> compile_unary bounds E.mk_bvnot expr
  (* ****************************************************************** *)
  (* Binary Operators                                                   *)
  (* ****************************************************************** *)
  | A.BinaryOp (pos, A.And, expr1, expr2) ->
    compile_binary bounds E.mk_and expr1 expr2
  | A.BinaryOp (pos, A.Or, expr1, expr2) ->
    compile_binary bounds E.mk_or expr1 expr2 
  | A.BinaryOp (pos, A.Xor, expr1, expr2) ->
    compile_binary bounds E.mk_xor expr1 expr2 
  | A.BinaryOp (pos, A.Impl, expr1, expr2) ->
    compile_binary bounds E.mk_impl expr1 expr2 
  | A.BinaryOp (pos, A.Mod, expr1, expr2) ->
    compile_binary bounds E.mk_mod expr1 expr2 
  | A.BinaryOp (pos, A.Minus, expr1, expr2) ->
    compile_binary bounds E.mk_minus expr1 expr2
  | A.BinaryOp (pos, A.Plus, expr1, expr2) ->
    compile_binary bounds E.mk_plus expr1 expr2
  | A.BinaryOp (pos, A.Div, expr1, expr2) ->
    compile_binary bounds E.mk_div expr1 expr2 
  | A.BinaryOp (pos, A.Times, expr1, expr2) ->
    compile_binary bounds E.mk_times expr1 expr2 
  | A.BinaryOp (pos, A.IntDiv, expr1, expr2) ->
    compile_binary bounds E.mk_intdiv expr1 expr2 
  | A.BinaryOp (pos, A.BVAnd, expr1, expr2) ->
    compile_binary bounds E.mk_bvand expr1 expr2
  | A.BinaryOp (pos, A.BVOr, expr1, expr2) ->
    compile_binary bounds E.mk_bvor expr1 expr2
  | A.BinaryOp (pos, A.BVShiftL, expr1, expr2) ->
    compile_binary bounds E.mk_bvshl expr1 expr2
  | A.BinaryOp (pos, A.BVShiftR, expr1, expr2) ->
    compile_binary bounds E.mk_bvshr expr1 expr2
  | A.CompOp (pos, A.Lte, expr1, expr2) ->
    compile_binary bounds E.mk_lte expr1 expr2 
  | A.CompOp (pos, A.Lt, expr1, expr2) ->
    compile_binary bounds E.mk_lt expr1 expr2 
  | A.CompOp (pos, A.Gte, expr1, expr2) ->
    compile_binary bounds E.mk_gte expr1 expr2 
  | A.CompOp (pos, A.Gt, expr1, expr2) ->
    compile_binary bounds E.mk_gt expr1 expr2 
  | A.Arrow (pos, expr1, expr2) ->
    compile_binary bounds E.mk_arrow expr1 expr2
  (* ****************************************************************** *)
  (* Quantifiers                                                        *)
  (* ****************************************************************** *)
  | A.Quantifier (pos, A.Forall, avars, expr) ->
    compile_quantifier bounds E.mk_forall avars expr
  | A.Quantifier (pos, A.Exists, avars, expr) ->
    compile_quantifier bounds E.mk_exists avars expr
  (* ****************************************************************** *)
  (* Other Operators                                                    *)
  (* ****************************************************************** *)
  | A.CompOp (pos, A.Eq, expr1, expr2) ->
    compile_equality bounds true expr1 expr2
  | A.CompOp (pos, A.Neq, expr1, expr2) ->
    compile_equality bounds false expr1 expr2
  | A.TernaryOp (pos, A.Ite, expr1, expr2, expr3) ->
    compile_ite bounds expr1 expr2 expr3
  | A.Last (pos, i) ->
    compile_ast_expr cstate ctx bounds map (A.Pre (pos, A.Ident (pos, i)))
  | A.Pre (pos, expr) -> compile_pre bounds expr
  | A.Merge (pos, clock_ident, merge_cases) ->
    compile_merge bounds pos clock_ident merge_cases
  (* ****************************************************************** *)
  (* Tuple and Record Operators                                         *)
  (* ****************************************************************** *)
  | A.RecordProject (pos, expr, field) ->
    compile_projection bounds expr (X.RecordIndex field)
  | A.TupleProject (pos, expr, field) ->
    compile_projection bounds expr (X.TupleIndex field)
  | A.GroupExpr (pos, A.ExprList, expr_list) ->
    let rec flatten_expr_list accum = function
      | [] -> List.rev accum
      | A.GroupExpr (pos, A.ExprList, expr_list) :: tl -> 
        flatten_expr_list accum (expr_list @ tl)
      | expr :: tl -> flatten_expr_list (expr :: accum) tl
    in let expr_list = flatten_expr_list [] expr_list in
    compile_group_expr bounds (fun j i -> X.ListIndex i :: j) expr_list
  | A.GroupExpr (pos, A.TupleExpr, expr_list) ->
    compile_group_expr bounds (fun j i -> X.TupleIndex i :: j) expr_list
  | A.RecordExpr (pos, record_type, expr_list) -> 
    compile_record_expr bounds expr_list
  | A.StructUpdate (pos, expr1, index, expr2) ->
    compile_struct_update expr1 index expr2
  (* ****************************************************************** *)
  (* Node Calls                                                         *)
  (* ****************************************************************** *)
  (* Node calls are abstracted to identifiers or group expressions by 
    the normalizer, making these expressions impossible at this stage *)
  | A.Condact (pos, cond, restart, ident, args, defaults) -> assert false
  | A.Call (pos, ident, args) -> assert false
  | A.RestartEvery (pos, ident, args, restart) -> assert false
  (* ****************************************************************** *)
  (* Array Operators                                                    *)
  (* ****************************************************************** *)
  | A.GroupExpr (pos, A.ArrayExpr, expr_list) ->
    compile_group_expr bounds (fun j i -> j @[X.ArrayIntIndex i]) expr_list
  | A.ArrayConstr (pos, expr, size_expr) ->
    compile_array_ctor bounds expr size_expr
  | A.ArrayIndex (pos, expr, i) -> compile_array_index bounds expr i
  (* ****************************************************************** *)
  (* Not Implemented                                                    *)
  (* ****************************************************************** *)
  (* TODO below, roughly in order of importance and difficulty *)
  | A.ArraySlice (pos, _, _) -> fail_at_position pos
    "Array slices not implemented"
  (* Concatenation of arrays [A|B] *)
  | A.ArrayConcat (pos, _, _) -> fail_at_position pos
    "Array concatenation not implemented"
  (* Interpolation to base clock *)
  | A.Current (pos, A.When (_, _, _)) -> fail_at_position pos
    "Current expression not supported"
  (* Boolean at-most-one constaint *)
  | A.NArityOp (pos, A.OneHot, _) -> fail_at_position pos
    "One-hot expression not supported"
  (* Followed by operator *)
  | A.Fby (pos, _, _, _) -> fail_at_position pos
    "Fby operator not implemented" 
  (* Projection on clock *)
  | A.When (pos, _, _) -> fail_at_position pos
    "When expression must be the argument of a current operator"
  (* Interpolation to base clock *)
  | A.Current (pos, _) -> fail_at_position pos
    "Current operator must have a when expression as argument"
  | A.Activate (pos, _, _, _, _) -> fail_at_position pos
    "Activate operator only supported in merge"
  (* With operator for recursive node calls *)
  | A.TernaryOp (pos, A.With, _, _, _) -> fail_at_position pos
    "Recursive nodes not supported"
  (* Node call to a parametric node *)
  | A.CallParam (pos, _, _, _) -> fail_at_position pos
    "Parametric nodes not supported" 

and compile_node pos ctx cstate map oracles outputs cond restart ident args defaults =
  let called_node = N.node_of_name ident cstate.nodes in
  let oracles = oracles
    |> List.map (fun n -> H.find map (mk_ident n) |> fst)
    |> List.combine called_node.oracles
    |> List.map (fun (sv, sv') ->
      N.set_state_var_instance sv' pos ident sv;
      sv')
  in let node_inputs_of_exprs inputs ast =
    let input_keys = X.bindings inputs in
    let result = ast
    |> List.map (fun e -> match e with
      | A.Ident(p, i) -> (p, i)
      | _ -> assert false (* enforced by normalization step *))
    |> List.map (fun (p, i) -> p, H.find map (mk_ident i) |> fst)
    |> List.rev
    |> List.combine input_keys
    |> List.fold_left
      (fun accum ((i, input_sv), (p, sv)) ->
        let i' = match i with | (X.ListIndex i)::idx -> idx | idx -> idx in 
        N.set_state_var_instance sv pos ident input_sv;
        if not (StateVar.is_input sv) then
          N.add_state_var_def sv (N.GeneratedEq (p, i'));
        X.add i sv accum)
      X.empty
    in result
  in let node_act_cond_of_expr outputs cond defaults =
    let cond_test = match cond with
      | A.Const (pos, A.True) -> true
      | _ -> false
    in if cond_test then None, None
    else
      let state_var, _ = cond |> extract_normalized |> H.find map in
      let defaults' = match defaults with
        | Some [d] -> Some (compile_ast_expr cstate ctx [] map d)
        | Some d -> Some (compile_ast_expr cstate ctx [] map
          (A.GroupExpr (dummy_pos, A.ExprList, d)))
        | None -> None
      in Some state_var, defaults'
  in let restart_cond_of_expr restart =
    let restart_test = match restart with
      | A.Const (pos, A.False) -> true
      | _ -> false
    in if restart_test then None
    else let state_var, _ = restart |> extract_normalized |> H.find map
    in Some state_var
  in let input_state_vars = node_inputs_of_exprs called_node.inputs args in
  let act_state_var, defaults = node_act_cond_of_expr called_node.outputs cond defaults in
  let restart_state_var = restart_cond_of_expr restart in
  let cond_state_var = match act_state_var, restart_state_var with
    | None, None -> []
    | Some c, None -> [N.CActivate c]
    | None, Some r -> [N.CRestart r]
    | Some c, Some r -> [N.CActivate c; N.CRestart r]
  in let node_call = {
    N.call_pos = pos;
    N.call_node_name = ident;
    N.call_cond = cond_state_var;
    N.call_inputs = input_state_vars;
    N.call_oracles = oracles;
    N.call_outputs = outputs;
    N.call_defaults = defaults
  }
  in node_call

  
and compile_node_decl gids is_function cstate ctx pos i ext inputs outputs locals items contracts =
  let name = mk_ident i in
  let node_scope = name |> I.to_scope in
  let state_var_source_map = SVM.empty in
  let is_extern = ext in
  let instance =
    StateVar.mk_state_var
      ~is_const:true
      (I.instance_ident |> I.string_of_ident false)
      (I.to_scope name @ I.reserved_scope)
      Type.t_int
  in let init_flag = 
    StateVar.mk_state_var
      (I.init_flag_ident |> I.string_of_ident false)
      (I.to_scope name @ I.reserved_scope)
      Type.t_bool
  in let ident_map = H.create 7
  (* ****************************************************************** *)
  (* Node Inputs                                                        *)
  (* ****************************************************************** *)
  in let (inputs, state_var_source_map) =
    (* TODO: The documentation on lustreNode says that a single argument
      node should have a non-list index (a singleton index), but the old
      node generation code does not seem to honor that *)
    let over_inputs = fun (compiled_input, svsm) (pos, i, ast_type, clock, is_const) ->
      match clock with
      | A.ClockTrue ->
        let n = X.top_max_index compiled_input |> succ in
        let ident = mk_ident i in
        let index_types = compile_ast_type ctx cstate ast_type in
        let over_indices = fun index index_type (accum, svsm) ->
          let state_var, svsm = mk_state_var
            ~is_input:true
            ~is_const
            (node_scope @ I.user_scope)
            ident
            index
            index_type
            (Some N.Input)
            svsm
          in let result = X.add (X.ListIndex n :: index) state_var accum
          in H.add ident_map ident (state_var, Some N.Input);
          result, svsm
        in X.fold over_indices index_types (compiled_input, svsm)
      | _ -> fail_at_position pos "Clocked node inputs not supported"
    in List.fold_left over_inputs (X.empty, state_var_source_map) inputs
  (* ****************************************************************** *)
  (* Node Outputs                                                       *)
  (* ****************************************************************** *)
  in let (outputs, state_var_source_map) =
    (* TODO: The documentation on lustreNode does not state anything about
      the requirements for indices of outputs, yet the old code makes it
      a singleton index in the event there is only one index *)
    let over_outputs = fun (is_single) (compiled_output, svsm) (pos, i, ast_type, clock) ->
      match clock with
      | A.ClockTrue ->
        let n = X.top_max_index compiled_output |> succ in
        let ident = mk_ident i in
        let index_types = compile_ast_type ctx cstate ast_type in
        let over_indices = fun index index_type (accum, svsm) ->
          let state_var, svsm = mk_state_var
            ~is_input:false
            (node_scope @ I.user_scope)
            ident
            index
            index_type
            (Some N.Output)
            svsm
          and index' = if is_single then index
            else X.ListIndex n :: index
          in let result = X.add index' state_var accum
          in H.add ident_map ident (state_var, Some N.Output);
          result, svsm
        in X.fold over_indices index_types (compiled_output, svsm)
      | _ -> fail_at_position pos "Clocked node outputs not supported"
    and is_single = List.length outputs = 1
    in List.fold_left (over_outputs is_single) (X.empty, state_var_source_map) outputs
  (* ****************************************************************** *)
  (* User Locals                                                        *)
  (* ****************************************************************** *)
  in let (locals, state_var_source_map) =
    let over_locals = fun local ->
      match local with
      | A.NodeVarDecl (_, (pos, i, ast_type, A.ClockTrue)) ->
        let ident = mk_ident i
        and index_types = compile_ast_type ctx cstate ast_type in
        let over_indices = fun index index_type (accum, svsm) ->
          let state_var, svsm = mk_state_var
            ~is_input:false
            (node_scope @ "impl" :: I.user_scope)
            ident
            index
            index_type
            (Some N.Local)
            svsm
          in let result = X.add index state_var accum
          in H.add ident_map ident (state_var, Some N.Local);
          add_state_var_bounds cstate state_var [];
          result, svsm
        in Some (X.fold over_indices index_types (X.empty, state_var_source_map))
      | A.NodeVarDecl (_, (pos, i, _, _)) -> fail_at_position pos
        (Format.asprintf
          "Clocked node local variable not supported for %a"
          A.pp_print_ident i)
      | _ -> None
    in let locals_and_sources = list_filter_map over_locals locals in
    let split = fun (sv_list, svsm') (sv, svsm) ->
      sv :: sv_list, SVM.union (fun _ v _ -> Some v) svsm svsm'
    in List.fold_left split ([], state_var_source_map) locals_and_sources
  (* ****************************************************************** *)
  (* (State Variables for) Generated Locals                             *)
  (* ****************************************************************** *)
  in let (glocals, state_var_source_map) =
    let locals_list = LAN.StringMap.bindings gids.LAN.locals in
    let over_generated_locals (glocals, svsm) (id, (expr_type, expr)) =
      let ident = mk_ident id in
      let nexpr_type = compile_ast_type ctx cstate expr_type in
      let nexpr_type' = nexpr_type |> X.values |> List.hd in
      let is_const = AH.expr_is_const expr in
      let state_var, svsm = mk_state_var
        ~is_const
        (node_scope @ I.reserved_scope)
        ident
        X.empty_index
        nexpr_type'
        None
        svsm
      in let result = X.singleton X.empty_index state_var in
      H.add ident_map ident (state_var, None);
      add_state_var_bounds cstate state_var [];
      result :: glocals, svsm
    in List.fold_left over_generated_locals
      ([], state_var_source_map)
      locals_list
  (* ****************************************************************** *)
  (* (State Variables for) Generated Locals for Node Arguments          *)
  (* ****************************************************************** *)
  in let (glocals, state_var_source_map) =
    let over_generated_locals (glocals, svsm) (id, expr_type, expr) =
      let ident = mk_ident id in
      let nexpr_type = compile_ast_type ctx cstate expr_type in
      let nexpr_type' = nexpr_type |> X.values |> List.hd in
      let is_const = AH.expr_is_const expr in
      let state_var, svsm = mk_state_var
        ~is_const
        (node_scope @ I.reserved_scope)
        ident
        X.empty_index
        nexpr_type'
        (Some N.KLocal)
        svsm
      in let result = X.singleton X.empty_index state_var in
      H.add ident_map ident (state_var, Some N.KLocal);
      add_state_var_bounds cstate state_var [];
      result :: glocals, svsm
    in List.fold_left over_generated_locals
      (glocals, state_var_source_map)
      gids.LAN.node_args
  (* ****************************************************************** *)
  (* Oracles                                                            *)
  (* ****************************************************************** *)
  in let (oracles, state_var_source_map, oracle_state_var_map) =
    let over_oracles (oracles, svsm, osvm) (id, expr) =
      let oracle_ident = mk_ident id in
      let (closed_sv, is_const, state_var_type) = match expr with
        | A.Ident (pos, id') ->
          let ident = mk_ident id' in
          let (closed_sv, _) = H.find ident_map ident in
          let is_const = StateVar.is_const closed_sv in
          let sv_type = StateVar.type_of_state_var closed_sv in
          (Some closed_sv), is_const, sv_type
        | A.Const (pos, v) -> None, true, (match v with
          | A.True | A.False -> Type.mk_bool ()
          | A.Dec _ -> Type.mk_real ()
          | A.Num _ -> Type.mk_int ())
        | _ -> assert false
      in let state_var, svsm = mk_state_var
        ~is_const:true
        (node_scope @ I.reserved_scope)
        oracle_ident
        X.empty_index
        state_var_type
        (Some N.Oracle)
        svsm
      in H.add ident_map oracle_ident (state_var, Some N.Oracle);
      add_state_var_bounds cstate state_var [];
      (match closed_sv with
        | Some sv -> SVT.add osvm state_var sv
        | None -> ());
      state_var :: oracles, svsm, osvm
    in List.fold_left over_oracles
      ([], state_var_source_map, SVT.create 7)
      gids.LAN.oracles
  (* ****************************************************************** *)
  (* Propagated Oracles                                                 *)
  (* ****************************************************************** *)
  in let (oracles, state_var_source_map) =
    let existing_oracles = cstate.nodes
      |> List.map (fun n -> n.N.oracles) 
      |> List.flatten
    in let over_propagated_oracles (oracles, svsm) (name, orc) =
      let oracle_ident = mk_ident name in
      let orc_state_var = List.find (fun o ->
        let existing_oracle_name = StateVar.name_of_state_var o
        and current_oracle_name = mk_state_var_name (mk_ident orc) X.empty_index
        in existing_oracle_name = current_oracle_name)
        existing_oracles
      in let state_var_type = StateVar.type_of_state_var orc_state_var in
      let is_const = StateVar.is_const orc_state_var in
      let state_var, svsm = mk_state_var
        ~is_input:true
        ~is_const
        (node_scope @ I.reserved_scope)
        oracle_ident
        X.empty_index
        state_var_type
        (Some N.Oracle)
        svsm
      in H.add ident_map oracle_ident (state_var, Some N.Oracle);
      add_state_var_bounds cstate state_var [];
      state_var :: oracles, svsm
    in List.fold_left over_propagated_oracles
      (oracles, state_var_source_map)
      gids.LAN.propagated_oracles
  (* ****************************************************************** *)
  (* Node Calls                                                         *)
  (* ****************************************************************** *)
  in let (calls, glocals, state_var_source_map) =
    let over_calls = fun (calls, glocals, svsm) (pos, oracles, vars, cond, restart, ident, args, defaults) ->
      let node_id = mk_ident ident in
      let called_node = N.node_of_name node_id cstate.nodes in
      let output_ast_types = (match C.lookup_node_ty ctx ident with
        | Some (A.TArr (pos, _, output_types)) ->
            (match output_types with
            | A.GroupType (_, types) -> types
            | t -> [t])
        | _ -> assert false)
      in 
      let output_types = List.map
        (fun t -> compile_ast_type ctx cstate t)
        output_ast_types
      in let is_single = List.length output_types = 1 in
      let local_map = H.create 7 in
      let source_maps = H.create 7 in
      let outputs =
        let over_vars = fun (is_single) compiled_vars (var, (i, sv)) ->
          let n = X.top_max_index compiled_vars |> succ in
          let var_id = mk_ident var in
          let index_types = List.nth output_types n in
          let over_indices = fun index index_type accum ->
            let state_var, svsm' = mk_state_var
              ~is_input:false
              (node_scope @ I.reserved_scope)
              var_id
              index
              index_type
              (Some N.Call)
              svsm
            and index' = if is_single then index else X.ListIndex n :: index
            in let result = X.add index' state_var accum in
            H.add local_map var_id state_var;
            H.add ident_map var_id (state_var, Some N.Call);
            H.add source_maps var_id svsm';
            N.add_state_var_def state_var (N.CallOutput (pos, index'));
            N.set_state_var_instance state_var pos node_id sv;
            add_state_var_bounds cstate state_var [];
            result
          in X.fold over_indices index_types compiled_vars
        in List.fold_left (over_vars is_single)
          X.empty
          (List.combine vars (X.bindings called_node.outputs))
      in let svsm' = H.fold (fun k v a -> SVM.union (fun _ v _ -> Some v) a v)
        source_maps svsm
      in let node_call = compile_node
        pos ctx cstate ident_map oracles outputs cond restart node_id args defaults
      in let glocals' = H.fold (fun k v a -> (X.singleton X.empty_index v) :: a) local_map [] in 
      node_call :: calls, glocals' @ glocals, svsm'
    in List.fold_left over_calls ([], glocals, state_var_source_map) gids.calls
  (* ****************************************************************** *)
  (* (Equations for) Generated Locals                                   *)
  (* ****************************************************************** *)
  in let (gequations, state_var_expr_map) =
    let locals_list = LAN.StringMap.bindings gids.LAN.locals in
    let over_generated_locals (geqns, svem) (id, (expr_type, expr)) =
      let ident = mk_ident id in
      let nexpr = compile_ast_expr cstate ctx [] ident_map expr in
      let nexpr' = nexpr |> X.values |> List.hd in
      let state_var, _ = H.find ident_map ident in
      let result = X.singleton X.empty_index state_var in
      let equation = expand_tuple pos result nexpr in
      SVT.add svem state_var nexpr';
      equation @ geqns, svem
    in List.fold_left over_generated_locals
      ([], SVT.create 7)
      locals_list
  (* ****************************************************************** *)
  (* (Equations for) Generated Locals for Node Arguments                *)
  (* ****************************************************************** *)
  in let (gequations, state_var_expr_map) =
    let over_generated_locals (geqns, svem) (id, _, expr) =
      let ident = mk_ident id in
      let nexpr = compile_ast_expr cstate ctx [] ident_map expr in
      let nexpr' = nexpr |> X.values |> List.hd in
      let state_var, _ = H.find ident_map ident in
      let result = X.singleton X.empty_index state_var in
      let equation = expand_tuple pos result nexpr in
      add_state_var_bounds cstate state_var [];
      SVT.add svem state_var nexpr';
      equation @ geqns, svem
    in List.fold_left over_generated_locals
      (gequations, state_var_expr_map)
      gids.LAN.node_args
  (* ****************************************************************** *)
  (* Split node items into relevant categories                          *)
  (* ****************************************************************** *)
  in let (node_props, node_eqs, node_asserts, node_automations, is_main) = 
    let over_items = fun (props, eqs, asserts, autos, is_main) (item) ->
      match item with
      | A.Body e -> (match e with
        | A.Assert (p, e) -> (props, eqs, (p, e) :: asserts, autos, is_main)
        | A.Equation (p, l, e) -> (props, (p, l, e) :: eqs, asserts, autos, is_main)
        | A.Automaton (p, s, i, r) -> (props, eqs, asserts, (p, s, i, r) :: autos, is_main))
      | A.AnnotMain flag -> (props, eqs, asserts, autos, flag || is_main)
      | A.AnnotProperty (p, n, e) -> ((p, n, e) :: props, eqs, asserts, autos, is_main) 
    in List.fold_left over_items ([], [], [], [], false) items
  (* ****************************************************************** *)
  (* Properties and Assertions                                          *)
  (* ****************************************************************** *)
  in let props =
    let op (pos, name_opt, expr) =
      let id_str = match expr with
        | A.Ident (_, id_str) -> id_str
        | _ -> assert false (* must be abstracted *)
      in let id = mk_ident id_str in
      let (sv, _) = H.find ident_map id in
      let name = match name_opt with
        | Some n -> n
        | None -> let abs = LAN.StringMap.find_opt id_str gids.LAN.locals in
          let name = match abs with | Some (_, e) -> e | None -> expr in
            Format.asprintf "@[<h>%a@]" A.pp_print_expr name
      in sv, name, (Property.PropAnnot pos)
    in List.map op node_props

  in let asserts =
    let op (pos, expr) =
      let id = extract_normalized expr in
      let (sv, _) = H.find ident_map id in
      N.add_state_var_def sv (N.Assertion pos);
      (pos, sv)
    in List.map op node_asserts
  (* ****************************************************************** *)
  (* Node Equations                                                     *)
  (* ****************************************************************** *)
  in let equations =
    let compile_struct_item = fun struct_item -> match struct_item with
      | A.SingleIdent (pos, i) ->
        let ident = mk_ident i in
        X.singleton X.empty_index (H.find ident_map ident |> fst), 0
      | A.ArrayDef (pos, i, l) ->
        let ident = mk_ident i in
        let (result, _) = H.find ident_map ident in
        (* TODO: Old code checks that array lengths between l and result match *)
        (* TODO: Old code checks that result must have at least one element *)
        (* TODO: Old code suggets that shadowing can occur here *)
        let indexes = List.length l in
        X.singleton X.empty_index result, indexes
      | A.TupleStructItem (pos, _)
      | A.TupleSelection (pos, _, _)
      | A.FieldSelection (pos, _, _)
      | A.ArraySliceStructItem (pos, _, _) ->
        fail_at_position pos "Assignment not supported"

    in let over_equations = fun eqns (pos, lhs, ast_expr) ->
      let eq_lhs, indexes = match lhs with
        | A.StructDef (pos, []) -> (X.empty, 0)
        | A.StructDef (pos, [e]) -> compile_struct_item e
        | A.StructDef (pos, l) ->
          let construct_index = fun i j e a -> X.add (X.ListIndex i :: j) e a in
          let over_items = fun (i, accum) e -> 
            let t, _ = compile_struct_item e in
              i + 1, X.fold (construct_index i) t accum
          in let i, res = List.fold_left over_items (0, X.empty) l
          in res, 0

      in let rm_array_var_index lst =
        List.filter (function
        | X.ArrayVarIndex _ -> false
        | _ -> true
        ) lst

      in let lhs_bounds = List.fold_left (fun acc (i, sv) ->
        N.add_state_var_def sv (N.ProperEq (AH.pos_of_expr ast_expr, rm_array_var_index i));
        List.fold_left (fun (acc, cpt) -> function
            | X.ArrayVarIndex b -> if cpt < indexes
              then E.Bound b :: acc, succ cpt
              else acc, cpt
            | _ -> acc, cpt
          ) (acc, 0) i
        |> fst
      ) [] (X.bindings eq_lhs)

      in let eq_rhs = compile_ast_expr cstate ctx lhs_bounds ident_map ast_expr
      in let equations = expand_tuple pos eq_lhs eq_rhs in
      (* TODO: Old code tries to infer a more strict type here
        lustreContext 2040+ *)
      equations @ eqns
    in List.fold_left over_equations [] node_eqs
  in let locals = locals @ glocals in
  let equations = equations @ gequations in
  
  (* TODO: Not currently handling contracts *)
  let contract = None
  in let silent_contracts = []

  in let (node:N.t) = { name;
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
    silent_contracts
  } in { cstate with
    nodes = node :: cstate.nodes;
  }

and compile_const_decl cstate ctx = function
  | A.FreeConst (pos, i, ty) ->
    let ident = mk_ident i in
    let cty = compile_ast_type ctx cstate ty in
    let over_index = fun i ty vt ->
      let state_var, _ = mk_state_var
        ?is_input:(Some false)
        ?is_const:(Some true)
        ?for_inv_gen:(Some true)
        I.user_scope
        ident
        i
        ty
        None
        SVM.empty
      in let v = Var.mk_const_state_var state_var in
      X.add i v vt
    in let vt = X.fold over_index cty X.empty in
    { cstate with free_constants = (ident, vt) :: cstate.free_constants }
  (* TODO: Old code does some subtyping checks for Typed constants
    Otherwise these other constants are used only for constant propagation *)
  | _ -> cstate

and compile_type_decl ctx cstate = function
  | A.AliasType (pos, ident, ltype) -> 
    let t = compile_ast_type ctx cstate ltype in
    let type_alias = StringMap.add ident t cstate.type_alias in
    { cstate with
      type_alias }
  | A.FreeType (pos, ident) -> cstate

and compile_declaration cstate gids ctx = function
  | A.TypeDecl (pos, type_rhs) -> compile_type_decl ctx cstate type_rhs
  | A.ConstDecl (pos, const_decl) -> compile_const_decl cstate ctx const_decl
  | A.FuncDecl (span, (i, ext, [], inputs, outputs, locals, items, contracts)) ->
    let pos = span.start_pos in
    let gids = LAN.StringMap.find i gids in
    compile_node_decl gids true cstate ctx pos i ext inputs outputs locals items contracts
  | A.NodeDecl (span, (i, ext, [], inputs, outputs, locals, items, contracts)) ->
    let pos = span.start_pos in
    let gids = LAN.StringMap.find i gids in
    compile_node_decl gids false cstate ctx pos i ext inputs outputs locals items contracts
  | A.ContractNodeDecl (pos, node_decl) -> Lib.todo __LOC__
  | A.NodeParamInst (pos, _)
  | A.NodeDecl (pos, _) ->
    fail_at_position pos.start_pos "Parametric nodes are not supported"
  | A.FuncDecl (pos, _) ->
    fail_at_position pos.start_pos "Parametric functions are not supported"
