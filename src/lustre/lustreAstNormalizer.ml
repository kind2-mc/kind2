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

(** Normalize a Lustre AST to ease in translation to a transition system

  The two main requirements of this normalization are to:
    1. Guard any unguarded pre expressions 
    2. Generate any needed local identifiers or oracles

  Identifiers are constructed with a numeral prefix followed by a type suffix.
  e.g. 2_glocal or 6_oracle. These are not valid lustre identifiers and are
  expected to be transformed into indexes with the numeral as a branch and the
  suffix type as the leaf.

  Generated locals/oracles are referenced inside the AST via an Ident expression
  but the actual definition is not added to the AST. Instead it is recoreded in
  the generated_identifiers record.

  pre operators are explicitly guarded in the AST by an oracle variable
  if they were originally unguarded
    e.g. pre expr => oracle -> pre expr

  The following parts of the AST are abstracted by locals:

  1. Arguments to node calls that are not identifiers
    e.g.
      Node expr1 expr2 ... exprn
      =>
      Node l1 l2 ... ln
    where each li is a local variable and li = expri

  2. Arguments to the pre operator that are not identifiers
    e.g.
      pre expr => pre l
    where l = expr

  3. Node calls
    e.g.
      x1, ..., xn = ... op node_call(a, b, c) op ...
      => x1, ..., xn = ... op (l1, ..., ln) op ...
    where (l1, ..., ln) is a group (list) expression
      and each li corresponds to an output of the node_call
      If node_call has only one output, it is instead just an ident expression
    (Note that there is no generated equality here, how the node call is
      referenced at the stage of a LustreNode is by the node_call record where
      the output holds the state variables produced by the node call)

  4. Properties checked expression
  5. Assertions checked expression
  6. Condition of node calls (if it is not equivalent to true)
  7. Restarts of node calls (if it is not a constant)

@author Andrew Marmaduke *)

open Lib
open GeneratedIdentifiers

module A = LustreAst
module NI = NodeId
module AH = LustreAstHelpers
module AIC = LustreAstInlineConstants
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

type error = [
  | `LustreAstNormalizerError
]

type warning_kind = 
  | UnguardedPreWarning of A.expr
  | UseOfAssertionWarning

let warning_message warning = match warning with
  | UnguardedPreWarning expr -> "Unguarded pre in expression " ^ A.string_of_expr expr
  | UseOfAssertionWarning ->
    "Assertions are not checked; please consider using a contract assumption instead"

let error_if_lus_strict = function
  | UnguardedPreWarning _ -> true
  | UseOfAssertionWarning -> false

type warning = [
  | `LustreAstNormalizerWarning of Lib.position * warning_kind
]

let mk_warning pos kind = `LustreAstNormalizerWarning (pos, kind)

let unwrap result = match result with
  | Ok r -> r
  | Error e ->
    let msg = LustreErrors.error_message e in
    Log.log L_debug "(Lustre AST Normalizer Internal Error: %s)" msg;
    assert false

module LocalHash = struct
  type t = A.expr
  let equal x y = (match AH.syn_expr_equal (Some 6) x y with
    | Ok true -> true
    | _ -> false)
  
  let hash = AH.hash (Some 6)
end

module LocalCache = Hashtbl.Make(LocalHash)

module NodeArgHash = struct
  type t = A.expr
  let equal x y = (match AH.syn_expr_equal None x y with
    | Ok true -> true
    | _ -> false)
  
  let hash = AH.hash (Some 6)
end

module NodeArgCache = Hashtbl.Make(NodeArgHash)

let force_fresh = true
  (*
  As of today, this flag should be true when the condition below holds
  (IVC, MCS and CONTRACTCK use modelElement which assumes it is the case)
  The flag is always set to true because it is safe to do so and in this way
  we don't need to worry about keeping the condition up-to-date:

  Flags.IVC.compute_ivc () ||
  (match Flags.enabled () with
  | modules when List.mem `MCS modules -> true
  | modules when List.mem `CONTRACTCK modules -> true
  | _ -> false
  )*)

let local_cache = LocalCache.create 20
let node_arg_cache = NodeArgCache.create 20

let clear_cache () =
  LocalCache.clear local_cache;
  NodeArgCache.clear node_arg_cache;

type info = {
  context : Ctx.tc_context;
  (* (index variable bound * Index variable type * array type) StringMap.t *)
  inductive_variables : (int option * LustreAst.lustre_type * LustreAst.lustre_type) StringMap.t;
  quantified_variables : LustreAst.typed_ident list;
  node_is_input_const : (bool list) NI.Map.t;
  contract_calls_info : LustreAst.contract_node_decl NI.Map.t;
  contract_scope : (Lib.position * NI.t) list;
  contract_ref : HString.t;
  interpretation : HString.t StringMap.t;
  local_group_projection : int;
  inlinable_funcs : LustreAst.node_decl NI.Map.t;
  call_context : LustreAst.expr list;
  inlined_expr_ctx : bool;
}

let pp_print_generated_identifiers ppf gids =
  let locals_list = StringMap.bindings gids.locals in
  let contract_calls_list = StringMap.bindings gids.contract_calls
    |> List.map (fun (x, (y, z, w)) -> x, y, z, w)
  in
  let pp_print_local ppf (id, ty) = Format.fprintf ppf "(%a, %a)"
    HString.pp_print_hstring id
    LustreAst.pp_print_lustre_type ty
  in
  let pp_print_node_arg ppf (id, b, ty, e) = Format.fprintf ppf "(%a, %b, %a, %a)"
    HString.pp_print_hstring id
    b
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_oracle ppf (id, ty, e) = Format.fprintf ppf "(%a, %a, %a)"
    HString.pp_print_hstring id
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_context ppf = function
    | Some ctx -> Format.fprintf ppf "%a" HString.pp_print_hstring ctx
    | None -> ()
  in
  let pp_print_call = (fun ppf (pos, output, cond, restart, ctx, node_id, args, defaults, inlined) ->
    Format.fprintf ppf 
      "%a: %a = call(%a,%a,(restart %a every %a)(%a),%a)%s"
      pp_print_position pos
      HString.pp_print_hstring output
      A.pp_print_expr cond
      pp_print_context ctx
      NI.pp_print_node_id_user_name node_id
      A.pp_print_expr restart
      (pp_print_list A.pp_print_expr ",@ ") args
      (pp_print_option (pp_print_list A.pp_print_expr ",@")) defaults
      (if inlined then " %inlined" else ""))
  in
  let pp_print_source ppf source = Format.fprintf ppf (match source with
    | Local -> "local"
    | Input -> "input"
    | Output -> "output"
    | Ghost -> "ghost")
  in
  let pp_print_refinement_type_constraint ppf (source, pos, id, rexpr, _) =
    Format.fprintf ppf "(%a, %a, %a, %a)"
      pp_print_source source
      Lib.pp_print_position pos
      HString.pp_print_hstring id
      A.pp_print_expr rexpr
  in
  let pp_print_empty_map ppf (id, kt, vt) =
    Format.fprintf ppf "(%a, %a, %a)"
      HString.pp_print_hstring id
      A.pp_print_lustre_type kt 
      A.pp_print_lustre_type vt
  in
  let pp_print_map_element_update ppf (id, expr1, expr2, expr3, idx, kt, vt) = 
    Format.fprintf ppf "(%a, %a, %a, %a, %a, %a, %a)" 
      HString.pp_print_hstring id 
      A.pp_print_expr expr1 
      A.pp_print_expr expr2 
      A.pp_print_expr expr3 
      HString.pp_print_hstring idx
      A.pp_print_lustre_type kt 
      A.pp_print_lustre_type vt 
  in
  let pp_print_contract_call ppf (ref, pos, scope, decl) = Format.fprintf ppf "%a := (%a, %a): %a"
    HString.pp_print_hstring ref
    pp_print_position pos
    (pp_print_list (pp_print_pair Lib.pp_print_position NI.pp_print_node_id_user_name ":") "::") scope
    (pp_print_list A.pp_print_contract_item ";") decl
  in
  let pp_print_equation ppf (_, _, lhs, expr, _) = Format.fprintf ppf "%a = %a"
  A.pp_print_eq_lhs lhs
  A.pp_print_expr expr
  in
  Format.fprintf ppf "%a\n%a\n%a\n%a\n%a\n%a\n%a\n%a\n%a\n%a\n"
    (pp_print_list pp_print_oracle "\n") gids.oracles
    (pp_print_list pp_print_local "\n") gids.ib_oracles
    (pp_print_list pp_print_node_arg "\n") gids.node_args
    (pp_print_list pp_print_local "\n") locals_list
    (pp_print_list pp_print_call "\n") gids.calls
    (pp_print_list pp_print_refinement_type_constraint "\n") gids.refinement_type_constraints
    (pp_print_list pp_print_empty_map "\n") gids.empty_maps
    (pp_print_list pp_print_map_element_update "\n") gids.map_element_updates
    (pp_print_list pp_print_contract_call "\n") contract_calls_list
    (pp_print_list pp_print_equation "\n") gids.equations

let compute_node_input_constant_mask decls =
  let over_decl map = function
  | A.NodeDecl (_, (id, _, _, _, inputs, _, _, _, _)) ->
    let is_consts = List.map (fun (_, _, _, _, c) -> c) inputs in
    NI.Map.add id is_consts map
  | FuncDecl (_, (id, _, _, _, inputs, _, _, _, _), _) ->
    let is_consts = List.map (fun (_, _, _, _, c) -> c) inputs in
    NI.Map.add id is_consts map
  | _ -> map
  in List.fold_left over_decl NI.Map.empty decls

let collect_contract_node_decls decls =
  let over_decl map = function
  | A.ContractNodeDecl (_, (id, params, inputs, outputs, equations)) ->
    NI.Map.add id (id, params, inputs, outputs, equations) map
  | _ -> map
  in List.fold_left over_decl NI.Map.empty decls


(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let contract_ref = ref 0

let dpos = Lib.dummy_pos

let union_list ids =
  List.fold_left (fun x y -> union x y ) (empty ()) ids

let record_source_expr gids normalized_expr original_expr =
  let key = HString.mk_hstring (A.string_of_expr normalized_expr) in
  { gids with expr_source_map = StringMap.add key original_expr gids.expr_source_map }

let get_inductive_vars ind_vars expr =
  let vars = AH.vars_without_node_call_ids expr in
  let ind_vars = List.map fst (StringMap.bindings ind_vars) in
  List.filter (fun x -> A.SI.mem x vars) ind_vars

let expr_has_inductive_var ind_vars expr =
  match get_inductive_vars ind_vars expr with
  | [] -> false
  | _ -> true

let new_contract_reference () =
  contract_ref := ! contract_ref + 1;
  HString.mk_hstring (string_of_int !contract_ref)

(** Build index type [0, size-1] for one dimension. Uses IntRange if size is
    concrete, RefinementType otherwise. *)
let mk_index_type pos size_expr =
    let id = HString.mk_hstring "_" in
    let zero = A.Const (pos, A.Num (HString.mk_hstring "0")) in
    let bound_var = A.Ident (pos, id) in
    let lb = A.CompOp (pos, A.Lte, zero, bound_var) in
    let ub = A.CompOp (pos, A.Lt, bound_var, size_expr) in
    A.RefinementType (pos, (pos, id, A.Int pos),
      A.BinaryOp (pos, A.And, lb, ub))

let rec index_types_of_array_type pos ty =
  match ty with
  | A.ArrayType (_, (inner_ty, size_expr)) -> (
    let r = index_types_of_array_type pos inner_ty in
    let index_ty = mk_index_type pos size_expr in
    match size_expr with 
    | A.Const (_, A.Num n) -> 
      (Some (n |> HString.string_of_hstring |> int_of_string), index_ty) :: r 
    | _ -> (None, index_ty) :: r 
    )
  | _ -> []

let generalize_to_array_expr name ind_vars expr nexpr =
  let (eq_lhs, nexpr) =
    match get_inductive_vars ind_vars expr with
    | [] ->
      A.StructDef (dpos, [SingleIdent (dpos, name)]), nexpr
    | ind_vars ->
      A.StructDef (dpos, [ArrayDef (dpos, name, ind_vars)]),
      List.fold_left (fun acc ind_var -> 
        A.IndexAccess (dpos, acc, A.Ident (dpos, ind_var), Array)  
      ) nexpr ind_vars 
  in
  eq_lhs, nexpr

let get_inline_func_expr inlinable_funcs name args =
  let (_, _, _, _, inputs, _, _, items, _) : A.node_decl =
    match NI.Map.find_opt name inlinable_funcs with
    | Some nd -> nd
    | None -> assert false
  in
  let var_map =
    items |> List.fold_left (fun acc item ->
      match item with
      | A.Body (Equation (_, StructDef (_, [lhs]), rhs)) -> (
        match lhs with
        | A.SingleIdent (_, v) ->
          (v, AH.apply_subst_in_expr acc rhs) :: acc
        | ArrayDef _ ->
          assert false (* rejected earlier in pipeline *)
        | TupleStructItem _ | TupleSelection _ | FieldSelection _
        | ArraySliceStructItem _ -> assert false (* unreachable *)
      )
      | IfBlock _ | WhenBlock _ | FrameBlock _ ->
        assert false (* desugared earlier in pipeline *)
      | Body (Assert _) | AnnotMain _ | AnnotProperty _ ->
        assert false (* rejected earlier in pipeline *)
      | A.Body (Equation (_, StructDef (_, _), _)) ->
        assert false (* rejected earlier in pipeline, should we support it? *)
    )
    []
  in
  let input_map =
    List.map2 (fun (_, id, _, _, _) e -> (id, e)) inputs args
  in
  match var_map with
  | (_, e) :: _ -> AH.apply_subst_in_expr input_map e
  | _ -> assert false

let mk_fresh_node_arg_local info pos is_const expr_type expr =
  match NodeArgCache.find_opt node_arg_cache expr with
  | Some nexpr -> nexpr, empty ()
  | None ->
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_gklocal") in
  let nexpr = A.Ident (pos, name) in
  let ind_vars = info.inductive_variables in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    node_args = [(name, is_const, expr_type, expr)];
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr, None)]; }
  in
  NodeArgCache.add node_arg_cache expr nexpr;
  nexpr, gids

let mk_fresh_dummy_index _ =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_index") in
  name

let rec mk_enum_expr ?(mk_enum=true) ctx node_id expr_type expr =
  let rec mk ctx n expr_type expr = 
    let expr_type = Chk.expand_type_syn_reftype_history ctx expr_type |> unwrap in
    match expr_type with
    | A.EnumType (_, _, values) when mk_enum -> (
      let first_value = List.hd values in
      let last_value = List.hd (List.rev values) in
      let l = A.CompOp (dpos, A.Lte, A.Ident(dpos, first_value), expr) in
      let u = A.CompOp (dpos, A.Lte, expr, A.Ident(dpos, last_value)) in
      [A.BinaryOp (dpos, A.And, l, u), true]
    )
    | A.ArrayType (_, (ty, upper_bound)) ->
      let id_str = HString.concat2 (HString.mk_hstring "x") (HString.mk_hstring (string_of_int n)) in
      let id = A.Ident (dpos, id_str) in
      let ctx = Ctx.add_ty ctx id_str (A.Int dpos) in
      let expr = A.IndexAccess (dpos, expr, id, Array) in
      let rexpr = mk ctx (succ n) ty expr in
      let l = A.CompOp (dpos, A.Lte, A.Const (dpos, A.Num (HString.mk_hstring "0")), id) in
      let u = A.CompOp (dpos, A.Lt, id, upper_bound) in
      let assumption = A.BinaryOp (dpos, A.And, l, u) in
      let var = dpos, id_str, (A.Int dpos) in
      let body = fun e -> A.BinaryOp (dpos, A.Impl, assumption, e) in
      List.map (fun (e, is_original) -> A.Quantifier (dpos, A.Forall, [var], body e), is_original) rexpr
    | TupleType (p, tys) ->
      List.mapi (fun i ty ->
         let i = i |> string_of_int |> HString.mk_hstring in
         mk ctx n ty (A.IndexAccess (dpos, expr, A.Const (p, A.Num i), A.Tuple))
      ) tys |> List.flatten
    | RecordType (_, _, tys) ->
      let mk_proj i = A.RecordProject (dpos, expr, i) in
      let tys = List.filter (fun (_, _, ty) -> Ctx.type_contains_enum ctx ty) tys in
      let tys = List.map (fun (_, i, ty) -> mk ctx n ty (mk_proj i)) tys in
      List.fold_left (@) [] tys
   | A.Set (_, kt) -> 
      let idx_str = HString.concat2 (HString.mk_hstring "x") 
                                    (HString.mk_hstring (string_of_int n)) in
      let idx = A.Ident (dpos, idx_str) in
      let ctx = Ctx.add_ty ctx idx_str kt in
      let rexpr1 = mk ctx (succ n) kt idx in
      let key_in_map = A.BinaryOp (dpos, A.In Set, idx, expr) in
      let enum_exprs = List.map fst (mk_enum_expr ctx node_id kt idx) in
      let assumption1 = List.fold_left (fun acc e ->
          A.BinaryOp (dpos, A.And, acc, e)
        ) key_in_map enum_exprs
      in
      let base_kt = Chk.expand_type_syn_reftype_history ctx kt |> Result.get_ok in 
      let var = dpos, idx_str, base_kt in
      let body = fun e a -> A.BinaryOp (dpos, A.Impl, a, e) in
      let res = 
      List.map (fun (e, _) -> 
        A.Quantifier (dpos, A.Forall, [var], body e assumption1), true
      ) rexpr1 
      in
      (*Format.fprintf Format.std_formatter "Generated constraints: %a\n"
        (Lib.pp_print_list (fun ppf (expr, b) -> 
          Format.fprintf ppf "<%a, %b>" 
            A.pp_print_expr expr b
        ) ", ") res;*)
      res
    | A.Map (_, kt, vt) -> 
      let idx_str = HString.concat2 (HString.mk_hstring "x") 
                                    (HString.mk_hstring (string_of_int n)) in
      let idx = A.Ident (dpos, idx_str) in
      let ctx = Ctx.add_ty ctx idx_str kt in
      let rexpr1 = mk ctx (succ n) kt idx in
      let rexpr2 = mk ctx (succ n) vt (A.IndexAccess (dpos, expr, idx, Map)) in
      let key_in_map = A.BinaryOp (dpos, A.In Map, idx, expr) in
      let enum_exprs = List.map fst (mk_enum_expr ctx node_id kt idx) in
      let assumption = List.fold_left (fun acc e ->
          A.BinaryOp (dpos, A.And, acc, e)
        ) key_in_map enum_exprs
      in
      let base_kt = Chk.expand_type_syn_reftype_history ctx kt |> Result.get_ok in 
      let var = dpos, idx_str, base_kt in
      let body = fun e a -> A.BinaryOp (dpos, A.Impl, a, e) in
      let res = 
      List.map (fun (e, _) -> 
        A.Quantifier (dpos, A.Forall, [var], body e assumption), true
      ) rexpr1 
      @ 
      List.map (fun (e, _) -> 
        A.Quantifier (dpos, A.Forall, [var], body e assumption), true
      ) rexpr2 in 
      (*Format.fprintf Format.std_formatter "Generated constraints: %a\n"
        (Lib.pp_print_list (fun ppf (expr, b) -> 
          Format.fprintf ppf "<%a, %b>" 
            A.pp_print_expr expr b
        ) ", ") res;*)
      res
    | _ -> []
  in
  mk ctx 0 expr_type expr

  (* `mk_ref_type_expr` translates a full nested type to refinement type expressions (i.e., 
      contract assumption and guarantee expressions),
      erasing bound variables, and does the proper handling to make sure the transformation is type correct. 
      For example, x: [subtype { y: int | P1(y) }, subtype { y: int | P2(y) }] returns two expressions, 
      P1(x[0]) and P2(x[1]). *)
and mk_ref_type_expr: Ctx.tc_context -> NodeId.t option -> A.expr -> A.lustre_type -> A.expr list
 = fun ctx node_id expr expr_type ->
  let ty = Ctx.expand_type_syn ctx expr_type in
  match ty with 
  | A.RefinementType (_, (_, id2, _), ref_expr) -> 
    (* For refinement type variable of the form x = { y: int | ... }, write the constraint
       in terms of x instead of y *)
    let expr = AH.substitute_naive id2 expr ref_expr in 
    [expr]
  | TupleType (pos, tys) 
  | GroupType (pos, tys) -> List.mapi (fun i ty ->
      let i = i |> string_of_int |> HString.mk_hstring in
      mk_ref_type_expr ctx node_id (A.IndexAccess (pos, expr, A.Const (pos, A.Num i), A.Tuple)) ty
    ) tys |> List.flatten
  | RecordType (p, _, tis) -> 
    List.map (fun (_, id2, ty) -> 
      let expr = A.RecordProject(p, expr, id2) in
      mk_ref_type_expr ctx node_id expr ty
    ) tis |> List.flatten
  | ArrayType (_, (ty, len)) -> 
    let pos = AH.pos_of_expr expr in
    let dummy_index = mk_fresh_dummy_index () in
    let exprs = mk_ref_type_expr ctx node_id (A.IndexAccess(pos, expr, Ident(pos, dummy_index), Array)) ty in
    List.map (fun expr ->
      let bound1 = 
        A.CompOp(pos, Lte, A.Const(pos, Num (HString.mk_hstring "0")), A.Ident(pos, dummy_index)) 
      in 
      let bound2 = A.CompOp(pos, Lt, A.Ident(pos, dummy_index), len) in
      let expr = A.BinaryOp(pos, Impl, A.BinaryOp(pos, And, bound1, bound2), expr) in
      A.Quantifier(pos, Forall, [pos, dummy_index, A.Int pos], expr)
    ) exprs
  | Set (_, ty) -> 
    let pos = AH.pos_of_expr expr in
    let dummy_index = mk_fresh_dummy_index () in
    let idx = A.Ident (pos, dummy_index) in
    let ctx = Ctx.add_ty ctx dummy_index ty in 
    let base_kt = Chk.expand_type_syn_reftype_history ctx ty |> Result.get_ok in 
    let exprs1 = mk_ref_type_expr ctx node_id idx ty in
    let key_in_map = A.BinaryOp (dpos, A.In Set, idx, expr) in
    let enum_exprs = List.map fst (mk_enum_expr ctx node_id ty idx) in
    let assumption1 = List.fold_left (fun acc e ->
        A.BinaryOp (dpos, A.And, acc, e)
      ) key_in_map enum_exprs
    in
    let var = dpos, dummy_index, base_kt in
    let body = fun e a -> A.BinaryOp (dpos, A.Impl, a, e) in
    List.map (fun e -> 
      A.Quantifier (dpos, A.Forall, [var], body e assumption1)
    ) exprs1
  | Map (_, kt, vt) -> 
    let pos = AH.pos_of_expr expr in
    let dummy_index = mk_fresh_dummy_index () in
    let idx = A.Ident (pos, dummy_index) in
    let ctx = Ctx.add_ty ctx dummy_index kt in 
    let base_kt = Chk.expand_type_syn_reftype_history ctx kt |> Result.get_ok in 
    let exprs1 = mk_ref_type_expr ctx node_id idx kt in
    let key_in_map = A.BinaryOp (dpos, A.In Map, idx, expr) in
    let enum_exprs = List.map fst (mk_enum_expr ctx node_id kt idx) in
    let assumption = List.fold_left (fun acc e ->
        A.BinaryOp (dpos, A.And, acc, e)
      ) key_in_map enum_exprs
    in
    let var = dpos, dummy_index, base_kt in
    let body = fun e a -> A.BinaryOp (dpos, A.Impl, a, e) in
    let exprs1 =
      List.map (fun e -> 
        A.Quantifier (dpos, A.Forall, [var], body e assumption)
      ) exprs1
    in
    let exprs2 = mk_ref_type_expr ctx node_id (A.IndexAccess(pos, expr, Ident(pos, dummy_index), Map)) vt in
    let exprs2 =
      List.map (fun (e) -> 
        A.Quantifier (dpos, A.Forall, [var], body e assumption)
      ) exprs2
    in
    exprs1 @ exprs2

  | _ -> []

let mk_enum_reftype_constraints node_id info vars =
  let enum_reftype_vars =
    vars |> List.filter (fun (_, _, ty) ->
      let ty' = Ctx.expand_type_syn info.context ty in
      Ctx.type_contains_enum_reftype info.context ty'
    )
  in
  let constraints =
    List.fold_left
      (fun acc (_, id, ty) ->
        let expr = A.Ident(dpos, id) in
        let range_exprs =
          List.map fst (mk_enum_expr info.context node_id ty expr) @
          (mk_ref_type_expr info.context node_id expr ty)
        in
        range_exprs :: acc
      )
      []
      enum_reftype_vars
    |> List.flatten
  in
  match constraints with
  | [] -> None
  | c :: cs ->
    let conj =
      List.fold_left
        (fun acc c' -> A.BinaryOp (dpos, A.And, c', acc)) c cs
    in
    Some conj

let mk_fresh_oracle expr_type expr =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_oracle") in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let gids = { (empty ()) with
    oracles = [name, expr_type, expr]; }
  in nexpr, name, gids

let mk_fresh_local force info pos ind_vars expr_type expr =
  match (LocalCache.find_opt local_cache expr, force) with
  | Some nexpr, false -> nexpr, empty ()
  | _ ->
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_glocal") in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    locals = StringMap.singleton name expr_type;
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr, None)]; }
  in
  LocalCache.add local_cache expr nexpr;
  nexpr, gids

let mk_fresh_constant pos name expr_type =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring name) in
  let nexpr = A.Ident (pos, name) in
  let gids = { (empty ()) with
    free_constants = [(name, expr_type)] }
  in
  nexpr, name, gids

let add_step_counter info =
  let dpos = Lib.dummy_pos in
  let eq_lhs = A.StructDef (dpos, [SingleIdent (dpos, ctr_id)]) in
  let expr =
    A.Arrow (dpos,
      Const (dpos, Num (HString.mk_hstring "0")),
      BinaryOp (dpos, Plus,
        Pre (dpos, Ident (dpos, ctr_id)),
        Const (dpos, Num (HString.mk_hstring "1"))
      )
    )
  in
  { (empty ()) with
    locals = StringMap.singleton ctr_id (A.Int dpos);
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr, None)]; }
(** Add local step 'counter' and an equation setting counter = 0 -> pre counter + 1 *)


(* If [expr] is already an id then we don't create a fresh local *)
let should_not_abstract info force = function
  | A.Ident (_, id) ->
    not (Ctx.is_enum_variant info.context id) && not force
  | _ -> false

let get_history_type ctx id =
  let base_ty = Ctx.lookup_ty ctx id |> get in
  let size =
    let one = A.Const (dpos, A.Num (HString.mk_hstring "1")) in
      A.BinaryOp (dpos, A.Plus, A.Ident(dpos, ctr_id), one)
    in
  A.ArrayType (dpos, (base_ty, size))


let rename_id info id =
  match StringMap.find_opt id info.interpretation with
  | Some new_id -> new_id
  | None -> id

let rename_id_expr info = function
  | A.Ident (pos, id) -> A.Ident (pos, rename_id info id)
  | _ -> assert false

let add_history_var_and_equation info id h_id =
  let ty = get_history_type info.context id in
  let locals = StringMap.singleton h_id ty in
  let equations =
    let index = HString.mk_hstring "i" in
    let eq_lhs = A.StructDef (dpos, [A.ArrayDef (dpos, h_id, [index])]) in
    let eq_rhs =
      let cond =
        A.CompOp (dpos, A.Eq, A.Ident(dpos, index), A.Ident(dpos, ctr_id))
      in
      let id = rename_id info id in
      let prev_hist =
        A.Arrow (dpos,
          A.Ident(dpos, id),
          A.IndexAccess (dpos, A.Pre (dpos, A.Ident (dpos, h_id)), A.Ident (dpos, index), Array)
        )
      in
      A.TernaryOp (dpos, A.Ite, cond, A.Ident(dpos, id), prev_hist)
    in
    [(info.quantified_variables, info.contract_scope, eq_lhs, eq_rhs, None)]
  in
  { (empty ()) with locals; equations }

let get_expr_ty info map node_id expr =
  let ty =
  let ivars = info.inductive_variables in
  if expr_has_inductive_var ivars expr then
    let _, (_, _, ty) = (StringMap.choose_opt info.inductive_variables) |> get in 
    ty 
  else
    let ctx =
      match node_id with 
      | Some node_id -> (
        (* Add generated local variables to context *)
        match NI.Map.find_opt node_id map with
        | Some { locals } ->
          StringMap.fold
            (fun id ty acc -> Ctx.add_ty acc id ty)
            locals info.context
        | None -> info.context 
      )
      | None -> info.context
    in
    Chk.infer_type_expr ctx node_id expr |> unwrap |> (fun (ty, _, _) -> ty) in
  Chk.expand_type_syn_reftype_history info.context ty |> unwrap

let normalize_list f list =
  let over_list (nitems, gids, warnings1) item =
    let (normal_item, ids, warnings2) = f item in
    normal_item :: nitems, union ids gids, warnings1 @ warnings2
  in let list, gids, warnings = List.fold_left over_list ([], empty (), []) list in
  List.rev list, gids, warnings

(** [desugar_history_in_expr c p e] desugars type constructors of
    the form history(x) occurring in [e] using [c] for the name of
    the counter variable and [p] as a prefix for the name of
    the history variables. It returns the set of variables passed as
    argument to the type constructors history and an expression that is
    the result of desugaring the type constructors ocurring in [e] *)
let desugar_history_in_expr ctx ctr_id prefix expr =
  let mk_range pos idx_id =
    A.BinaryOp (pos, And,
      CompOp (pos, Lte,
        Const (pos, Num (HString.mk_hstring "0")),
        Ident(pos, idx_id)
      ),
      CompOp (pos, Lte, Ident(pos, idx_id), Ident(pos, ctr_id))
    )
  in
  let rec r map expr =
  match expr with
  | A.Quantifier (pos, kind, idents, e) -> (
    let vars, map, idents, constrs =
      List.fold_left
        (fun (vars, map, idents, constrs) (pos, bv, ty) ->
          match ty with
          | A.History (_, i) -> (
            let hist_varid =
              HString.mk_hstring
                (Format.asprintf "%s_%a" prefix HString.pp_print_hstring i)
            in
            match kind with
            | Exists -> (
              let rng = mk_range pos bv in
              let bound_ty = A.RefinementType (pos, (pos, bv, A.Int pos), rng) in
              StringSet.add i vars,
              StringMap.add bv hist_varid map,
              (pos, bv, bound_ty) :: idents,
              constrs
            )
            | Forall -> (
              let idx_varid =
                HString.mk_hstring
                  (Format.asprintf "_idx_%a" HString.pp_print_hstring bv)
              in
              let c =
                let rng = mk_range pos idx_varid in
                let bound_ty =
                  A.RefinementType (pos, (pos, idx_varid, A.Int pos), rng)
                in
                let eq =
                  let lhs = A.Ident(pos, bv) in
                  let rhs =
                    A.IndexAccess(pos,
                      Ident(pos, hist_varid), Ident(pos, idx_varid), Array)
                  in
                  A.CompOp(pos, A.Eq, lhs, rhs)
                in
                A.Quantifier (pos, A.Exists, [(pos, idx_varid, bound_ty)], eq)
              in
              let base_ty = Ctx.lookup_ty ctx i |> get in
              StringSet.add i vars, map,
              (pos, bv, base_ty) :: idents,
              c :: constrs
            )
          )
          | _ -> vars, map, (pos, bv, ty) :: idents, constrs
        )
        (StringSet.empty, map, [], [])
        idents
    in
    let vars', e' = r map e in
    let e' =
      match constrs with
      | [] -> e'
      | [c] -> (
        match kind with
        | Exists -> A.BinaryOp(pos, And, c, e')
        | Forall -> A.BinaryOp(pos, Impl, c, e')
      )
      | _ -> (
        let conj =
          List.fold_left
            (fun acc c -> A.BinaryOp(pos, And, c, acc))
            (List.hd constrs)
            (List.tl constrs)
        in
        match kind with
        | Exists -> BinaryOp(pos, And, conj, e')
        | Forall -> BinaryOp(pos, Impl, conj, e')
      )
    in
    StringSet.union vars vars',
    Quantifier (pos, kind, List.rev idents, e')
  )
  | Ident (pos, id) -> (
    match StringMap.find_opt id map with
    | None -> StringSet.empty, expr
    | Some hist_varid ->
      StringSet.empty, IndexAccess(pos, Ident(pos, hist_varid), expr, Array)
  )
  | ModeRef _ -> StringSet.empty, expr
  | RecordProject (pos, e, idx) ->
    let vars, e' = r map e in
    vars, RecordProject (pos, e', idx)
  | Const _ -> StringSet.empty, expr
  | UnaryOp (pos, op, e) ->
    let vars, e' = r map e in
    vars, UnaryOp (pos, op, e')
  | Extract (pos, e, ub, lb) -> 
    let vars, e' = r map e in 
    vars, Extract (pos, e', ub, lb)
  | BinaryOp (pos, op, e1, e2) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    StringSet.union vars1 vars2,
    BinaryOp (pos, op, e1', e2')
  | TernaryOp (pos, op, e1, e2, e3) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    let vars3, e3' = r map e3 in
    StringSet.(vars1 |> union vars2 |> union vars3),
    TernaryOp (pos, op, e1', e2', e3')
  | ConvOp (pos, op, e) ->
    let vars, e' = r map e in
    vars, ConvOp (pos, op, e')
  | CompOp (pos, op, e1, e2) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    StringSet.union vars1 vars2,
    CompOp (pos, op, e1', e2')
  | AnyOp _ -> assert false (* desugared in lustreDesugarAnyChooseOps *)
  | ChooseOp _ -> assert false (* desugared in lustreDesugarAnyChooseOps *)
  | RecordExpr (pos, ident, ps, expr_list) ->
    let vars, expr_list' = desugar_idx_expr_list map expr_list in
    vars, RecordExpr (pos, ident, ps, expr_list')
  | GroupExpr (pos, kind, expr_list) ->
    let vars, expr_list' = desugar_expr_list map expr_list in
    vars, GroupExpr (pos, kind, expr_list')
  | StructUpdate (pos, e1, idx_list, Some e2) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    StringSet.union vars1 vars2,
    StructUpdate (pos, e1', idx_list, Some e2')
  | StructUpdate (pos, e, idx_list, None) ->
    let vars, e' = r map e in
    vars,
    StructUpdate (pos, e', idx_list, None)
  | ArrayConstr (pos, e1, e2) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    StringSet.union vars1 vars2,
    ArrayConstr (pos, e1', e2')
  | IndexAccess (pos, e1, e2, kind) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    StringSet.union vars1 vars2,
    IndexAccess (pos, e1', e2', kind)
  | When (pos, e, c) ->
    let vars, e' = r map e in
    vars, When (pos, e', c)
  | Pre (pos, e) ->
    let vars, e' = r map e in
    vars, Pre (pos, e')
  | Arrow (pos, e1, e2) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    StringSet.union vars1 vars2,
    Arrow (pos, e1', e2')
  | TypeAscription (pos, e, ty) ->
    let vars, e = r map e in
    vars, TypeAscription (pos, e, ty)
  | Call(pos, ty_args, id, expr_list) ->
    let vars, expr_list' = desugar_expr_list map expr_list in
    vars, Call(pos, ty_args, id, expr_list')
  | EmptyMap _ 
  | EmptySet _ -> StringSet.empty, expr
  | Merge (pos, ident, expr_list) ->
    let vars, expr_list' = desugar_idx_expr_list map expr_list in
    vars, Merge (pos, ident, expr_list')
  | Activate (pos, ident, e1, e2, expr_list) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    let vars3, expr_list' = desugar_expr_list map expr_list in
    StringSet.(vars1 |> union vars2 |> union vars3),
    Activate (pos, ident, e1', e2', expr_list')
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let vars1, e1' = r map e1 in
    let vars2, e2' = r map e2 in
    let vars3, expr_list1' = desugar_expr_list map expr_list1 in
    let vars4, expr_list2' = desugar_expr_list map expr_list2 in
    StringSet.(vars1 |> union vars2 |> union vars3 |> union vars4),
    Condact (pos, e1', e2', id, expr_list1', expr_list2')
  | RestartEvery (pos, ident, expr_list, e) ->
    let vars1, e' = r map e in
    let vars2, expr_list' = desugar_expr_list map expr_list in
    StringSet.union vars1 vars2,
    RestartEvery (pos, ident, expr_list', e')
  and desugar_expr_list map expr_list =
    let vars, expr_list' =
        expr_list
        |> List.map (fun e -> r map e)
        |> List.split
    in
    List.fold_left
      (fun acc vars -> StringSet.union acc vars)
      StringSet.empty
      vars,
    expr_list'
  and desugar_idx_expr_list map record_list =
    let vars, idx_exp_list' =
      record_list
      |> List.map
        (fun (i, e) -> let vars, e' = r map e in vars, (i, e'))
      |> List.split
    in
    List.fold_left
      (fun acc vars -> StringSet.union acc vars)
      StringSet.empty
      vars,
    idx_exp_list'
  in
  r StringMap.empty expr


let get_inlinable_func_decls inlinable_funcs decls =
  List.fold_left
    (fun acc decl ->
     match decl with
     | A.NodeDecl (_, nd) (* Type ascription nodes are inlinable *)
     | A.FuncDecl (_, nd, _) ->
       let (id, _, _, _, _, _, _, _, _) = nd in
       if NI.Set.mem id inlinable_funcs then
         NI.Map.add id nd acc
       else
         acc
     | _ -> acc
    )
    NI.Map.empty
    decls

let rec normalize ctx inlinable_funcs (decls:LustreAst.t) gids =
  let info = { context = ctx;
    inductive_variables = StringMap.empty;
    quantified_variables = [];
    node_is_input_const = compute_node_input_constant_mask decls;
    contract_calls_info = collect_contract_node_decls decls;
    contract_ref = HString.mk_hstring "";
    contract_scope = [];
    interpretation = StringMap.empty;
    local_group_projection = -1;
    inlinable_funcs = get_inlinable_func_decls inlinable_funcs decls;
    call_context = [];
    inlined_expr_ctx = false }
  in 
  let over_declarations (nitems, accum, warnings_accum) item =
    clear_cache ();
    let (normal_item, accum, warnings) =
      normalize_declaration info accum item in
    (match normal_item with 
      | Some ni -> ni :: nitems
      | None -> nitems),
    accum,
    warnings @ warnings_accum
  in
  let ast, map, warnings =
    List.fold_left over_declarations ([], gids, []) decls
  in
  let ast = List.rev ast in
  
  Debug.parse ("===============================================\n"
    ^^ "Generated Identifiers:\n%a\n\n"
    ^^ "Normalized lustre AST:\n%a\n"
    ^^ "===============================================\n")
    (pp_print_list
      (pp_print_pair
        NI.pp_print_node_id_user_name
        pp_print_generated_identifiers
        ":")
      "\n")
      (NI.Map.bindings map)
    A.pp_print_program ast;

  Res.ok (ast, map, warnings)

  and add_ref_type_constraints info map kind node_id vars =
  vars
  |> List.filter (fun (_, _, ty) -> 
    Ctx.type_contains_ref info.context ty)
  |> List.fold_left (fun (acc_gids, acc_w) (p, id, ty) ->
    let ty = AIC.inline_constants_of_lustre_type info.context ty in
    let gids, warnings = mk_fresh_refinement_type_constraint kind info map p node_id (A.Ident (p, id)) ty in
    union acc_gids gids, acc_w @ warnings)
    (empty (), [])

  and mk_fresh_refinement_type_constraint source info map pos node_id expr expr_type =
    let ref_type_exprs = mk_ref_type_expr info.context node_id expr expr_type in
    let gids, warnings = List.map (fun ref_type_expr ->
      i := !i + 1;
      let output_expr = AH.rename_contract_vars ref_type_expr in
      let prefix = HString.mk_hstring (string_of_int !i) in
      let name = HString.concat2 prefix (HString.mk_hstring "_reftype") in
      let nexpr = A.Ident (pos, name) in
      let (eq_lhs, _) = generalize_to_array_expr name StringMap.empty ref_type_expr nexpr in
      let ref_type_nexpr, gids1, warnings = normalize_expr info node_id map ref_type_expr in 
      let gids2 = { (empty ()) with
        refinement_type_constraints = [(source, pos, name, output_expr, node_id)];
        equations = [(info.quantified_variables, info.contract_scope, eq_lhs, ref_type_nexpr, None)]; }
      in
      union gids1 gids2, warnings 
    ) ref_type_exprs |> List.split
    in
    List.fold_left union (empty ()) gids, List.flatten warnings

(* In this function, we normalize generated identifiers that were created earlier in the pipeline. 
   It is a bit hacky with respect to how scoping is handled. More concretely, 
   because these equations were not generated within the normalizer,
   and because our identifiers are not inherently scoped, 
   we need to recover some scoping information (namely, whether or not the generated equations 
   are contract or node body equations).
   Future changes should be done carefully.
*)
  and normalize_gid_equations info gids_map (node_id : NI.t option) =
  match node_id with | None -> empty (), [] | Some node_id -> 
  match NI.Map.find_opt node_id gids_map with
  | None -> empty(), []
  | Some gids -> (
    let ctx =
      StringMap.fold
        (fun id ty acc -> Ctx.add_ty acc id ty)
        gids.locals info.context
    in
    (* Normalize all equations in gids *)
    let gids_list, warnings, eqs = List.map (fun (tis, sc, lhs, expr, source) ->
      match source with 
      (* Generated equations created during the normalization step don't need to be normalized *)
      | None ->  
         empty (), [], (tis, sc, lhs, expr, source)
      (* Generated equations created before the normalization step; we need to use the right 
         info.interpretation and info.contract_scope *)
      | Some Ghost -> 
        let nexpr, gids, warnings = normalize_expr info (Some node_id) gids_map expr in
        gids, warnings, (info.quantified_variables, info.contract_scope, lhs, nexpr, None)
      | Some _ -> 
        let info =
          { info with context = ctx; interpretation = StringMap.empty; contract_scope = [] }
        in 
        let neq, gids, warnings =
          normalize_equation info node_id gids_map (A.Equation (Lib.dummy_pos, lhs, expr))
        in
        let nexpr =
          match neq with
          | A.Equation (_, _, nexpr) -> nexpr
          | _ -> assert false
        in
        gids, warnings, (info.quantified_variables, info.contract_scope, lhs, nexpr, None)
    ) gids.equations |> Lib.split3 in

    (* Take out old equations that were not normalized *)
    let gids = { gids with equations = [] } in
    let gids = List.fold_left (fun acc g -> union g acc) gids gids_list in

    (* Keep equations generated during normalization *)
    let eqs2 = gids.equations in
    let gids = { gids with equations = eqs @ eqs2; } in
    (gids, List.flatten warnings)
  )

and normalize_declaration info map = function
  | A.NodeDecl (span, decl) ->
    let normal_decl, map, warnings = normalize_node info map decl in
    Some (A.NodeDecl(span, normal_decl)), map, warnings
  | FuncDecl (span, decl, is_rec) ->
    let normal_decl, map, warnings = normalize_node info map decl in
    Some (A.FuncDecl (span, normal_decl, is_rec)), map, warnings
  | ContractNodeDecl (_, (id, ps, ips, ops, _)) ->
    let ctx = Chk.add_io_node_ctx info.context id ps ips ops in
    let info = { info with context = ctx } in
    let ngids, warnings = normalize_gid_equations info map (Some id) in
    let map = NI.Map.add id ngids map in
    None, map, warnings
  | ConstDecl (p, FreeConst (p2, id, ty)) ->
    let ty, _, warnings = normalize_ty ~id:(Some id) info None map ty in 
    Some (A.ConstDecl (p, FreeConst (p2, id, ty))), map, warnings 
  | ConstDecl (p, TypedConst (p2, id, expr, ty)) ->
    let ty, _, warnings1 = normalize_ty ~id:(Some id) info None map ty in 
    let expr, _, warnings2 = normalize_expr info None map expr in 
    Some (A.ConstDecl (p, TypedConst (p2, id, expr, ty))), map, warnings1 @ warnings2
  | ConstDecl (p, UntypedConst (p2, id, expr)) ->
    let expr, _, warnings = normalize_expr info None map expr in 
    Some (A.ConstDecl (p, UntypedConst (p2, id, expr))), map, warnings
  | decl -> Some decl, map, []

and normalize_node_contract info (node_id : NI.t) map is_extern cref inputs outputs (id, _, ivars, ovars, body) =
  (* Normalize types *)
  let ivars, gids1, warnings1 = List.map (fun (p, id, ty, cl, c) -> 
    let ty, gids, warnings = normalize_ty ~id:(Some id) info (Some node_id) map ty in 
    (p, id, ty, cl, c), gids, warnings
  ) ivars |> Lib.split3 in
  let ovars, gids2, warnings2 = List.map (fun (p, id, ty, cl) -> 
    let ty, gids, warnings = normalize_ty ~id:(Some id) info (Some node_id) map ty in 
    (p, id, ty, cl), gids, warnings
  ) ovars |> Lib.split3 in
  let contract_ref = cref in
  let ivars_names = List.map (fun (_, id, _, _, _) -> id) ivars in
  let ovars_names = List.map (fun (_, id, _, _) -> id) ovars in
  let input_interp = List.fold_left (fun acc (i, e) ->
      StringMap.merge union_keys acc (StringMap.singleton i e))
    StringMap.empty
    (List.combine ivars_names (List.map fst inputs))
  in
  let output_interp = List.fold_left (fun acc (i, e) ->
      StringMap.merge union_keys acc (StringMap.singleton i e))
    StringMap.empty
    (List.combine ovars_names (List.map fst outputs))
  in
  let interp = StringMap.merge union_keys input_interp output_interp in
  let type_exports = Ctx.lookup_contract_exports info.context id |> get in
  let ctx = List.fold_left (fun c (id, ty) -> Ctx.add_ty c id ty)
    info.context
    (Ctx.IMap.bindings type_exports) in
  let ctx = List.fold_left (fun c (_, id, ty, _, _) -> Ctx.add_ty c id ty)
    ctx ivars in
  let ctx = List.fold_left (fun c (_, id, ty, _) -> Ctx.add_ty c id ty)
    ctx ovars in
  let info = { info with
    context = ctx;
    interpretation = interp;
    contract_ref; }
  in
  (* As an optimization we omit input and output variables for which
     we know a stronger constraint is already accounted.
     Future improvement: filter out variables based on subtyping relation
     on their types instead of equality.
  *)
  let gids3, warnings3 =
    let vars = List.map (fun (p,id,ty,_,_) -> (p,id,ty)) ivars in
    add_ref_type_constraints info map Input (Some node_id) vars
  in
  let gids4, warnings4 = 
    let vars = List.map (fun (p,id,ty,_) -> (p,id,ty)) ovars in
    add_ref_type_constraints info map Output (Some node_id) vars
  in
  let nbody, gids5, _, warnings5 = normalize_contract info node_id map is_extern ivars ovars body in
  let gids = List.fold_left union (empty ()) [union_list gids1; union_list gids2; gids3; gids4; gids5;] in
  nbody, gids, 
  List.flatten (warnings1 @ warnings2) @ warnings3 @ warnings4 @ warnings5,
  StringMap.empty

and normalize_ghost_declaration source info node_id map = function
  | A.UntypedConst (pos, id, expr) ->
    let new_id = StringMap.find id info.interpretation in
    let nexpr, gids, warnings = normalize_expr ?guard:None info (Some node_id) map expr in
    A.UntypedConst (pos, new_id, nexpr), gids, warnings
  | TypedConst (pos, id, expr, ty) ->
    let gids1, warnings1 = mk_fresh_refinement_type_constraint source info map pos (Some node_id) (A.Ident (pos, id)) ty in
    let ty, gids2, warnings2 = normalize_ty ~id:(Some id) info (Some node_id) map ty in
    let new_id = StringMap.find id info.interpretation in
    let nexpr, gids3, warnings3 = normalize_expr ?guard:None info (Some node_id) map expr in
    let gids = List.fold_left union (empty ()) [gids1; gids2; gids3;] in 
    A.TypedConst (pos, new_id, nexpr, ty), gids, warnings1 @ warnings2 @ warnings3 
  | FreeConst (pos, id, ty) -> 
    let gids1, warnings1 = mk_fresh_refinement_type_constraint source info map pos (Some node_id) (A.Ident (pos, id)) ty in
    let ty, gids2, warnings2 = normalize_ty ~id:(Some id) info (Some node_id) map ty in
    FreeConst (pos, id, ty), union gids1 gids2, warnings1 @ warnings2 

and normalize_node info map
    (node_id, is_extern, opac, params, inputs, outputs, locals, items, contract) =
  (* Setup the typing context *)
  let ctx = Chk.add_io_node_ctx info.context node_id params inputs outputs in
  let ctx = Ctx.add_ty ctx ctr_id (A.Int dpos) in
  let info = { info with context = ctx } in
  let locals, gids3, warnings3 = List.map (fun decl -> 
    match decl with 
    | A.NodeConstDecl (p1, FreeConst (p2, id, ty)) ->
      let ty, gids, warnings = normalize_ty ~id:(Some id) info (Some node_id) map ty in 
      A.NodeConstDecl (p1, FreeConst (p2, id, ty)), gids, warnings
    | A.NodeConstDecl (p1, UntypedConst (p2, id, e)) ->
      A.NodeConstDecl (p1, UntypedConst (p2, id, e)), empty (), []
    | A.NodeConstDecl (p, TypedConst (p2, id, e, ty)) -> 
      let ty, gids, warnings = normalize_ty ~id:(Some id) info (Some node_id) map ty in
      A.NodeConstDecl (p, TypedConst (p2, id, e, ty)), gids, warnings
    | A.NodeVarDecl (p1, (p2, id, ty, cl)) -> 
      let ty, gids, warnings = normalize_ty ~id:(Some id) info (Some node_id) map ty in 
      A.NodeVarDecl (p1, (p2, id, ty, cl)), gids, warnings
  ) locals |> Lib.split3 in
  (* Record refinement type constraints on inputs, outputs *)
  let gids4, warnings4 =
    let vars = List.map (fun (p,id,ty,_,_) -> (p,id,ty)) inputs in
    add_ref_type_constraints info map Input (Some node_id) vars
  in
  let gids5, warnings5 = 
    let vars = List.map (fun (p,id,ty,_) -> (p,id,ty)) outputs in
    add_ref_type_constraints info map Output (Some node_id) vars
  in
  (* Normalize types *)
  let inputs, gids1, warnings1 = List.map (fun (p, id, ty, cl, c) -> 
    let ty, gids, warnings = normalize_ty ~id:(Some id) info (Some node_id) map ty in 
    (p, id, ty, cl, c), gids, warnings
  ) inputs |> Lib.split3 in
  let outputs, gids2, warnings2 = List.map (fun (p, id, ty, cl) -> 
    let ty, gids, warnings = normalize_ty ~id:(Some id) info (Some node_id) map ty in 
    (p, id, ty, cl), gids, warnings
  ) outputs |> Lib.split3 in
  (* We have to handle contracts before locals
    Otherwise the typing contexts collide *)
  let ncontracts, gids6, interpretation, warnings6 = match contract with
    | Some contract ->
      let ctx = Chk.tc_ctx_of_contract info.context Ghost node_id contract |> unwrap |> fun (_, ctx, _) -> ctx
      in
      let contract_ref = new_contract_reference () in
      let info = { info with context = ctx; contract_ref } in
      let ncontracts, gids, interpretation, warnings =
        normalize_contract info node_id map is_extern inputs outputs contract
      in
      (Some ncontracts), gids, interpretation, warnings
    | None -> None, empty (), StringMap.empty, []
  in
  let ctx = Chk.add_local_node_ctx ctx locals in
  let info = { info with context = ctx } in
  (* Record constraints on locals *)
  let gids7, warnings7 = locals
    |> List.filter (function
      | A.NodeVarDecl (_, (_, id, _, _)) 
      | A.NodeConstDecl (_, TypedConst (_, id, _, _)) -> 
        let ty = Ctx.lookup_ty info.context id |> get in 
        let ty = Ctx.expand_type_syn info.context ty in
        Ctx.type_contains_ref ctx ty
      | A.NodeConstDecl (_, FreeConst _)
      | A.NodeConstDecl (_, UntypedConst _) -> false)
    |> List.fold_left (fun (acc_g, acc_w) l -> match l with
      | A.NodeVarDecl (p, (_, id, _, _)) 
      | A.NodeConstDecl (p, TypedConst (_, id, _, _)) ->  
        let ty = Ctx.lookup_ty info.context id |> get in 
        let ty = Ctx.expand_type_syn info.context ty in
        let ty = AIC.inline_constants_of_lustre_type info.context ty in
        let gids2, warnings2 = mk_fresh_refinement_type_constraint Local info map p (Some node_id) (A.Ident (p, id)) ty in
        union acc_g gids2, acc_w @ warnings2
      | A.NodeConstDecl (_, FreeConst _)
      | A.NodeConstDecl (_, UntypedConst _)-> assert false)
      (empty (), [])
  in
  let items =
    if Flags.check_reach () then
      items
    else (
      items |> List.filter (function
        | A.AnnotProperty (_, _, _, Reachable _) -> false
        | _ -> true
      )
    )
  in
  let exists_reachability_prop_with_bounds =
    let reachability_prop_with_bounds = function
    | A.AnnotProperty (_, _, _, Reachable (Some _)) -> true
    | _ -> false
    in
    Flags.check_reach () && List.exists reachability_prop_with_bounds items
  in
  (* Normalize equations and the contract *)
  let nitems, gids8, warnings8 = normalize_list (normalize_item info node_id map) items in
  let gids6_8 = union gids6 gids8 in
  let gids9 =
    if exists_reachability_prop_with_bounds ||
       not (StringMap.is_empty gids6_8.history_vars) then (
      add_step_counter info
    )
    else
      empty ()
  in
  let new_gids = union_list [union_list gids1; union_list gids2; union_list gids3; 
                             gids4; gids5; gids7; gids6_8; gids9] in
  let old_gids, warnings9 = normalize_gid_equations { info with interpretation = interpretation; } map (Some node_id) in
  let map = NI.Map.add node_id (union old_gids new_gids) map in
  (node_id, is_extern, opac, params, inputs, outputs, locals, List.flatten nitems, ncontracts),
  map, 
  List.flatten warnings1 @ List.flatten warnings2 @ List.flatten warnings3 
  @ warnings4 @ warnings5 @ warnings6 @ warnings7 @ warnings8 @ warnings9


and desugar_history info expr =
  let prefix = "_history" in
  let history_arg_vars, expr =
    desugar_history_in_expr info.context ctr_id prefix expr
  in
  let info, h_gids =
    StringSet.fold
      (fun id (info, gids) ->
        let name = HString.mk_hstring
          (Format.asprintf "%s_%a" prefix HString.pp_print_hstring id)
        in
        let ty = get_history_type info.context id in
        let history_vars = StringMap.singleton id name in
        {info with context = Ctx.add_ty info.context name ty},
        union gids { (empty ()) with history_vars }
      )
      history_arg_vars
      (info, empty ())
  in
  let gids =
    StringMap.fold
      (fun id h_id acc ->
        union acc (add_history_var_and_equation info id h_id)
      )
      h_gids.history_vars
      h_gids
  in
  info, gids, expr

and normalize_item info node_id map = function
  | A.Body equation ->
    let nequation, gids, warnings = normalize_equation info node_id map equation in
    [A.Body nequation], gids, warnings
  (* shouldn't be possible *)
  | IfBlock _ 
  | WhenBlock _
  | FrameBlock _ -> 
    assert false
  | AnnotMain (pos, b) -> [AnnotMain (pos, b)], empty (), []
  | AnnotProperty (pos, name, expr, k) ->
    let info, h_gids, expr = desugar_history info expr in
    let name' = Some (AH.name_of_prop pos name k) in
    let decls, gids, warnings =
      match k with
      (* expr or counter < b *) 
      | Reachable Some (From b) -> 
        let expr =
          A.BinaryOp (pos, Or, A.UnaryOp (pos, A.Not, expr), 
          A.CompOp(pos, A.Lt, Ident(dpos, ctr_id), 
                              Const (dpos, Num (HString.mk_hstring (string_of_int b)))))
        in
        let nexpr, gids, warnings = abstract_expr false info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        [A.AnnotProperty (pos, name', nexpr, k)], gids, warnings

      (* expr or counter != b *)
      | Reachable Some (At b) -> 
        let expr = 
          A.BinaryOp (pos, Or, A.UnaryOp (pos, A.Not, expr), 
          A.CompOp(pos, A.Neq, Ident(dpos, ctr_id), 
                              Const (dpos, Num (HString.mk_hstring (string_of_int b)))))
        in
        let nexpr, gids, warnings = abstract_expr false info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        [AnnotProperty (pos, name', nexpr, k)], gids, warnings

      (* expr or counter > b *)
      | Reachable Some (Within b) -> 
        let expr = 
          A.BinaryOp (pos, Or, A.UnaryOp (pos, A.Not, expr), 
          A.CompOp(pos, A.Gt, Ident(dpos, ctr_id), 
                              Const (dpos, Num (HString.mk_hstring (string_of_int b)))))
        in
        let nexpr, gids, warnings = abstract_expr false info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        [AnnotProperty (pos, name', nexpr, k)], gids, warnings
      
      (* expr or counter < b1 or counter > b2 *)
      | Reachable Some (FromWithin (b1, b2)) -> 
        let expr = 
          A.BinaryOp (pos, Or, A.UnaryOp (pos, A.Not, expr), 
          A.BinaryOp (pos, Or, 
            A.CompOp(pos, A.Lt, Ident(dpos, ctr_id), 
            Const (dpos, Num (HString.mk_hstring (string_of_int b1)))),
            A.CompOp(pos, A.Gt, Ident(dpos, ctr_id), 
                                Const (dpos, Num (HString.mk_hstring (string_of_int b2)))))
          )
        in
        let nexpr, gids, warnings = abstract_expr false info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        [AnnotProperty (pos, name', nexpr, k)], gids, warnings

      | Reachable _ -> 
        let expr = A.UnaryOp (pos, A.Not, expr) in
        let nexpr, gids, warnings = abstract_expr false info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        [AnnotProperty (pos, name', nexpr, k)], gids, warnings

      | Provided expr2 ->
        let expr1 = A.BinaryOp (pos, A.Impl, expr2, expr) in
        let nexpr1, gids1, warnings1 = abstract_expr false info (Some node_id) map expr1 in
        let inv_prop = A.AnnotProperty (pos, name', nexpr1, Invariant) in
        if Flags.check_nonvacuity () then (
          let pos' =  AH.pos_of_expr expr2 in
          let expr2 = A.UnaryOp (pos', A.Not, expr2) in
          let nexpr2, gids2, warnings2 = abstract_expr false info (Some node_id) map expr2 in
          let gids1 = record_source_expr gids1 nexpr1 expr1 in
          let gids2 = record_source_expr gids2 nexpr2 expr2 in
          let name'', gids2 = match name' with
            | Some name ->
              let name'' = HString.concat2 (HString.mk_hstring "Guard of ") name in
              Some name'', { gids2 with
                nonvacuity_props = StringSet.add name'' gids2.nonvacuity_props
              }
            | None -> None, gids2
          in
          [inv_prop; AnnotProperty (pos', name'', nexpr2, Reachable None)],
          union gids1 gids2, warnings1 @ warnings2
        )
        else (
          [inv_prop], gids1, warnings1
        )

      | _ ->
        let nexpr, gids, warnings = abstract_expr false info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        [AnnotProperty (pos, name', nexpr, k)], gids, warnings
    in
    decls, union h_gids gids, warnings



and rename_ghost_variables info contract =
  let sep = HString.mk_hstring "_contract_" in
  match contract with
  | [] -> [StringMap.empty], info
  | (A.GhostConst (UntypedConst (_, id, _))
  | GhostConst (TypedConst (_, id, _, _))) :: t ->
    let ty = Ctx.lookup_ty info.context id |> get in
    let ty = Chk.expand_type_syn_reftype_history info.context ty |> unwrap in
    let new_id = HString.concat sep [info.contract_ref;id] in
    let info = { info with context = Ctx.add_ty info.context new_id ty } in
    let tail, info = rename_ghost_variables info t in
    (StringMap.singleton id new_id) :: tail, info
  (* Recurse through each declaration one at a time *)
  | GhostVars (pos1, A.GhostVarDec(pos2, (_, id, ty)::tis), e) :: t -> 
    let ty = Chk.expand_type_syn_reftype_history info.context ty |> unwrap in
    let new_id = HString.concat sep [info.contract_ref;id] in
    let info = { info with context = Ctx.add_ty info.context new_id ty } in
    let tail, info = rename_ghost_variables info (A.GhostVars (pos1, A.GhostVarDec(pos2, tis), e) :: t) in
    (StringMap.singleton id new_id) :: tail, info
  | _ :: t -> rename_ghost_variables info t

and normalize_contract info node_id map is_extern ivars ovars (p, items) =
  let gids = ref (empty ()) in
  let warnings = ref [] in
  let result = ref [] in
  let ghost_interp, info = rename_ghost_variables info items in
  let ghost_interp = List.fold_left (StringMap.merge union_keys)
    StringMap.empty ghost_interp
  in
  let interp = StringMap.merge union_keys ghost_interp info.interpretation in
  let interpretation = ref interp in

  for j = 0 to (List.length items) - 1 do
    let info = { info with interpretation = !interpretation } in
    let item = List.nth items j in
    let nitem, gids', warnings', interpretation' = match item with
      | Assume (pos, name, soft, expr) ->
        let info, h_gids, expr = desugar_history info expr in

        let nexpr, gids, warnings = abstract_expr force_fresh info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        A.Assume (pos, name, soft, nexpr), union h_gids gids, warnings, StringMap.empty
      | Guarantee (pos, name, soft, expr) -> 
        let info, h_gids, expr = desugar_history info expr in
        let nexpr, gids, warnings = abstract_expr force_fresh info (Some node_id) map expr in
        let gids = record_source_expr gids nexpr expr in
        Guarantee (pos, name, soft, nexpr), union h_gids gids, warnings, StringMap.empty
      | Decreases (pos, expr) -> 
        Decreases (pos, expr), empty (), [], StringMap.empty
      | Mode (pos, name, requires, ensures) ->
(*         let new_name = info.contract_ref ^ "_contract_" ^ name in
        let interpretation = StringMap.singleton name new_name in
        let info = { info with interpretation } in *)
        let over_property info map (pos, name, expr) =
          let info, h_gids, expr = desugar_history info expr in
          let nexpr, gids, warnings = abstract_expr true info (Some node_id) map expr in
          let gids = record_source_expr gids nexpr expr in
          (pos, name, nexpr), union h_gids gids, warnings
        in
        let nrequires, gids1, warnings1 = normalize_list (over_property info map) requires in
        let nensures, gids2, warnings2 = normalize_list (over_property info map) ensures in
        Mode (pos, name, nrequires, nensures), union gids1 gids2, warnings1 @ warnings2, StringMap.empty
      | ContractCall (pos, name, ty_args, inputs, outputs) ->
        let ninputs, gids1, warnings1 = normalize_list (abstract_expr false info (Some node_id) map) inputs in
        let noutputs = List.map
          (fun id ->
            let ty =
              (* If output argument is an output of the caller, keep type *)
              match List.find_opt (fun (_, oid, _, _) -> HString.equal id oid) ovars with
              | None -> None
              | Some (_, _, ty, _) -> Some ty
            in
            match StringMap.find_opt id info.interpretation with
            | Some new_id -> (new_id, ty)
            | None -> (id, ty))
          outputs
        in
        let ninputs = List.map (fun e ->
          match e with
          | A.Ident (_, i) ->
            let ty =
              (* If input argument is an input of the caller, keep type *)
              match List.find_opt (fun (_, id, _, _, _) -> HString.equal i id) ivars with
              | None -> None
              | Some (_, _, ty, _, _) -> Some ty
            in
            (i, ty)
          | _ -> assert false)
          ninputs
        in
        let cref = new_contract_reference () in
        let info = { info with
            contract_scope = info.contract_scope @ [(pos, name)];
            contract_ref = cref;
          }
        in
        let called_node = NI.Map.find name info.contract_calls_info in
        let (_, normalized_call), gids2, warnings2, interp = 
          normalize_node_contract info name map is_extern cref ninputs noutputs called_node
        in
        let gids = union gids1 gids2 in
        let warnings = warnings1 @ warnings2 in
        let gids = { gids with
          contract_calls = StringMap.add info.contract_ref
            (pos, info.contract_scope, normalized_call)
            gids.contract_calls
          }
        in
        ContractCall (pos, (NI.mk_node_id cref), ty_args, inputs, outputs), gids, warnings, interp
      | GhostConst decl ->
        let ndecl, map, warnings = normalize_ghost_declaration Ghost info node_id map decl in
        GhostConst ndecl, map, warnings, StringMap.empty
      | GhostVars (pos, ((GhostVarDec (pos2, tis)) as lhs), expr) ->
        let items = match lhs with | A.GhostVarDec (_, items) -> items in
        let lhs_arity = List.length items in
        let rhs_arity = match expr with
          | A.GroupExpr(_, A.ExprList, expr_list) -> List.length expr_list
          | _ -> 1
        in
        let vars_of_calls = AH.vars_of_node_calls expr in

        (* Currently, parallel ghost variable assignment is not supported with 
          arrays (only simple typed identifiers). But, the following code with
          "has_inductive" is included because we plan on offering this functionality
          in the future.*)
          let array_sizes =
            StringMap.fold
              (fun v (size_opt, _, _) acc ->
                if A.SI.mem v vars_of_calls then
                  (v, size_opt) :: acc
                else acc
              )
              info.inductive_variables
              []
          in
          let expand =
            array_sizes <> [] &&
            array_sizes |> List.for_all (fun (_, sz) ->
              match sz with
              | Some _ -> true
              | None -> false
            )
          in
        let (nexpr, gids1, warnings), expanded = (
          if expand && lhs_arity <> rhs_arity then
            (match StringMap.choose_opt info.inductive_variables with
            | Some (ivar, (size_opt, _, _)) ->
              let size = Option.get size_opt in
              let expanded_expr = expand_node_calls_in_place info node_id ivar size expr in
              let exprs, gids, warnings = Lib.split3 (List.init lhs_arity
                (
                  fun i -> 
                  let info = { info with local_group_projection = i } in
                  normalize_expr ?guard:None info (Some node_id) map expanded_expr
                )
              ) 
              in
              let gids = List.fold_left (fun acc g -> union g acc) (empty ()) gids in
              let warnings = List.flatten warnings in
            (A.GroupExpr (dpos, A.ExprList, exprs), gids, warnings), true
            | None -> normalize_expr ?guard:None info (Some node_id) map expr, false)
            
          else if expand && lhs_arity = rhs_arity then
            let expanded_expr = List.fold_left
              (fun acc (v, (size_opt, _, _)) -> 
                let size = Option.get size_opt in
                expand_node_calls_in_place info node_id v size acc)
              expr
              (StringMap.bindings info.inductive_variables)
            in
            normalize_expr ?guard:None info (Some node_id) map expanded_expr, true
          else normalize_expr ?guard:None info (Some node_id) map expr, false
        )
        in
        let gids2 = (
          if expanded then
          let items = match lhs with | GhostVarDec (_, items) -> items in
          let ids = List.map (function (_, i, _) -> i) items
          in
          { (empty ()) with  expanded_variables = StringSet.of_list ids }
          else empty ()
        )
        in

        let tis, gids3, warnings2 = (
          let tis, gids_list, warnings = (
            List.map (
              fun (pos, i, ty) -> 
                let ty, gids1, warnings1 = normalize_ty ~id:(Some i) info (Some node_id) map ty in
                let new_id = StringMap.find i info.interpretation in
                if Ctx.type_contains_ref info.context ty then
                  let gids2, warnings2 = 
                    mk_fresh_refinement_type_constraint Ghost info map pos (Some node_id) (A.Ident (pos, new_id)) ty 
                  in
                  (pos, i, ty),
                  union gids1 gids2, 
                  warnings1 @ warnings2 
                else (pos, i, ty), gids1, []
            )
            tis |> Lib.split3
          ) in
          tis, List.fold_left union (empty ()) gids_list, List.flatten warnings
        ) in

        (* Get new identifiers for LHS *)
        let tis' = List.map (fun (p, id, ty) -> 
          (p, StringMap.find id info.interpretation, ty)
        ) tis
        in

        GhostVars (pos, GhostVarDec(pos2, tis'), nexpr), 
        union (union gids1 gids2) gids3, 
        warnings @ warnings2, 
        StringMap.empty
      
      | AssumptionVars decl ->
        AssumptionVars decl, empty (), [], StringMap.empty
    in
    interpretation := StringMap.merge union_keys !interpretation interpretation';
    result := nitem :: !result;
    gids := union !gids gids';
    warnings := !warnings @ warnings';
  done;
  (p, !result), !gids, !interpretation, !warnings


and normalize_equation info node_id map = function
  | A.Assert (pos, expr) ->
    let info, h_gids, expr = desugar_history info expr in
    let nexpr, gids, warnings = abstract_expr true info (Some node_id) map expr in
    let warnings = mk_warning pos UseOfAssertionWarning :: warnings in
    A.Assert (pos, nexpr), union h_gids gids, warnings
  | Equation (pos, lhs, expr) ->
    (* Need to track array indexes of the left hand side if there are any *)
    let items = match lhs with | A.StructDef (_, items) -> items in
    let info = List.fold_left (fun info item -> match item with
      | A.ArrayDef (pos, v, is) ->
        let ty = match Ctx.lookup_ty info.context v with
          | Some t -> t | None -> assert false
        in
        let index_types = index_types_of_array_type pos ty in
        let info = List.fold_left2
          (fun info i (_, index_ty) ->
            { info with context = Ctx.add_ty info.context i index_ty })
          info
          is
          index_types 
        in
        let ivars = List.fold_left2
          (fun m i (size_opt, index_ty) -> StringMap.add i (size_opt, index_ty, ty) m)
          StringMap.empty
          is
          index_types
        in { info with inductive_variables = ivars}
      | _ -> info)
      info
      items
    in
    let lhs_arity = List.length items in
    let rhs_arity = match expr with
      | A.GroupExpr(_, A.ExprList, expr_list) -> List.length expr_list
      | _ -> 1
    in
    let vars_of_calls = AH.vars_of_node_calls expr in
    let array_sizes =
      StringMap.fold
        (fun v (size_opt, _, _) acc ->
          if A.SI.mem v vars_of_calls then
            (v, size_opt) :: acc
          else acc
        )
        info.inductive_variables
        []
    in
    let expand =
      array_sizes <> [] &&
      array_sizes |> List.for_all (fun (_, sz) ->
        match sz with
        | Some _ -> true
        | None -> false
      )
    in
    let (nexpr, gids1, warnings), expanded = (
      if expand && lhs_arity <> rhs_arity then
        (match StringMap.choose_opt info.inductive_variables with
        | Some (ivar, (size_opt, _, _)) ->
          let size = Option.get size_opt in
          let expanded_expr = expand_node_calls_in_place info node_id ivar size expr in
          let exprs, gids, warnings = Lib.split3 (List.init lhs_arity
            (fun i -> 
              let info = { info with local_group_projection = i } in
              normalize_expr info (Some node_id) map expanded_expr))
          in
          let gids = List.fold_left (fun acc g -> union g acc) (empty ()) gids in
          let warnings = List.flatten warnings in
        (A.GroupExpr (dpos, A.ExprList, exprs), gids, warnings), true
        | None -> normalize_expr info (Some node_id) map expr, false)
      else if expand && lhs_arity = rhs_arity then
        let expanded_expr = List.fold_left
          (fun acc (v, (size_opt, _, _)) -> 
            let size = Option.get size_opt in
            expand_node_calls_in_place info node_id v size acc)
          expr
          (StringMap.bindings info.inductive_variables)
        in
        normalize_expr info (Some node_id) map expanded_expr, true
      else normalize_expr info (Some node_id) map expr, false)
    in
    let gids2 = if expanded then
      let items = match lhs with | StructDef (_, items) -> items in
      let ids = List.map (function
        | A.SingleIdent (_, i) | ArrayDef (_, i, _) -> i
        | _ -> assert false)
        items
      in
      { (empty ()) with  expanded_variables = StringSet.of_list ids }
      else empty ()
    in
    Equation (pos, lhs, nexpr), union gids1 gids2, warnings

and abstract_expr ?guard ?ty force info (node_id : NI.t option) map expr = 
  let nexpr, gids1, warnings = normalize_expr ?guard info node_id map expr in
  if should_not_abstract info force nexpr then
    nexpr, gids1, warnings
  else
    let ivars = info.inductive_variables in
    let pos = AH.pos_of_expr expr in
    let ty =
      match ty with
      | Some ty -> ty
      | None when expr_has_inductive_var ivars expr ->
        let _, (_, _, ty) = StringMap.choose_opt info.inductive_variables |> get in 
        ty
      | None ->
        Chk.infer_type_expr info.context node_id expr |> unwrap |> fun (ty, _, _) -> ty
    in
    let iexpr, gids2 = mk_fresh_local force info pos ivars ty nexpr in
    iexpr, union gids1 gids2, warnings

and mk_fresh_call ?(vmap=[]) info (id : NI.t) map pos cond restart args defaults =
  let inlined = vmap <> [] in
  let call_ctx, gids1 =
    match info.call_context with
    | [] -> None, empty ()
    | c :: cs -> (
      let conj =
        let c = if inlined then AH.apply_subst_in_expr vmap c else c in
        List.fold_left
          (fun acc c' ->
            let c' = if inlined then AH.apply_subst_in_expr vmap c' else c' in
            A.BinaryOp (dpos, A.And, c', acc))
          c cs
      in
      let nexpr, gids, warnings =
        (* `conj` is a conjunction of normalized boolean expressions.
           It may contain internal variables whose types are not present in
           the typing context, which can cause type inference to fail.
           We therefore explicitly annotate the type.
        *)
        abstract_expr ~ty:(A.Bool dummy_pos) false info (Some id) map conj
      in
      assert (warnings = []);
      match AH.id_of_expr nexpr with
      | None -> assert false
      | Some id -> Some id, gids
    )
  in
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix  (HString.mk_hstring "_call") in
  let proj = if info.local_group_projection < 0 then (HString.mk_hstring "")
    else HString.concat2
      (HString.mk_hstring (string_of_int info.local_group_projection))
      (HString.mk_hstring "proj_")
  in
  let nexpr = A.Ident (pos, HString.concat2 proj name) in
  let call = (pos, name, cond, restart, call_ctx, id, args, defaults, inlined) in
  let gids2 = { (empty ()) with calls = [call] } in
  nexpr, union gids1 gids2

and expand_node_call info node_id expr var count =
  let ty, _, _ = Chk.infer_type_expr info.context node_id expr |> unwrap in
  let mk_index i = A.Const (dpos, Num (HString.mk_hstring (string_of_int i))) in
  let expr_array = List.init count (fun i -> AH.substitute_naive var (mk_index i) expr) in
  match ty with
  | A.ArrayType _ -> A.GroupExpr (dpos, ArrayExpr, expr_array)
  | _ -> List.fold_left
    (fun acc (i, e) ->
      let pos = Lib.dummy_pos in
      let i = HString.mk_hstring (Int.to_string i) in
      let cond = A.CompOp (pos, A.Eq, A.Ident (pos, var), A.Const (pos, A.Num i)) in
      A.TernaryOp (pos, A.Ite, cond, e, acc))
    (List.nth expr_array 0)
    (List.tl (List.init count (fun i -> i, List.nth expr_array i)))

and combine_args_with_const info args flags =
  let output_arity = List.map (fun e -> match e with
    | A.Call (_, _, node_id, _) ->
      (* This node type is guaranteed to exist by type checking *)
      let node_type = Ctx.lookup_node_ty info.context node_id |> get in
      (match node_type with
      | TArr (_, _, GroupType (_, es)) -> List.length es
      | _ -> 1)
    | _ -> 1)
    args
  in
  let over_args_arity (i, acc) (e, arity) =
    if arity > 1 then
      i + arity, (e, false) :: acc
    else
      succ i, (e, List.nth flags i) :: acc
  in
  List.fold_left over_args_arity (0, []) (List.combine args output_arity)
  |> snd |> List.rev

and normalize_expr ?guard info (node_id : NI.t option) map =
  let abstract_array_literal info expr nexpr =
    let ivars = info.inductive_variables in
    let pos = AH.pos_of_expr expr in
    let ty = if expr_has_inductive_var ivars expr then
      let _, (_, _, ty) = StringMap.choose_opt info.inductive_variables |> get in 
      ty
    else 
      Chk.infer_type_expr info.context node_id expr |> unwrap |> fun (ty, _, _) -> ty in 
    let nexpr, gids = mk_fresh_local false info pos ivars ty nexpr in
    let id =
      match nexpr with
      | A.Ident (_, name) -> name
      | _ -> assert false
    in
    let gids =
      { gids with 
        array_literal_vars = StringSet.add id gids.array_literal_vars
      }
    in
    nexpr, gids
  in
  let abstract_node_arg ?guard force is_const info map expr =
    let nexpr, gids1, warnings = normalize_expr ?guard info node_id map expr in
    if should_not_abstract info force nexpr then
      nexpr, gids1, warnings
    else
      let ivars = info.inductive_variables in
      let pos = AH.pos_of_expr expr in
      let ty = if expr_has_inductive_var ivars expr then
        let _, (_, _, ty) = StringMap.choose_opt info.inductive_variables |> get in 
        ty
      else 
        Chk.infer_type_expr info.context node_id expr |> unwrap |> fun (ty, _, _) -> ty in
      let iexpr, gids2 = mk_fresh_node_arg_local info pos is_const ty nexpr in
      iexpr, union gids1 gids2, warnings
  in
  function
  (* ************************************************************************ *)
  (* Node calls                                                               *)
  (* ************************************************************************ *)
  | Call (pos, _, id, args) ->
    let is_inlinable = NI.Map.mem id info.inlinable_funcs in
    let info, vmap, gids0 =
      if is_inlinable then (* Only generate variables if inlinable *)
        let args_vars =
          List.fold_left
            (fun acc e -> A.SI.union acc (AH.vars_without_node_call_ids e))
            A.SI.empty
            args
        in
        let ind_vars = List.map 
          (fun (v, (_, ind_ty, _)) -> (Lib.dummy_pos, v, ind_ty))
          (StringMap.bindings info.inductive_variables)
        in
        List.fold_left
          (fun (info, vmap, gids) (pos_v, v, ty) ->
            if A.SI.mem v args_vars then
              let nexpr, id, gids' =
                mk_fresh_constant pos_v "_quant_arg" ty
              in
              let info =
                let ctx = Ctx.add_ty info.context id ty in
                { info with context = ctx }
              in
              (info, (v, nexpr) :: vmap, union gids gids')
            else
              (info, vmap, gids)
          )
          (info, [], (empty ()))
          (info.quantified_variables @ ind_vars)
      else
        (info, [], empty())
    in
    let handle_call vmap args =
      let flags = NI.Map.find id info.node_is_input_const in
      let cond = A.Const (Lib.dummy_pos, A.True) in
      let restart =  A.Const (Lib.dummy_pos, A.False) in
      let nargs, gids1, warnings = normalize_list
        (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
        (combine_args_with_const info args flags)
      in
      let nexpr, gids2 =
        mk_fresh_call ~vmap info id map pos cond restart nargs None
      in
      let gids2 = 
        if NI.get_node_type id = NI.TypeAscription && args <> [] then
          let original_expr = List.hd args in
          { gids2 with type_ascription_exprs = NI.Map.add id original_expr gids2.type_ascription_exprs }
        else
          gids2
      in
      nexpr, union gids1 gids2, warnings
    in
    (* Once a call is inlined, we inline the remaining calls in the body of
     * the inlined function as well. Otherwise, calls inside the inlined
     * function body may be duplicated. A check in LustreAstNormalizer ensures
     * all calls within an inlined function are inlinable.
     *)
    let call_context_has_quantified_vars =
      let quant_ids = List.map (fun (_, q, _) -> q) info.quantified_variables in
      let has_quant_vars e =
        let vars = AH.vars_without_node_call_ids e in
        List.exists (fun q -> A.SI.mem q vars) quant_ids
      in
      List.exists has_quant_vars info.call_context
    in
    let should_inline =
      vmap <> [] || info.inlined_expr_ctx ||
      (is_inlinable && call_context_has_quantified_vars)
    in
    if should_inline
    then (
      assert (is_inlinable);
      let nargs, gids1, warnings1 = normalize_list
        (fun arg -> normalize_expr ?guard info node_id map arg)
        args
      in
      let expr = get_inline_func_expr info.inlinable_funcs id nargs in
      let inlined_info = { info with inlined_expr_ctx = true } in
      let nexpr, gids2, warnings2 =
        normalize_expr ?guard inlined_info node_id map expr
      in
      if info.inlined_expr_ctx then
        nexpr, union_list [gids0; gids1; gids2], warnings1 @ warnings2
      else
        let args =
          List.map (fun a -> AH.apply_subst_in_expr vmap a) args
        in
        let _, gids3, warnings3 = handle_call vmap args in
        nexpr, union_list [gids0; gids1; gids2; gids3],
        warnings1 @ warnings2 @ warnings3
    )
    else (
      handle_call vmap args
    )
  | Condact (pos, cond, restart, id, args, defaults) ->
    let flags = NI.Map.find id info.node_is_input_const in
    let ncond, gids1, warnings1 = if AH.expr_is_true cond then cond, empty (), []
      else abstract_expr ?guard true info node_id map cond in
    let nrestart, gids2, warnings2 = if AH.expr_is_const restart then restart, empty (), []
      else abstract_expr ?guard true info node_id map restart
    in let nargs, gids3, warnings3 = normalize_list
      (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
      (combine_args_with_const info args flags)
    in
    let ndefaults, gids4, warnings4 = normalize_list (normalize_expr ?guard info node_id map) defaults in
    let nexpr, gids5 = mk_fresh_call info id map pos ncond nrestart nargs (Some ndefaults) in
    let gids = union_list [gids1; gids2; gids3; gids4; gids5] in
    let warnings = warnings1 @ warnings2 @ warnings3 @ warnings4 in
    nexpr, gids, warnings
  | RestartEvery (pos, id, args, restart) ->
    let flags = NI.Map.find id info.node_is_input_const in
    let cond = A.Const (dummy_pos, A.True) in
    let nrestart, gids1, warnings1 = if AH.expr_is_const restart then restart, empty (), []
      else abstract_expr ?guard true info node_id map restart
    in let nargs, gids2, warnings2 = normalize_list
      (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
      (combine_args_with_const info args flags)
    in
    let nexpr, gids3 = mk_fresh_call info id map pos cond nrestart nargs None in
    let gids = union_list [gids1; gids2; gids3] in
    nexpr, gids, warnings1 @ warnings2
  | Merge (pos, clock_id, cases) ->
    let normalize' info map ?guard = function
      | clock_value, A.Activate (pos, id, cond, restart, args) ->
        let flags = NI.Map.find id info.node_is_input_const in
        let ncond, gids1, warnings1 = if AH.expr_is_true cond then cond, empty (), []
          else abstract_expr ?guard false info node_id map cond in
        let nrestart, gids2 , warnings2 = if AH.expr_is_const restart then restart, empty (), []
          else abstract_expr ?guard false info node_id map restart in
        let nargs, gids3, warnings3 = normalize_list
          (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
          (combine_args_with_const info args flags)
        in
        let nexpr, gids4 = mk_fresh_call info id map pos ncond nrestart nargs None in
        let gids = union_list [gids1; gids2; gids3; gids4] in
        let warnings = warnings1 @ warnings2 @ warnings3 in
        (clock_value, nexpr), gids, warnings
      | clock_value, A.Call (pos, _, id, args) ->
        let flags = NI.Map.find id info.node_is_input_const in
        let cond_expr = match HString.string_of_hstring clock_value with
          | "true" -> A.Ident (pos, clock_id)
          | "false" -> A.UnaryOp (pos, A.Not, A.Ident (pos, clock_id))
          | _ -> A.CompOp (pos, A.Eq, A.Ident (pos, clock_id), A.Ident (pos, clock_value))
        in let ncond, gids1, warnings1 = abstract_expr ?guard false info node_id map cond_expr in
        let restart =  A.Const (Lib.dummy_pos, A.False) in
        let nargs, gids2, warnings2 = normalize_list
          (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
          (combine_args_with_const info args flags)
        in
        let nexpr, gids3 = mk_fresh_call info id map pos ncond restart nargs None in
        let gids = union_list [gids1; gids2; gids3] in
        let warnings = warnings1 @ warnings2 in
        (clock_value, nexpr), gids, warnings
      | clock_value, expr ->
        let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
        (clock_value, nexpr), gids, warnings
    in let ncases, gids, warnings = normalize_list (normalize' ?guard info map) cases in
    Merge (pos, clock_id, ncases), gids, warnings
  (* ************************************************************************ *)
  (* Guarding and abstracting pres                                            *)
  (* ************************************************************************ *)
  | Arrow (pos, expr1, expr2) ->
    let nexpr1, gids1, warnings1 = normalize_expr ?guard info node_id map expr1 in
    let nexpr2, gids2, warnings2 = normalize_expr ?guard:(Some nexpr1) info node_id map expr2 in
    let gids = union gids1 gids2 in
    let warnings = warnings1 @ warnings2 in
    Arrow (pos, nexpr1, nexpr2), gids, warnings
  | Pre (pos1, IndexAccess (pos2, expr1, expr2, kind)) ->
    let expr = A.IndexAccess (pos2, Pre (pos1, expr1), expr2, kind) in
    normalize_expr ?guard info node_id map expr
  | Pre (pos, expr) ->
    let ivars = info.inductive_variables in
    let ty, force = if expr_has_inductive_var ivars expr then
        let _, (_, _, ty) = StringMap.choose_opt info.inductive_variables |> get in 
        ty, true
      else 
        let ty, _, _ = Chk.infer_type_expr info.context node_id expr |> unwrap in 
        ty, false
      in
    let nexpr, gids1, warnings1 = abstract_expr ?guard:None force info node_id map expr in
    let guard, gids2, warnings2, previously_guarded = match guard with
      | Some guard -> guard, empty (), [], true
      | None ->
        let guard, _, gids = mk_fresh_oracle ty nexpr in
        let warnings = [mk_warning pos (UnguardedPreWarning (Pre (pos, expr)))] in
        guard, gids, warnings, false
    in
    let gids = union gids1 gids2 in
    let warnings = warnings1 @ warnings2 in
    if previously_guarded then
      let rec process_expr nexpr = 
        match nexpr with
        | A.IndexAccess (pos2, expr1, expr2, kind) ->
          A.IndexAccess (pos2, process_expr expr1, expr2, kind)
        | e -> Pre (pos, e)
      in 
      process_expr nexpr, gids, warnings
    else
      let rec process_expr nexpr = 
        match nexpr with
        | A.IndexAccess (pos2, expr1, expr2, kind) ->
          A.IndexAccess (pos2, process_expr expr1, expr2, kind)
        | e -> A.Arrow (pos, guard, Pre (pos, e))
      in 
      process_expr nexpr, gids, warnings
  (* ************************************************************************ *)
  (* Misc. abstractions                                                       *)
  (* ************************************************************************ *)
  | ArrayConstr (pos, expr, _) as e -> (
    (* Desugar v^N into a new array variable A, defined as A[i]=v *)
    let base_expr, gids1, warnings =
      normalize_expr ?guard info node_id map expr
    in
    i := !i + 1;
    let prefix = HString.mk_hstring (string_of_int !i) in
    let name = HString.concat2 prefix (HString.mk_hstring "_array_ctor") in
    let gids2 =
      let locals =
        let expr_type, _, _ =
          Chk.infer_type_expr info.context node_id e |> unwrap
        in
        StringMap.singleton name expr_type
      in
      let indices = info.inductive_variables |> StringMap.bindings |> List.map fst |> List.rev in
      match List.length indices with 
      | 1 ->
        let eq_lhs = A.StructDef (dpos, [A.ArrayDef (dpos, name, indices)]) in
        let equations =
          [(info.quantified_variables, info.contract_scope, eq_lhs, base_expr, None)]
        in
        { (empty ()) with locals; equations }
      (* Array constructors containing inductive variables in definitions of multi-dimensional 
         arrays are rejected in lustreSyntaxChecks. So if there is not exactly one index 
         variable, then the generated name does not matter. *)
      | _ -> 
        let eq_lhs = 
            A.StructDef (dpos, [A.ArrayDef (dpos, name, [HString.mk_hstring "i"])]) 
        in
        let equations =
          [(info.quantified_variables, info.contract_scope, eq_lhs, base_expr, None)]
        in
        { (empty ()) with locals; equations }
    in
    let nexpr = A.Ident (pos, name) in
    nexpr, union gids1 gids2, warnings
  )
  | GroupExpr (pos, ArrayExpr, expr_list) as expr ->
    let nexpr_list, gids1, warnings = normalize_list
      (normalize_expr ?guard:None info node_id map)
      expr_list
    in
    let nexpr = A.GroupExpr (pos, ArrayExpr, nexpr_list) in
    let nexpr, gids2 = abstract_array_literal info expr nexpr in
    nexpr, union gids1 gids2, warnings
  (* ************************************************************************ *)
  (* Variable renaming to ease handling contract scopes                       *)
  (* ************************************************************************ *)
  | Ident _ as e -> rename_id_expr info e, empty (), []
  (* ************************************************************************ *)
  (* The remaining expr kinds are all just structurally recursive             *)
  (* ************************************************************************ *)
  | ModeRef _ as expr -> expr, empty (), []
  | StructUpdate (p1, EmptyMap (p2, None), [A.MapIndex (p3, e1)], Some e2) -> 
    let kt, _, _ = Chk.infer_type_expr info.context node_id e1 |> Result.get_ok in 
    let vt, _, _ = Chk.infer_type_expr info.context node_id e2 |> Result.get_ok in 
    (* Use base types *)
    let kt = Chk.expand_type_syn_reftype_history info.context kt |> Result.get_ok in
    let vt = Chk.expand_type_syn_reftype_history info.context vt |> Result.get_ok in
    let expr = A.StructUpdate (p1, EmptyMap (p2, Some (kt, vt)), [A.MapIndex (p3, e1)], Some e2) in 
    normalize_expr ?guard info node_id map expr
  | StructUpdate (p1, EmptySet (p2, None), [A.SetIndex (p3, e)], None) ->
    let ty, _, _ = Chk.infer_type_expr info.context node_id e |> Result.get_ok in
    (* Use base types *)
    let ty = Chk.expand_type_syn_reftype_history info.context ty |> Result.get_ok in
    let expr = A.StructUpdate (p1, EmptySet (p2, Some ty), [A.SetIndex (p3, e)], None) in 
    normalize_expr ?guard info node_id map expr
  | EmptyMap (_, None) | EmptySet (_, None) -> assert false 
  | EmptySet (pos, Some ty) -> 
    i := !i + 1;
    (* Use base types *)
    let ty = Chk.expand_type_syn_reftype_history info.context ty |> Result.get_ok in
    let ty, gids1, warnings = normalize_ty info None map ty in 
    let prefix = HString.mk_hstring (string_of_int !i) in
    let name = HString.concat2 prefix (HString.mk_hstring "_empty_set") in
    let gids2 = { (empty ()) with 
      empty_sets = [ name, ty ]; 
      locals = StringMap.singleton name (A.Set (pos, ty));
    } in
    let nexpr = A.Ident (pos, name) in 
    nexpr, union gids1 gids2, warnings 
  | EmptyMap (pos, Some (kt, vt)) -> 
    i := !i + 1;
    (* Use base types *)
    let kt = Chk.expand_type_syn_reftype_history info.context kt |> Result.get_ok in
    let vt = Chk.expand_type_syn_reftype_history info.context vt |> Result.get_ok in
    let kt, gids1, warnings1 = normalize_ty info None map kt in 
    let vt, gids2, warnings2 = normalize_ty info None map vt in 
    let prefix = HString.mk_hstring (string_of_int !i) in
    let name = HString.concat2 prefix (HString.mk_hstring "_empty_map") in
    let gids3 = { (empty ()) with 
      empty_maps = [ name, kt, vt ]; 
      locals = StringMap.singleton name (A.Map (pos, kt, vt));
    } in
    let nexpr = A.Ident (pos, name) in
    nexpr, union (union gids1 gids2) gids3, warnings1 @ warnings2
  | StructUpdate (pos, expr1, [A.MapIndex (_, expr2)], Some expr3) as expr ->
    (* Don't supply the guard when normalizing subexpressions, 
       because we need to generate oracle variables in initial step 
       if there are unguarded pres *)
    let nexpr1, gids1, _ = normalize_expr info node_id map expr1 in 
    let nexpr2, gids2, _ = normalize_expr info node_id map expr2 in 
    let nexpr3, gids3, _ = normalize_expr info node_id map expr3 in 
    (* Hacky: to generate correct user-facing warnings, we call normalize_expr 
       while supplying the guard, but ignore all other outputs *)
    let _, _, warnings1 = normalize_expr ?guard info node_id map expr1 in 
    let _, _, warnings2 = normalize_expr ?guard info node_id map expr2 in 
    let _, _, warnings3 = normalize_expr ?guard info node_id map expr3 in 
    i := !i + 1; 
    let prefix = HString.mk_hstring (string_of_int !i) in 
    let name1 = HString.concat2 prefix (HString.mk_hstring "_map_update") in 
    let name2 = HString.concat2 prefix (HString.mk_hstring "_idx") in 
    let kt, vt = match Chk.infer_type_expr info.context node_id expr with 
    | Ok (A.Map (_, kt, vt), _, _) -> kt, vt 
    | _ -> assert false 
    in 
    (* Use base types *)
    let kt = Chk.expand_type_syn_reftype_history info.context kt |> Result.get_ok in
    let vt = Chk.expand_type_syn_reftype_history info.context vt |> Result.get_ok in
    let gids4 = { (empty ()) with   
      map_element_updates = [ name1, nexpr1, nexpr2, nexpr3, name2, kt, vt ]; 
      locals = StringMap.add name2 kt (StringMap.singleton name1 (A.Map (pos, kt, vt)));
    } in 
    let nexpr = A.Ident (pos, name1) in 
    let gids = List.fold_left union (empty ()) [gids1; gids2; gids3; gids4] in 
    nexpr, gids, warnings1 @ warnings2 @ warnings3 
    | StructUpdate (pos, expr1, [A.SetIndex (_, expr2)], None) as expr ->
    (* Don't supply the guard when normalizing subexpressions, 
       because we need to generate oracle variables in initial step 
       if there are unguarded pres *)
    let nexpr1, gids1, _ = normalize_expr info node_id map expr1 in 
    let nexpr2, gids2, _ = normalize_expr info node_id map expr2 in 
    (* Hacky: to generate correct user-facing warnings, we call normalize_expr 
       while supplying the guard, but ignore all other outputs *)
    let _, _, warnings1 = normalize_expr ?guard info node_id map expr1 in 
    let _, _, warnings2 = normalize_expr ?guard info node_id map expr2 in 
    i := !i + 1; 
    let prefix = HString.mk_hstring (string_of_int !i) in 
    let name1 = HString.concat2 prefix (HString.mk_hstring "_set_update") in 
    let name2 = HString.concat2 prefix (HString.mk_hstring "_idx") in 
    let ty = match Chk.infer_type_expr info.context node_id expr with 
    | Ok (A.Set (_, ty), _, _) -> ty
    | _ -> assert false 
    in 
    (* Use base types *)
    let ty = Chk.expand_type_syn_reftype_history info.context ty |> Result.get_ok in
    let gids3 = { (empty ()) with   
      set_insertions = [ name1, nexpr1, nexpr2, name2, ty ]; 
      locals = StringMap.add name2 ty (StringMap.singleton name1 (A.Set (pos, ty)));
    } in 
    let nexpr = A.Ident (pos, name1) in 
    let gids = List.fold_left union (empty ()) [gids1; gids2; gids3] in 
    nexpr, gids, warnings1 @ warnings2 

  | RecordProject (pos, expr, i) ->
    let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
    RecordProject (pos, nexpr, i), gids, warnings
  | Const _ as expr -> expr, empty (), []
  | UnaryOp (pos, op, expr) ->
    let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
    UnaryOp (pos, op, nexpr), gids, warnings
  | Extract (pos, expr, ub, lb) ->
    let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
    Extract (pos, nexpr, ub, lb), gids, warnings
  | BinaryOp (pos, AndThen, expr1, expr2) ->
    let e =
      let not_e1 = A.UnaryOp (pos, Not, expr1) in
      A.TernaryOp (pos, LazyIte, not_e1, A.Const (pos, A.False), expr2)
    in
    normalize_expr ?guard info node_id map e
  | BinaryOp (pos, OrElse, expr1, expr2) ->
    let e =
      A.TernaryOp (pos, LazyIte, expr1, A.Const (pos, A.True), expr2)
    in
    normalize_expr ?guard info node_id map e
  | BinaryOp (pos, LazyImpl, expr1, expr2) ->
    let e =
      let not_e1 = A.UnaryOp (pos, Not, expr1) in
      A.BinaryOp (pos, OrElse, not_e1, expr2)
    in
    normalize_expr ?guard info node_id map e
  | BinaryOp (pos, In Unknown, expr1, expr2) -> 
    let ty = get_expr_ty info map node_id expr2 in  
    let ty = Chk.expand_type_syn_reftype_history info.context ty |> unwrap in 
    let expr = match ty with 
    | A.Map _ -> A.BinaryOp (pos, In Map, expr1, expr2) 
    | A.Set _ -> A.BinaryOp (pos, In Set, expr1, expr2) 
    | _ -> assert false
    in 
    normalize_expr ?guard info node_id map expr
  | BinaryOp (pos, ((Plus | Times | Minus) as op), expr1, expr2) ->
    let ty, _, _ = Chk.infer_type_expr info.context node_id expr1 |> unwrap in 
    let ty = Chk.expand_type_syn_reftype_history info.context ty |> unwrap in (
    match ty, op with 
    | Set _, Plus -> 
      normalize_expr ?guard info node_id map (A.BinaryOp (pos, A.Union, expr1, expr2))
    | Set _, Times -> 
      normalize_expr ?guard info node_id map (A.BinaryOp (pos, A.Intersection, expr1, expr2))
    | Set _, Minus | Map _, Minus ->
      normalize_expr ?guard info node_id map (A.BinaryOp (pos, A.Difference, expr1, expr2))
    | _ ->  
      let nexpr1, gids1, warnings1 = normalize_expr ?guard info node_id map expr1 in
      let nexpr2, gids2, warnings2 = normalize_expr ?guard info node_id map expr2 in
      BinaryOp (pos, op, nexpr1, nexpr2), union gids1 gids2, warnings1 @ warnings2
    )
  | BinaryOp (pos, ((Union | Intersection | Difference) as op), expr1, expr2) ->
    (* Don't supply the guard when normalizing subexpressions, 
       because we need to generate oracle variables in initial step 
       if there are unguarded pres *)
    let nexpr1, gids1, _ = normalize_expr info node_id map expr1 in 
    let nexpr2, gids2, _ = normalize_expr info node_id map expr2 in 
    (* Hacky: to generate correct user-facing warnings, we call normalize_expr 
       while supplying the guard, but ignore all other outputs *)
    let _, _, warnings1 = normalize_expr ?guard info node_id map expr1 in 
    let _, _, warnings2 = normalize_expr ?guard info node_id map expr2 in 
    i := !i + 1; 
    let prefix = HString.mk_hstring (string_of_int !i) in 
    let name2 = HString.concat2 prefix (HString.mk_hstring "_idx") in 
    let ty1 = match Chk.infer_type_expr info.context node_id expr1 with 
    | Ok (ty, _, _) -> (
      match Chk.expand_type_syn_reftype_history info.context ty with 
      | Ok ty -> ty
      | _ -> assert false
    )
    | Error _ -> assert false 
    in
    (match op, ty1 with
    | A.Difference, A.Map (_, kt, vt) ->
      (* Map subtraction: remove from the map all keys contained in the set *)
      let name1 = HString.concat2 prefix (HString.mk_hstring "_map_subtraction") in
      let kt = Chk.expand_type_syn_reftype_history info.context kt |> Result.get_ok in
      let vt = Chk.expand_type_syn_reftype_history info.context vt |> Result.get_ok in
      let gids3 = { (empty ()) with
        map_subtractions = [ name1, nexpr1, nexpr2, name2, kt, vt ];
        locals = StringMap.add name2 kt (StringMap.singleton name1 (A.Map (pos, kt, vt)));
      } in
      let nexpr = A.Ident (pos, name1) in
      let gids = List.fold_left union (empty ()) [gids1; gids2; gids3] in
      nexpr, gids, warnings1 @ warnings2
    | _ ->
      let name1 = HString.concat2 prefix (HString.mk_hstring "_set_binop") in
      let ty = match ty1 with Set (_, ty) -> ty | _ -> assert false in
      let gids3 = { (empty ()) with
        set_binops = [ name1, nexpr1, nexpr2, name2, op, ty ];
        locals = StringMap.add name2 ty (StringMap.singleton name1 (A.Set (pos, ty)));
      } in
      let nexpr = A.Ident (pos, name1) in
      let gids = List.fold_left union (empty ()) [gids1; gids2; gids3] in
      nexpr, gids, warnings1 @ warnings2)
  | BinaryOp (pos, op, expr1, expr2) ->
    let nexpr1, gids1, warnings1 = normalize_expr ?guard info node_id map expr1 in
    let nexpr2, gids2, warnings2 = normalize_expr ?guard info node_id map expr2 in
    BinaryOp (pos, op, nexpr1, nexpr2), union gids1 gids2, warnings1 @ warnings2
  | TernaryOp (pos, Ite, expr1, expr2, expr3) ->
    let nexpr1, gids1, warnings1= normalize_expr ?guard info node_id map expr1 in
    let nexpr2, gids2, warnings2 = normalize_expr ?guard info node_id map expr2 in
    let nexpr3, gids3, warnings3 = normalize_expr ?guard info node_id map expr3 in
    let gids = union (union gids1 gids2) gids3 in
    let warnings = warnings1 @ warnings2 @ warnings3 in
    TernaryOp (pos, Ite, nexpr1, nexpr2, nexpr3), gids, warnings
  | TernaryOp (pos, LazyIte, expr1, expr2, expr3) ->
    let nexpr1, gids1, warnings1= normalize_expr ?guard info node_id map expr1 in
    let info2 = { info with call_context = nexpr1 :: info.call_context } in
    let nexpr2, gids2, warnings2 = normalize_expr ?guard info2 node_id map expr2 in
    let info3 = { info with call_context =
      A.UnaryOp (AH.pos_of_expr expr1, Not, nexpr1) :: info.call_context }
    in
    let nexpr3, gids3, warnings3 = normalize_expr ?guard info3 node_id map expr3 in
    let gids = union (union gids1 gids2) gids3 in
    let warnings = warnings1 @ warnings2 @ warnings3 in
    TernaryOp (pos, LazyIte, nexpr1, nexpr2, nexpr3), gids, warnings
  | ConvOp (pos, op, expr) ->
    let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
    ConvOp (pos, op, nexpr), gids, warnings
  | CompOp (pos, op, expr1, expr2) ->
    let nexpr1, gids1, warnings1 = normalize_expr ?guard info node_id map expr1 in
    let nexpr2, gids2, warnings2 = normalize_expr ?guard info node_id map expr2 in
    CompOp (pos, op, nexpr1, nexpr2), union gids1 gids2, warnings1 @ warnings2
  | TypeAscription _ -> assert false (* desugared earlier in pipeline *)
  | AnyOp _ -> assert false (* desugared earlier in pipeline *)
  | ChooseOp _ -> assert false (* desugared earlier in pipeline *)
  | RecordExpr (pos, id, ps, id_expr_list) ->
    let normalize' info map ?guard (id, expr) =
      let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
      (id, nexpr), gids, warnings
    in 
    let nid_expr_list, gids, warnings = normalize_list 
      (normalize' ?guard info map)
      id_expr_list in
    RecordExpr (pos, id, ps, nid_expr_list), gids, warnings
  | GroupExpr (pos, kind, expr_list) ->
    let nexpr_list, gids, warnings = normalize_list
      (normalize_expr ?guard info node_id map)
      expr_list in
    GroupExpr (pos, kind, nexpr_list), gids, warnings
  | StructUpdate (pos, expr1, i, expr2) ->
    let i = 
      List.map (Chk.desugar_generic_index info.context node_id expr1) i 
      |> List.map unwrap 
    in
    if List.exists (fun idx -> match idx with | A.MapIndex _ | A.SetIndex _ -> true | _ -> false) i 
      (* The MapIndex and SetIndex cases are handled specially *)
      then normalize_expr ?guard info node_id map (StructUpdate (pos, expr1, i, expr2)) 
    else 
      let nexpr1, gids1, warnings1 = normalize_expr ?guard info node_id map expr1 in
      let nexpr2, gids2, warnings2 = match expr2 with 
      | Some expr2 -> 
        let nexpr2, gids2, warnings2 = normalize_expr ?guard info node_id map expr2 in 
        Some nexpr2, gids2, warnings2
      | None -> None, empty (), [] 
      in
      StructUpdate (pos, nexpr1, i, nexpr2), union gids1 gids2, warnings1 @ warnings2
  | IndexAccess (pos, expr1, expr2, _) ->
    let expr1_ty = get_expr_ty info map node_id expr1 in 
    let nexpr1, gids1, warnings1 = normalize_expr ?guard info node_id map expr1 in
    let nexpr2, gids2, warnings2 = normalize_expr ?guard info node_id map expr2 in
    let kind' =
      match expr1_ty with
      | ArrayType _ -> A.Array
      | Map _ -> Map
      | TupleType _ -> Tuple
      | _ -> assert false
    in
    IndexAccess (pos, nexpr1, nexpr2, kind'), union gids1 gids2, warnings1 @ warnings2
  | Quantifier (pos, kind, vars, expr) ->
    let ctx = List.fold_left Ctx.union info.context
      (List.map (fun (_, i, ty) -> Ctx.singleton_ty i ty) vars)
    in
    let info = { 
      info with context = ctx;
        quantified_variables = info.quantified_variables @ vars }
    in
    let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
    List.fold_left (fun acc ((p, id, ty) as var) ->
      (* Assume constraints are constant expressions, and thus,
           no normalization is required *)
      let c = mk_enum_reftype_constraints node_id info [var] in 
      match c, kind with
      | None, _ -> A.Quantifier (pos, kind, [var], acc)
      | Some c, A.Exists -> 
        let ty = Chk.expand_type_syn_reftype_history ctx ty |> unwrap in 
        A.Quantifier (pos, kind, [p, id, ty], A.BinaryOp (pos, A.And, c, acc))
      | Some c, A.Forall -> 
        let ty = Chk.expand_type_syn_reftype_history ctx ty |> unwrap in 
        A.Quantifier (pos, kind, [p, id, ty], A.BinaryOp (pos, A.Impl, c, acc))
    ) nexpr (List.rev vars), gids, warnings
  | When (pos, expr, clock_expr) ->
    let nexpr, gids, warnings = normalize_expr ?guard info node_id map expr in
    When (pos, nexpr, clock_expr), gids, warnings
  | Activate (pos, id, expr1, expr2, expr_list) ->
    let nexpr1, gids1, warnings1 = normalize_expr ?guard info node_id map expr1 in
    let nexpr2, gids2, warnings2 = normalize_expr ?guard info node_id map expr2 in
    let nexpr_list, gids3, warnings3 = normalize_list
      (normalize_expr ?guard info node_id map)
      expr_list in
    let gids = union (union gids1 gids2) gids3 in
    let warnings = warnings1 @ warnings2 @ warnings3 in
    Activate (pos, id, nexpr1, nexpr2, nexpr_list), gids, warnings

and expand_node_calls_in_place info node_id var count expr =
  let r = expand_node_calls_in_place info node_id var count in
  match expr with
  | A.RecordProject (p, e, i) -> A.RecordProject (p, r e, i)
  | UnaryOp (p, op, e) -> A.UnaryOp (p, op, r e)
  | ConvOp (p, op, e) -> A.ConvOp (p, op, r e)
  | Quantifier (p, k, ids, e) -> A.Quantifier (p, k, ids, r e)
  | When (p, e, c) -> A.When (p, r e, c)
  | Pre (p, e) -> A.Pre (p, r e)
  | BinaryOp (p, op, e1, e2) -> A.BinaryOp (p, op, r e1, r e2)
  | CompOp (p, op, e1, e2) -> A.CompOp (p, op, r e1, r e2)
  | StructUpdate (p, e1, u, Some e2) -> A.StructUpdate (p, r e1, u, Some (r e2))
  | StructUpdate (p, e1, u, None) -> A.StructUpdate (p, r e1, u, None)
  | ArrayConstr (p, e1, e2) -> A.ArrayConstr (p, r e1, r e2)
  | IndexAccess (p, e1, e2, k) -> A.IndexAccess (p, r e1, r e2, k)
  | Arrow (p, e1, e2) -> A.Arrow (p, r e1, r e2)
  | TypeAscription (p, e, ty) -> A.TypeAscription (p, r e, ty)
  | TernaryOp (p, op, e1, e2, e3) -> A.TernaryOp (p, op, r e1, r e2, r e3)
  | GroupExpr (p, k, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    A.GroupExpr (p, k, expr_list)
  | RecordExpr (p, n, ps, expr_list) ->
    let expr_list = List.map (fun (i, e) -> (i, r e)) expr_list in
    A.RecordExpr (p, n, ps, expr_list)
  | Merge (p, n, expr_list) ->
    let expr_list = List.map (fun (i, e) -> (i, r e)) expr_list in
    A.Merge (p, n, expr_list)
  | Activate (p, n, e1, e2, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    A.Activate (p, n, r e1, r e2, expr_list)
  | Call (p, ty_args, n, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    expand_node_call info (Some node_id) (A.Call (p, ty_args, n, expr_list)) var count
  | Condact (p, e1, e2, id, expr_list1, expr_list2) ->
    let expr_list1 = List.map (fun e -> r e) expr_list1 in
    let expr_list2 = List.map (fun e -> r e) expr_list2 in
    let e = A.Condact (p, r e1, r e2, id, expr_list1, expr_list2) in
    expand_node_call info (Some node_id) e var count
  | RestartEvery (p, id, expr_list, e) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    let e = A.RestartEvery (p, id, expr_list, r e) in
    expand_node_call info (Some node_id) e var count
  | e -> e

and normalize_ty ?(guard = None) ?(id = None) info node_id map ty = 
  match ty with 
  | A.RefinementType (p1, (p2, id2, ty2), expr) -> 
    let id' = match id with 
    | Some id -> id 
    | None -> mk_fresh_dummy_index () 
    in
    let expr = AH.substitute_naive id2 (A.Ident (p1, id')) expr in
    let info = match id with 
    | Some _ -> info
    | None -> { info with context = Ctx.add_ty info.context id' ty2 }
    in 
    let info, h_gids, expr = desugar_history info expr in
    let nexpr, gids, warnings = normalize_expr info node_id map expr in
    let gids1 = union h_gids gids in
    let gids2 = match id with 
    | Some _ -> empty () 
    | None -> { gids with locals = StringMap.singleton id' ty2 } 
    in
    A.RefinementType (p1, (p2, id', ty2), nexpr), union gids1 gids2, warnings
  | TupleType (p, tys) -> 
    let tys, gids, warnings = List.map (normalize_ty ~guard ~id info node_id map) tys |> Lib.split3 in
    let gids = List.fold_left union (empty ()) gids in 
    let warnings = List.concat warnings in
    TupleType (p, tys), gids, warnings 
  | GroupType (p, tys) ->
    let tys, gids, warnings = List.map (normalize_ty ~guard ~id info node_id map) tys |> Lib.split3 in
    let gids = List.fold_left union (empty ()) gids in 
    let warnings = List.concat warnings in
    GroupType (p, tys), gids, warnings 
  | RecordType (p, id, tis) -> 
    let tis, gids, warnings = List.map (fun (p, id, ty) -> 
      let ty, gids, warnings = normalize_ty ~guard ~id:(Some id) info node_id map ty in 
      (p, id, ty), gids, warnings 
    ) tis |> Lib.split3 in 
    let gids = List.fold_left union (empty ()) gids in 
    let warnings = List.concat warnings in
    RecordType (p, id, tis), gids, warnings 
  | ArrayType (p, (ty, len)) -> 
    let ty, gids1, warnings1 = normalize_ty ~guard ~id info node_id map ty in 
    let len, gids2, warnings2  = normalize_expr ?guard info node_id  map len in 
    ArrayType (p, (ty, len)), union gids1 gids2, warnings1 @ warnings2
  | TArr (p, ty1, ty2) ->
    let ty1, gids1, warnings1 = normalize_ty ~guard ~id info node_id map ty1 in 
    let ty2, gids2, warnings2 = normalize_ty ~guard ~id info node_id map ty2 in 
    TArr (p, ty1, ty2 ), union gids1 gids2, warnings1 @ warnings2 
  | Map (p, kt, vt) -> 
    let kt, gids1, warnings1 = normalize_ty ~guard ~id info node_id map kt in 
    let vt, gids2, warnings2 = normalize_ty ~guard ~id info node_id map vt in 
    Map (p, kt, vt), union gids1 gids2, warnings1 @ warnings2 
  | Set (p, ty) -> 
    let ty, gids, warnings = normalize_ty ~guard ~id info node_id map ty in 
    Set (p, ty), gids, warnings 
  | Int _ | History _ | Bool _ | Real _  
  | UserType _ | AbstractType _ 
  | EnumType _ | SBitVector _ | UBitVector _ -> ty, empty (), []
