(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(* Desugaring of non-recursive algebraic data types (ADTs) to records.

    For each ADT declaration
      type T = C0 | C1(t1_0, t1_1) | C2(t2_0)
    we produce a discriminant enum type and an equivalent record type:
      type T_tag = C0 | C1 | C2;
      type T = { T_tag: T_tag;
                 C1_0: t1_0; C1_1: t1_1;
                 C2_0: t2_0 }
    where the enum tag field encodes the active constructor and the
    payload fields for non-selected constructors carry junk values.

    ADTTerm expressions and Match expressions are desugared during
    normalization: ADTTerm becomes a RecordExpr, and Match becomes
    a nested ITE chain on the tag field.

    This module handles the pre-pass (TypeDecl transformation and context
    update) and exports shared infrastructure used by the normalizer. *)

module LA = LustreAst
module LH = LustreAstHelpers
module Ctx = TypeCheckerContext
module HStringMap = HString.HStringMap

type adt_info = {
  type_name : HString.t;

  (* type parameters of the ADT declaration (for polymorphic ADTs) *)
  type_params : HString.t list;

  (* name of the tag field in the record *)
  disc_field : HString.t;

  (* name of the generated enum type for the discriminant *)
  disc_enum : HString.t;

  (* ordered list of constructor names, also used as enum variant names *)
  ctor_variants : HString.t list;

  (* constructor name -> ordered list of (payload_field_name, field_type) *)
  ctor_fields : (HString.t * LA.lustre_type) list HStringMap.t;

  (* all payload fields across all constructors, in declaration order,
     deduplicated by field name *)
  all_payload_fields : (HString.t * LA.lustre_type) list;
}

type adt_map = adt_info HStringMap.t

let disc_field_name type_name =
  HString.mk_hstring (HString.string_of_hstring type_name ^ "_tag")

let payload_field_name_of ctor user_fname =
  HString.mk_hstring (HString.string_of_hstring ctor ^ "_" ^ HString.string_of_hstring user_fname)

let build_adt_info type_name type_params ctors =
  let disc_field = disc_field_name type_name in
  let disc_enum = disc_field_name type_name in
  let ctor_variants = List.map fst ctors in
  let ctor_fields =
    List.fold_left (fun m (ctor, fields) ->
      let named_fields =
        List.map (fun (user_fname, ty) -> (payload_field_name_of ctor user_fname, ty)) fields
      in
      HStringMap.add ctor named_fields m
    ) HStringMap.empty ctors
  in
  let all_payload_fields =
    List.concat_map (fun (ctor, _) -> HStringMap.find ctor ctor_fields) ctors
  in
  { type_name; type_params; disc_field; disc_enum; ctor_variants; ctor_fields; all_payload_fields }

(* Collect all ADT type declarations from a program into an adt_map. *)
let build_adt_map decls =
  List.fold_left (fun m decl ->
    match decl with
    | LA.TypeDecl (_, LA.AliasType (_, name, ty_params, LA.ADT (_, _, ctors))) ->
      HStringMap.add name (build_adt_info name ty_params ctors) m
    | _ -> m
  ) HStringMap.empty decls

let record_type_of_adt pos ?(ty_args = []) info =
  let subst =
    if List.length info.type_params = List.length ty_args
    then List.combine info.type_params ty_args
    else []
  in
  let disc_fld = (pos, info.disc_field, LA.UserType (pos, [], info.disc_enum)) in
  let payload_flds =
    List.map (fun (fname, ftype) ->
      (pos, fname, LH.apply_type_subst_in_type subst ftype)
    ) info.all_payload_fields
  in
  LA.RecordType (pos, info.type_name, disc_fld :: payload_flds)

(* Build a FieldProject accessing the tag field of an expression. *)
let tag_of pos info scrut =
  LA.FieldProject (pos, scrut, info.disc_field, None)

(* Direct lookup: only matches types that are themselves an ADT name.
   Used by desugar_type so that a UserType aliasing a refinement-of-ADT is
   NOT replaced with the bare record type (the refinement wrapper must be kept). *)
let adt_info_of_type_direct adt_map ty =
  match ty with
  | LA.UserType (_, _, name) -> HStringMap.find_opt name adt_map
  | LA.ADT (_, name, _) -> HStringMap.find_opt name adt_map
  | _ -> None

(* Full lookup: traverses type synonyms and refinement types to find the
   underlying ADT.  Used by desugar_expr (Match) and collect_pattern_constraints
   where the scrutinee may have a refinement type that wraps an ADT. *)
let rec adt_info_of_type ctx adt_map ty =
  match ty with
  | LA.UserType (_, ty_args, name) ->
    (match HStringMap.find_opt name adt_map with
    | Some _ as r -> r
    | None ->
      match Ctx.lookup_ty_syn ctx name ty_args with
      | Some expanded -> adt_info_of_type ctx adt_map expanded
      | None -> None)
  | LA.ADT (_, name, _) -> HStringMap.find_opt name adt_map
  | LA.RefinementType (_, (_, _, inner_ty), _) -> adt_info_of_type ctx adt_map inner_ty
  | _ -> None

(* Recursively collect the conjunction of tag equality conditions and the
   variable->field-projection substitutions imposed by a (possibly nested)
   constructor pattern.  Returns (conditions, substitutions). *)
let rec collect_pattern_constraints pos ctx adt_map info scrut pat =
  match pat with
  | LA.VarPat (_, name) -> ([], [(name, scrut)])
  | LA.Pat (_, name, sub_pats) ->
  if List.mem name info.ctor_variants then
    let ctor = name in
    let outer_cond =
      LA.CompOp (pos, LA.Eq, tag_of pos info scrut, LA.Ident (pos, ctor))
    in
    let ctor_fields =
      match HStringMap.find_opt ctor info.ctor_fields with
      | Some fs -> fs
      | None -> []
    in
    let sub_conds, sub_subs =
      List.fold_left2 (fun (conds, subs) (fname, ftype) sub_pat ->
        let field_expr = LA.FieldProject (pos, scrut, fname, None) in
        match sub_pat with
        | LA.VarPat (_, sub_name) ->
          (conds, subs @ [(sub_name, field_expr)])
        | LA.Pat (_, sub_name, _) ->
          (match adt_info_of_type ctx adt_map ftype with
          | Some sub_info when List.mem sub_name sub_info.ctor_variants ->
            let (c, s) = collect_pattern_constraints pos ctx adt_map sub_info field_expr sub_pat in
            (conds @ c, subs @ s)
          | _ -> assert false)
      ) ([], []) ctor_fields sub_pats
    in
    (outer_cond :: sub_conds, sub_subs)
  else
    ([], [(name, scrut)])

(* Desugar a single match arm into a (condition option, body) pair.
   Substitutes pattern variables with field projections in body. *)
let desugar_arm pos ctx adt_map info scrut pat body =
  let (conds, subs) = collect_pattern_constraints pos ctx adt_map info scrut pat in
  let body =
    List.fold_left (fun b (var, expr) -> LH.substitute_naive var expr b) body subs
  in
  match conds with
  | [] -> (None, body)
  | first :: rest ->
    let cond = List.fold_left (fun acc c -> LA.BinaryOp (pos, LA.And, acc, c)) first rest in
    (Some cond, body)

(* Build a nested ITE from a list of (condition option, body) pairs. *)
let rec build_ite pos arms =
  match arms with
  | [] -> assert false
  (* More cases after a catch-all; will be caught in later PR by redundancy checks *)
  | (None, _) :: _ :: _ -> assert false 
  (* Last case must always cover all cases so far uncovered (problems here will be caught by later PR's exhaustiveness checks) *)
  | [(_, body)] -> body 
  | (Some cond, body) :: rest ->
    LA.TernaryOp (pos, LA.LazyIte, cond, body, build_ite pos rest)

let update_context adt_map ctx =
  HStringMap.fold (fun type_name info acc_ctx ->
    let pos = Lib.dummy_pos in
    let enum_user_ty = LA.UserType (pos, [], info.disc_enum) in
    let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
    let acc_ctx = Ctx.add_enum_variants acc_ctx info.disc_enum info.ctor_variants in
    let acc_ctx = Ctx.add_ty_syn acc_ctx info.disc_enum enum_ty in
    let acc_ctx = Ctx.add_ty_decl acc_ctx info.disc_enum in
    let type_bindings = List.map (fun v -> Ctx.singleton_ty v enum_user_ty) info.ctor_variants in
    let const_bindings = List.map (fun v ->
      Ctx.singleton_const v (LA.Ident (pos, v)) enum_user_ty Global
    ) info.ctor_variants in
    let acc_ctx = List.fold_left Ctx.union acc_ctx (type_bindings @ const_bindings) in
    let record_ty = record_type_of_adt pos info in
    let acc_ctx = Ctx.add_ty_syn acc_ctx type_name record_ty in
    List.fold_left Ctx.remove_adt_ctor acc_ctx info.ctor_variants
  ) adt_map ctx

(* Generate a default (junk) value for a type. Used for unused ADT payload fields. *)
let rec default_value ctx adt_map pos ty =
  let ty = desugar_type pos ctx adt_map ty in
  match ty with
  | LA.Bool _ -> LA.Const (pos, LA.False)
  | LA.Int _ -> LA.Const (pos, LA.Num (HString.mk_hstring "0"))
  | LA.SBitVector (_, n) ->
    LA.ConvOp (pos, LA.ToBV n, LA.Const (pos, LA.Num (HString.mk_hstring "0")))
  | LA.UBitVector (_, n) ->
    LA.ConvOp (pos, LA.ToUBV n, LA.Const (pos, LA.Num (HString.mk_hstring "0")))
  | LA.Real _ -> LA.Const (pos, LA.Dec (HString.mk_hstring "0.0"))
  | LA.EnumType (_, _, v :: _) -> LA.Ident (pos, v)
  | LA.EnumType (_, _, []) -> assert false
  | LA.RecordType (_, rname, fields) ->
    LA.RecordExpr (pos, rname, [],
      List.map (fun (_, fname, ftype) -> (fname, default_value ctx adt_map pos ftype)) fields)
  | LA.TupleType (_, tys) ->
    LA.GroupExpr (pos, LA.TupleExpr, List.map (default_value ctx adt_map pos) tys)
  | LA.GroupType (_, tys) ->
    LA.GroupExpr (pos, LA.ExprList, List.map (default_value ctx adt_map pos) tys)
  | LA.ArrayType (_, (ety, size)) ->
    LA.ArrayConstr (pos, default_value ctx adt_map pos ety, size)
  | LA.UserType _ ->
    (match Ctx.expand_type_syn ctx ty with
    | LA.UserType _ -> assert false
    | expanded -> default_value ctx adt_map pos expanded)
  | LA.Set (_, ty) -> LA.EmptySet (pos, Some ty)
  | LA.Map (_, kt, vt) -> LA.EmptyMap (pos, Some (kt, vt))
  | LA.RefinementType (_, (_, _, inner_ty), _) -> default_value ctx adt_map pos inner_ty
  | LA.History (_, id) ->
    (match Ctx.lookup_ty ctx id with
    | Some expanded -> default_value ctx adt_map pos expanded
    | None -> assert false)
  | LA.TArr _ -> assert false
  | LA.ADT _ -> assert false (* desugar_type should have handled this *)
  | LA.AbstractType _ -> failwith "Unsupported: abstract type in ADT constructor"

(* Replace every ADT type with its desugared record equivalent. *)
and desugar_type pos ctx adt_map ty =
  match ty with
  | LA.ADT (_, name, cons) ->
    let info = build_adt_info name [] cons in
    record_type_of_adt pos info
  | LA.RefinementType (p, (p2, id, t), e) ->
    LA.RefinementType (p, (p2, id, desugar_type pos ctx adt_map t), desugar_expr ctx adt_map e)
  | _ ->
  match adt_info_of_type_direct adt_map ty with
  | Some adt_info ->
    let ty_args = match ty with
      | LA.UserType (_, args, _) -> List.map (desugar_type pos ctx adt_map) args
      | _ -> []
    in
    record_type_of_adt pos ~ty_args adt_info
  | None ->
    let ds = desugar_type pos ctx adt_map in
    match ty with
    | LA.Bool _ | LA.Int _ | LA.Real _
    | LA.SBitVector _ | LA.UBitVector _
    | LA.AbstractType _
    | LA.EnumType _ | LA.History _ -> ty
    | LA.UserType (p, params, name) ->
      LA.UserType (p, List.map ds params, name)
    | LA.TupleType (p, ts) -> LA.TupleType (p, List.map ds ts)
    | LA.GroupType (p, ts) -> LA.GroupType (p, List.map ds ts)
    | LA.RecordType (p, n, fields) ->
      LA.RecordType (p, n,
        List.map (fun (fp, fn, ft) -> (fp, fn, ds ft)) fields)
    | LA.ArrayType (p, (t, e)) -> LA.ArrayType (p, (ds t, e))
    | LA.TArr (p, t1, t2) -> LA.TArr (p, ds t1, ds t2)
    | LA.Map (p, kt, vt) -> LA.Map (p, ds kt, ds vt)
    | LA.Set (p, t) -> LA.Set (p, ds t)
    | LA.RefinementType _ -> assert false (* handled above *)
    | LA.ADT _ -> assert false (* unreachable: handled above *)

(* Desugar ADTTerm and Match expressions throughout an expression. *)
and desugar_expr ctx adt_map expr =
  let r e = desugar_expr ctx adt_map e in
  let rlist es = List.map r es in
  let rilist ies = List.map (fun (i, e) -> (i, r e)) ies in
  let rloi = function
    | LA.Label _ as l -> l
    | LA.Index (p, e) -> LA.Index (p, r e)
    | LA.MapIndex (p, e) -> LA.MapIndex (p, r e)
    | LA.SetIndex (p, e) -> LA.SetIndex (p, r e)
    | LA.GenericIndex (p, e) -> LA.GenericIndex (p, r e)
  in
  match expr with
  | LA.ADTTerm (pos, ty_args, ctor, args) ->
    let args' = rlist args in
    let adt_info =
      HStringMap.fold (fun _ info acc ->
        match acc with Some _ -> acc | None ->
          if HStringMap.mem ctor info.ctor_fields then Some info else None
      ) adt_map None
      |> (function Some i -> i | None -> assert false)
    in
    let ty_args' = List.map (desugar_type pos ctx adt_map) ty_args in
    let subst =
      if List.length adt_info.type_params = List.length ty_args'
      then List.combine adt_info.type_params ty_args'
      else []
    in
    let inst_fields fields =
      List.map (fun (fn, ft) -> (fn, LH.apply_type_subst_in_type subst ft)) fields
    in
    let disc_e = LA.Ident (pos, ctor) in
    let this_ctor_fields = inst_fields (
      HStringMap.find_opt ctor adt_info.ctor_fields
      |> (function Some fs -> fs | None -> assert false))
    in
    let arg_map =
      List.combine (List.map fst this_ctor_fields) args'
      |> List.fold_left (fun m (fn, e) -> HStringMap.add fn e m) HStringMap.empty
    in
    let payload_pairs = List.map (fun (fname, ftype) ->
      match HStringMap.find_opt fname arg_map with
      | Some e -> (fname, e)
      | None -> (fname, default_value ctx adt_map pos ftype)
    ) (inst_fields adt_info.all_payload_fields) in
    LA.RecordExpr (pos, adt_info.type_name, [],
      (adt_info.disc_field, disc_e) :: payload_pairs)
  | LA.Match (pos, scrut, arms, scrut_ty_opt) ->
    let adt_info =
      (match scrut_ty_opt with
      | Some ty -> adt_info_of_type ctx adt_map ty
      | None -> None)
      |> (function Some i -> i | None -> assert false)
    in
    let scrut' = r scrut in
    let desugared_arms = List.map (fun (pat, body) ->
      let (cond_opt, body') = desugar_arm pos ctx adt_map adt_info scrut' pat body in
      (cond_opt, r body')
    ) arms in
    build_ite pos desugared_arms
  | LA.ADTTester (pos, e, c) ->
    let adt_info =
      HStringMap.fold (fun _ info acc ->
        match acc with Some _ -> acc | None ->
          if List.mem c info.ctor_variants then Some info else None
      ) adt_map None
      |> (function Some i -> i | None -> assert false)
    in
    LA.CompOp (pos, LA.Eq,
      tag_of pos adt_info (r e),
      LA.Ident (pos, c))
  | LA.Ident _ | LA.ModeRef _ | LA.Const _ | LA.EmptyMap _ | LA.EmptySet _ | LA.Last _ -> expr
  | LA.FieldProject (p, e, fld, Some adt_ty) ->
    let e' = r e in
    let info = adt_info_of_type ctx adt_map adt_ty
      |> (function Some i -> i | None -> assert false)
    in
    let ctor = HStringMap.fold (fun ctor internal_fields acc ->
      match acc with
      | Some _ -> acc
      | None ->
        let target = payload_field_name_of ctor fld in
        if List.exists (fun (fn, _) -> HString.equal fn target) internal_fields
        then Some ctor
        else None
    ) info.ctor_fields None
    |> (function Some c -> c | None -> assert false)
    in
    let internal_fld = payload_field_name_of ctor fld in
    LA.FieldProject (p, e', internal_fld, None)
  | LA.FieldProject (p, e, i, None) -> LA.FieldProject (p, r e, i, None)
  | LA.UnaryOp (p, op, e) -> LA.UnaryOp (p, op, r e)
  | LA.BinaryOp (p, op, e1, e2) -> LA.BinaryOp (p, op, r e1, r e2)
  | LA.TernaryOp (p, op, e1, e2, e3) -> LA.TernaryOp (p, op, r e1, r e2, r e3)
  | LA.ConvOp (p, op, e) -> LA.ConvOp (p, op, r e)
  | LA.CompOp (p, op, e1, e2) -> LA.CompOp (p, op, r e1, r e2)
  | LA.RecordExpr (p, n, ps, flds) -> LA.RecordExpr (p, n, ps, rilist flds)
  | LA.GroupExpr (p, k, es) -> LA.GroupExpr (p, k, rlist es)
  | LA.StructUpdate (p, e1, idx, Some e2) ->
    LA.StructUpdate (p, r e1, List.map rloi idx, Some (r e2))
  | LA.StructUpdate (p, e, idx, None) ->
    LA.StructUpdate (p, r e, List.map rloi idx, None)
  | LA.ArrayConstr (p, e1, e2) -> LA.ArrayConstr (p, r e1, r e2)
  | LA.IndexAccess (p, e1, e2, k) -> LA.IndexAccess (p, r e1, r e2, k)
  | LA.When (p, e, c) -> LA.When (p, r e, c)
  | LA.Pre (p, e) -> LA.Pre (p, r e)
  | LA.Arrow (p, e1, e2) -> LA.Arrow (p, r e1, r e2)
  | LA.TypeAscription (p, e, ty) -> LA.TypeAscription (p, r e, desugar_type p ctx adt_map ty)
  | LA.Call (p, ty_args, id, es) ->
    LA.Call (p, List.map (desugar_type p ctx adt_map) ty_args, id, rlist es)
  | LA.Merge (p, id, flds) -> LA.Merge (p, id, rilist flds)
  | LA.Activate (p, id, e1, e2, es) -> LA.Activate (p, id, r e1, r e2, rlist es)
  | LA.Condact (p, e1, e2, id, es1, es2) ->
    LA.Condact (p, r e1, r e2, id, rlist es1, rlist es2)
  | LA.RestartEvery (p, id, es, e) -> LA.RestartEvery (p, id, rlist es, r e)
  | LA.Quantifier (p, k, idents, e) ->
    let idents' = List.map (fun (p, id, ty) -> (p, id, desugar_type p ctx adt_map ty)) idents in
    LA.Quantifier (p, k, idents', r e)
  | LA.Extract (p, e, ub, lb) -> LA.Extract (p, r e, ub, lb)
  | LA.AnyOp _ | LA.ChooseOp _ ->
    assert false (* desugared before this pipeline step *)

let desugar_const_decl ctx adt_map = function
  | LA.FreeConst (p, id, ty) -> LA.FreeConst (p, id, desugar_type p ctx adt_map ty)
  | LA.UntypedConst (p, id, e) -> LA.UntypedConst (p, id, desugar_expr ctx adt_map e)
  | LA.TypedConst (p, id, e, ty) ->
    LA.TypedConst (p, id, desugar_expr ctx adt_map e, desugar_type p ctx adt_map ty)

let desugar_contract_item ctx adt_map item =
  let r = desugar_expr ctx adt_map in
  let dt p ty = desugar_type p ctx adt_map ty in
  match item with
  | LA.Assume (p, n, s, e) -> LA.Assume (p, n, s, r e)
  | LA.Guarantee (p, n, s, e) -> LA.Guarantee (p, n, s, r e)
  | LA.Decreases (p, e) -> LA.Decreases (p, r e)
  | LA.Mode (p, n, requires, ensures) ->
    let r3 (p, n, e) = (p, n, r e) in
    LA.Mode (p, n, List.map r3 requires, List.map r3 ensures)
  | LA.ContractCall (p, name, ty_args, inputs, outputs) ->
    LA.ContractCall (p, name, ty_args, List.map r inputs, outputs)
  | LA.GhostConst cd -> LA.GhostConst (desugar_const_decl ctx adt_map cd)
  | LA.GhostVars (p, LA.GhostVarDec (p2, tis), e) ->
    let tis' = List.map (fun (p, id, ty) -> (p, id, dt p ty)) tis in
    LA.GhostVars (p, LA.GhostVarDec (p2, tis'), r e)
  | LA.AssumptionVars _ as a -> a

let rec desugar_node_item ctx adt_map item =
  let r = desugar_expr ctx adt_map in
  match item with
  | LA.Auto _ -> item
  | LA.Body (LA.Equation (p, lhs, e)) -> LA.Body (LA.Equation (p, lhs, r e))
  | LA.Body (LA.Assert (p, e)) -> LA.Body (LA.Assert (p, r e))
  | LA.AnnotMain _ as a -> a
  | LA.AnnotProperty (p, n, e, LA.Provided e2) ->
    LA.AnnotProperty (p, n, r e, LA.Provided (r e2))
  | LA.AnnotProperty (p, n, e, k) -> LA.AnnotProperty (p, n, r e, k)
  | LA.IfBlock (p, e, then_items, else_items) ->
    let di = desugar_node_item ctx adt_map in
    LA.IfBlock (p, r e, List.map di then_items, List.map di else_items)
  | LA.WhenBlock (p, e, then_items, else_items) ->
    let di = desugar_node_item ctx adt_map in
    LA.WhenBlock (p, r e, List.map di then_items, List.map di else_items)
  | LA.FrameBlock (p, vars, eqs, items) ->
    let di = desugar_node_item ctx adt_map in
    let de = function
      | LA.Assert (p2, e) -> LA.Assert (p2, r e)
      | LA.Equation (p2, lhs, e) -> LA.Equation (p2, lhs, r e)
    in
    LA.FrameBlock (p, vars, List.map de eqs, List.map di items)

let desugar_node ctx adt_map (id, is_extern, opac, params, inputs, outputs, locals, items, contract) =
  let dt p ty = desugar_type p ctx adt_map ty in
  let di (p, id, ty, cl, c) = (p, id, dt p ty, cl, c) in
  let do_ (p, id, ty, cl) = (p, id, dt p ty, cl) in
  let dl = function
    | LA.NodeVarDecl (sp, (p, id, ty, cl)) -> LA.NodeVarDecl (sp, (p, id, dt p ty, cl))
    | LA.NodeConstDecl (sp, cd) -> LA.NodeConstDecl (sp, desugar_const_decl ctx adt_map cd)
  in
  let contract' = Option.map (fun (p, items) ->
    (p, List.map (desugar_contract_item ctx adt_map) items)
  ) contract in
  (id, is_extern, opac, params,
   List.map di inputs,
   List.map do_ outputs,
   List.map dl locals,
   List.map (desugar_node_item ctx adt_map) items,
   contract')

let desugar_contract_node ctx adt_map (id, params, inputs, outputs, (p, body)) =
  let dt pos ty = desugar_type pos ctx adt_map ty in
  let di (p, id, ty, cl, c) = (p, id, dt p ty, cl, c) in
  let do_ (p, id, ty, cl) = (p, id, dt p ty, cl) in
  (id, params,
   List.map di inputs,
   List.map do_ outputs,
   (p, List.map (desugar_contract_item ctx adt_map) body))

(* Desugar ADTs: TypeDecls → enum + record TypeDecls; ADTTerm/Match → RecordExpr/ITE.
   Returns transformed type/const decls, transformed node/contract decls, and updated context. *)
let desugar_adts ctx type_and_const_decls node_contract_decls =
  let adt_map = build_adt_map (type_and_const_decls @ node_contract_decls) in
  if HStringMap.is_empty adt_map then
    (type_and_const_decls, node_contract_decls, ctx, adt_map)
  else
    let ctx' = update_context adt_map ctx in
    let type_and_const_decls' = List.concat_map (fun decl ->
      match decl with
      | LA.TypeDecl (sp, LA.AliasType (_, name, ty_params, LA.ADT (pos, _, _))) ->
        (match HStringMap.find_opt name adt_map with
        | Some info ->
          let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
          let enum_decl = LA.TypeDecl (sp, LA.AliasType (pos, info.disc_enum, [], enum_ty)) in
          let record_ty = record_type_of_adt pos info in
          let record_decl = LA.TypeDecl (sp, LA.AliasType (pos, name, ty_params, record_ty)) in
          [enum_decl; record_decl]
        | None -> assert false)
      | LA.TypeDecl (sp, LA.AliasType (p, name, ty_params, ty)) ->
        let ty = desugar_type p ctx' adt_map ty in
        [LA.TypeDecl (sp, LA.AliasType (p, name, ty_params, ty))]
      | LA.ConstDecl (p, cd) ->
        [LA.ConstDecl (p, desugar_const_decl ctx' adt_map cd)]
      | _ -> [decl]
    ) type_and_const_decls in
    let node_contract_decls' = List.map (fun decl ->
      match decl with
      | LA.NodeDecl (sp, nd) -> LA.NodeDecl (sp, desugar_node ctx' adt_map nd)
      | LA.FuncDecl (sp, nd, attrs) -> LA.FuncDecl (sp, desugar_node ctx' adt_map nd, attrs)
      | LA.ContractNodeDecl (sp, cnd) ->
        LA.ContractNodeDecl (sp, desugar_contract_node ctx' adt_map cnd)
      | LA.ConstDecl (p, cd) ->
        LA.ConstDecl (p, desugar_const_decl ctx' adt_map cd)
      | _ -> decl
    ) node_contract_decls in
    let ctx' = List.fold_left (fun acc_ctx decl ->
      match decl with
      | LA.TypeDecl (_, LA.AliasType (_, name, [], ty)) when not (HStringMap.mem name adt_map) ->
        Ctx.add_ty_syn acc_ctx name ty
      | _ -> acc_ctx
    ) ctx' type_and_const_decls' in
    (type_and_const_decls', node_contract_decls', ctx', adt_map)

(* Rewrite a desugared expression back toward source-level ADT syntax.
   RecordExprs whose type name is in adt_map are reconstructed as ADTTerm nodes
   so that pp_print_expr renders them as "Ctor(arg1, arg2)" or just "Ctor".
   This is the partial inverse of desugar_expr for the ADTTerm case. *)
let rec rewrite_as_adt_terms adt_map expr =
  let r e = rewrite_as_adt_terms adt_map e in
  let rlist = List.map r in
  let rilist = List.map (fun (i, e) -> (i, r e)) in
  let rloi = function
    | LA.Label _ as l -> l
    | LA.Index (p, e) -> LA.Index (p, r e)
    | LA.MapIndex (p, e) -> LA.MapIndex (p, r e)
    | LA.SetIndex (p, e) -> LA.SetIndex (p, r e)
    | LA.GenericIndex (p, e) -> LA.GenericIndex (p, r e)
  in
  (* Rewrite a desugared type back toward its source-level named form so that,
     e.g., a quantifier over an ADT prints as "Message" rather than the inline
     record definition, and an enum prints by its declared type name.  Record
     and enum types always carry their declared type name, so a bare UserType
     with that name renders correctly. *)
  let rec rewrite_type ty =
    match ty with
    | LA.RecordType (pos, name, _) -> LA.UserType (pos, [], name)
    | LA.EnumType (pos, name, _) -> LA.UserType (pos, [], name)
    | LA.UserType (pos, args, name) ->
      LA.UserType (pos, List.map rewrite_type args, name)
    | LA.TupleType (pos, ts) -> LA.TupleType (pos, List.map rewrite_type ts)
    | LA.GroupType (pos, ts) -> LA.GroupType (pos, List.map rewrite_type ts)
    | LA.ArrayType (pos, (t, e)) -> LA.ArrayType (pos, (rewrite_type t, r e))
    | LA.TArr (pos, t1, t2) -> LA.TArr (pos, rewrite_type t1, rewrite_type t2)
    | LA.Map (pos, kt, vt) -> LA.Map (pos, rewrite_type kt, rewrite_type vt)
    | LA.Set (pos, t) -> LA.Set (pos, rewrite_type t)
    | LA.RefinementType (pos, (p2, id, t), e) ->
      LA.RefinementType (pos, (p2, id, rewrite_type t), r e)
    | LA.Bool _ | LA.Int _ | LA.Real _ | LA.SBitVector _ | LA.UBitVector _
    | LA.AbstractType _ | LA.History _ | LA.ADT _ -> ty
  in
  match expr with
  | LA.RecordExpr (pos, type_name, [], fields) when HStringMap.mem type_name adt_map ->
    let info = HStringMap.find type_name adt_map in
    (match List.assoc_opt info.disc_field fields with
    | Some (LA.Ident (_, ctor_name)) ->
      let ctor_field_names =
        HStringMap.find_opt ctor_name info.ctor_fields
        |> Option.value ~default:[]
        |> List.map fst
      in
      let args = List.filter_map (fun fname ->
        match List.assoc_opt fname fields with
        | Some arg_expr -> Some (r arg_expr)
        | None -> None
      ) ctor_field_names in
      LA.ADTTerm (pos, [], ctor_name, args)
    | _ -> expr)
  | LA.Ident _ | LA.ModeRef _ | LA.Const _ | LA.EmptyMap _ | LA.EmptySet _ | LA.Last _ -> expr
  | LA.FieldProject (p, e, id, ty_opt) -> 
    let ty_opt = Option.map (LH.map_lustre_ty r) ty_opt in
    LA.FieldProject (p, r e, id, ty_opt)
  | LA.ADTTester (p, e, id) -> LA.ADTTester (p, r e, id)
  | LA.UnaryOp (p, op, e) -> LA.UnaryOp (p, op, r e)
  | LA.BinaryOp (p, op, e1, e2) -> LA.BinaryOp (p, op, r e1, r e2)
  | LA.TernaryOp (p, op, e1, e2, e3) -> LA.TernaryOp (p, op, r e1, r e2, r e3)
  | LA.ConvOp (p, op, e) -> LA.ConvOp (p, op, r e)
  | LA.CompOp (p, op, e1, e2) -> LA.CompOp (p, op, r e1, r e2)
  | LA.RecordExpr (p, n, ps, flds) -> LA.RecordExpr (p, n, ps, rilist flds)
  | LA.GroupExpr (p, k, es) -> LA.GroupExpr (p, k, rlist es)
  | LA.StructUpdate (p, e1, idx, e2_opt) ->
    LA.StructUpdate (p, r e1, List.map rloi idx, Option.map r e2_opt)
  | LA.ArrayConstr (p, e1, e2) -> LA.ArrayConstr (p, r e1, r e2)
  | LA.IndexAccess (p, e1, e2, k) -> LA.IndexAccess (p, r e1, r e2, k)
  | LA.When (p, e, c) -> LA.When (p, r e, c)
  | LA.Pre (p, e) -> LA.Pre (p, r e)
  | LA.Arrow (p, e1, e2) -> LA.Arrow (p, r e1, r e2)
  | LA.TypeAscription (p, e, ty) -> LA.TypeAscription (p, r e, rewrite_type ty)
  | LA.Call (p, ty_args, id, es) ->
    LA.Call (p, List.map rewrite_type ty_args, id, rlist es)
  | LA.Merge (p, id, flds) -> LA.Merge (p, id, rilist flds)
  | LA.Activate (p, id, e1, e2, es) -> LA.Activate (p, id, r e1, r e2, rlist es)
  | LA.Condact (p, e1, e2, id, es1, es2) ->
    LA.Condact (p, r e1, r e2, id, rlist es1, rlist es2)
  | LA.RestartEvery (p, id, es, e) -> LA.RestartEvery (p, id, rlist es, r e)
  | LA.Quantifier (p, k, idents, e) ->
    let idents = List.map (fun (ip, id, ty) -> (ip, id, rewrite_type ty)) idents in
    LA.Quantifier (p, k, idents, r e)
  | LA.Extract (p, e, ub, lb) -> LA.Extract (p, r e, ub, lb)
  | LA.AnyOp _ | LA.ChooseOp _ -> expr
  | LA.ADTTerm _ | LA.Match _ -> expr

let string_of_expr_as_source adt_map expr =
  LA.string_of_expr (rewrite_as_adt_terms adt_map expr)
