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
      type _adt_T_tag = _adt_T_tag_C0 | _adt_T_tag_C1 | _adt_T_tag_C2;
      type T = { _adt_T_tag: _adt_T_tag;
                 _adt_T_C1_0: t1_0; _adt_T_C1_1: t1_1;
                 _adt_T_C2_0: t2_0 }
    where the enum tag field encodes the active constructor and the
    payload fields for non-selected constructors carry junk values.

    ADTTerm expressions and Match expressions are desugared
    correspondingly: ADTTerm becomes a RecordExpr, and Match becomes
    a nested ITE chain on the tag field. *)

module LA = LustreAst
module LH = LustreAstHelpers
module Ctx = TypeCheckerContext
module HStringMap = HString.HStringMap

type adt_info = {
  type_name : HString.t;

  (* name of the tag field in the record *)
  disc_field : HString.t;

  (* name of the generated enum type for the discriminant *)
  disc_enum : HString.t;

  (* ordered list of enum variant names, one per constructor *)
  ctor_variants : HString.t list;

  (* constructor name -> enum variant name *)
  ctor_variant : HString.t HStringMap.t;

  (* constructor name -> ordered list of (payload_field_name, field_type) *)
  ctor_fields : (HString.t * LA.lustre_type) list HStringMap.t;

  (* all payload fields across all constructors, in declaration order,
     deduplicated by field name *)
  all_payload_fields : (HString.t * LA.lustre_type) list;
}

type adt_map = adt_info HStringMap.t

let disc_field_name type_name =
  HString.mk_hstring (HString.string_of_hstring type_name ^ "_tag")

let disc_enum_name type_name =
  HString.mk_hstring (HString.string_of_hstring type_name ^ "_tag")

let ctor_variant_name type_name ctor = ctor 

let payload_field_name type_name ctor i = 
  HString.mk_hstring (
    HString.string_of_hstring ctor ^ "_"
    ^ string_of_int i)

let build_adt_info type_name ctors =
  let disc_field = disc_field_name type_name in
  let disc_enum = disc_enum_name type_name in
  let ctor_variants = List.map (fun (c, _) -> ctor_variant_name type_name c) ctors in
  let ctor_variant =
    List.fold_left (fun m (c, _) ->
      HStringMap.add c (ctor_variant_name type_name c) m
    ) HStringMap.empty ctors
  in
  let ctor_fields =
    List.fold_left (fun m (ctor, field_types) ->
      let fields =
        List.mapi (fun j ty -> (payload_field_name type_name ctor j, ty)) field_types
      in
      HStringMap.add ctor fields m
    ) HStringMap.empty ctors
  in
  let seen = Hashtbl.create 8 in
  let all_payload_fields =
    List.concat_map (fun (ctor, _) ->
      HStringMap.find ctor ctor_fields
      |> List.filter (fun (fname, _) ->
        if Hashtbl.mem seen (HString.string_of_hstring fname) then false
        else (Hashtbl.add seen (HString.string_of_hstring fname) (); true))
    ) ctors
  in
  { type_name; disc_field; disc_enum; ctor_variants; ctor_variant; ctor_fields; all_payload_fields }

(* Collect all ADT type declarations from a program into an adt_map. *)
let build_adt_map decls =
  List.fold_left (fun m decl ->
    match decl with
    | LA.TypeDecl (_, LA.AliasType (_, name, _, LA.ADT (_, _, ctors))) ->
      HStringMap.add name (build_adt_info name ctors) m
    | _ -> m
  ) HStringMap.empty decls

let record_type_of_adt pos info =
  let disc_fld = (pos, info.disc_field, LA.UserType (pos, [], info.disc_enum)) in
  let payload_flds =
    List.map (fun (fname, ftype) -> (pos, fname, ftype)) info.all_payload_fields
  in
  LA.RecordType (pos, info.type_name, disc_fld :: payload_flds)

let rec default_val pos adt_map ty =
  match ty with
  | LA.Bool _           -> LA.Const (pos, LA.False)
  | LA.Int _            -> LA.Const (pos, LA.Num (HString.mk_hstring "0"))
  | LA.Real _           -> LA.Const (pos, LA.Dec (HString.mk_hstring "0.0"))
  | LA.IntRange (_, Some lb, _) -> lb
  | LA.IntRange _       -> LA.Const (pos, LA.Num (HString.mk_hstring "0"))
  | LA.SBitVector (_, w)
  | LA.UBitVector (_, w) ->
    LA.Const (pos, LA.Num (HString.mk_hstring (string_of_int w ^ "d0")))
  | LA.UserType (_, _, name) ->
    (match HStringMap.find_opt name adt_map with
    | Some info ->
      (* Build a zero-value record: first variant tag, all payload fields junk *)
      let disc_e = LA.Ident (pos, List.hd info.ctor_variants) in
      let payload_flds =
        List.map (fun (fname, ftype) ->
          (fname, default_val pos adt_map ftype)
        ) info.all_payload_fields
      in
      LA.RecordExpr (pos, info.type_name, [], (info.disc_field, disc_e) :: payload_flds)
    | None ->
      (* Non-ADT user type: generate a free constant of this type.
         This handles e.g. enum types or abstract types used as fields. *)
      LA.Ident (pos, HString.mk_hstring ("_adt_default_" ^ HString.string_of_hstring name)))
  | LA.EnumType (_, _, v :: _) -> LA.Ident (pos, v)
  | _ ->
    (* For other composite types (records, arrays, tuples), generating a
       default is non-trivial. These shouldn't appear as direct ADT field
       types in the typical non-recursive use cases we support. *)
    LA.Ident (pos, HString.mk_hstring "_adt_default")

(* Build the desugared RecordExpr for an ADTTerm.
   Fields for the selected constructor are filled from `args`; all other
   payload fields receive junk default values. *)
let desugar_adt_term pos adt_map info ctor args =
  let variant =
    match HStringMap.find_opt ctor info.ctor_variant with
    | Some v -> v
    | None -> assert false
  in
  let disc_e = LA.Ident (pos, variant) in
  let this_ctor_fields =
    match HStringMap.find_opt ctor info.ctor_fields with
    | Some fs -> fs
    | None -> assert false
  in
  (* Build a map from this constructor's field names to the provided args *)
  let arg_map =
    List.combine (List.map fst this_ctor_fields) args
    |> List.fold_left (fun m (fname, e) -> HStringMap.add fname e m) HStringMap.empty
  in
  (* For each payload field: use the arg if it belongs to this constructor,
     otherwise use a junk default value *)
  let payload_flds =
    List.map (fun (fname, ftype) ->
      match HStringMap.find_opt fname arg_map with
      | Some e -> (fname, e)
      | None   -> (fname, default_val pos adt_map ftype)
    ) info.all_payload_fields
  in
  LA.RecordExpr (pos, info.type_name, [], (info.disc_field, disc_e) :: payload_flds)

(* Build a RecordProject accessing the tag field of an expression. *)
let tag_of pos info scrut =
  LA.RecordProject (pos, scrut, info.disc_field)

let is_ctor_name s = String.length s > 0 && s.[0] >= 'A' && s.[0] <= 'Z'

let adt_info_of_type adt_map ty =
  match ty with
  | LA.UserType (_, _, name) -> HStringMap.find_opt name adt_map
  | LA.ADT (_, name, _) -> HStringMap.find_opt name adt_map
  | _ -> None

(* Recursively collect the conjunction of tag equality conditions and the
   variable->field-projection substitutions imposed by a (possibly nested)
   constructor pattern.  Returns (conditions, substitutions). *)
let rec collect_pattern_constraints pos adt_map info scrut (LA.Pat (_, name, sub_pats)) =
  if is_ctor_name (HString.string_of_hstring name) then
    let ctor = name in
    let variant =
      match HStringMap.find_opt ctor info.ctor_variant with
      | Some v -> v
      | None -> assert false
    in
    let outer_cond =
      LA.CompOp (pos, LA.Eq, tag_of pos info scrut, LA.Ident (pos, variant))
    in
    let ctor_fields =
      match HStringMap.find_opt ctor info.ctor_fields with
      | Some fs -> fs
      | None -> []
    in
    let sub_conds, sub_subs =
      List.fold_left2 (fun (conds, subs) (fname, ftype) sub_pat ->
        let field_expr = LA.RecordProject (pos, scrut, fname) in
        let LA.Pat (_, sub_name, _) = sub_pat in
        if is_ctor_name (HString.string_of_hstring sub_name) then
          match adt_info_of_type adt_map ftype with
          | Some sub_info ->
            let (c, s) = collect_pattern_constraints pos adt_map sub_info field_expr sub_pat in
            (conds @ c, subs @ s)
          | None -> (conds, subs)
        else
          (conds, subs @ [(sub_name, field_expr)])
      ) ([], []) ctor_fields sub_pats
    in
    (outer_cond :: sub_conds, sub_subs)
  else
    ([], [(name, scrut)])

(* Desugar a single match arm into a (condition, body) pair.
   The condition is a conjunction of all tag equality constraints imposed by
   the pattern (including nested constructor sub-patterns).  Pattern variables
   are substituted by field projections throughout the body. *)
let desugar_arm pos adt_map info scrut pat body =
  let (conds, subs) = collect_pattern_constraints pos adt_map info scrut pat in
  let body =
    List.fold_left (fun b (var, expr) -> LH.substitute_naive var expr b) body subs
  in
  match conds with
  | [] -> (None, body)
  | first :: rest ->
    let cond = List.fold_left (fun acc c -> LA.BinaryOp (pos, LA.And, acc, c)) first rest in
    (Some cond, body)

(* Build a nested ITE from a list of (condition option, body) pairs.
   The last arm acts as the else branch regardless of its condition. *)
let rec build_ite pos arms =
  match arms with
  | [] -> assert false
  | (None, _) :: _ -> assert false (* More cases after a catch-all *)
  | [(_, body)] -> body (* Last case must always cover all cases so far uncovered *)
  | (Some cond, body) :: rest ->
    LA.TernaryOp (pos, LA.Ite, cond, body, build_ite pos rest)

let rec desugar_type adt_map ctx ty =
  let r = desugar_type adt_map ctx in
  let r_e = desugar_expr adt_map ctx in
  match ty with
  | LA.ADT (pos, name, _) ->
    (match HStringMap.find_opt name adt_map with
    | Some info -> record_type_of_adt pos info
    | None -> ty)
  | LA.Bool _ | LA.Int _ | LA.Real _
  | LA.UBitVector _ | LA.SBitVector _
  | LA.AbstractType _ | LA.EnumType _ | LA.History _ -> ty
  | LA.IntRange (p, e1_opt, e2_opt) ->
    LA.IntRange (p, Option.map r_e e1_opt, Option.map r_e e2_opt)
  | LA.UserType (p, tys, name) ->
    LA.UserType (p, List.map r tys, name)
  | LA.TupleType (p, tys) ->
    LA.TupleType (p, List.map r tys)
  | LA.GroupType (p, tys) ->
    LA.GroupType (p, List.map r tys)
  | LA.ArrayType (p, (t, len)) ->
    LA.ArrayType (p, (r t, r_e len))
  | LA.RecordType (p, n, flds) ->
    LA.RecordType (p, n, List.map (fun (fp, fn, ft) -> (fp, fn, r ft)) flds)
  | LA.Map (p, kt, vt) ->
    LA.Map (p, r kt, r vt)
  | LA.Set (p, t) ->
    LA.Set (p, r t)
  | LA.TArr (p, t1, t2) ->
    LA.TArr (p, r t1, r t2)
  | LA.RefinementType (p, (p2, id, t), e) ->
    LA.RefinementType (p, (p2, id, r t), r_e e)

(* Desugar all ADTTerm and Match nodes in an expression. *)
and desugar_expr adt_map ctx e =
  let r = desugar_expr adt_map ctx in
  let r_ty = desugar_type adt_map ctx in
  match e with
  | LA.ADTTerm (pos, ctor, args) ->
    let args = List.map r args in
    (match Ctx.lookup_constructor ctx ctor with
    | None -> assert false  (* should have been a type error *)
    | Some (ty_name, _) ->
      match HStringMap.find_opt ty_name adt_map with
      | None -> e
      | Some info -> desugar_adt_term pos adt_map info ctor args)
  | LA.Match (pos, scrut, arms, scrut_ty_opt) ->
    let scrut = r scrut in
    let arms = List.map (fun (pat, body) -> (pat, r body)) arms in
    let adt_info_opt = match scrut_ty_opt with
      | Some (LA.UserType (_, _, name)) -> HStringMap.find_opt name adt_map
      | Some (LA.ADT (_, name, _)) -> HStringMap.find_opt name adt_map
      | Some _ -> None 
      | None -> assert false
    in
    (match adt_info_opt with
    | None -> assert false
    | Some info ->
      let desugared_arms =
        List.map (fun (pat, body) -> desugar_arm pos adt_map info scrut pat body) arms
      in
      build_ite pos desugared_arms)
  | LA.Ident _ | LA.ModeRef _ | LA.Const _ -> e
  | LA.EmptySet (p, None)           -> LA.EmptySet (p, None)
  | LA.EmptySet (p, Some ty)        -> LA.EmptySet (p, Some (r_ty ty))
  | LA.EmptyMap (p, None)           -> LA.EmptyMap (p, None)
  | LA.EmptyMap (p, Some (kt, vt))  -> LA.EmptyMap (p, Some (r_ty kt, r_ty vt))
  | LA.RecordProject (p, e1, f)        -> LA.RecordProject (p, r e1, f)
  | LA.UnaryOp (p, op, e1)             -> LA.UnaryOp (p, op, r e1)
  | LA.ConvOp (p, op, e1)              -> LA.ConvOp (p, op, r e1)
  | LA.Extract (p, e1, i, j)           -> LA.Extract (p, r e1, i, j)
  | LA.When (p, e1, c)                 -> LA.When (p, r e1, c)
  | LA.Pre (p, e1)                     -> LA.Pre (p, r e1)
  | LA.TypeAscription (p, e1, ty)      -> LA.TypeAscription (p, r e1, r_ty ty)
  | LA.BinaryOp (p, op, e1, e2)        -> LA.BinaryOp (p, op, r e1, r e2)
  | LA.CompOp (p, op, e1, e2)          -> LA.CompOp (p, op, r e1, r e2)
  | LA.ArrayConstr (p, e1, e2)         -> LA.ArrayConstr (p, r e1, r e2)
  | LA.IndexAccess (p, e1, e2, k)      -> LA.IndexAccess (p, r e1, r e2, k)
  | LA.Arrow (p, e1, e2)               -> LA.Arrow (p, r e1, r e2)
  | LA.TernaryOp (p, op, e1, e2, e3)   -> LA.TernaryOp (p, op, r e1, r e2, r e3)
  | LA.RecordExpr (p, n, ts, flds)     ->
    LA.RecordExpr (p, n, List.map r_ty ts, List.map (fun (f, e1) -> (f, r e1)) flds)
  | LA.GroupExpr (p, k, es)            -> LA.GroupExpr (p, k, List.map r es)
  | LA.StructUpdate (p, e1, lbl, e2)   -> LA.StructUpdate (p, r e1, lbl, Option.map r e2)
  | LA.Quantifier (p, q, qs, e1) ->
    LA.Quantifier (p, q, List.map (fun (p2, i, ty) -> (p2, i, r_ty ty)) qs, r e1)
  | LA.Call (p, ts, n, es)             -> LA.Call (p, List.map r_ty ts, n, List.map r es)
  | LA.Condact (p, e1, e2, n, es1, es2) ->
    LA.Condact (p, r e1, r e2, n, List.map r es1, List.map r es2)
  | LA.Activate (p, n, e1, e2, es)    -> LA.Activate (p, n, r e1, r e2, List.map r es)
  | LA.Merge (p, c, cases)            -> LA.Merge (p, c, List.map (fun (l, e1) -> (l, r e1)) cases)
  | LA.RestartEvery (p, n, es, e1)    -> LA.RestartEvery (p, n, List.map r es, r e1)
  | LA.AnyOp (p, (p2, i, ty), e1)    -> LA.AnyOp (p, (p2, i, r_ty ty), r e1)
  | LA.ChooseOp (p, (p2, i, ty), e1) -> LA.ChooseOp (p, (p2, i, r_ty ty), r e1)

let desugar_type_decl adt_map ctx td =
  match td with
  | LA.AliasType (pos, name, ps, ty) ->
    LA.AliasType (pos, name, ps, desugar_type adt_map ctx ty)
  | LA.FreeType _ -> td

let desugar_const_decl adt_map ctx cd =
  match cd with
  | LA.FreeConst (p, i, ty)        -> LA.FreeConst (p, i, desugar_type adt_map ctx ty)
  | LA.UntypedConst (p, i, e)      -> LA.UntypedConst (p, i, desugar_expr adt_map ctx e)
  | LA.TypedConst (p, i, e, ty)    ->
    LA.TypedConst (p, i, desugar_expr adt_map ctx e, desugar_type adt_map ctx ty)

let desugar_clocked_typed_decl adt_map ctx (p, i, ty, c) =
  (p, i, desugar_type adt_map ctx ty, c)

let desugar_const_clocked_typed_decl adt_map ctx (p, i, ty, c, ic) =
  (p, i, desugar_type adt_map ctx ty, c, ic)

let desugar_node_local_decl adt_map ctx ld =
  match ld with
  | LA.NodeConstDecl (p, cd) -> LA.NodeConstDecl (p, desugar_const_decl adt_map ctx cd)
  | LA.NodeVarDecl (p, ctd)  -> LA.NodeVarDecl (p, desugar_clocked_typed_decl adt_map ctx ctd)

let desugar_node_equation adt_map ctx eq =
  let r_e = desugar_expr adt_map ctx in
  match eq with
  | LA.Assert (p, e)        -> LA.Assert (p, r_e e)
  | LA.Equation (p, lhs, e) -> LA.Equation (p, lhs, r_e e)

let rec desugar_node_item adt_map ctx ni =
  let r_e = desugar_expr adt_map ctx in
  let r_ni = desugar_node_item adt_map ctx in
  match ni with
  | LA.Body eq ->
    LA.Body (desugar_node_equation adt_map ctx eq)
  | LA.IfBlock (p, e, nis1, nis2) ->
    LA.IfBlock (p, r_e e, List.map r_ni nis1, List.map r_ni nis2)
  | LA.FrameBlock (p, vars, eqs, nis) ->
    LA.FrameBlock (p, vars,
      List.map (desugar_node_equation adt_map ctx) eqs,
      List.map r_ni nis)
  | LA.AnnotProperty (p, name, e, kind) ->
    LA.AnnotProperty (p, name, r_e e, kind)
  | LA.AnnotMain _ as x -> x

let desugar_contract_node_eq adt_map ctx eq =
  let r_e = desugar_expr adt_map ctx in
  match eq with
  | LA.GhostConst cd         -> LA.GhostConst (desugar_const_decl adt_map ctx cd)
  | LA.GhostVars (p, lhs, e) -> LA.GhostVars (p, lhs, r_e e)
  | LA.Assume (p, n, s, e)   -> LA.Assume (p, n, s, r_e e)
  | LA.Guarantee (p, n, s, e)-> LA.Guarantee (p, n, s, r_e e)
  | LA.Mode (p, n, reqs, ensures) ->
    LA.Mode (p, n,
      List.map (fun (p2, n2, e) -> (p2, n2, r_e e)) reqs,
      List.map (fun (p2, n2, e) -> (p2, n2, r_e e)) ensures)
  | LA.ContractCall _ as cc  -> cc
  | LA.AssumptionVars _ as av -> av

let desugar_contract adt_map ctx (p, eqs) =
  (p, List.map (desugar_contract_node_eq adt_map ctx) eqs)

let desugar_declaration adt_map ctx decl =
  match decl with
  | LA.TypeDecl (p, td) ->
    LA.TypeDecl (p, desugar_type_decl adt_map ctx td)
  | LA.ConstDecl (p, cd) ->
    LA.ConstDecl (p, desugar_const_decl adt_map ctx cd)
  | LA.NodeDecl (p, (nid, imp, opac, ps, inputs, outputs, locals, items, contract_opt)) ->
    let inputs  = List.map (desugar_const_clocked_typed_decl adt_map ctx) inputs in
    let outputs = List.map (desugar_clocked_typed_decl adt_map ctx) outputs in
    let locals  = List.map (desugar_node_local_decl adt_map ctx) locals in
    let items   = List.map (desugar_node_item adt_map ctx) items in
    let contract_opt = Option.map (desugar_contract adt_map ctx) contract_opt in
    LA.NodeDecl (p, (nid, imp, opac, ps, inputs, outputs, locals, items, contract_opt))
  | LA.FuncDecl (p, (nid, imp, opac, ps, inputs, outputs, locals, items, contract_opt)) ->
    let inputs  = List.map (desugar_const_clocked_typed_decl adt_map ctx) inputs in
    let outputs = List.map (desugar_clocked_typed_decl adt_map ctx) outputs in
    let locals  = List.map (desugar_node_local_decl adt_map ctx) locals in
    let items   = List.map (desugar_node_item adt_map ctx) items in
    let contract_opt = Option.map (desugar_contract adt_map ctx) contract_opt in
    LA.FuncDecl (p, (nid, imp, opac, ps, inputs, outputs, locals, items, contract_opt))
  | LA.ContractNodeDecl (p, (nid, ps, inputs, outputs, contract)) ->
    let inputs   = List.map (desugar_const_clocked_typed_decl adt_map ctx) inputs in
    let outputs  = List.map (desugar_clocked_typed_decl adt_map ctx) outputs in
    let contract = desugar_contract adt_map ctx contract in
    LA.ContractNodeDecl (p, (nid, ps, inputs, outputs, contract))
  | LA.NodeParamInst _ -> decl

let update_context adt_map ctx =
  HStringMap.fold (fun type_name info acc_ctx ->
    let pos = Lib.dummy_pos in
    let enum_user_ty = LA.UserType (pos, [], info.disc_enum) in
    let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
    (* Register the discriminant enum type (mirrors how type_check_infer_globals handles EnumType) *)
    let acc_ctx = Ctx.add_enum_variants acc_ctx info.disc_enum info.ctor_variants in
    let acc_ctx = Ctx.add_ty_syn acc_ctx info.disc_enum enum_ty in
    let acc_ctx = Ctx.add_ty_decl acc_ctx info.disc_enum in
    let type_bindings = List.map (fun v -> Ctx.singleton_ty v enum_user_ty) info.ctor_variants in
    let const_bindings = List.map (fun v ->
      Ctx.singleton_const v (LA.Ident (pos, v)) enum_user_ty Global
    ) info.ctor_variants in
    let acc_ctx = List.fold_left Ctx.union acc_ctx (type_bindings @ const_bindings) in
    (* Register the record type replacing the ADT *)
    let record_ty = record_type_of_adt pos info in
    Ctx.add_ty_syn acc_ctx type_name record_ty
  ) adt_map ctx

let desugar_adts ctx type_and_const_decls node_and_contract_decls =
  let adt_map = build_adt_map type_and_const_decls in
  if HStringMap.is_empty adt_map then
    (type_and_const_decls, node_and_contract_decls, ctx)
  else
    let type_and_const_decls =
      List.concat_map (fun decl ->
        match decl with
        | LA.TypeDecl (sp, LA.AliasType (_, name, _, LA.ADT (pos, _, _))) ->
          (match HStringMap.find_opt name adt_map with
          | Some info ->
            let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
            let enum_decl = LA.TypeDecl (sp, LA.AliasType (pos, info.disc_enum, [], enum_ty)) in
            [enum_decl; desugar_declaration adt_map ctx decl]
          | None -> [desugar_declaration adt_map ctx decl])
        | _ -> [desugar_declaration adt_map ctx decl]
      ) type_and_const_decls
    in
    let node_and_contract_decls =
      List.map (desugar_declaration adt_map ctx) node_and_contract_decls
    in
    let ctx = update_context adt_map ctx in
    (type_and_const_decls, node_and_contract_decls, ctx)
