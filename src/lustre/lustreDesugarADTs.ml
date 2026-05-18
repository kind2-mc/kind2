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

    ADTTerm expressions and Match expressions are desugared during
    normalization: ADTTerm becomes a RecordExpr, and Match becomes
    a nested ITE chain on the tag field.

    This module handles the pre-pass (TypeDecl transformation and context
    update) and exports shared infrastructure used by the normalizer. *)

module LA = LustreAst
module LH = LustreAstHelpers
module Ctx = TypeCheckerContext
module GI = GeneratedIdentifiers
module HStringMap = HString.HStringMap

(** Counter for generating unique oracle variable names. *)
let oracle_counter = ref 0

type adt_info = {
  type_name : HString.t;

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

let payload_field_name ctor i =
  HString.mk_hstring (HString.string_of_hstring ctor ^ "_" ^ string_of_int i)

let build_adt_info type_name ctors =
  let disc_field = disc_field_name type_name in
  let disc_enum = disc_field_name type_name in
  let ctor_variants = List.map fst ctors in
  let ctor_fields =
    List.fold_left (fun m (ctor, field_types) ->
      let fields =
        List.mapi (fun j ty -> (payload_field_name ctor j, ty)) field_types
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
  { type_name; disc_field; disc_enum; ctor_variants; ctor_fields; all_payload_fields }

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

(* Mint a fresh unconstrained oracle variable for a junk payload field.
   Returns the identifier expression and a gids record containing the oracle. *)
let mk_fresh_adt_term_oracle pos ty =
  incr oracle_counter;
  let name = HString.mk_hstring (string_of_int !oracle_counter ^ "_adt_junk") in
  let gids = { (GI.empty ()) with GI.adt_term_oracles = [(name, ty)] } in
  LA.Ident (pos, name), gids

(* Build a RecordProject accessing the tag field of an expression. *)
let tag_of pos info scrut =
  LA.RecordProject (pos, scrut, info.disc_field)

let adt_info_of_type adt_map ty =
  match ty with
  | LA.UserType (_, _, name) -> HStringMap.find_opt name adt_map
  | LA.ADT (_, name, _) -> HStringMap.find_opt name adt_map
  | _ -> None

(* Recursively collect the conjunction of tag equality conditions and the
   variable->field-projection substitutions imposed by a (possibly nested)
   constructor pattern.  Returns (conditions, substitutions). *)
let rec collect_pattern_constraints pos adt_map info scrut (LA.Pat (_, name, sub_pats)) =
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
        let field_expr = LA.RecordProject (pos, scrut, fname) in
        let LA.Pat (_, sub_name, _) = sub_pat in
        match adt_info_of_type adt_map ftype with
        | Some sub_info when List.mem sub_name sub_info.ctor_variants ->
          let (c, s) = collect_pattern_constraints pos adt_map sub_info field_expr sub_pat in
          (conds @ c, subs @ s)
        | _ ->
          (conds, subs @ [(sub_name, field_expr)])
      ) ([], []) ctor_fields sub_pats
    in
    (outer_cond :: sub_conds, sub_subs)
  else
    ([], [(name, scrut)])

(* Desugar a single match arm into a (condition option, body) pair.
   Substitutes pattern variables with field projections in body. *)
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

(* Build a nested ITE from a list of (condition option, body) pairs. *)
let rec build_ite pos arms =
  match arms with
  | [] -> assert false
  | (None, _) :: _ :: _ -> assert false (* More cases after a catch-all; will be caught in later PR by redundancy checks *)
  | [(_, body)] -> body (* Last case must always cover all cases so far uncovered *)
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
    let acc_ctx = HStringMap.fold (fun ctor fields acc ->
      let field_tys = List.map snd fields in
      Ctx.add_adt_ctor acc ctor type_name field_tys
    ) info.ctor_fields acc_ctx in
    let record_ty = record_type_of_adt pos info in
    Ctx.add_ty_syn acc_ctx type_name record_ty
  ) adt_map ctx

(* Pre-pass: transform ADT TypeDecls into enum + record TypeDecls and update
   the type-checker context. Expression-level desugaring (ADTTerm, Match)
   is handled later within the normalizer. *)
let desugar_adts_program ctx decls =
  let adt_map = build_adt_map decls in
  if HStringMap.is_empty adt_map then
    (decls, ctx, adt_map)
  else
    let decls = List.concat_map (fun decl ->
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
      | _ -> [decl]
    ) decls in
    let ctx = update_context adt_map ctx in
    (decls, ctx, adt_map)
