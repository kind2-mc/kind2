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
module GI = GeneratedIdentifiers
module NI = NodeId
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

(* Split a list of [(value, gids)] pairs into their components,
   merging all gids. *)
let split2 results =
  let vs = List.map fst results in
  let g  = List.fold_left (fun acc (_, g) -> GI.union acc g) (GI.empty ()) results in
  vs, g


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

(* Desugar a single match arm into a (condition, body) pair. *)
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

(* Desugar all ADT types and ADTTerm/Match nodes in a type.
   Returns (desugared_type, accumulated_gids). *)
let rec desugar_type adt_map ctx ty =
  let r ty = desugar_type adt_map ctx ty in
  let r_e e = desugar_expr adt_map ctx e in
  let map_r_ty tys = split2 (List.map r tys) in
  match ty with
  | LA.ADT (pos, name, _) ->
    (match HStringMap.find_opt name adt_map with
    | Some info -> r (record_type_of_adt pos info)
    | None -> assert false)
  | LA.Bool _ | LA.Int _ | LA.Real _
  | LA.UBitVector _ | LA.SBitVector _
  | LA.AbstractType _ | LA.EnumType _ | LA.History _ -> ty, GI.empty ()
  | LA.IntRange (p, e1_opt, e2_opt) ->
    let e1_opt', g1 = match e1_opt with
      | None -> None, GI.empty ()
      | Some e -> let e', g = r_e e in Some e', g
    in
    let e2_opt', g2 = match e2_opt with
      | None -> None, GI.empty ()
      | Some e -> let e', g = r_e e in Some e', g
    in
    LA.IntRange (p, e1_opt', e2_opt'), GI.union g1 g2
  | LA.UserType (p, tys, name) ->
    let tys', g = map_r_ty tys in
    LA.UserType (p, tys', name), g
  | LA.TupleType (p, tys) ->
    let tys', g = map_r_ty tys in
    LA.TupleType (p, tys'), g
  | LA.GroupType (p, tys) ->
    let tys', g = map_r_ty tys in
    LA.GroupType (p, tys'), g
  | LA.ArrayType (p, (t, len)) ->
    let t', g1 = r t in
    let len', g2 = r_e len in
    LA.ArrayType (p, (t', len')), GI.union g1 g2
  | LA.RecordType (p, n, flds) ->
    let fld_results = List.map (fun (fp, fn, ft) -> let ft', g = r ft in (fp, fn, ft'), g) flds in
    let flds', g = split2 fld_results in
    LA.RecordType (p, n, flds'), g
  | LA.Map (p, kt, vt) ->
    let kt', g1 = r kt in
    let vt', g2 = r vt in
    LA.Map (p, kt', vt'), GI.union g1 g2
  | LA.Set (p, t) ->
    let t', g = r t in
    LA.Set (p, t'), g
  | LA.TArr (p, t1, t2) ->
    let t1', g1 = r t1 in
    let t2', g2 = r t2 in
    LA.TArr (p, t1', t2'), GI.union g1 g2
  | LA.RefinementType (p, (p2, id, t), e) ->
    let t', g1 = r t in
    let e', g2 = r_e e in
    LA.RefinementType (p, (p2, id, t'), e'), GI.union g1 g2

(* Desugar all ADTTerm and Match nodes in an expression.
   Returns (desugared_expr, accumulated_gids). *)
and desugar_expr adt_map ctx e =
  let r e = desugar_expr adt_map ctx e in
  let r_ty ty = desugar_type adt_map ctx ty in
  let map_r es = split2 (List.map r es) in
  match e with
  | LA.ADTTerm (pos, ctor, args) ->
    let args', g0 = map_r args in
    (match Ctx.lookup_constructor ctx ctor with
    | None -> assert false  (* should have been a type error *)
    | Some (ty_name, _) ->
      match HStringMap.find_opt ty_name adt_map with
      | None -> assert false
      | Some info ->
        let e', g1 = desugar_adt_term adt_map ctx pos info ctor args' in
        e', GI.union g0 g1)
  | LA.Match (pos, scrut, arms, scrut_ty_opt) ->
    let scrut', g0 = r scrut in
    let arm_results = List.map (fun (pat, body) ->
      let body', g = r body in (pat, body'), g
    ) arms in
    let arms', g1 = split2 arm_results in
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
        List.map (fun (pat, body) -> desugar_arm pos adt_map info scrut' pat body) arms'
      in
      build_ite pos desugared_arms, GI.union g0 g1)
  | LA.Ident _ | LA.ModeRef _ | LA.Const _ -> e, GI.empty ()
  | LA.EmptySet (p, None)          -> LA.EmptySet (p, None), GI.empty ()
  | LA.EmptySet (p, Some ty) ->
    let ty', g = r_ty ty in
    LA.EmptySet (p, Some ty'), g
  | LA.EmptyMap (p, None)          -> LA.EmptyMap (p, None), GI.empty ()
  | LA.EmptyMap (p, Some (kt, vt)) ->
    let kt', g1 = r_ty kt in
    let vt', g2 = r_ty vt in
    LA.EmptyMap (p, Some (kt', vt')), GI.union g1 g2
  | LA.RecordProject (p, e1, f) ->
    let e1', g = r e1 in
    LA.RecordProject (p, e1', f), g
  | LA.UnaryOp (p, op, e1) ->
    let e1', g = r e1 in
    LA.UnaryOp (p, op, e1'), g
  | LA.ConvOp (p, op, e1) ->
    let e1', g = r e1 in
    LA.ConvOp (p, op, e1'), g
  | LA.Extract (p, e1, i, j) ->
    let e1', g = r e1 in
    LA.Extract (p, e1', i, j), g
  | LA.When (p, e1, c) ->
    let e1', g = r e1 in
    LA.When (p, e1', c), g
  | LA.Pre (p, e1) ->
    let e1', g = r e1 in
    LA.Pre (p, e1'), g
  | LA.TypeAscription (p, e1, ty) ->
    let e1', g1 = r e1 in
    let ty', g2 = r_ty ty in
    LA.TypeAscription (p, e1', ty'), GI.union g1 g2
  | LA.BinaryOp (p, op, e1, e2) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    LA.BinaryOp (p, op, e1', e2'), GI.union g1 g2
  | LA.CompOp (p, op, e1, e2) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    LA.CompOp (p, op, e1', e2'), GI.union g1 g2
  | LA.ArrayConstr (p, e1, e2) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    LA.ArrayConstr (p, e1', e2'), GI.union g1 g2
  | LA.IndexAccess (p, e1, e2, k) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    LA.IndexAccess (p, e1', e2', k), GI.union g1 g2
  | LA.Arrow (p, e1, e2) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    LA.Arrow (p, e1', e2'), GI.union g1 g2
  | LA.TernaryOp (p, op, e1, e2, e3) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    let e3', g3 = r e3 in
    LA.TernaryOp (p, op, e1', e2', e3'), GI.union (GI.union g1 g2) g3
  | LA.RecordExpr (p, n, ts, flds) ->
    let fld_results = List.map (fun (f, e1) ->
      let e1', g = r e1 in (f, e1'), g
    ) flds in
    let flds', gf = split2 fld_results in
    let ts', gt = split2 (List.map r_ty ts) in
    LA.RecordExpr (p, n, ts', flds'), GI.union gf gt
  | LA.GroupExpr (p, k, es) ->
    let es', g = map_r es in
    LA.GroupExpr (p, k, es'), g
  | LA.StructUpdate (p, e1, lbl, e2_opt) ->
    let e1', g1 = r e1 in
    let e2_opt', g2 = match e2_opt with
      | None -> None, GI.empty ()
      | Some e2 -> let e2', g = r e2 in Some e2', g
    in
    LA.StructUpdate (p, e1', lbl, e2_opt'), GI.union g1 g2
  | LA.Quantifier (p, q, qs, e1) ->
    let e1', ge = r e1 in
    let q_results = List.map (fun (p2, i, ty) -> let ty', g = r_ty ty in (p2, i, ty'), g) qs in
    let qs', gq = split2 q_results in
    LA.Quantifier (p, q, qs', e1'), GI.union ge gq
  | LA.Call (p, ts, n, es) ->
    let es', ge = map_r es in
    let ts', gt = split2 (List.map r_ty ts) in
    LA.Call (p, ts', n, es'), GI.union ge gt
  | LA.Condact (p, e1, e2, n, es1, es2) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    let es1', g3 = map_r es1 in
    let es2', g4 = map_r es2 in
    LA.Condact (p, e1', e2', n, es1', es2'),
    GI.union (GI.union g1 g2) (GI.union g3 g4)
  | LA.Activate (p, n, e1, e2, es) ->
    let e1', g1 = r e1 in
    let e2', g2 = r e2 in
    let es', g3 = map_r es in
    LA.Activate (p, n, e1', e2', es'), GI.union (GI.union g1 g2) g3
  | LA.Merge (p, c, cases) ->
    let case_results = List.map (fun (l, e1) ->
      let e1', g = r e1 in (l, e1'), g
    ) cases in
    let cases', g = split2 case_results in
    LA.Merge (p, c, cases'), g
  | LA.RestartEvery (p, n, es, e1) ->
    let es', g1 = map_r es in
    let e1', g2 = r e1 in
    LA.RestartEvery (p, n, es', e1'), GI.union g1 g2
  | LA.AnyOp (p, (p2, i, ty), e1) ->
    let e1', g1 = r e1 in
    let ty', g2 = r_ty ty in
    LA.AnyOp (p, (p2, i, ty'), e1'), GI.union g1 g2
  | LA.ChooseOp (p, (p2, i, ty), e1) ->
    let e1', g1 = r e1 in
    let ty', g2 = r_ty ty in
    LA.ChooseOp (p, (p2, i, ty'), e1'), GI.union g1 g2

(* Build the desugared RecordExpr for an ADTTerm.
   Fields for the selected constructor are filled from [args]; all other
   payload fields receive fresh oracle variables whose types are desugared. *)
and desugar_adt_term adt_map ctx pos info ctor args =
  let disc_e = LA.Ident (pos, ctor) in
  let this_ctor_fields =
    match HStringMap.find_opt ctor info.ctor_fields with
    | Some fs -> fs
    | None -> assert false
  in
  let arg_map =
    List.combine (List.map fst this_ctor_fields) args
    |> List.fold_left (fun m (fname, e) -> HStringMap.add fname e m) HStringMap.empty
  in
  let payload_results = List.map (fun (fname, ftype) ->
    match HStringMap.find_opt fname arg_map with
    | Some e -> (fname, e), GI.empty ()
    | None ->
      let ftype', gf = desugar_type adt_map ctx ftype in
      let e, go = mk_fresh_adt_term_oracle pos ftype' in
      (fname, e), GI.union gf go
  ) info.all_payload_fields in
  let payload_flds, g = split2 payload_results in
  LA.RecordExpr (pos, info.type_name, [], (info.disc_field, disc_e) :: payload_flds), g

let desugar_type_decl adt_map ctx td =
  match td with
  | LA.AliasType (pos, name, ps, ty) ->
    let ty', g = desugar_type adt_map ctx ty in
    LA.AliasType (pos, name, ps, ty'), g
  | LA.FreeType _ -> td, GI.empty ()

let desugar_const_decl adt_map ctx cd =
  match cd with
  | LA.FreeConst (p, i, ty) ->
    let ty', g = desugar_type adt_map ctx ty in
    LA.FreeConst (p, i, ty'), g
  | LA.UntypedConst (p, i, e) ->
    let e', g = desugar_expr adt_map ctx e in
    LA.UntypedConst (p, i, e'), g
  | LA.TypedConst (p, i, e, ty) ->
    let e', g1 = desugar_expr adt_map ctx e in
    let ty', g2 = desugar_type adt_map ctx ty in
    LA.TypedConst (p, i, e', ty'), GI.union g1 g2

let desugar_clocked_typed_decl adt_map ctx (p, i, ty, c) =
  let ty', g = desugar_type adt_map ctx ty in
  (p, i, ty', c), g

let desugar_const_clocked_typed_decl adt_map ctx (p, i, ty, c, ic) =
  let ty', g = desugar_type adt_map ctx ty in
  (p, i, ty', c, ic), g

let desugar_node_local_decl adt_map ctx ld =
  match ld with
  | LA.NodeConstDecl (p, cd) ->
    let cd', g = desugar_const_decl adt_map ctx cd in
    LA.NodeConstDecl (p, cd'), g
  | LA.NodeVarDecl (p, ctd) ->
    let ctd', g = desugar_clocked_typed_decl adt_map ctx ctd in
    LA.NodeVarDecl (p, ctd'), g

let desugar_node_equation adt_map ctx eq =
  match eq with
  | LA.Assert (p, e) ->
    let e', g = desugar_expr adt_map ctx e in
    LA.Assert (p, e'), g
  | LA.Equation (p, lhs, e) ->
    let e', g = desugar_expr adt_map ctx e in
    LA.Equation (p, lhs, e'), g

let rec desugar_node_item adt_map ctx ni =
  match ni with
  | LA.Body eq ->
    let eq', g = desugar_node_equation adt_map ctx eq in
    LA.Body eq', g
  | LA.IfBlock (p, e, nis1, nis2) ->
    let e', g0 = desugar_expr adt_map ctx e in
    let nis1', g1 = split2 (List.map (desugar_node_item adt_map ctx) nis1) in
    let nis2', g2 = split2 (List.map (desugar_node_item adt_map ctx) nis2) in
    LA.IfBlock (p, e', nis1', nis2'), GI.union (GI.union g0 g1) g2
  | LA.FrameBlock (p, vars, eqs, nis) ->
    let eqs', g0 = split2 (List.map (desugar_node_equation adt_map ctx) eqs) in
    let nis', g1 = split2 (List.map (desugar_node_item adt_map ctx) nis) in
    LA.FrameBlock (p, vars, eqs', nis'), GI.union g0 g1
  | LA.AnnotProperty (p, name, e, kind) ->
    let e', g = desugar_expr adt_map ctx e in
    LA.AnnotProperty (p, name, e', kind), g
  | LA.AnnotMain _ as x -> x, GI.empty ()

let desugar_contract_node_eq adt_map ctx eq =
  let r_e e = desugar_expr adt_map ctx e in
  match eq with
  | LA.GhostConst cd ->
    let cd', g = desugar_const_decl adt_map ctx cd in
    LA.GhostConst cd', g
  | LA.GhostVars (p, LA.GhostVarDec (p2, tis), e) ->
    let e', ge = r_e e in
    let ti_results = List.map (fun (p3, id, ty) ->
      let ty', g = desugar_type adt_map ctx ty in (p3, id, ty'), g
    ) tis in
    let tis', gt = split2 ti_results in
    LA.GhostVars (p, LA.GhostVarDec (p2, tis'), e'), GI.union ge gt
  | LA.Assume (p, n, s, e) ->
    let e', g = r_e e in
    LA.Assume (p, n, s, e'), g
  | LA.Guarantee (p, n, s, e) ->
    let e', g = r_e e in
    LA.Guarantee (p, n, s, e'), g
  | LA.Mode (p, n, reqs, ensures) ->
    let req_results = List.map (fun (p2, n2, e) ->
      let e', g = r_e e in (p2, n2, e'), g
    ) reqs in
    let ens_results = List.map (fun (p2, n2, e) ->
      let e', g = r_e e in (p2, n2, e'), g
    ) ensures in
    let reqs', g0 = split2 req_results in
    let ensures', g1 = split2 ens_results in
    LA.Mode (p, n, reqs', ensures'), GI.union g0 g1
  | LA.ContractCall (p, id, tys, es, out_params) ->
    let tys', gt = split2 (List.map (desugar_type adt_map ctx) tys) in
    let es', ge = split2 (List.map (desugar_expr adt_map ctx) es) in
    LA.ContractCall (p, id, tys', es', out_params), GI.union gt ge
  | LA.AssumptionVars _ as av -> av, GI.empty ()

let desugar_contract adt_map ctx (p, eqs) =
  let eqs', g = split2 (List.map (desugar_contract_node_eq adt_map ctx) eqs) in
  (p, eqs'), g

let desugar_declaration adt_map ctx decl =
  match decl with
  | LA.TypeDecl (p, td) ->
    let td', _ = desugar_type_decl adt_map ctx td in
    (LA.TypeDecl (p, td'), NI.Map.empty)
  | LA.ConstDecl (p, cd) ->
    let cd', _ = desugar_const_decl adt_map ctx cd in
    (LA.ConstDecl (p, cd'), NI.Map.empty)
  | LA.NodeDecl (p, (nid, imp, opac, ps, inputs, outputs, locals, items, contract_opt)) ->
    let input_results = List.map (desugar_const_clocked_typed_decl adt_map ctx) inputs in
    let inputs', gi = split2 input_results in
    let output_results = List.map (desugar_clocked_typed_decl adt_map ctx) outputs in
    let outputs', go = split2 output_results in
    let locals', g0 = split2 (List.map (desugar_node_local_decl adt_map ctx) locals) in
    let items',  g1 = split2 (List.map (desugar_node_item adt_map ctx) items) in
    let contract_opt', g2 = match contract_opt with
      | None -> None, GI.empty ()
      | Some c -> let c', g = desugar_contract adt_map ctx c in Some c', g
    in
    let g = GI.union (GI.union (GI.union gi go) (GI.union g0 g1)) g2 in
    (LA.NodeDecl (p, (nid, imp, opac, ps, inputs', outputs', locals', items', contract_opt')),
     NI.Map.singleton nid g)
  | LA.FuncDecl (p, (nid, imp, opac, ps, inputs, outputs, locals, items, contract_opt)) ->
    let input_results = List.map (desugar_const_clocked_typed_decl adt_map ctx) inputs in
    let inputs', gi = split2 input_results in
    let output_results = List.map (desugar_clocked_typed_decl adt_map ctx) outputs in
    let outputs', go = split2 output_results in
    let locals', g0 = split2 (List.map (desugar_node_local_decl adt_map ctx) locals) in
    let items',  g1 = split2 (List.map (desugar_node_item adt_map ctx) items) in
    let contract_opt', g2 = match contract_opt with
      | None -> None, GI.empty ()
      | Some c -> let c', g = desugar_contract adt_map ctx c in Some c', g
    in
    let g = GI.union (GI.union (GI.union gi go) (GI.union g0 g1)) g2 in
    (LA.FuncDecl (p, (nid, imp, opac, ps, inputs', outputs', locals', items', contract_opt')),
     NI.Map.singleton nid g)
  | LA.ContractNodeDecl (p, (nid, ps, inputs, outputs, contract)) ->
    let input_results = List.map (desugar_const_clocked_typed_decl adt_map ctx) inputs in
    let inputs', gi = split2 input_results in
    let output_results = List.map (desugar_clocked_typed_decl adt_map ctx) outputs in
    let outputs', go = split2 output_results in
    let contract', gc = desugar_contract adt_map ctx contract in
    let g = GI.union (GI.union gi go) gc in
    (LA.ContractNodeDecl (p, (nid, ps, inputs', outputs', contract')), NI.Map.singleton nid g)
  | LA.NodeParamInst _ -> (decl, NI.Map.empty)

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
    Ctx.add_ty_syn acc_ctx type_name record_ty
  ) adt_map ctx

let desugar_adts_program ctx decls =
  let adt_map = build_adt_map decls in
  if HStringMap.is_empty adt_map then
    (decls, ctx, NI.Map.empty)
  else
    let decl_results = List.concat_map (fun decl ->
      match decl with
      | LA.TypeDecl (sp, LA.AliasType (_, name, _, LA.ADT (pos, _, _))) ->
        (match HStringMap.find_opt name adt_map with
        | Some info ->
          let enum_ty = LA.EnumType (pos, info.disc_enum, info.ctor_variants) in
          let enum_decl = LA.TypeDecl (sp, LA.AliasType (pos, info.disc_enum, [], enum_ty)) in
          let (decl', gids) = desugar_declaration adt_map ctx decl in
          [(enum_decl, NI.Map.empty); (decl', gids)]
        | None -> assert false)
      | _ ->
        let (decl', gids) = desugar_declaration adt_map ctx decl in
        [(decl', gids)]
    ) decls in
    let decls = List.map fst decl_results in
    let gids = List.fold_left
      (fun acc (_, g) -> NI.Map.merge GI.union_keys2 acc g)
      NI.Map.empty decl_results
    in
    let ctx = update_context adt_map ctx in
    (decls, ctx, gids)
