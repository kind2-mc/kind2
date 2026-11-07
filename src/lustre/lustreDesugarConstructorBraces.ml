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

module A = LustreAst
module R = Res
module NI = NodeId
module AH = LustreAstHelpers
module SM = HString.HStringMap

type error_kind =
  | ConstructorNamedAsType of HString.t
  | MissingConstructorField of HString.t * HString.t
  | UnknownConstructorField of HString.t * HString.t
  | RepeatedConstructorField of HString.t * HString.t

let error_message =
  let s = HString.string_of_hstring in
  function
  | ConstructorNamedAsType c ->
    "Constructor '" ^ s c ^ "' has the same name as a type. A constructor may "
    ^ "only be named after the datatype that declares it."
  | MissingConstructorField (f, c) ->
    "Missing field '" ^ s f ^ "' in constructor '" ^ s c ^ "'"
  | UnknownConstructorField (f, c) ->
    "Constructor '" ^ s c ^ "' has no field '" ^ s f ^ "'"
  | RepeatedConstructorField (f, c) ->
    "Field '" ^ s f ^ "' is given more than once in constructor '" ^ s c ^ "'"

type error = [
  | `LustreDesugarConstructorBracesError of Lib.position * error_kind
]

(* Raised deep in the walk, under the non-monadic LustreAstHelpers.map_lustre_ty,
   and turned into an error at the entry point *)
exception Brace_error of Lib.position * error_kind

(* A constructor may only share its name with the datatype declaring it *)
let check_name_clashes decls =
  let type_names = List.fold_left (fun acc -> function
    | A.TypeDecl (_, (A.AliasType (_, id, _, _) | A.FreeType (_, id))) -> A.SI.add id acc
    | A.ConstDecl _ | A.NodeDecl _ | A.FuncDecl _
    | A.ContractNodeDecl _ | A.NodeParamInst _ -> acc
  ) A.SI.empty decls
  in
  let check_decl = function
    | A.TypeDecl (_, A.AliasType (pos, owner, _, A.ADT (_, _, ctors))) ->
      List.iter (fun (c, _) ->
        if A.SI.mem c type_names && not (HString.equal c owner) then
          raise (Brace_error (pos, ConstructorNamedAsType c))
      ) ctors
    | A.TypeDecl _ | A.ConstDecl _ | A.NodeDecl _ | A.FuncDecl _
    | A.ContractNodeDecl _ | A.NodeParamInst _ -> ()
  in
  List.iter check_decl decls

(* Each constructor's field names, in declaration order. A constructor declared
   twice is left out, for the type checker to report. *)
let collect_constructors decls =
  let declared = List.concat_map (function
    | A.TypeDecl (_, A.AliasType (_, _, _, A.ADT (_, _, ctors))) -> ctors
    | A.TypeDecl _ | A.ConstDecl _ | A.NodeDecl _ | A.FuncDecl _
    | A.ContractNodeDecl _ | A.NodeParamInst _ -> []
  ) decls
  in
  let count c = List.length (List.filter (fun (c', _) -> HString.equal c c') declared) in
  List.fold_left (fun acc (c, fields) ->
    if count c > 1 then acc else SM.add c (List.map fst fields) acc
  ) SM.empty declared

type ctors = {
  fields : HString.t list SM.t;
  in_type_decl : bool;
  in_constant_type : bool;
}

(* The values of the given fields, in declaration order *)
let order_fields pos ctor declared fields =
  let check_field seen (f, _) =
    if not (List.exists (HString.equal f) declared) then
      raise (Brace_error (pos, UnknownConstructorField (f, ctor)));
    if A.SI.mem f seen then
      raise (Brace_error (pos, RepeatedConstructorField (f, ctor)));
    A.SI.add f seen
  in
  let _ : A.SI.t = List.fold_left check_field A.SI.empty fields in
  List.map (fun f ->
    match List.find_opt (fun (g, _) -> HString.equal f g) fields with
    | Some (_, e) -> e
    | None -> raise (Brace_error (pos, MissingConstructorField (f, ctor)))
  ) declared

(* The form the parser gives a positional constructor, so both forms are treated
   alike. Only an ADTTerm takes fields and type arguments, or stays legal in the
   predicate of a global type. A Call in the type of a constant is rejected. *)
let mk_constructor ctors pos ty_args name args =
  let call () = A.Call (pos, ty_args, NI.mk_node_id name, args) in
  let term () = A.ADTTerm (pos, ty_args, name, args) in
  match ty_args, args with
  | [], [] -> A.Ident (pos, name)
  | _ :: _, [] -> term ()
  | [], _ :: _ -> if ctors.in_type_decl then term () else call ()
  | _ :: _, _ :: _ -> if ctors.in_constant_type then call () else term ()

let rec rw_ty ctors ty = AH.map_lustre_ty (rw_expr ctors) ty

(* A type that must be constant: of a constant, ghost, quantified variable or
   type argument of a call. The predicate of a global type is exempt. *)
and rw_constant_ty ctors ty =
  rw_ty { ctors with in_constant_type = not ctors.in_type_decl } ty

and rw_typed_ident ctors (pos, id, ty) = (pos, id, rw_ty ctors ty)

and rw_expr ctors e =
  let r = rw_expr ctors in
  let rt = rw_ty ctors in
  let rti = rw_typed_ident ctors in
  match e with
  | A.RecordExpr (pos, name, ty_args, fields) ->
    let ty_args = List.map rt ty_args in
    let fields = List.map (fun (f, e) -> (f, r e)) fields in
    (match SM.find_opt name ctors.fields with
     | Some declared ->
       mk_constructor ctors pos ty_args name (order_fields pos name declared fields)
     | None -> A.RecordExpr (pos, name, ty_args, fields))
  | A.Ident _ | A.ModeRef _ | A.Const _ | A.Last _
  | A.EmptyMap (_, None) | A.EmptySet (_, None) -> e
  | A.EmptyMap (p, Some (kt, vt)) -> A.EmptyMap (p, Some (rt kt, rt vt))
  | A.EmptySet (p, Some ty) -> A.EmptySet (p, Some (rt ty))
  | A.AbstractSymConst (p, ty) -> A.AbstractSymConst (p, rt ty)
  | A.FieldProject (p, e, idx, kind) ->
    let kind = match kind with
      | A.Unresolved | A.RecordField -> kind
      | A.Selector (origin, ty, c) -> A.Selector (origin, rt ty, c)
    in
    A.FieldProject (p, r e, idx, kind)
  | A.Extract (p, e, i1, i2) -> A.Extract (p, r e, i1, i2)
  | A.UnaryOp (p, op, e) -> A.UnaryOp (p, op, r e)
  | A.BinaryOp (p, op, e1, e2) -> A.BinaryOp (p, op, r e1, r e2)
  | A.TernaryOp (p, op, e1, e2, e3) -> A.TernaryOp (p, op, r e1, r e2, r e3)
  | A.ConvOp (p, op, e) -> A.ConvOp (p, op, r e)
  | A.CompOp (p, op, e1, e2) -> A.CompOp (p, op, r e1, r e2)
  | A.AnyOp (p, ti, e) -> A.AnyOp (p, rti ti, r e)
  | A.ChooseOp (p, ti, e) -> A.ChooseOp (p, rti ti, r e)
  | A.GroupExpr (p, k, es) -> A.GroupExpr (p, k, List.map r es)
  | A.StructUpdate (p, e1, idx, e2) ->
    A.StructUpdate (p, r e1, List.map (rw_label_or_index ctors) idx, Option.map r e2)
  | A.ArrayConstr (p, e1, e2) -> A.ArrayConstr (p, r e1, r e2)
  | A.IndexAccess (p, e1, e2, k) -> A.IndexAccess (p, r e1, r e2, k)
  | A.Quantifier (p, q, tis, e) ->
    let tis = List.map (fun (tp, i, ty) -> (tp, i, rw_constant_ty ctors ty)) tis in
    A.Quantifier (p, q, tis, r e)
  | A.ArrayComprehension (p, bs, e) ->
    A.ArrayComprehension (p, List.map (fun (bp, i, n) -> (bp, i, r n)) bs, r e)
  | A.Restart (p, e1, e2) -> A.Restart (p, r e1, r e2)
  | A.RestartEvery (p, i, es, e) -> A.RestartEvery (p, i, List.map r es, r e)
  | A.Pre (p, e) -> A.Pre (p, r e)
  | A.Arrow (p, e1, e2) -> A.Arrow (p, r e1, r e2)
  | A.Fby (p, e1, e2) -> A.Fby (p, r e1, r e2)
  | A.Call (p, ty_args, i, es) ->
    A.Call (p, List.map (rw_constant_ty ctors) ty_args, i, List.map r es)
  | A.TypeAscription (p, e, ty) -> A.TypeAscription (p, r e, rt ty)
  | A.ADTTerm (p, ty_args, c, es) -> A.ADTTerm (p, List.map rt ty_args, c, List.map r es)
  | A.Match (p, e, arms, ty) ->
    A.Match (p, r e, List.map (fun (pat, e) -> (pat, r e)) arms, Option.map rt ty)
  | A.ADTTester (p, e, c) -> A.ADTTester (p, r e, c)

and rw_label_or_index ctors = function
  | A.Label _ as l -> l
  | A.Index (p, e, k) -> A.Index (p, rw_expr ctors e, k)
  | A.MapIndex (p, e) -> A.MapIndex (p, rw_expr ctors e)
  | A.SetIndex (p, e) -> A.SetIndex (p, rw_expr ctors e)
  | A.GenericIndex (p, e) -> A.GenericIndex (p, rw_expr ctors e)

let rec rw_struct_item ctors item =
  let r = rw_expr ctors in
  match item with
  | A.SingleIdent _ | A.FieldSelection _ | A.ArrayDef _ -> item
  | A.TupleStructItem (p, items) ->
    A.TupleStructItem (p, List.map (rw_struct_item ctors) items)
  | A.TupleSelection (p, i, e) -> A.TupleSelection (p, i, r e)
  | A.ArraySliceStructItem (p, i, slices) ->
    A.ArraySliceStructItem (p, i, List.map (fun (e1, e2) -> (r e1, r e2)) slices)

let rw_equation ctors = function
  | A.Assert (p, e) -> A.Assert (p, rw_expr ctors e)
  | A.Equation (p, A.StructDef (sp, items), e) ->
    let items = List.map (rw_struct_item ctors) items in
    A.Equation (p, A.StructDef (sp, items), rw_expr ctors e)

let rec rw_node_item ctors item =
  let r = rw_expr ctors in
  let ris = List.map (rw_node_item ctors) in
  match item with
  | A.Body eq -> A.Body (rw_equation ctors eq)
  | A.IfBlock (p, e, l1, l2) -> A.IfBlock (p, r e, ris l1, ris l2)
  | A.WhenBlock (p, e, l1, l2) -> A.WhenBlock (p, r e, ris l1, ris l2)
  | A.MatchBlock (p, e, arms, ty) ->
    A.MatchBlock (p, r e,
                  List.map (fun (pat, items) -> (pat, ris items)) arms,
                  Option.map (rw_ty ctors) ty)
  | A.RestartBlock (p, items, e) -> A.RestartBlock (p, ris items, r e)
  | A.FrameBlock (p, vars, eqs, items) ->
    A.FrameBlock (p, vars, List.map (rw_equation ctors) eqs, ris items)
  | A.AnnotProperty (p, name, e, kind) ->
    let kind = match kind with
      | A.Invariant | A.Reachable _ -> kind
      | A.Provided e -> A.Provided (r e)
    in
    A.AnnotProperty (p, name, r e, kind)
  | A.AnnotMain _ | A.Auto _ -> item

let rw_const_decl ctors = function
  | A.FreeConst (p, i, ty) -> A.FreeConst (p, i, rw_constant_ty ctors ty)
  | A.UntypedConst (p, i, e) -> A.UntypedConst (p, i, rw_expr ctors e)
  | A.TypedConst (p, i, e, ty) -> A.TypedConst (p, i, rw_expr ctors e, rw_constant_ty ctors ty)

(* A declared type. Only its refinement predicates are exempt from the rules for
   a positional constructor. *)
let rec rw_declared_ty ctors ty =
  let r = rw_declared_ty ctors in
  match ty with
  | A.Int _ | A.Bool _ | A.Real _ | A.SBitVector _ | A.UBitVector _
  | A.EnumType _ | A.AbstractType _ | A.History _ -> ty
  | A.UserType (p, args, id) -> A.UserType (p, List.map r args, id)
  | A.Map (p, kt, vt) -> A.Map (p, r kt, r vt)
  | A.Set (p, ty) -> A.Set (p, r ty)
  | A.ArrayType (p, (ty, len)) ->
    A.ArrayType (p, (r ty, rw_expr { ctors with in_constant_type = true } len))
  | A.TArr (p, ty1, ty2) -> A.TArr (p, r ty1, r ty2)
  | A.GroupType (p, tys) -> A.GroupType (p, List.map r tys)
  | A.TupleType (p, tys) -> A.TupleType (p, List.map r tys)
  | A.RecordType (p, id, tis) ->
    A.RecordType (p, id, List.map (fun (fp, f, ty) -> (fp, f, r ty)) tis)
  | A.RefinementType (p1, (p2, id, ty), e) ->
    A.RefinementType (p1, (p2, id, r ty), rw_expr { ctors with in_type_decl = true } e)
  | A.ADT (p, id, cons) ->
    A.ADT (p, id, List.map (fun (c, flds) -> (c, List.map (fun (f, ty) -> (f, r ty)) flds)) cons)

let rw_type_decl ctors = function
  | A.AliasType (p, i, params, ty) -> A.AliasType (p, i, params, rw_declared_ty ctors ty)
  | A.FreeType _ as d -> d

let rw_contract_item ctors item =
  let r = rw_expr ctors in
  let rti (p, i, ty) = (p, i, rw_constant_ty ctors ty) in
  let named_expr (p, name, e) = (p, name, r e) in
  match item with
  | A.GhostConst d -> A.GhostConst (rw_const_decl ctors d)
  | A.GhostVars (p, A.GhostVarDec (lp, tis), e) ->
    A.GhostVars (p, A.GhostVarDec (lp, List.map rti tis), r e)
  | A.GhostVars (p, A.GhostArrayDef (lp, ti, ids), e) ->
    A.GhostVars (p, A.GhostArrayDef (lp, rti ti, ids), r e)
  | A.Assume (p, name, soft, e) -> A.Assume (p, name, soft, r e)
  | A.Guarantee (p, name, soft, e) -> A.Guarantee (p, name, soft, r e)
  | A.Mode (p, id, reqs, ens) ->
    A.Mode (p, id, List.map named_expr reqs, List.map named_expr ens)
  | A.ContractCall (p, id, ty_args, es, rets) ->
    A.ContractCall (p, id, List.map (rw_ty ctors) ty_args, List.map r es, rets)
  | A.AssumptionVars _ -> item
  | A.Decreases (p, e) -> A.Decreases (p, r e)

let rw_contract ctors (p, items) = (p, List.map (rw_contract_item ctors) items)

let rw_inputs ctors =
  List.map (fun (p, i, ty, clock, is_const) -> (p, i, rw_ty ctors ty, clock, is_const))

let rw_outputs ctors = List.map (fun (p, i, ty, clock) -> (p, i, rw_ty ctors ty, clock))

let rw_local ctors = function
  | A.NodeConstDecl (p, d) -> A.NodeConstDecl (p, rw_const_decl ctors d)
  | A.NodeVarDecl (p, (vp, i, ty, clock)) ->
    A.NodeVarDecl (p, (vp, i, rw_ty ctors ty, clock))

let rw_node_decl ctors (id, imported, opacity, params, ins, outs, locals, items, contract) =
  ( id, imported, opacity, params,
    rw_inputs ctors ins, rw_outputs ctors outs,
    List.map (rw_local ctors) locals,
    List.map (rw_node_item ctors) items,
    Option.map (rw_contract ctors) contract )

let rw_declaration ctors = function
  | A.TypeDecl (s, d) -> A.TypeDecl (s, rw_type_decl ctors d)
  | A.ConstDecl (s, d) -> A.ConstDecl (s, rw_const_decl ctors d)
  | A.NodeDecl (s, d) -> A.NodeDecl (s, rw_node_decl ctors d)
  | A.FuncDecl (s, d, attrs) -> A.FuncDecl (s, rw_node_decl ctors d, attrs)
  | A.ContractNodeDecl (s, (id, params, ins, outs, contract)) ->
    A.ContractNodeDecl (s, (id, params, rw_inputs ctors ins, rw_outputs ctors outs,
                            rw_contract ctors contract))
  | A.NodeParamInst (s, (id, base, tys)) ->
    A.NodeParamInst (s, (id, base, List.map (rw_ty ctors) tys))

let desugar_constructor_braces decls =
  try
    check_name_clashes decls;
    let ctors = { fields = collect_constructors decls; in_type_decl = false; in_constant_type = false } in
    R.ok (List.map (rw_declaration ctors) decls)
  with Brace_error (pos, kind) ->
    Error (`LustreDesugarConstructorBracesError (pos, kind))
