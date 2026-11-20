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
module AH = LustreAstHelpers
module IMap = HString.HStringMap

type env = {
  (* The constructors of every datatype, which a pattern variable cannot be *)
  ctors : A.SI.t;
  (* The fresh name of each binder in scope *)
  sub : A.ident IMap.t;
}

let wildcard = HString.mk_hstring "_"

let lookup env i =
  match IMap.find_opt i env.sub with Some i' -> i' | None -> i

let bind env i =
  let i' = AH.fresh_bound_ident i in
  i', { env with sub = IMap.add i i' env.sub }

let rec rename_type env ty =
  let r = rename_type env in
  match ty with
  | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _
  | A.AbstractType _ | A.EnumType _ -> ty
  (* The argument of a history type is a variable, possibly a binder *)
  | A.History (p, i) -> A.History (p, lookup env i)
  | A.UserType (p, args, id) -> A.UserType (p, List.map r args, id)
  | A.TupleType (p, tys) -> A.TupleType (p, List.map r tys)
  | A.GroupType (p, tys) -> A.GroupType (p, List.map r tys)
  | A.RecordType (p, id, tis) ->
    A.RecordType (p, id, List.map (fun (p, f, ty) -> (p, f, r ty)) tis)
  | A.ArrayType (p, (ty, e)) -> A.ArrayType (p, (r ty, rename_expr env e))
  | A.TArr (p, ty1, ty2) -> A.TArr (p, r ty1, r ty2)
  | A.RefinementType (p, (p2, i, ty), e) ->
    (* The binder's own type lies outside its scope *)
    let ty = r ty in
    let i, env = bind env i in
    A.RefinementType (p, (p2, i, ty), rename_expr env e)
  | A.Map (p, inf, kt, vt) -> A.Map (p, inf, r kt, r vt)
  | A.Set (p, inf, ty) -> A.Set (p, inf, r ty)
  | A.ADT (p, id, cons) ->
    A.ADT (p, id,
      List.map (fun (c, flds) -> (c, List.map (fun (f, ty) -> (f, r ty)) flds)) cons)

and rename_typed_ident env (p, i, ty) = (p, i, rename_type env ty)

(* A variable pattern named after a constructor is a constructor pattern, so it
   is left alone even under a binder of that name. The wildcard '_', which may
   occur several times in a pattern, keeps its name. *)
and bind_pattern env pat =
  let is_ctor i = A.SI.mem i env.ctors in
  let env =
    A.SI.fold (fun i env ->
      if is_ctor i then env
      else if HString.equal i wildcard then { env with sub = IMap.remove i env.sub }
      else snd (bind env i)
    ) (AH.pat_bound_vars pat) env
  in
  let rec rename_pat = function
    | A.VarPat (p, i) -> if is_ctor i then A.VarPat (p, i) else A.VarPat (p, lookup env i)
    | A.Pat (p, c, ps) -> A.Pat (p, c, List.map rename_pat ps)
  in
  rename_pat pat, env

and rename_expr env e =
  let r = rename_expr env in
  let rt = rename_type env in
  match e with
  | A.Ident (p, i) -> A.Ident (p, lookup env i)
  | A.ModeRef _ | A.Const _ | A.Last _ -> e
  | A.FieldProject (p, e, f, pk) ->
    let pk = match pk with
      | A.Unresolved | A.RecordField -> pk
      | A.Selector (o, ty, c) -> A.Selector (o, rt ty, c)
    in
    A.FieldProject (p, r e, f, pk)
  | A.UnaryOp (p, op, e) -> A.UnaryOp (p, op, r e)
  | A.BinaryOp (p, op, e1, e2) -> A.BinaryOp (p, op, r e1, r e2)
  | A.TernaryOp (p, op, e1, e2, e3) -> A.TernaryOp (p, op, r e1, r e2, r e3)
  | A.ConvOp (p, op, e) -> A.ConvOp (p, op, r e)
  | A.CompOp (p, op, e1, e2) -> A.CompOp (p, op, r e1, r e2)
  | A.AnyOp (p, (ip, i, ty), e) ->
    let ty = rt ty in
    let i, env' = bind env i in
    A.AnyOp (p, (ip, i, ty), rename_expr env' e)
  | A.ChooseOp (p, (ip, i, ty), e) ->
    let ty = rt ty in
    let i, env' = bind env i in
    A.ChooseOp (p, (ip, i, ty), rename_expr env' e)
  | A.Extract (p, e, i, j) -> A.Extract (p, r e, i, j)
  | A.RecordExpr (p, id, ps, flds) ->
    A.RecordExpr (p, id, List.map rt ps, List.map (fun (f, e) -> (f, r e)) flds)
  | A.GroupExpr (p, k, es) -> A.GroupExpr (p, k, List.map r es)
  | A.StructUpdate (p, e1, lois, e2) ->
    let lois = List.map (function
      | A.Label _ as l -> l
      | A.Index (p, e, k) -> A.Index (p, r e, k)
      | A.MapIndex (p, e) -> A.MapIndex (p, r e)
      | A.SetIndex (p, e) -> A.SetIndex (p, r e)
      | A.GenericIndex (p, e) -> A.GenericIndex (p, r e)
    ) lois in
    A.StructUpdate (p, r e1, lois, Option.map r e2)
  | A.EmptyMap (p, kv) -> A.EmptyMap (p, Option.map (fun (k, v) -> (rt k, rt v)) kv)
  | A.EmptySet (p, ty) -> A.EmptySet (p, Option.map rt ty)
  | A.ArrayConstr (p, e1, e2) -> A.ArrayConstr (p, r e1, r e2)
  | A.IndexAccess (p, e1, e2, k) -> A.IndexAccess (p, r e1, r e2, k)
  | A.Quantifier (p, q, tis, e) ->
    (* As in the type checker, a binder is in scope in the types of the binders
       after it, and a repeated name shadows the earlier binder *)
    let env', tis =
      List.fold_left_map (fun env (ip, i, ty) ->
        let ty = rename_type env ty in
        let i, env = bind env i in
        env, (ip, i, ty)
      ) env tis
    in
    A.Quantifier (p, q, tis, rename_expr env' e)
  | A.ArrayComprehension (p, bs, e) ->
    let env', bs =
      List.fold_left_map (fun env' (ip, i, n) ->
        let i, env' = bind env' i in
        env', (ip, i, r n)
      ) env bs
    in
    A.ArrayComprehension (p, bs, rename_expr env' e)
  | A.Restart (p, e1, e2) -> A.Restart (p, r e1, r e2)
  | A.RestartEvery (p, id, es, e) -> A.RestartEvery (p, id, List.map r es, r e)
  | A.Pre (p, e) -> A.Pre (p, r e)
  | A.Arrow (p, e1, e2) -> A.Arrow (p, r e1, r e2)
  | A.Fby (p, e1, e2) -> A.Fby (p, r e1, r e2)
  | A.Call (p, ty_args, id, es) -> A.Call (p, List.map rt ty_args, id, List.map r es)
  | A.TypeAscription (p, e, ty) -> A.TypeAscription (p, r e, rt ty)
  | A.ADTTerm (p, ty_args, c, es) -> A.ADTTerm (p, List.map rt ty_args, c, List.map r es)
  | A.Match (p, e, arms, ty) ->
    let arms = List.map (fun (pat, arm_e) ->
      let pat, env' = bind_pattern env pat in
      (pat, rename_expr env' arm_e)
    ) arms in
    A.Match (p, r e, arms, Option.map rt ty)
  | A.AbstractSymConst (p, ty) -> A.AbstractSymConst (p, rt ty)
  | A.ADTTester (p, e, c) -> A.ADTTester (p, r e, c)

let rename_const_decl env = function
  | A.FreeConst (p, i, ty) -> A.FreeConst (p, i, rename_type env ty)
  | A.UntypedConst (p, i, e) -> A.UntypedConst (p, i, rename_expr env e)
  | A.TypedConst (p, i, e, ty) ->
    A.TypedConst (p, i, rename_expr env e, rename_type env ty)

(* A left-hand side names the variables an equation defines, which are never
   binders, but its index expressions are evaluated in scope *)
let rec rename_struct_item env = function
  | A.SingleIdent _ | A.FieldSelection _ | A.ArrayDef _ as si -> si
  | A.TupleStructItem (p, sis) -> A.TupleStructItem (p, List.map (rename_struct_item env) sis)
  | A.TupleSelection (p, i, e) -> A.TupleSelection (p, i, rename_expr env e)
  | A.ArraySliceStructItem (p, i, slices) ->
    A.ArraySliceStructItem (p, i,
      List.map (fun (e1, e2) -> (rename_expr env e1, rename_expr env e2)) slices)

let rename_equation env = function
  | A.Assert (p, e) -> A.Assert (p, rename_expr env e)
  | A.Equation (p, A.StructDef (sp, sis), e) ->
    let sis = List.map (rename_struct_item env) sis in
    (* The indices of an element-wise array definition bind over its right-hand
       side only *)
    let rhs_env, sis =
      List.fold_left_map (fun rhs_env si -> match si with
        | A.ArrayDef (ap, i, is) ->
          let rhs_env, is = List.fold_left_map (fun rhs_env j ->
            let j, rhs_env = bind rhs_env j in rhs_env, j) rhs_env is
          in
          rhs_env, A.ArrayDef (ap, i, is)
        | A.SingleIdent _ | A.TupleStructItem _ | A.TupleSelection _
        | A.FieldSelection _ | A.ArraySliceStructItem _ -> rhs_env, si
      ) env sis
    in
    A.Equation (p, A.StructDef (sp, sis), rename_expr rhs_env e)

let rec rename_item env item =
  let ri = List.map (rename_item env) in
  let re = rename_expr env in
  match item with
  | A.Body eq -> A.Body (rename_equation env eq)
  | A.IfBlock (p, e, l1, l2) -> A.IfBlock (p, re e, ri l1, ri l2)
  | A.WhenBlock (p, e, l1, l2) -> A.WhenBlock (p, re e, ri l1, ri l2)
  | A.MatchBlock (p, e, arms, ty) ->
    let arms = List.map (fun (pat, items) ->
      let pat, env' = bind_pattern env pat in
      (pat, List.map (rename_item env') items)
    ) arms in
    A.MatchBlock (p, re e, arms, Option.map (rename_type env) ty)
  | A.RestartBlock (p, items, e) -> A.RestartBlock (p, ri items, re e)
  | A.FrameBlock (p, vars, eqs, items) ->
    A.FrameBlock (p, vars, List.map (rename_equation env) eqs, ri items)
  | A.AnnotProperty (p, name, e, A.Provided e2) ->
    A.AnnotProperty (p, name, re e, A.Provided (re e2))
  | A.AnnotProperty (p, name, e, (A.Invariant | A.Reachable _ as k)) ->
    A.AnnotProperty (p, name, re e, k)
  | A.AnnotMain _ | A.Auto _ -> item

let rename_contract_item env = function
  | A.GhostConst c -> A.GhostConst (rename_const_decl env c)
  | A.GhostVars (p, A.GhostVarDec (dp, tis), e) ->
    A.GhostVars (p, A.GhostVarDec (dp, List.map (rename_typed_ident env) tis),
      rename_expr env e)
  | A.GhostVars (p, A.GhostArrayDef (dp, ti, is), e) ->
    let ti = rename_typed_ident env ti in
    let env, is = List.fold_left_map (fun env j ->
      let j, env = bind env j in env, j) env is
    in
    A.GhostVars (p, A.GhostArrayDef (dp, ti, is), rename_expr env e)
  | A.Assume (p, name, soft, e) -> A.Assume (p, name, soft, rename_expr env e)
  | A.Guarantee (p, name, soft, e) -> A.Guarantee (p, name, soft, rename_expr env e)
  | A.Mode (p, name, reqs, enss) ->
    let rn (p, n, e) = (p, n, rename_expr env e) in
    A.Mode (p, name, List.map rn reqs, List.map rn enss)
  | A.ContractCall (p, id, ty_args, args, outs) ->
    A.ContractCall (p, id, List.map (rename_type env) ty_args,
      List.map (rename_expr env) args, outs)
  | A.AssumptionVars _ as item -> item
  | A.Decreases (p, e) -> A.Decreases (p, rename_expr env e)

let rename_contract env (p, items) = (p, List.map (rename_contract_item env) items)

let rename_inputs env =
  List.map (fun (p, i, ty, clk, is_const) -> (p, i, rename_type env ty, clk, is_const))

let rename_outputs env =
  List.map (fun (p, i, ty, clk) -> (p, i, rename_type env ty, clk))

let rename_node_decl env (id, ext, opac, params, ins, outs, locals, items, contract) =
  let locals = List.map (function
    | A.NodeVarDecl (p, (vp, i, ty, clk)) ->
      A.NodeVarDecl (p, (vp, i, rename_type env ty, clk))
    | A.NodeConstDecl (p, c) -> A.NodeConstDecl (p, rename_const_decl env c)
  ) locals in
  (id, ext, opac, params, rename_inputs env ins, rename_outputs env outs, locals,
   List.map (rename_item env) items, Option.map (rename_contract env) contract)

let rename_declaration env = function
  | A.TypeDecl (span, A.AliasType (p, i, ps, ty)) ->
    A.TypeDecl (span, A.AliasType (p, i, ps, rename_type env ty))
  | A.TypeDecl (_, A.FreeType _) as d -> d
  | A.ConstDecl (span, c) -> A.ConstDecl (span, rename_const_decl env c)
  | A.NodeDecl (span, nd) -> A.NodeDecl (span, rename_node_decl env nd)
  | A.FuncDecl (span, nd, attrs) -> A.FuncDecl (span, rename_node_decl env nd, attrs)
  | A.ContractNodeDecl (span, (id, params, ins, outs, c)) ->
    A.ContractNodeDecl (span,
      (id, params, rename_inputs env ins, rename_outputs env outs, rename_contract env c))
  | A.NodeParamInst (span, (i, n, tys)) ->
    A.NodeParamInst (span, (i, n, List.map (rename_type env) tys))

let constructors decls =
  List.fold_left (fun acc decl -> match decl with
    | A.TypeDecl (_, A.AliasType (_, _, _, A.ADT (_, _, cons))) ->
      List.fold_left (fun acc (c, _) -> A.SI.add c acc) acc cons
    | A.TypeDecl _ | A.ConstDecl _ | A.NodeDecl _ | A.FuncDecl _
    | A.ContractNodeDecl _ | A.NodeParamInst _ -> acc
  ) A.SI.empty decls

let rename_binders decls =
  let env = { ctors = constructors decls; sub = IMap.empty } in
  List.map (rename_declaration env) decls
