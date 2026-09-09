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

(* Check match expressions for redundant/unreachable patterns and incomplete
    pattern coverage. *)

module A = LustreAst
module Ctx = TypeCheckerContext
module TC = LustreTypeChecker
module R = Res

let (let*) = R.(>>=)

type error_kind =
  | RedundantPattern of A.pattern
  | IncompletePatternMatch 

type error = [ `LustreCheckMatchExpressionsError of Lib.position * error_kind ]

let error_message = function
  | RedundantPattern (patt) ->
    Format.asprintf "Redundant pattern: %a" 
      A.pp_print_pattern patt
  | IncompletePatternMatch ->
    "Incomplete pattern match: cases are not exhaustive"

let mk_error pos kind = Error (`LustreCheckMatchExpressionsError (pos, kind))

type pat =
  | Wild
  | Ctor of A.ident * pat list

let rec pat_of_ast = function
  | A.VarPat _ -> Wild
  | A.Pat (_, ctor, sub_pats) -> Ctor (ctor, List.map pat_of_ast sub_pats)

let pos_of_pattern = function
  | A.VarPat (pos, _) | A.Pat (pos, _, _) -> pos

let base_type ctx ty = R.safe_unwrap ty (TC.expand_type_syn_reftype_history ctx ty)

(* The constructors of [ty]'s datatype, in declaration order, each paired with
   its (already instantiated) field types. [None] if [ty] is not a datatype. *)
let signature_of_type ctx ty =
  match base_type ctx ty with
  | A.ADT (_, _, ctors) ->
    Some (List.map (fun (c, fields) -> (c, List.map snd fields)) ctors)
  | A.Bool _ | A.Int _ | A.SBitVector _ | A.UBitVector _ | A.Real _
  | A.UserType _ | A.AbstractType _ | A.TupleType _ | A.GroupType _
  | A.RecordType _ | A.ArrayType _ | A.EnumType _ | A.History _
  | A.TArr _ | A.RefinementType _ | A.Map _ | A.Set _ -> None

(* Field types of constructor [ctor] in [ty]'s datatype. A constructor pattern
   only type checks against the datatype declaring it, so the lookup succeeds. *)
let field_types ctx ty ctor =
  match signature_of_type ctx ty with
  | None -> assert false
  | Some signature ->
    match List.find_opt (fun (c, _) -> HString.equal c ctor) signature with
    | None -> assert false
    | Some (_, field_tys) -> field_tys

(* Root constructors of a matrix's first column *)
let head_ctors matrix =
  List.filter_map (function
    | Ctor (c, _) :: _ -> Some c
    | Wild :: _ -> None
    | [] -> assert false)
    matrix

(* The whole signature of [ty]'s datatype when [ctors] covers all of it. An
   empty [ctors] is never complete: a datatype has at least one constructor. *)
let complete_signature ctx ty ctors =
  match signature_of_type ctx ty with
  | None -> None
  | Some signature ->
    if List.for_all
         (fun (c, _) -> List.exists (HString.equal c) ctors) signature
    then Some signature
    else None

(* Specialized matrix S(c, P): the rows whose first pattern is [ctor] or a
   wildcard, with that pattern replaced by the constructor's arguments
   ([arity] wildcards in the wildcard case). *)
let specialize ctor arity matrix =
  List.filter_map (function
    | Wild :: tl -> Some (List.init arity (fun _ -> Wild) @ tl)
    | Ctor (c, args) :: tl ->
      if HString.equal c ctor then Some (args @ tl) else None
    | [] -> assert false)
    matrix

(* Default matrix D(P): the rows whose first pattern is a wildcard, with that
   pattern dropped *)
let default_matrix matrix =
  List.filter_map (function
    | Wild :: tl -> Some tl
    | Ctor _ :: _ -> None
    | [] -> assert false)
    matrix

(* Is there a value vector that [q] filters and that no row of [matrix]
   filters? [tys] holds the type of each column; it is what decides whether the
   root constructors of a column form a complete signature. *)
let rec useful ctx tys matrix q =
  match tys, q with
  (* No column left: only an empty matrix leaves a value vector unmatched *)
  | [], [] -> (match matrix with [] -> true | _ :: _ -> false)
  (* The type vector is kept in step with the pattern vector *)
  | [], _ :: _ | _ :: _, [] -> assert false
  | ty :: tys, p :: q -> (
    match p with
    | Ctor (ctor, args) ->
      useful ctx (field_types ctx ty ctor @ tys)
        (specialize ctor (List.length args) matrix) (args @ q)
    | Wild -> (
      match complete_signature ctx ty (head_ctors matrix) with
      (* Every value of this column has one of these constructors as its root,
         so it suffices to look for an unmatched value under each of them *)
      | Some signature ->
        List.exists (fun (ctor, field_tys) ->
          let arity = List.length field_tys in
          useful ctx (field_tys @ tys) (specialize ctor arity matrix)
            (List.init arity (fun _ -> Wild) @ q))
          signature
      (* Some constructor is missing from the column, so an unmatched value can
         be built from it, and only the rows starting with a wildcard matter *)
      | None -> useful ctx tys (default_matrix matrix) q
    )
  )

(* Report the first arm that no value can reach, then a match that leaves some
   value of the scrutinee's type unmatched. *)
let check_arms ctx pos scrut_ty arms =
  let* matrix =
    R.seq_chain (fun matrix (ast_pat, pat) ->
      if useful ctx [scrut_ty] matrix [pat] then R.ok (matrix @ [[pat]])
      else mk_error (pos_of_pattern ast_pat) (RedundantPattern ast_pat))
      [] arms
  in
  if useful ctx [scrut_ty] matrix [Wild] then
    mk_error pos IncompletePatternMatch
  else R.ok ()

let check_match (ctx, pos, arms, scrut_ty_opt) =
  match scrut_ty_opt with
  | Some scrut_ty ->
    let arms = List.map (fun (ast_pat, _) -> (ast_pat, pat_of_ast ast_pat)) arms in
    check_arms ctx pos scrut_ty arms
  (* The type checker records the scrutinee's datatype in every match it checks,
     and every match in the AST it hands on has been checked *)
  | None -> assert false

(* The bindings a pattern introduces, resolved against the type of the value it
   matches *)
let rec bind_pattern ctx ty = function
  | A.VarPat (_, id) -> Ctx.add_ty ctx id ty
  | A.Pat (_, ctor, sub_pats) ->
    List.fold_left2 bind_pattern ctx (field_types ctx ty ctor) sub_pats

(* Context, position, arms and scrutinee type of every match expression
   occurring in [expr], nested ones included *)
let rec matches_of_expr ctx expr =
  let r = matches_of_expr ctx in
  let rlist es = List.concat_map r es in
  let rty ty = matches_of_type ctx ty in
  let rtys tys = List.concat_map rty tys in
  let rloi = function
    | A.Label _ -> []
    | A.Index (_, e, _) | A.MapIndex (_, e) | A.SetIndex (_, e)
    | A.GenericIndex (_, e) -> r e
  in
  match expr with
  | A.Match (pos, e, arms, ty_opt) ->
    let arm_body (pat, body) =
      let arm_ctx = match ty_opt with
        | Some scrut_ty -> bind_pattern ctx scrut_ty pat
        | None -> ctx
      in
      matches_of_expr arm_ctx body
    in
    (ctx, pos, arms, ty_opt) :: (r e @ List.concat_map arm_body arms)
  | A.Ident _ | A.ModeRef _ | A.Const _ | A.Last _ | A.AbstractSymConst _ -> []
  | A.EmptyMap (_, None) | A.EmptySet (_, None) -> []
  | A.EmptyMap (_, Some (kt, vt)) -> rty kt @ rty vt
  | A.EmptySet (_, Some ty) -> rty ty
  | A.FieldProject (_, e, _, _) | A.UnaryOp (_, _, e) | A.ConvOp (_, _, e)
  | A.When (_, e, _) | A.Extract (_, e, _, _) | A.Pre (_, e)
  | A.ADTTester (_, e, _) -> r e
  | A.BinaryOp (_, _, e1, e2) | A.CompOp (_, _, e1, e2)
  | A.ArrayConstr (_, e1, e2) | A.IndexAccess (_, e1, e2, _)
  | A.Arrow (_, e1, e2) -> r e1 @ r e2
  | A.TernaryOp (_, _, e1, e2, e3) -> r e1 @ r e2 @ r e3
  | A.RecordExpr (_, _, ty_args, flds) ->
    rtys ty_args @ rlist (List.map snd flds)
  | A.GroupExpr (_, _, es) -> rlist es
  | A.StructUpdate (_, e, idx, e_opt) ->
    r e @ List.concat_map rloi idx
    @ (match e_opt with Some e -> r e | None -> [])
  | A.Quantifier (_, _, tis, e) ->
    let ctx = List.fold_left (fun ctx (_, i, ty) -> Ctx.add_ty ctx i ty) ctx tis in
    rtys (List.map (fun (_, _, ty) -> ty) tis) @ matches_of_expr ctx e
  | A.AnyOp (_, (_, i, ty), e) | A.ChooseOp (_, (_, i, ty), e) ->
    rty ty @ matches_of_expr (Ctx.add_ty ctx i ty) e
  | A.Condact (_, e1, e2, _, es1, es2) -> r e1 @ r e2 @ rlist es1 @ rlist es2
  | A.Activate (_, _, e1, e2, es) -> r e1 @ r e2 @ rlist es
  | A.Merge (_, _, flds) -> rlist (List.map snd flds)
  | A.RestartEvery (_, _, es, e) -> rlist es @ r e
  | A.Call (_, ty_args, _, es) -> rtys ty_args @ rlist es
  | A.TypeAscription (_, e, ty) -> r e @ rty ty
  | A.ADTTerm (_, ty_args, _, args) -> rtys ty_args @ rlist args

(* Matches occurring in the expressions [ty] embeds: array sizes and refinement
   predicates, in [ty]'s type arguments as well as in [ty] itself *)
and matches_of_type ctx ty =
  let r = matches_of_type ctx in
  match ty with
  | A.Bool _ | A.Int _ | A.Real _ | A.SBitVector _ | A.UBitVector _
  | A.EnumType _ | A.AbstractType _ | A.History _ -> []
  | A.UserType (_, ty_args, _) -> List.concat_map r ty_args
  | A.TupleType (_, tys) | A.GroupType (_, tys) -> List.concat_map r tys
  | A.RecordType (_, _, tis) -> List.concat_map (fun (_, _, ty) -> r ty) tis
  | A.Map (_, kt, vt) -> r kt @ r vt
  | A.TArr (_, ty1, ty2) -> r ty1 @ r ty2
  | A.Set (_, ty) -> r ty
  | A.ArrayType (_, (ty, e)) -> r ty @ matches_of_expr ctx e
  | A.RefinementType (_, (_, i, ty), e) ->
    r ty @ matches_of_expr (Ctx.add_ty ctx i ty) e
  | A.ADT (_, _, ctors) ->
    List.concat_map
      (fun (_, fields) -> List.concat_map (fun (_, ty) -> r ty) fields) ctors

(* A constant declaration's matches, and the context extended with its binding *)
let matches_of_const_decl ctx = function
  | A.FreeConst (_, i, ty) -> (Ctx.add_ty ctx i ty, matches_of_type ctx ty)
  | A.UntypedConst (_, _, e) -> (ctx, matches_of_expr ctx e)
  | A.TypedConst (_, i, e, ty) ->
    (Ctx.add_ty ctx i ty, matches_of_expr ctx e @ matches_of_type ctx ty)

let rec matches_of_struct_item ctx = function
  | A.SingleIdent _ | A.FieldSelection _ | A.ArrayDef _ -> []
  | A.TupleStructItem (_, sis) -> List.concat_map (matches_of_struct_item ctx) sis
  | A.TupleSelection (_, _, e) -> matches_of_expr ctx e
  | A.ArraySliceStructItem (_, _, bounds) ->
    List.concat_map
      (fun (e1, e2) -> matches_of_expr ctx e1 @ matches_of_expr ctx e2) bounds

let matches_of_equation ctx = function
  | A.Assert (_, e) -> matches_of_expr ctx e
  | A.Equation (_, A.StructDef (_, sis), e) ->
    List.concat_map (matches_of_struct_item ctx) sis @ matches_of_expr ctx e

let rec matches_of_node_item ctx item =
  let ri = List.concat_map (matches_of_node_item ctx) in
  match item with
  | A.Auto _ | A.AnnotMain _ -> []
  | A.Body eq -> matches_of_equation ctx eq
  | A.AnnotProperty (_, _, e, A.Provided e2) ->
    matches_of_expr ctx e @ matches_of_expr ctx e2
  | A.AnnotProperty (_, _, e, (A.Invariant | A.Reachable _)) -> matches_of_expr ctx e
  | A.IfBlock (_, e, items1, items2) | A.WhenBlock (_, e, items1, items2) ->
    matches_of_expr ctx e @ ri items1 @ ri items2
  | A.FrameBlock (_, _, eqs, items) ->
    List.concat_map (matches_of_equation ctx) eqs @ ri items

(* A contract item's matches, and the context extended with the bindings it
   introduces: a later item can refer to a ghost constant or variable *)
let matches_of_contract_item ctx = function
  | A.Assume (_, _, _, e) | A.Guarantee (_, _, _, e) | A.Decreases (_, e) ->
    (ctx, matches_of_expr ctx e)
  | A.Mode (_, _, requires, ensures) ->
    (ctx, List.concat_map (fun (_, _, e) -> matches_of_expr ctx e) (requires @ ensures))
  | A.ContractCall (_, _, ty_args, inputs, _) ->
    (ctx,
     List.concat_map (matches_of_type ctx) ty_args
     @ List.concat_map (matches_of_expr ctx) inputs)
  | A.GhostConst cd -> matches_of_const_decl ctx cd
  | A.GhostVars (_, A.GhostVarDec (_, tis), e) ->
    let matches =
      List.concat_map (fun (_, _, ty) -> matches_of_type ctx ty) tis
      @ matches_of_expr ctx e
    in
    (List.fold_left (fun ctx (_, i, ty) -> Ctx.add_ty ctx i ty) ctx tis, matches)
  | A.AssumptionVars _ -> (ctx, [])

let matches_of_contract ctx (_, items) =
  List.fold_left (fun (ctx, acc) item ->
    let ctx, matches = matches_of_contract_item ctx item in
    (ctx, acc @ matches))
    (ctx, []) items
  |> snd

(* The check resolves the types it is given (a [history] type in particular) in
   the context of the match, so a node's or contract's own bindings have to be in
   scope in its body *)
let add_interface_ctx ctx inputs outputs =
  let ctx =
    List.fold_left (fun ctx (_, i, ty, _, _) -> Ctx.add_ty ctx i ty) ctx inputs
  in
  List.fold_left (fun ctx (_, i, ty, _) -> Ctx.add_ty ctx i ty) ctx outputs

let matches_of_node ctx (_, _, _, _, inputs, outputs, locals, items, contract) =
  let ctx = add_interface_ctx ctx inputs outputs in
  let ctx =
    List.fold_left (fun ctx -> function
      | A.NodeConstDecl (_, (A.FreeConst (_, i, ty) | A.TypedConst (_, i, _, ty)))
      | A.NodeVarDecl (_, (_, i, ty, _)) -> Ctx.add_ty ctx i ty
      | A.NodeConstDecl (_, A.UntypedConst _) -> ctx)
      ctx locals
  in
  List.concat_map (fun (_, _, ty, _, _) -> matches_of_type ctx ty) inputs
  @ List.concat_map (fun (_, _, ty, _) -> matches_of_type ctx ty) outputs
  @ List.concat_map (function
      | A.NodeConstDecl (_, cd) -> snd (matches_of_const_decl ctx cd)
      | A.NodeVarDecl (_, (_, _, ty, _)) -> matches_of_type ctx ty)
      locals
  @ List.concat_map (matches_of_node_item ctx) items
  @ (match contract with Some c -> matches_of_contract ctx c | None -> [])

let matches_of_declaration ctx = function
  | A.TypeDecl (_, A.AliasType (_, _, _, ty)) -> matches_of_type ctx ty
  | A.TypeDecl (_, A.FreeType _) -> []
  | A.ConstDecl (_, cd) -> snd (matches_of_const_decl ctx cd)
  | A.NodeDecl (_, nd) | A.FuncDecl (_, nd, _) -> matches_of_node ctx nd
  | A.ContractNodeDecl (_, (_, _, inputs, outputs, contract)) ->
    let ctx = add_interface_ctx ctx inputs outputs in
    List.concat_map (fun (_, _, ty, _, _) -> matches_of_type ctx ty) inputs
    @ List.concat_map (fun (_, _, ty, _) -> matches_of_type ctx ty) outputs
    @ matches_of_contract ctx contract
  | A.NodeParamInst (_, (_, _, tys)) -> List.concat_map (matches_of_type ctx) tys

let check_match_expressions (ctx : Ctx.tc_context) (ast : A.t) : (A.t, [> error]) result =
  let* () =
    R.seq_chain (fun () m -> check_match m) ()
      (List.concat_map (matches_of_declaration ctx) ast)
  in
  Ok ast
