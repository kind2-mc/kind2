(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(**
@author Andrew Marmaduke *)

open Lib
module LA = LustreAst
module Ctx = TypeCheckerContext
module TC = LustreTypeChecker

module R = Res

type error_kind = Unknown of string
  | ConstantOutOfSubrange of HString.t

type error = [
  | `LustreAbstractInterpretationError of Lib.position * error_kind
]

let error_message kind = match kind with
  | Unknown s -> s
  | ConstantOutOfSubrange i -> "Constant " ^ (HString.string_of_hstring i) ^ 
  " is assigned a value outside of its subrange type"

let inline_error pos kind = Error (`LustreAbstractInterpretationError (pos, kind))

let unwrap result = match result with
  | Ok r -> r
  | Error _ -> assert false

module IMap = HString.HStringMap

(** Context from a node identifier to a map of its
  variable identifiers to their inferred subrange bounds *)
type context = LA.lustre_type IMap.t IMap.t

let dpos = Lib.dummy_pos

let dnode_id = HString.mk_hstring "dummy_node_id"

let empty_context = IMap.empty

let union a b = IMap.union
  (fun _ n1 n2 -> Some (IMap.union
    (fun _ _ i2 -> Some i2)
    n1 n2))
  a b

let get_type ctx node_name id = match IMap.find_opt node_name ctx with
  | Some node_ctx -> (match IMap.find_opt id node_ctx with
    | Some ty -> Some ty
    | None -> None)
  | None -> None

let add_type ctx node_name id ty =
  let update = IMap.singleton node_name (IMap.singleton id ty) in
  union ctx update

let extract_bounds_from_type ty =
  (match ty with
  | LA.IntRange (_, Some Const (_, Num l), Some Const (_, Num r)) ->
    let l = Numeral.of_string (HString.string_of_hstring l) in
    let r = Numeral.of_string (HString.string_of_hstring r) in
    Some l, Some r
  | LA.IntRange (_, None, Some Const (_, Num r)) ->
    let r = Numeral.of_string (HString.string_of_hstring r) in
    None, Some r
  | LA.IntRange (_, Some Const (_, Num l), None) ->
    let l = Numeral.of_string (HString.string_of_hstring l) in
    Some l, None
  (* If the int range is not constant, we treat it as an int for now *)
  | IntRange _ -> None, None
  | _ -> None, None)

let subrange_from_bounds pos l r =
  let l = HString.mk_hstring (Numeral.string_of_numeral l) in
  let r = HString.mk_hstring (Numeral.string_of_numeral r) in
  LA.IntRange (pos, Some (Const (pos, Num l)), Some (Const (pos, Num r)))

let subrange_from_lower pos l = 
  let l = HString.mk_hstring (Numeral.string_of_numeral l) in
  LA.IntRange (pos, Some (Const (pos, Num l)), None)

let subrange_from_upper pos r = 
  let r = HString.mk_hstring (Numeral.string_of_numeral r) in
  LA.IntRange (pos, None, Some (Const (pos, Num r)))

let rec merge_types a b = match a, b with
  | LA.ArrayType (_, (t1, e)), LA.ArrayType (_, (t2, _)) ->
    let t = merge_types t1 t2 in
    LA.ArrayType (dpos, (t, e))
  | RecordType (_, name, t1s), RecordType (_, _, t2s) ->
    let ts = List.map2
      (fun (p, i, t1) (_, _, t2) -> p, i, merge_types t1 t2)
      t1s t2s
    in
    LA.RecordType (dpos, name, ts)
  | TupleType (_, t1s), TupleType (_, t2s) ->
    let ts = List.map2 (fun t1 t2 -> merge_types t1 t2) t1s t2s in
    LA.TupleType (dpos, ts)
  | IntRange (_, l1, u1),
    IntRange (_, l2, u2) ->
    let lower = match l1, l2 with 
      | (Some Const (_, Num l1)), (Some Const (_, Num l2)) -> 
        let l1 = Numeral.of_string (HString.string_of_hstring l1) in
        let l2 = Numeral.of_string (HString.string_of_hstring l2) in
        let l = HString.mk_hstring (Numeral.string_of_numeral (Numeral.min l1 l2)) in
        Some (LA.Const (dpos, Num l))
      | _ -> None 
    in
    let upper = match u1, u2 with 
      | (Some Const (_, Num u1)), (Some Const (_, Num u2)) ->
        let u1 = Numeral.of_string (HString.string_of_hstring u1) in
        let u2 = Numeral.of_string (HString.string_of_hstring u2) in
        let u = HString.mk_hstring (Numeral.string_of_numeral (Numeral.max u1 u2)) in
        Some (LA.Const (dpos, Num u))
      | _ -> None
    in
    IntRange (dpos, lower, upper)
  | IntRange _, (Int _ as t) -> t
  | Int _ as t, IntRange _ -> t
  | t, _ -> t

let rec restrict_type_by ty restrict = match ty, restrict with
  | LA.ArrayType (_, (t1, e)), LA.ArrayType (_, (t2, _)) ->
    let t, is_restricted = restrict_type_by t1 t2 in
    LA.ArrayType (dpos, (t, e)), is_restricted
  | RecordType (_, name, t1s), RecordType (_, _, t2s) ->
    let ts = List.map2
      (fun (p, i, t1) (_, _, t2) -> 
        let t, is_restricted = restrict_type_by t1 t2 in
        (p, i, t), is_restricted)
      t1s t2s
    in
    let ts, is_restricted_list = List.split ts in
    let is_restricted = List.fold_left (||) false is_restricted_list in
    LA.RecordType (dpos, name, ts), is_restricted
  | TupleType (_, t1s), TupleType (_, t2s) ->
    let ts = List.map2 (fun t1 t2 -> restrict_type_by t1 t2) t1s t2s in
    let ts, is_restricted_list = List.split ts in
    let is_restricted = List.fold_left (||) false is_restricted_list in
    LA.TupleType (dpos, ts), is_restricted
  | IntRange (_, l1, u1),
    IntRange (_, l2, u2) ->
    let lower, is_restricted1 = match l1, l2 with 
      | (Some Const (_, Num l1)), (Some Const (_, Num l2)) -> 
        let l1 = Numeral.of_string (HString.string_of_hstring l1) in
        let l2 = Numeral.of_string (HString.string_of_hstring l2) in
        let lnum = Numeral.max l1 l2 in
        let l = HString.mk_hstring (Numeral.string_of_numeral lnum) in
        Some (LA.Const (dpos, Num l)), not (Numeral.equal l1 lnum)
      | (Some _ as l), None -> l, false
      | None, (Some _ as l) -> l, true 
      | _ -> None, false
      
    in
    let upper, is_restricted2 = match u1, u2 with 
      | (Some Const (_, Num u1)), (Some Const (_, Num u2)) ->
        let u1 = Numeral.of_string (HString.string_of_hstring u1) in
        let u2 = Numeral.of_string (HString.string_of_hstring u2) in
        let unum = Numeral.min u1 u2 in
        let u = HString.mk_hstring (Numeral.string_of_numeral unum) in
        Some (LA.Const (dpos, Num u)), not (Numeral.equal u1 unum)
      | (Some _ as u), None -> u, false
      | None, (Some _ as u) -> u, true
      | _ -> None, false  
    in
    let is_restricted = is_restricted1 || is_restricted2 in
    if (lower = None && upper = None) 
    then Int dpos, is_restricted
    else IntRange (dpos, lower, upper), is_restricted
  | IntRange _ as t, Int _ -> t, false
  | Int _, (IntRange _ as t) -> t, true
  | t, _ -> t, false

let rec interpret_program ty_ctx gids = function
  | [] -> empty_context
  | h :: t -> union (interpret_decl ty_ctx gids h) (interpret_program ty_ctx gids t)

and interpret_contract node_id ctx ty_ctx contract =
  let ty_ctx = TC.tc_ctx_of_contract ~ignore_modes:true ty_ctx Ghost node_id contract |> unwrap |> fst
  in
  List.fold_left (fun acc eqn ->
      union acc (interpret_contract_eqn node_id acc ty_ctx eqn))
    ctx
    (snd contract)

and interpret_contract_eqn node_id ctx ty_ctx = function
  | LA.GhostConst _ -> empty_context
  | Assume _ | Guarantee _ | Mode _
  | ContractCall _ | AssumptionVars _ -> empty_context
  | GhostVars (_, (GhostVarDec (_, tis)), rhs) ->
  let eqns =
    List.init (Ctx.arity_of_expr ty_ctx rhs) (fun p -> rhs, p)
  in
  List.fold_left2 (
    fun acc (_, i, ty) (expr, p) -> 
      let restrict_ty = interpret_expr_by_type node_id ctx ty_ctx ty p expr in
      let ty1, is_restricted = restrict_type_by ty restrict_ty in
      if is_restricted then
        add_type acc node_id i ty1
      else acc
  )
    ctx
    tis
    eqns

and interpret_decl ty_ctx gids = function
  | LA.TypeDecl _
  | ConstDecl _ -> empty_context
  | NodeDecl (_, decl)
  | FuncDecl (_, decl) -> interpret_node ty_ctx gids decl
  | ContractNodeDecl (_, decl) -> interpret_contract_node ty_ctx decl
  | NodeParamInst _ -> empty_context

and interpret_contract_node ty_ctx (id, _, ins, outs, contract) =
  (* Setup the typing context *)
  let ty_ctx = TC.add_io_node_ctx ty_ctx ins outs in
  interpret_contract id empty_context ty_ctx contract

and interpret_node ty_ctx gids (id, _, _, ins, outs, locals, items, contract) =
  (* Setup the typing context *)
  let ty_ctx = TC.add_io_node_ctx ty_ctx ins outs in
  let ctx = IMap.empty in
  let contract_ctx = match contract with
    | Some contract -> interpret_contract id ctx ty_ctx contract 
    | None -> empty_context
  in
  let ty_ctx = TC.add_local_node_ctx ty_ctx id locals |> unwrap in
  let gids_node = GeneratedIdentifiers.StringMap.find id gids in
  let ty_ctx = GeneratedIdentifiers.StringMap.fold
    (fun id ty ctx -> Ctx.add_ty ctx id ty) (gids_node.GeneratedIdentifiers.locals) ty_ctx
  in
  let eqns = List.fold_left (fun acc -> function
    | LA.Body eqn -> (match eqn with
      | LA.Assert _ -> acc
      | Equation (_, lhs, rhs) -> (lhs, rhs) :: acc)
    | AnnotMain _ 
    | AnnotProperty _ -> acc
    (* Shouldn't be possible *)
    | LA.IfBlock _ 
    | LA.FrameBlock _ -> assert false)
    []
    items
  in
  let eqn_ctx = List.fold_left (fun acc (lhs, rhs) ->
      let ctx = interpret_eqn id acc ty_ctx lhs rhs in
      union acc ctx)
    ctx
    eqns
  in
  union contract_ctx eqn_ctx

and interpret_eqn node_id ctx ty_ctx lhs rhs =
  let struct_items = match lhs with
    | StructDef (_, items) -> items
  in
  let eqns =
    List.init (Ctx.arity_of_expr ty_ctx rhs) (fun p -> rhs, p)
  in
  List.fold_left2 (fun acc lhs (expr, p) -> match lhs with
      | LA.SingleIdent (_, id) ->
        let ty1 = Ctx.lookup_ty ty_ctx id |> get in
        let ty1 = TC.expand_type_syn_reftype_history ty_ctx ty1 |> unwrap in
        let restrict_ty = interpret_expr_by_type node_id ctx ty_ctx ty1 p expr in
        let ty, is_restricted = restrict_type_by ty1 restrict_ty in
        if is_restricted then
          add_type acc node_id id ty
        else acc
      | LA.ArrayDef (_, array, indices) ->
        let array_type = Ctx.lookup_ty ty_ctx array |> get in
        let array_type = TC.expand_type_syn_reftype_history ty_ctx array_type |> unwrap in
        let ty_ctx, ty1, sizes = List.fold_left (fun (acc, ty, sizes) idx ->
            match ty with
            | LA.ArrayType (_, (idx_ty, size)) -> 
              Ctx.add_ty acc idx (Int dpos), idx_ty, size :: sizes
            | _ -> assert false)
          (ty_ctx, array_type, [])
          indices
        in
        let restrict_ty = interpret_expr_by_type node_id ctx ty_ctx ty1 p expr in
        let ty, is_restricted = restrict_type_by ty1 restrict_ty in
        let ty = List.fold_left
          (fun acc size -> LA.ArrayType (dpos, (acc, size)))
          ty sizes
        in
        if is_restricted then
          add_type acc node_id array ty
        else acc
      | _ -> assert false)
    ctx
    struct_items
    eqns

and interpret_expr_by_type node_id ctx ty_ctx ty proj expr : LA.lustre_type =
  match ty with
  | LA.RecordType (_, name, ts) -> 
    let f = function
      | LA.RecordExpr (_, _, es) ->
        let emap = List.fold_left
          (fun acc (id, e) -> IMap.add id e acc)
          IMap.empty es
        in
        let ts = List.map (fun (p, i, t) ->
            let e = IMap.find i emap in
            p, i, interpret_expr_by_type node_id ctx ty_ctx t proj e)
          ts
        in
        Some (LA.RecordType (dpos, name, ts))
      | StructUpdate _ -> Some ty
      | _ -> None
    in
    interpret_structured_expr f node_id ctx ty_ctx ty proj expr
  | ArrayType (_, (t, s)) ->
    let f = function
      | LA.GroupExpr (_, ArrayExpr, (e :: _ as es)) ->
        let t = List.fold_left (fun acc e ->
            let t' = interpret_expr_by_type node_id ctx ty_ctx t proj e in
            merge_types acc t')
          (interpret_expr_by_type node_id ctx ty_ctx t 0 e) es
        in
        Some (LA.ArrayType (dpos, (t, s)))
      | LA.GroupExpr (pos, ArrayExpr, []) -> Some (ArrayType (pos, (t, s)))
      | ArrayConstr (_, e1, _) ->
        let t = interpret_expr_by_type node_id ctx ty_ctx t proj e1 in
        Some (ArrayType (dpos, (t, s)))
      | _ -> None
    in
    interpret_structured_expr f node_id ctx ty_ctx ty proj expr
  | TupleType (_, ts) ->
    let f = function
      | LA.GroupExpr (_, TupleExpr, es) ->
        let ts = List.map2
          (fun t e -> interpret_expr_by_type node_id ctx ty_ctx t proj e)
          ts es
        in
        Some (LA.TupleType (dpos, ts))
      | _ -> None
    in
    interpret_structured_expr f node_id ctx ty_ctx ty proj expr
  | IntRange (pos, (Some Const (_, Num l1)), (Some Const (_, Num r1))) as t ->
    let l1 = Numeral.of_string (HString.string_of_hstring l1) in
    let r1 = Numeral.of_string (HString.string_of_hstring r1) in
    let l2, r2 = interpret_int_expr node_id ctx ty_ctx proj expr in
    (match l2, r2 with
    | Some l2, Some r2 ->
      let l, r = Numeral.max l1 l2, Numeral.min r1 r2 in
      subrange_from_bounds pos l r
    | Some l2, None ->
      let l = Numeral.max l1 l2 in 
      subrange_from_bounds pos l r1
    | None, Some r2 ->
      let r = Numeral.min r1 r2 in 
      subrange_from_bounds pos l1 r
    | _ -> t)
  | IntRange (pos, (Some Const (_, Num l1)), None) as t ->
    let l1 = Numeral.of_string (HString.string_of_hstring l1) in
    let l2, r2 = interpret_int_expr node_id ctx ty_ctx proj expr in
    (match l2, r2  with
    | Some l2, Some r2 ->
      let l = Numeral.max l1 l2 in
      subrange_from_bounds pos l r2
    | Some l2, None ->
      let l = Numeral.max l1 l2 in 
      subrange_from_lower pos l 
    | None, Some r2 ->
      subrange_from_bounds pos l1 r2
    | _ -> t)
  | IntRange (pos, None, (Some Const (_, Num r1))) as t ->
    let r1 = Numeral.of_string (HString.string_of_hstring r1) in
    let l2, r2 = interpret_int_expr node_id ctx ty_ctx proj expr in
    (match l2, r2 with
    | Some l2, Some r2 ->
      let r = Numeral.min r1 r2 in
      subrange_from_bounds pos l2 r
    | Some l2, None ->
      subrange_from_bounds pos l2 r1
    | None, Some r2 ->
      let r = Numeral.min r1 r2 in 
      subrange_from_upper pos r
    | _ -> t)
  | Int pos | IntRange (pos, None, None) ->
    let l, r = interpret_int_expr node_id ctx ty_ctx proj expr in
    (match l, r with
    | Some l, Some r -> subrange_from_bounds pos l r
    | Some l, None -> subrange_from_lower pos l
    | None, Some r -> subrange_from_upper pos r
    | _ -> LA.Int dpos)
  | t -> t

and interpret_structured_expr f node_id ctx ty_ctx ty proj expr =
  let infer e =
    let ty = TC.infer_type_expr ty_ctx e |> unwrap
    in
    TC.expand_type_syn_reftype_history ty_ctx ty |> unwrap
  in
  match f expr with
  | Some ty -> ty
  | None ->
    (match expr with
    | LA.Ident (_, id) -> (match (get_type ctx node_id id) with
      | Some id_ty -> id_ty
      | None -> 
        let id_ty = Ctx.lookup_ty ty_ctx id |> get in
        TC.expand_type_syn_reftype_history ty_ctx id_ty |> unwrap)
    | Call _ | Condact _ | Activate _ | RestartEvery _ -> ty
    | TernaryOp (_, Ite, _, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | Pre (_, e) -> interpret_expr_by_type node_id ctx ty_ctx ty proj e
    | Arrow (_, e1, e2) ->
      let t1 = interpret_expr_by_type node_id ctx ty_ctx ty proj e1 in
      let t2 = interpret_expr_by_type node_id ctx ty_ctx ty proj e2 in
      merge_types t1 t2
    | RecordProject (_, e, idx) ->
      let parent_ty = infer e in
      let parent_ty = interpret_expr_by_type node_id ctx ty_ctx parent_ty proj e in
      let parent_ty = TC.expand_type_syn_reftype_history ty_ctx parent_ty |> unwrap in
      (match parent_ty with
        | LA.RecordType (_, _, idents) ->
          let (_, _, t) = List.find (fun (_, i, _) -> HString.equal i idx) idents in
          t

        | TVar _ | Bool _ | Int _ | UInt8 _ | UInt16 _ | UInt32 _
        | UInt64 _ | Int8 _ | Int16 _ | Int32 _ | Int64 _ | IntRange _ | Real _
        | UserType _ | AbstractType _ | TupleType _ | GroupType _ | ArrayType _
        | EnumType _ | TArr _ | RefinementType _ | History _ -> assert false)
    | TupleProject (_, e, idx) ->
      let parent_ty = infer e in
      let parent_ty = interpret_expr_by_type node_id ctx ty_ctx parent_ty proj e in
      (match parent_ty with
      | TupleType (_, types) -> List.nth types idx
      | _ -> assert false)
    | ArrayIndex (_, e, _) ->
      let parent_ty = infer e in
      let parent_ty = interpret_expr_by_type node_id ctx ty_ctx parent_ty proj e in
      (match parent_ty with
      | ArrayType (_, (ty, _)) -> ty
      | _ -> assert false)
    | GroupExpr (_, ExprList, es) -> (
      let g = interpret_structured_expr f node_id ctx ty_ctx ty in
      Ctx.traverse_group_expr_list g ty_ctx proj es
    )
    | _ -> assert false)

and interpret_int_expr node_id ctx ty_ctx proj expr = 
  let infer e =
    let ty = TC.infer_type_expr ty_ctx e |> unwrap
    in
    let ty = TC.expand_type_syn_reftype_history ty_ctx ty |> unwrap in 
    interpret_expr_by_type node_id ctx ty_ctx ty proj e
  in
  match expr with
  | LA.Ident (_, id) ->
    (match get_type ctx node_id id with
    | Some ty ->
      extract_bounds_from_type ty
    | None ->
      let ty = Ctx.lookup_ty ty_ctx id |> get in
      let ty = TC.expand_type_syn_reftype_history ty_ctx ty |> unwrap in
      extract_bounds_from_type ty)
  | ModeRef (_, _) -> assert false
  | RecordProject (_, e, p) -> 
    let ty = infer e in 
    let ty = TC.expand_type_syn_reftype_history ty_ctx ty |> unwrap in
    (match ty with
      | LA.RecordType (_, _, nested) ->
        let (_, _, ty) = List.find (fun (_, id, _) -> HString.equal id p) nested in
        extract_bounds_from_type ty
      
      | TVar _ | Bool _ | Int _ | UInt8 _ | UInt16 _ | UInt32 _
      | UInt64 _ | Int8 _ | Int16 _ | Int32 _ | Int64 _ | IntRange _ | Real _
      | UserType _ | AbstractType _ | TupleType _ | GroupType _ | ArrayType _
      | EnumType _ | TArr _ | RefinementType _ | History _ -> assert false) 
  | TupleProject (_, e, idx) -> (match infer e with
    | TupleType (_, nested) -> 
      let ty = List.nth nested idx in
      extract_bounds_from_type ty
    | _ -> assert false)
  | ArrayIndex (_, e, _) -> (match infer e with
    | ArrayType (_, (t, _)) -> extract_bounds_from_type t
    | _ -> assert false)
  | Const (_, const) -> (match const with
    | True | False -> assert false
    | Num x -> 
      let v = Numeral.of_string (HString.string_of_hstring x) in
      Some v, Some v
    | Dec _ -> assert false)
  | UnaryOp (_, op, e) ->
    interpret_int_unary_expr node_id ctx ty_ctx op proj e
  | BinaryOp (_, op, e1, e2) ->
    interpret_int_binary_expr node_id ctx ty_ctx proj op e1 e2
  | TernaryOp (_, Ite, _, e1, e2) ->
    interpret_int_branch_expr node_id ctx ty_ctx proj e1 e2
  | ConvOp (_, _, e) -> interpret_int_expr node_id ctx ty_ctx proj e
  | CompOp _-> assert false
  | AnyOp _ -> assert false (* desugared in lustreDesugarAnyOps *)
  | RecordExpr _ -> assert false
  | GroupExpr (_, ExprList, es) -> (
    let g = interpret_int_expr node_id ctx ty_ctx in
    Ctx.traverse_group_expr_list g ty_ctx proj es
  )
  | GroupExpr _ -> assert false
  | StructUpdate _ -> assert false
  | ArrayConstr _ -> assert false
  | Quantifier _ -> assert false
  | When _ -> assert false
  | Condact (_, _, _, id, _, _)
  | Activate (_, id, _, _, _)
  | RestartEvery (_, id, _, _)
  | Call (_, id, _) ->
    let ty = Ctx.lookup_node_ty ty_ctx id |> get in
    let output_ty = match ty with
      | TArr (_, _, GroupType (_, tys)) -> List.nth tys proj
      | TArr (_, _, ty) -> ty
      | _ -> assert false
    in
    extract_bounds_from_type output_ty
  | Merge _ -> None, None
  | Pre (_, e) -> interpret_int_expr node_id ctx ty_ctx proj e
  | Arrow (_, e1, e2) -> interpret_int_branch_expr node_id ctx ty_ctx proj e1 e2

and interpret_int_unary_expr node_id ctx ty_ctx op proj e =
  let (l, r) = interpret_int_expr node_id ctx ty_ctx proj e in
  (match op with
    | Uminus ->
      let l = (match l with
        | Some l -> Some (Numeral.neg l)
        | _ -> None)
      in
      let r = (match r with
        | Some r -> Some (Numeral.neg r)
        | _ -> None)
      in
      r, l
    | _ -> assert false)

and interpret_int_binary_expr node_id ctx ty_ctx proj op e1 e2 =
  let (l1, r1) = interpret_int_expr node_id ctx ty_ctx proj e1 in
  let (l2, r2) = interpret_int_expr node_id ctx ty_ctx proj e2 in
  let template op =
    let l = (match l1, l2 with
      | Some l1, Some l2 -> Some (op l1 l2)
      | _ -> None)
    in
    let r = (match r1, r2 with
      | Some r1, Some r2 -> Some (op r1 r2)
      | _ -> None)
    in
    l, r
  in
  (match op with
  | Mod ->
    let r = (match r1, r2 with
      | Some r1, Some r2 -> 
        let left = Numeral.abs r1 in
        let right = Numeral.abs r2 in
        let result = Numeral.(-) (Numeral.max left right) (Numeral.one) in
        Some result
      | _ -> None)
    in
    Some Numeral.zero, r
  | Minus -> template Numeral.(-)
  | Plus -> template Numeral.(+)
  | Times -> template Numeral.( * )
  | IntDiv | Div ->
    (match l1, l2, r1, r2 with
      | Some l1, Some l2, Some r1, Some r2 ->
        let lmin = Numeral.min l1 l2 in
        let lmax = Numeral.max l1 l2 in
        let rmax = Numeral.max r1 r2 in
        let rmin = Numeral.min r1 r2 in
        Some (Numeral.(/) lmin rmax), Some (Numeral.(/) lmax rmin)
      | _ -> None, None)
  | _ -> assert false)

and interpret_int_branch_expr node_id ctx ty_ctx proj e1 e2 =
  let (l1, r1) = interpret_int_expr node_id ctx ty_ctx proj e1 in
  let (l2, r2) = interpret_int_expr node_id ctx ty_ctx proj e2 in
  let l = (match l1, l2 with
    | Some l1, Some l2 -> Some (Numeral.min l1 l2)
    | _ -> None)
  in
  let r = (match r1, r2 with
    | Some r1, Some r2 -> Some (Numeral.max r1 r2)
    | _ -> None)
  in
  l, r

let expr_opt_lte e1 e2 =
  match e1 with 
    | None -> true
    | Some (LA.Const (_, Num l1)) -> (
      match e2 with 
        | None -> false
        | Some (LA.Const (_, Num l2)) -> 
          int_of_string (HString.string_of_hstring l1) <= int_of_string (HString.string_of_hstring l2)
        | _ -> assert false (* Not possible as we require subranges to have concrete bounds *)
      )
    | _ -> assert false (* Not possible as we require subranges to have concrete bounds *)

let expr_opt_gte e1 e2 =
  match e1 with 
    | None -> true
    | Some (LA.Const (_, Num l1)) -> (
      match e2 with 
        | None -> false
        | Some (LA.Const (_, Num l2)) -> 
          int_of_string (HString.string_of_hstring l1) >= int_of_string (HString.string_of_hstring l2)
        | _ -> assert false (* Not possible as we require subranges to have concrete bounds *)
      )
    | _ -> assert false (* Not possible as we require subranges to have concrete bounds *)

(* Compare a constant's actual range to its inferred range to see if assignment is legal *)
let rec compare_ranges id pos_map actual_ty inferred_range =
  let error () =
    let pos = IMap.find id pos_map in
    inline_error pos (ConstantOutOfSubrange id)
  in
  match inferred_range with 
  | LA.IntRange (_, e1, e2) ->
    (match actual_ty with 
      | LA.IntRange (_, e3, e4) -> 
        if expr_opt_lte e3 e1 && expr_opt_gte e4 e2 && expr_opt_lte e1 e2
        then R.ok () 
        else error ()
      | _ -> R.ok ())
  | Int _ ->
    (match actual_ty with 
      | LA.IntRange (_, Some _, _) -> error ()
      | LA.IntRange (_, _, Some _) -> error ()
      | _ -> R.ok ())
  | ArrayType (_, (ty1, _)) -> 
    (match actual_ty with 
      | ArrayType (_, (ty2, _)) -> compare_ranges id pos_map ty2 ty1
      | _ -> R.ok ())
  | TupleType (_, types1) -> 
    (match actual_ty with 
      | TupleType (_, types2) -> 
        R.seq_ (List.map2 (compare_ranges id pos_map) types2 types1)
      | _ -> R.ok ())
  | _ -> R.ok ()

let rec most_general_int_ty = function 
  | LA.IntRange (pos, _, _) -> LA.Int pos
  | LA.GroupType (pos, types)
  | TupleType (pos, types) -> 
    let types = List.map most_general_int_ty types in 
    LA.TupleType (pos, types)
  | RecordType (pos, id, tis) -> 
    let tis = List.map (fun (p, id, ty) -> (p, id, most_general_int_ty ty)) tis in 
    RecordType (pos, id, tis)
  | LA.ArrayType (pos, (ty, expr)) -> 
    let ty = most_general_int_ty ty in 
    LA.ArrayType (pos, (ty, expr))
  | _ as t -> t


let interpret_const_decl ctx pos_map ty_ctx = function
  | LA.ConstDecl (_, TypedConst (_, id, e, _)) 
  | ConstDecl (_, UntypedConst (_, id, e)) -> 
    (* Get inferred bounds from expr *)
    let ty = Ctx.lookup_ty ty_ctx id |> get in
    let ty = TC.expand_type_syn_reftype_history ty_ctx ty |> unwrap in
    let ty = most_general_int_ty ty in 
    let ty = interpret_expr_by_type dnode_id ctx ty_ctx ty 0 e in
    let pos = LustreAstHelpers.pos_of_expr e in
    add_type ctx dnode_id id ty, IMap.add id pos pos_map
  | _ -> ctx, pos_map

let rec interpret_global_consts ty_ctx decls = 
  let ctx, pos_map = List.fold_left (fun (ctx, pos_map) decl ->
    let ctx, pos_map = interpret_const_decl ctx pos_map ty_ctx decl in
    ctx, pos_map
  ) (empty_context, IMap.empty) decls in
  Res.seq_ (check_global_const_subrange ty_ctx ctx pos_map)

and check_global_const_subrange ty_ctx ctx pos_map =
  let ctx =
    match IMap.find_opt dnode_id ctx with
    | None -> empty_context
    | Some ctx -> ctx
  in
  IMap.fold (fun id inferred_range acc ->
    let actual_ty = Ctx.lookup_ty ty_ctx id |> get in
    let actual_ty = TC.expand_type_syn_reftype_history ty_ctx actual_ty |> unwrap in
    (* Check if inferred range is outside of declared type *)
    compare_ranges id pos_map actual_ty inferred_range :: acc
  )
  ctx
  []