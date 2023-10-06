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

(** Inlining constants throughout the program
  
    @author Apoorv Ingle *)

exception Out_of_bounds of (Lib.position * string) 

module TC = TypeCheckerContext
module LA = LustreAst
module LH = LustreAstHelpers

module R = Res
let (>>=) = R.(>>=)
let (let*) = Res.(>>=)

type error_kind = Unknown of string
  | FreeIntIdentifier of HString.t
  | ConstantMustBeInt of LA.expr
  | UnaryMustBeInt of LA.expr
  | BinaryMustBeInt of LA.expr
  | FreeBoolIdentifier of HString.t
  | ConstantMustBeBool of LA.expr
  | UnaryMustBeBool of LA.expr
  | BinaryMustBeBool of LA.expr
  | IdentifierMustBeConstant of HString.t
  | UnableToEvaluate of LA.expr
  | WidthOperatorUnsupported
  | OutOfBounds of string

type error = [
  | `LustreAstInlineConstantsError of Lib.position * error_kind
]

let error_message kind = match kind with
  | Unknown s -> s
  | FreeIntIdentifier i -> "Cannot evaluate free constant '"
    ^ (HString.string_of_hstring i) ^ "' to an int constant"
  | ConstantMustBeInt e -> "Cannot evaluate non-int constant '"
    ^ LA.string_of_expr e ^ "' to an int constant"
  | UnaryMustBeInt e -> "Cannot evaluate non-int unary expression '"
    ^ LA.string_of_expr e ^ "' to an int constant"
  | BinaryMustBeInt e -> "Cannot evaluate non-int binary expression '"
    ^ LA.string_of_expr e ^ "' to an int constant"
  | FreeBoolIdentifier i ->  "Cannot evaluate free constant '"
    ^ (HString.string_of_hstring i) ^ "' to a bool constant"
  | ConstantMustBeBool e -> "Cannot evaluate non-bool constant '"
    ^ LA.string_of_expr e ^ "' to a bool constant"
  | UnaryMustBeBool e -> "Cannot evaluate non-bool unary expression '"
    ^ LA.string_of_expr e ^ "' to a bool constant"
  | BinaryMustBeBool e -> "Cannot evaluate non-bool binary expression '"
    ^ LA.string_of_expr e ^ "' to a bool constant"
  | IdentifierMustBeConstant i -> "Not a constant identifier '"
    ^ (HString.string_of_hstring i) ^ "'"
  | UnableToEvaluate e -> "Cannot evaluate expression '" ^ LA.string_of_expr e ^ "'"
  | WidthOperatorUnsupported -> "Width operator is not supported"
  | OutOfBounds s -> s


let inline_error pos kind = Error (`LustreAstInlineConstantsError (pos, kind))
(** [type_error] returns an [Error] of [tc_result] *)
                      
let int_value_of_const: LA.expr -> (int, [> error]) result =
  function
  | LA.Const (_, LA.Num n) -> R.ok (n |> HString.string_of_hstring |> int_of_string)
  | e -> inline_error (LH.pos_of_expr e) (ConstantMustBeInt e) 

let bool_value_of_const: LA.expr -> (bool, [> error]) result =
  function
  | LA.Const (_, LA.True) -> R.ok true
  | LA.Const (_, LA.False) -> R.ok false                             
  | e -> inline_error (LH.pos_of_expr e) (ConstantMustBeBool e)

let lift_bool: bool -> LA.constant = function
  | true -> LA.True
  | false -> LA.False

let rec is_normal_form: TC.tc_context -> LA.expr -> bool = fun ctx ->
  function
  | Const _ -> true
  | RecordExpr (_, _, id_exprs) -> List.for_all (fun (_, e) -> is_normal_form ctx e) id_exprs
  | RecordProject (_, e, _)
    | TupleProject (_, e, _) -> is_normal_form ctx e
  | _ -> false
(** is the expression in a normal form? *)
         
let rec eval_int_expr: TC.tc_context -> LA.expr -> (int, [> error]) result = fun ctx ->
  function
  | LA.Ident (pos, i) ->
     (match (TC.lookup_const ctx i) with
      | Some (const_expr, _) ->
         if is_normal_form ctx const_expr
         then int_value_of_const const_expr
         else (match const_expr with
               | LA.Ident (_, i') as e ->
                  if HString.compare i i' = 0
                  then inline_error pos (FreeIntIdentifier i)
                  else eval_int_expr ctx e 
               | _ -> eval_int_expr ctx const_expr)
      | None -> inline_error pos (IdentifierMustBeConstant i))
  | LA.Const _ as c -> int_value_of_const c
  | LA.UnaryOp (pos, uop, e) -> eval_int_unary_op ctx pos uop e
  | LA.BinaryOp (pos, bop, e1, e2) -> eval_int_binary_op ctx pos bop e1 e2
  | LA.TernaryOp (pos, top, e1, e2, e3) -> eval_int_ternary_op ctx pos top e1 e2 e3
  | e -> inline_error (LH.pos_of_expr e) (UnableToEvaluate e)  
(** try and evalutate expression to int, return error otherwise *)

and eval_int_unary_op ctx pos op e1 =
  eval_int_expr ctx e1 >>= fun v1 ->
  match op with
  | LA.Uminus -> R.ok (-v1)
  | _ -> inline_error pos (UnaryMustBeInt (LA.UnaryOp (pos, op, e1)))

and eval_bool_unary_op ctx pos op e1 =
  eval_bool_expr ctx e1 >>= fun v1 ->
  match op with
  | LA.Not -> R.ok (not v1)
  | _ -> inline_error pos (UnaryMustBeBool (LA.UnaryOp (pos, op, e1)))

and eval_int_binary_op: TC.tc_context -> Lib.position -> LA.binary_operator
                        -> LA.expr -> LA.expr -> (int, [> error]) result =
  fun ctx pos bop e1 e2 ->
  eval_int_expr ctx e1 >>= fun v1 ->
  eval_int_expr ctx e2 >>= fun v2 ->
  match bop with
  | Plus -> R.ok (v1 + v2)
  | Times -> R.ok (v1 * v2)
  | Minus -> R.ok (v1 - v2)
  | IntDiv -> R.ok (v1 / v2)
  | _ -> inline_error pos (BinaryMustBeInt (LA.BinaryOp (pos, bop, e1, e2)))
(** try and evalutate binary op expression to int, return error otherwise *)
             
and eval_bool_expr: TC.tc_context -> LA.expr -> (bool, [> error]) result = fun ctx ->
  function
  | LA.Ident (pos, i) ->
     (match (TC.lookup_const ctx i) with
      | Some (const_expr, _) ->
         if is_normal_form ctx const_expr
         then bool_value_of_const const_expr
         else (match const_expr with
               | LA.Ident (_, i') as e ->
                  if (HString.compare i i' = 0)
                  then inline_error pos (FreeBoolIdentifier i)
                  else eval_bool_expr ctx e 
               | _ ->  eval_bool_expr ctx const_expr)
      | None -> inline_error pos (IdentifierMustBeConstant i))
  | LA.Const _ as c -> bool_value_of_const c
  | LA.BinaryOp (pos, bop, e1, e2) -> eval_bool_binary_op ctx pos bop e1 e2
  | LA.TernaryOp (pos, top, e1, e2, e3) -> eval_bool_ternary_op ctx pos top e1 e2 e3
  | LA.CompOp (_, cop, e1, e2) -> eval_comp_op ctx cop e1 e2
  | e -> inline_error (LH.pos_of_expr e) (UnableToEvaluate e)  
(** try and evalutate expression to bool, return error otherwise *)

and eval_bool_binary_op: TC.tc_context -> Lib.position -> LA.binary_operator
                         -> LA.expr -> LA.expr -> (bool, [> error]) result = 
  fun ctx pos bop e1 e2 ->
  eval_bool_expr ctx e1 >>= fun v1 ->
  eval_bool_expr ctx e2 >>= fun v2 ->
  match bop with
  | And -> R.ok (v1 && v2) 
  | Or -> R.ok (v1 || v2)
  | Xor -> R.ok ((v1 && not v2) || (v2 && not v1))
  | Impl -> R.ok (not v1 || v2)
  | _ -> inline_error pos (BinaryMustBeBool (LA.BinaryOp (pos, bop, e1, e2)))
(** try and evalutate binary op expression to bool, return error otherwise *)
  
and eval_bool_ternary_op: TC.tc_context -> Lib.position -> LA.ternary_operator
                     -> LA.expr -> LA.expr -> LA.expr -> (bool, [> error]) result
  = fun ctx _ top b1 e1 e2 ->
  eval_bool_expr ctx b1 >>= fun c ->
  eval_bool_expr ctx e1 >>= fun v1 ->
  eval_bool_expr ctx e2 >>= fun v2 ->
  match top with
  | LA.Ite -> if c then R.ok v1 else R.ok v2
(** try and evalutate ternary op expression to bool, return error otherwise *)

and eval_int_ternary_op: TC.tc_context -> Lib.position -> LA.ternary_operator
                     -> LA.expr -> LA.expr -> LA.expr -> (int, [> error]) result
  = fun ctx _ top b1 e1 e2 ->
  match top with
  | LA.Ite ->
     eval_bool_expr ctx b1 >>= fun c ->
     if c
     then eval_int_expr ctx e1
     else eval_int_expr ctx e2
(** try and evalutate ternary op expression to int, return error otherwise *)

             
and eval_comp_op: TC.tc_context -> LA.comparison_operator
                  -> LA.expr -> LA.expr -> (bool, [> error]) result = 
  fun ctx cop e1 e2 ->
  eval_int_expr ctx e1 >>= fun v1 ->
  eval_int_expr ctx e2 >>= fun v2 ->
  match cop with
  | Eq -> R.ok (v1 = v2)
  | Neq -> R.ok (v1 <> v2)
  | Lte -> R.ok (v1 <= v2)
  | Lt -> R.ok (v1 < v2)
  | Gte -> R.ok (v1 >= v2)
  | Gt -> R.ok (v1 > v2)
(** try and evalutate comparison op expression to bool, return error otherwise *)

and simplify_array_index: TC.tc_context -> Lib.position -> LA.expr -> LA.expr -> LA.expr
  = fun ctx pos e1 idx -> 
  let e1' = simplify_expr ctx e1 in
  let idx' = simplify_expr ctx idx in
  let raise_error () =
    raise (Out_of_bounds (pos, "Array element access out of bounds."))
  in
  match e1' with
  | LA.GroupExpr (_, ArrayExpr, es) ->
     (match (eval_int_expr ctx idx) with
      | Ok i -> if List.length es > i then List.nth es i else raise_error ()
      | Error _ -> LA.ArrayIndex (pos, e1', idx'))
  | LA.ArrayConstr (_, v, s) ->
     (match (eval_int_expr ctx idx), (eval_int_expr ctx s) with
     | Ok i, Ok j -> if j > i then v else raise_error ()
     | _, _ -> LA.ArrayIndex (pos, e1', idx'))
  | _ ->
    ArrayIndex (pos, e1', idx')
(** picks out the idx'th component of an array if it can *)

and simplify_tuple_proj: TC.tc_context -> Lib.position -> LA.expr -> int -> LA.expr
  = fun ctx pos e1 idx ->
  match (simplify_expr ctx e1) with
  | LA.GroupExpr (_, _, es) ->
     if List.length es > idx
     then List.nth es idx
     else (raise (Out_of_bounds (pos, "Tuple element access out of bounds.")))
  | _ -> TupleProject (pos, e1, idx)
(** picks out the idx'th component of a tuple if it is possible *)

and push_pre is_guarded pos =
  let r e = push_pre is_guarded pos e in
  function
  | LA.Ident _ as e -> LA.Pre (pos, e)
  | ModeRef _ as e -> LA.Pre (pos, e)
  | RecordProject (p, e, i) -> RecordProject (p, r e, i)
  | TupleProject (p, e, i) -> TupleProject (p, r e, i)
  | Const _ as e -> if is_guarded then e else Pre (pos, e)
  | UnaryOp (p, op, e) -> UnaryOp (p, op, r e)
  | BinaryOp (p, op, e1, e2) -> BinaryOp (p, op, r e1, r e2)
  | TernaryOp (p, Ite, e1, e2, e3) -> TernaryOp (p, Ite, e1, r e2, r e3)
  | ConvOp (p, op, e) -> ConvOp (p, op, r e)
  | CompOp (p, op, e1, e2) -> CompOp (p, op, r e1, r e2)
  | RecordExpr (p, i, es) ->
    let es' = List.map (fun (i, e) -> (i, r e)) es in
    RecordExpr (p, i, es')
  | GroupExpr (p, op, es) ->
    let es' = List.map (fun e -> r e) es in
    GroupExpr (p, op, es')
  | StructUpdate (p, e1, l, e2) -> StructUpdate (p, r e1, l, r e2)
  | ArrayConstr (p, e1, e2) -> ArrayConstr (p, r e1, e2)
  | ArrayIndex (p, e1, e2) -> ArrayIndex (p, r e1, e2)
  | Quantifier (p, e1, l, e2) -> Quantifier (p, e1, l, r e2)
  | ChooseOp _ -> assert false (* desugared in lustreDesugarChooseOps *)
  | When _ as e -> LA.Pre (pos, e)
  | Condact _ as e -> LA.Pre (pos, e)
  | Activate _ as e -> LA.Pre (pos, e)
  | Merge _ as e -> LA.Pre (pos, e)
  | RestartEvery _ as e -> LA.Pre (pos, e)
  | Pre _ as e -> LA.Pre (pos, e)
  | Arrow _ as e -> LA.Pre (pos, e)
  | Call _ as e -> LA.Pre (pos, e)

and simplify_expr ?(is_guarded = false) ctx =
  function
  | LA.Const _ as c -> c
  | LA.Ident (pos, i) ->
     (match (TC.lookup_const ctx i) with
      | Some (const_expr, _) ->
         (match const_expr with
          | LA.Ident (_, i') as ident' ->
             if HString.compare i i' = 0 (* If This is a free constant *)
             then ident' 
             else simplify_expr ~is_guarded ctx ident'
          | _ -> simplify_expr ~is_guarded ctx const_expr)
      | None -> LA.Ident (pos, i))
  | LA.UnaryOp (pos, op, e1) ->
    let e1' = simplify_expr ~is_guarded ctx e1 in
    let e' = LA.UnaryOp (pos, op, e1') in
    (match op with
    | LA.Uminus -> (match eval_int_unary_op ctx pos op e1' with
      | Ok v -> LA.Const (pos, Num (v |> string_of_int |> HString.mk_hstring))
      | Error _ -> e')
    | LA.Not -> (match eval_bool_unary_op ctx pos op e1' with
      | Ok v -> if v then LA.Const(pos, True) else LA.Const (pos, False)
      | Error _ -> e')
    | _ -> e')
  | LA.Pre (pos, e) ->
    let e' = simplify_expr ~is_guarded:false ctx e in
    if is_guarded && LH.expr_is_const e' then e'
    else
      if Flags.lus_push_pre ()
      then push_pre is_guarded pos e'
      else Pre (pos, e')
  | Arrow (pos, e1, e2) ->
    let e1' = simplify_expr ~is_guarded ctx e1 in
    let e2' = simplify_expr ~is_guarded:true ctx e2 in
    Arrow (pos, e1', e2')
  | LA.BinaryOp (pos, bop, e1, e2) ->
     let e1' = simplify_expr ~is_guarded ctx e1 in
     let e2' = simplify_expr ~is_guarded ctx e2 in
     let e' = LA.BinaryOp (pos, bop, e1', e2') in
     (match (eval_int_binary_op ctx pos bop e1' e2') with
      | Ok v -> LA.Const (pos, Num (v |> string_of_int |> HString.mk_hstring))
      | Error _ -> e')
  | LA.TernaryOp (pos, top, cond, e1, e2) ->
     (match top with
     | Ite -> 
        (match eval_bool_expr ctx cond with
        | Ok v -> if v then simplify_expr ~is_guarded ctx e1
          else simplify_expr ~is_guarded ctx e2 
        | Error _ ->
          let cond' = simplify_expr ~is_guarded ctx cond in
          let e1' = simplify_expr ~is_guarded ctx e1 in
          let e2' = simplify_expr ~is_guarded ctx e2 in
            TernaryOp (pos, top, cond', e1', e2')))
  | LA.CompOp (pos, cop, e1, e2) ->
     let e1' = simplify_expr ~is_guarded ctx e1 in
     let e2' = simplify_expr ~is_guarded ctx e2 in
     let e' = LA.CompOp (pos, cop, e1', e2') in
     (match (eval_comp_op ctx cop e1' e2') with
      | Ok v -> LA.Const (pos, lift_bool v)
      | Error _ -> e')
  | LA.GroupExpr (pos, g, es) ->
     let es' = List.map (fun e -> simplify_expr ~is_guarded ctx e) es in 
     LA.GroupExpr (pos, g, es')
  | LA.RecordExpr (pos, i, fields) ->
     let fields' = List.map (fun (f, e) -> (f, simplify_expr ~is_guarded ctx e)) fields in
     LA.RecordExpr (pos, i, fields')
  | LA.ArrayConstr (pos, e1, e2) ->
     let e1' = simplify_expr ~is_guarded ctx e1 in
     let e2' = simplify_expr ~is_guarded ctx e2 in
     let e' = LA.ArrayConstr (pos, e1', e2') in e'
     (*(match (eval_int_expr ctx e2) with
      | Ok size -> LA.GroupExpr (pos, LA.ArrayExpr, Lib.list_init (fun _ -> e1') size)
      | Error _ -> e')*)
  | LA.ArrayIndex (pos, e1, e2) -> simplify_array_index ctx pos e1 e2
  | LA.TupleProject (pos, e1, e2) -> simplify_tuple_proj ctx pos e1 e2  
  | Call (pos, i, es) ->
    let es' = List.map (fun e -> simplify_expr ~is_guarded:false ctx e) es in
    Call (pos, i, es')
  | e -> e
(** Assumptions: These constants are arranged in dependency order, 
   all of the constants have been type checked *)

let rec inline_constants_of_lustre_type ctx = function
  | LA.IntRange (pos, lbound, ubound) ->
    let lbound' = match lbound with 
      | None -> None
      | Some lbound -> Some (simplify_expr ctx lbound) in
    let ubound' = match ubound with
      | None -> None
      | Some ubound -> Some (simplify_expr ctx ubound) in
    LA.IntRange (pos, lbound', ubound')
  | LA.TupleType (pos, types) ->
    let types' = List.map (fun t -> inline_constants_of_lustre_type ctx t) types in
    LA.TupleType (pos, types')
  | LA.GroupType (pos, types) ->
    let types' = List.map (fun t -> inline_constants_of_lustre_type ctx t) types in
    LA.GroupType (pos, types')
  | LA.RecordType (pos, name, types) ->
    let types' = List.map (fun (p, i, t) -> (p, i, inline_constants_of_lustre_type ctx t)) types in
    LA.RecordType (pos, name, types')
  | ArrayType (pos, (ty, expr)) ->
    let ty' = inline_constants_of_lustre_type ctx ty in
    let expr' = simplify_expr ctx expr in
    ArrayType (pos, (ty', expr'))
  | TArr (pos, ty1, ty2) ->
    let ty1' = inline_constants_of_lustre_type ctx ty1 in
    let ty2' = inline_constants_of_lustre_type ctx ty2 in
    TArr (pos, ty1', ty2')
  | ty -> ty

let inline_constants_of_node_equation: TC.tc_context -> LA.node_equation -> LA.node_equation
  = fun ctx ->
  function
  | (LA.Assert (pos, e)) -> (Assert (pos, simplify_expr ctx e))
  | (LA.Equation (pos, lhs, e)) ->
    (LA.Equation (pos, lhs, simplify_expr ctx e))

let rec inline_constants_of_const_clocked_type_decl ctx = function
  | [] -> []
  | (pos, id, lustre_type, expr, is_const) :: t ->
    let lustre_type' = inline_constants_of_lustre_type ctx lustre_type in
    let t' = inline_constants_of_const_clocked_type_decl ctx t in
    (pos, id, lustre_type', expr, is_const) :: t'

let rec inline_constants_of_clocked_type_decl ctx = function
  | [] -> []
  | (pos, id, lustre_type, expr) :: t ->
    let lustre_type' = inline_constants_of_lustre_type ctx lustre_type in
    let t' = inline_constants_of_clocked_type_decl ctx t in
    (pos, id, lustre_type', expr) :: t'

let rec inline_constants_of_node_locals ctx = function
  | [] -> ctx, []
  | (LA.NodeConstDecl (_, (FreeConst _))) as c :: t ->
    let ctx', t' = inline_constants_of_node_locals ctx t in
    ctx', c :: t'
  | (LA.NodeConstDecl (pos1, (UntypedConst (pos2, i, e)))) :: t ->
    let e' = simplify_expr ctx e in
    let ctx = match (TC.lookup_ty ctx i) with
      | None -> TC.add_untyped_const ctx i e'
      | Some ty ->
        let ty' = inline_constants_of_lustre_type ctx ty in
        TC.add_const ctx i e' ty'
    in
    let decl' = LA.NodeConstDecl (pos1, (UntypedConst (pos2, i, e'))) in
    let ctx', t' = inline_constants_of_node_locals ctx t in
    ctx', decl' :: t'
  | (LA.NodeConstDecl (pos1, (LA.TypedConst (pos2, i, e, ty)))) :: t ->
    let ty' = inline_constants_of_lustre_type ctx ty in
    let e' = simplify_expr ctx e in
    let ctx' = TC.add_const ctx i e' ty' in
    let ctx'', t' = inline_constants_of_node_locals ctx' t in
    let decl' = LA.NodeConstDecl (pos1, (TypedConst (pos2, i, e', ty'))) in
    ctx'', decl' :: t'
  | (LA.NodeVarDecl (pos, decl)) :: t ->
    let decl' = inline_constants_of_clocked_type_decl ctx [decl] |> List.hd in
    let ctx', t' = inline_constants_of_node_locals ctx t in
    ctx', (LA.NodeVarDecl (pos, decl')) :: t'

let rec inline_constants_of_node_items: TC.tc_context -> LA.node_item list -> LA.node_item list 
  = fun ctx
  -> function
  | [] -> []
  | (Body b) :: items ->
    (Body (inline_constants_of_node_equation ctx b))
    :: inline_constants_of_node_items ctx items
  (* shouldn't be possible *)
  | (IfBlock _) :: _ 
  | (FrameBlock _) :: _ ->
    assert false
  | (AnnotProperty (pos, n, e, k)) :: items ->
    (AnnotProperty (pos, n, simplify_expr ctx e, k))
    :: inline_constants_of_node_items ctx items
  | (AnnotMain (pos, b)) :: items
    -> (AnnotMain (pos, b)) :: inline_constants_of_node_items ctx items

let rec inline_constants_of_contract: TC.tc_context -> LA.contract -> LA.contract =
  fun ctx ->
  function
  | [] -> []
  | (LA.GhostConst (FreeConst (pos, i, ty))) :: others ->
     (LA.GhostConst (FreeConst (pos, i, ty)))
     :: inline_constants_of_contract ctx others 
  | (LA.GhostConst (UntypedConst (pos, i, e))) :: others ->
     (LA.GhostConst (UntypedConst (pos, i, simplify_expr ctx e)))
     :: inline_constants_of_contract ctx others 
  | (LA.GhostConst (TypedConst (pos', i, e, ty))) :: others ->
     (LA.GhostConst (TypedConst (pos', i, simplify_expr ctx e, ty)))
     :: inline_constants_of_contract ctx others 
  | (LA.GhostVars (pos, lhs, e)) :: others ->
    (LA.GhostVars (pos, lhs, simplify_expr ctx e))
     :: inline_constants_of_contract ctx others 
  | (LA.Assume (pos, n, b, e)) :: others ->
     (LA.Assume (pos, n, b, simplify_expr ctx e))
     :: inline_constants_of_contract ctx others 
  | (LA.Guarantee (pos, n, b, e)) :: others ->
     (LA.Guarantee (pos, n, b, simplify_expr ctx e))
     :: inline_constants_of_contract ctx others 
  | (LA.Mode (pos, i, rs, es)) :: others ->
     (LA.Mode (pos, i
               , List.map (fun (p, s, e) -> (p, s, simplify_expr ctx e)) rs
               , List.map (fun (p, s, e) -> (p, s, simplify_expr ctx e)) es))
      :: inline_constants_of_contract ctx others
   (* | (LA.ContractCall) :: others -> () :: inline_constants_of_contract ctx others  *)
  | e -> e 

let substitute: TC.tc_context -> LA.declaration -> (TC.tc_context * LA.declaration) = fun ctx ->
  function
  | TypeDecl (span, AliasType (pos, i, t)) ->
    let t' = inline_constants_of_lustre_type ctx t in
    ctx, LA.TypeDecl (span, AliasType (pos, i, t'))
  | ConstDecl (span, FreeConst (pos, id, ty)) ->
    let ty' = inline_constants_of_lustre_type ctx ty in
    ctx, ConstDecl (span, FreeConst (pos, id, ty'))
  | ConstDecl (span, UntypedConst (pos', i, e)) ->
    let e' = simplify_expr ctx e in
    (match (TC.lookup_ty ctx i) with
      | None ->
          (TC.add_untyped_const ctx i e'
          , ConstDecl (span, UntypedConst (pos', i, e')))
      | Some ty ->
        let ty' = inline_constants_of_lustre_type ctx ty in
        (TC.add_const ctx i e' ty', ConstDecl (span, UntypedConst (pos', i, e'))))
  | ConstDecl (span, TypedConst (pos', i, e, ty)) ->
    let ty' = inline_constants_of_lustre_type ctx ty in
    let e' = simplify_expr ctx e in 
    (TC.add_const ctx i e' ty', ConstDecl (span, TypedConst (pos', i, e', ty')))
  | (LA.NodeDecl (span, (i, imported, params, ips, ops, ldecls, items, contract))) ->
    let ips' = inline_constants_of_const_clocked_type_decl ctx ips in
    let ops' = inline_constants_of_clocked_type_decl ctx ops in
    let contract' = match contract with
      | Some contract -> Some (inline_constants_of_contract ctx contract)
      | None -> None
    in
    let ctx', ldecls' = inline_constants_of_node_locals ctx ldecls in
    let items' = inline_constants_of_node_items ctx' items in
     ctx, (LA.NodeDecl (span, (i, imported, params, ips', ops', ldecls', items', contract')))
  | (LA.FuncDecl (span, (i, imported, params, ips, ops, ldecls, items, contract))) ->
    let ips' = inline_constants_of_const_clocked_type_decl ctx ips in
    let ops' = inline_constants_of_clocked_type_decl ctx ops in
    let contract' = match contract with
      | Some contract -> Some (inline_constants_of_contract ctx contract)
      | None -> None
    in
    let ctx', ldecls' = inline_constants_of_node_locals ctx ldecls in
    let items' = inline_constants_of_node_items ctx' items in
     ctx, (LA.FuncDecl (span, (i, imported, params, ips', ops', ldecls', items', contract')))
  | (LA.ContractNodeDecl (span, (i, params, ips, ops, contract))) ->
     ctx, (LA.ContractNodeDecl (span, (i, params, ips, ops, inline_constants_of_contract ctx contract)))
  | e -> (ctx, e)
(** propogate constants post type checking into the AST and constant store*)

let rec inline_constants: TC.tc_context -> LA.t -> ((TC.tc_context * LA.t), [> error]) result = fun ctx decl ->
  match decl with
  | [] -> R.ok (ctx, [])
  | c :: rest ->
    let* (ctx', c') = (try R.ok (substitute ctx c) with
      | Out_of_bounds (pos, err) -> 
        inline_error pos (OutOfBounds err)) in
    let* (ctx'', decls) = inline_constants ctx' rest in
    R.ok (ctx'', c'::decls)
(** Best effort at inlining constants *)
