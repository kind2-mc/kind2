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

type 'a inline_result = ('a, Lib.position * string) result

let inline_error pos err = R.error (pos, "Error: " ^ err)
(** [type_error] returns an [Error] of [tc_result] *)
                      
let int_value_of_const: LA.expr -> int inline_result =
  function
  | LA.Const (_, LA.Num n) -> R.ok (int_of_string n)
  | e -> inline_error (LH.pos_of_expr e)
           ("Cannot evaluate non-int constant "
            ^ LA.string_of_expr e
            ^ " to an int.") 

let bool_value_of_const: LA.expr -> bool inline_result =
  function
  | LA.Const (_, LA.True) -> R.ok true
  | LA.Const (_, LA.False) -> R.ok false                             
  | e -> inline_error (LH.pos_of_expr e)
           ("Cannot evaluate non-bool "
            ^ LA.string_of_expr e
            ^" constant to a bool.")

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
         
let rec eval_int_expr: TC.tc_context -> LA.expr -> int inline_result = fun ctx ->
  function
  | LA.Ident (pos, i) ->
     (match (TC.lookup_const ctx i) with
      | Some (const_expr, _) ->
         if is_normal_form ctx const_expr
         then int_value_of_const const_expr
         else (match const_expr with
               | LA.Ident (_, i') as e ->
                  if Stdlib.compare i i' = 0
                  then inline_error pos ("Cannot evaluate a free int const "
                                       ^ i ^ ".")
                  else eval_int_expr ctx e 
               | _ -> eval_int_expr ctx const_expr)
      | None -> inline_error pos ("Not a constant identifier" ^ i))  
  | LA.Const _ as c -> int_value_of_const c
  | LA.BinaryOp (pos, bop, e1, e2) -> eval_int_binary_op ctx pos bop e1 e2
  | LA.TernaryOp (pos, top, e1, e2, e3) -> eval_int_ternary_op ctx pos top e1 e2 e3
  | e -> inline_error (LH.pos_of_expr e) ("Cannot evaluate expression" ^ LA.string_of_expr e)  
(** try and evalutate expression to int, return error otherwise *)

and eval_int_unary_op ctx pos op e1 =
  eval_int_expr ctx e1 >>= fun v1 ->
  match op with
  | LA.Uminus -> R.ok (-v1)
  | _ -> inline_error pos ("Cannot evaluate non-int unary expression"
    ^ LA.string_of_expr (LA.UnaryOp (pos, op, e1))
    ^ "to an int value")

and eval_bool_unary_op ctx pos op e1 =
  eval_bool_expr ctx e1 >>= fun v1 ->
  match op with
  | LA.Not -> R.ok (not v1)
  | _ -> inline_error pos ("Cannot evaluate non-bool unary expression"
    ^ LA.string_of_expr (LA.UnaryOp (pos, op, e1))
    ^ "to a bool value")

and eval_int_binary_op: TC.tc_context -> Lib.position -> LA.binary_operator
                        -> LA.expr -> LA.expr -> int inline_result =
  fun ctx pos bop e1 e2 ->
  eval_int_expr ctx e1 >>= fun v1 ->
  eval_int_expr ctx e2 >>= fun v2 ->
  match bop with
  | Plus -> R.ok (v1 + v2)
  | Times -> R.ok (v1 * v2)
  | Minus -> R.ok (v1 - v2)
  | IntDiv -> R.ok (v1 / v2)
  | _ -> inline_error pos ("Cannot evaluate non-int binary expression"
                         ^ LA.string_of_expr (LA.BinaryOp (pos, bop, e1, e2))
                         ^" to an int value")    
(** try and evalutate binary op expression to int, return error otherwise *)
             
and eval_bool_expr: TC.tc_context -> LA.expr -> bool inline_result = fun ctx ->
  function
  | LA.Ident (pos, i) ->
     (match (TC.lookup_const ctx i) with
      | Some (const_expr, _) ->
         if is_normal_form ctx const_expr
         then bool_value_of_const const_expr
         else (match const_expr with
               | LA.Ident (_, i') as e ->
                  if (Stdlib.compare i i' = 0)
                  then inline_error pos ("Cannot evaluate a free bool const "
                                       ^ i ^ ".")
                  else eval_bool_expr ctx e 
               | _ ->  eval_bool_expr ctx const_expr)
      | None -> inline_error pos ("Not a constant cannot evaluate identifier " ^ i))
  | LA.Const _ as c -> bool_value_of_const c
  | LA.BinaryOp (pos, bop, e1, e2) -> eval_bool_binary_op ctx pos bop e1 e2
  | LA.TernaryOp (pos, top, e1, e2, e3) -> eval_bool_ternary_op ctx pos top e1 e2 e3
  | LA.CompOp (pos, cop, e1, e2) -> eval_comp_op ctx pos cop e1 e2
  | e -> inline_error (LH.pos_of_expr e) ("Cannot evaluate expression" ^ LA.string_of_expr e)  
(** try and evalutate expression to bool, return error otherwise *)

and eval_bool_binary_op: TC.tc_context -> Lib.position -> LA.binary_operator
                         -> LA.expr -> LA.expr -> bool inline_result = 
  fun ctx pos bop e1 e2 ->
  eval_bool_expr ctx e1 >>= fun v1 ->
  eval_bool_expr ctx e2 >>= fun v2 ->
  match bop with
  | And -> R.ok (v1 && v2) 
  | Or -> R.ok (v1 || v2)
  | Xor -> R.ok ((v1 && not v2) || (v2 && not v1))
  | Impl -> R.ok (not v1 || v2)
  | _ -> inline_error pos ("Cannot evaluate non-bool binary expression"
                         ^ LA.string_of_expr (LA.BinaryOp (pos, bop, e1, e2))
                         ^" to a bool value")
(** try and evalutate binary op expression to bool, return error otherwise *)
  
and eval_bool_ternary_op: TC.tc_context -> Lib.position -> LA.ternary_operator
                     -> LA.expr -> LA.expr -> LA.expr -> bool inline_result
  = fun ctx pos top b1 e1 e2 ->
  eval_bool_expr ctx b1 >>= fun c ->
  eval_bool_expr ctx e1 >>= fun v1 ->
  eval_bool_expr ctx e2 >>= fun v2 ->
  match top with
  | LA.Ite -> if c then R.ok v1 else R.ok v2
  | LA.With -> inline_error pos "With operator is not supported"
(** try and evalutate ternary op expression to bool, return error otherwise *)

and eval_int_ternary_op: TC.tc_context -> Lib.position -> LA.ternary_operator
                     -> LA.expr -> LA.expr -> LA.expr -> int inline_result
  = fun ctx pos top b1 e1 e2 ->
  match top with
  | LA.Ite ->
     eval_bool_expr ctx b1 >>= fun c ->
     if c
     then eval_int_expr ctx e1
     else eval_int_expr ctx e2
  | LA.With -> inline_error pos "With operator is not supported"
(** try and evalutate ternary op expression to int, return error otherwise *)

             
and [@ocaml.warning "-27"] eval_comp_op: TC.tc_context -> Lib.position -> LA.comparison_operator
                  -> LA.expr -> LA.expr -> bool inline_result = 
  fun ctx pos cop e1 e2 ->
  eval_int_expr ctx e1 >>= fun v1 ->
  eval_int_expr ctx e2 >>= fun v2 ->
  match cop with
  | Eq -> R.ok (v1 = v2)
  | Neq -> R.ok (v1 <> v2)
  | Lte -> R.ok (v1 <= v2)
  | Lt -> R.ok (v1 < v2)
  | Gte -> R.ok (v1 > v2)
  | Gt -> R.ok (v1 >= v2)
(** try and evalutate comparison op expression to bool, return error otherwise *)

and simplify_array_index: TC.tc_context -> Lib.position -> LA.expr -> LA.expr -> LA.expr
  = fun ctx pos e1 idx -> 
  match (simplify_expr ctx e1) with
  | LA.GroupExpr (_, ArrayExpr, es) ->
     (match (eval_int_expr ctx idx) with
      | Ok i -> if List.length es > i
                then List.nth es i
                else
                  (raise (Out_of_bounds (pos, "Array element access out of bounds.")))
      | Error _ -> LA.ArrayIndex (pos, e1, idx))
  | _ -> ArrayIndex (pos, e1, idx)
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
       
and simplify_expr: TC.tc_context -> LA.expr -> LA.expr = fun ctx ->
  function
  | LA.Const _ as c -> c
  | LA.Ident (pos, i) ->
     (match (TC.lookup_const ctx i) with
      | Some (const_expr, _) ->
         (match const_expr with
          | LA.Ident (_, i') as ident' ->
             if Stdlib.compare i i' = 0 (* If This is a free constant *)
             then ident' 
             else simplify_expr ctx ident'
          | _ -> simplify_expr ctx const_expr)
      | None -> LA.Ident (pos, i))
  | LA.UnaryOp (pos, op, e1) ->
    let e1' = simplify_expr ctx e1 in
    let e' = LA.UnaryOp (pos, op, e1') in
    (match op with
    | LA.Uminus -> (match eval_int_unary_op ctx pos op e1' with
      | Ok v -> LA.Const (pos, Num (string_of_int v))
      | Error _ -> e')
    | LA.Not -> (match eval_bool_unary_op ctx pos op e1' with
      | Ok v -> if v then LA.Const(pos, True) else LA.Const (pos, False)
      | Error _ -> e')
    | _ -> e')
  | LA.Pre (pos, e1) -> LA.Pre (pos, simplify_expr ctx e1)
  | LA.BinaryOp (pos, bop, e1, e2) ->
     let e1' = simplify_expr ctx e1 in
     let e2' = simplify_expr ctx e2 in
     let e' = LA.BinaryOp (pos, bop, e1', e2') in
     (match (eval_int_binary_op ctx pos bop e1' e2') with
      | Ok v -> LA.Const (pos, Num (string_of_int v))
      | Error _ -> e')
  | LA.TernaryOp (_, top, cond, e1, e2) as e ->
     (match top with
     | Ite -> 
        (match eval_bool_expr ctx cond with
         | Ok v -> if v then simplify_expr ctx e1 else simplify_expr ctx e2 
         | Error _ -> e)
     | _ -> Lib.todo __LOC__)
  | LA.CompOp (pos, cop, e1, e2) ->
     let e1' = simplify_expr ctx e1 in
     let e2' = simplify_expr ctx e2 in
     let e' = LA.CompOp (pos, cop, e1', e2') in
     (match (eval_comp_op ctx pos cop e1' e2') with
      | Ok v -> LA.Const (pos, lift_bool v)
      | Error _ -> e')
  | LA.GroupExpr (pos, g, es) ->
     let es' = List.map (fun e -> simplify_expr ctx e) es in 
     LA.GroupExpr (pos, g, es')
  | LA.RecordExpr (pos, i, fields) ->
     let fields' = List.map (fun (f, e) -> (f, simplify_expr ctx e)) fields in
     LA.RecordExpr (pos, i, fields')
  | LA.ArrayConstr (pos, e1, e2) ->
     let e1' = simplify_expr ctx e1 in
     let e2' = simplify_expr ctx e2 in
     let e' = LA.ArrayConstr (pos, e1', e2') in
     (match (eval_int_expr ctx e2) with
      | Ok size -> LA.GroupExpr (pos, LA.ArrayExpr, Lib.list_init (fun _ -> e1') size)
      | Error _ -> e')
  | LA.ArrayIndex (pos, e1, e2) -> simplify_array_index ctx pos e1 e2
  | LA.ArrayConcat (pos, e1, e2) as e->
     (match (simplify_expr ctx e1, simplify_expr ctx e2) with
      | LA.GroupExpr (_, LA.ArrayExpr, es1), LA.GroupExpr (_, LA.ArrayExpr, es2) ->
         LA.GroupExpr(pos, LA.ArrayExpr, es1 @ es2)
      | _ -> e)
  | LA.TupleProject (pos, e1, e2) -> simplify_tuple_proj ctx pos e1 e2  
  | Call (pos, i, es) ->
    let es' = List.map (fun e -> simplify_expr ctx e) es in
    Call (pos, i, es')
  | e -> e
(** Assumptions: These constants are arranged in dependency order, 
   all of the constants have been type checked *)

let rec inline_constants_of_lustre_type ctx = function
  | LA.IntRange (pos, lbound, ubound) ->
    let lbound' = simplify_expr ctx lbound in
    let ubound' = simplify_expr ctx ubound in
    LA.IntRange (pos, lbound', ubound')
  | LA.TupleType (pos, types) ->
    let types' = List.map (fun t -> inline_constants_of_lustre_type ctx t) types in
    LA.TupleType (pos, types')
  | LA.GroupType (pos, types) ->
    let types' = List.map (fun t -> inline_constants_of_lustre_type ctx t) types in
    LA.GroupType (pos, types')
  | LA.RecordType (pos, types) ->
    let types' = List.map (fun (p, i, t) -> (p, i, inline_constants_of_lustre_type ctx t)) types in
    LA.RecordType (pos, types')
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
  | e -> e

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
  | (AnnotProperty (pos, n, e)) :: items ->
     (AnnotProperty (pos, n, simplify_expr ctx e))
     :: inline_constants_of_node_items ctx items
  | (AnnotMain b) :: items
    -> (AnnotMain b) :: inline_constants_of_node_items ctx items

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
  | (LA.GhostVar (FreeConst (pos, i, ty))) :: others ->
     (LA.GhostVar (FreeConst (pos, i, ty)))
     :: inline_constants_of_contract ctx others 
  | (LA.GhostVar (UntypedConst (pos, i, e))) :: others ->
     (LA.GhostVar (UntypedConst (pos, i, simplify_expr ctx e)))
     :: inline_constants_of_contract ctx others 
  | (LA.GhostVar (TypedConst (pos', i, e, ty))) :: others ->
     (LA.GhostVar (TypedConst (pos', i, simplify_expr ctx e, ty)))
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
  | ConstDecl (_, FreeConst _) as c -> (ctx, c)
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
    let ctx', ldecls' = inline_constants_of_node_locals ctx ldecls in
    let items' = inline_constants_of_node_items ctx' items in
     ctx, (LA.NodeDecl (span, (i, imported, params, ips', ops', ldecls', items', contract)))
  | (LA.FuncDecl (span, (i, imported, params, ips, ops, ldecls, items, contract))) ->
    let ips' = inline_constants_of_const_clocked_type_decl ctx ips in
    let ops' = inline_constants_of_clocked_type_decl ctx ops in
    let ctx', ldecls' = inline_constants_of_node_locals ctx ldecls in
    let items' = inline_constants_of_node_items ctx' items in
     ctx, (LA.FuncDecl (span, (i, imported, params, ips', ops', ldecls', items', contract)))
  | (LA.ContractNodeDecl (span, (i, params, ips, ops, contract))) ->
     ctx, (LA.ContractNodeDecl (span, (i, params, ips, ops, inline_constants_of_contract ctx contract)))
  | e -> (ctx, e)
(** propogate constants post type checking into the AST and constant store*)


let rec inline_constants: TC.tc_context -> LA.t -> (TC.tc_context * LA.t) inline_result = fun ctx ->
  function
  | [] -> R.ok (ctx, [])
  | c :: rest ->
     (try R.ok (substitute ctx c) with
      | Out_of_bounds (pos, err) -> inline_error pos err) >>= fun (ctx', c') ->
     inline_constants ctx' rest >>= fun (ctx'', decls) -> 
     R.ok (ctx'', c'::decls)
(** Best effort at inlining constants *)
