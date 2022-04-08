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

(**
    @author Andrew Marmaduke *)

module A = LustreAst
module AH = LustreAstHelpers
module AIC = LustreAstInlineConstants
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

module StringMap = struct
  include Map.Make(struct
    type t = HString.t
    let compare i1 i2 = HString.compare i1 i2
  end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end

type error_kind = Unknown of string
  | ComplicatedExpr of LustreAst.expr
  | ExprNotSmaller of LustreAst.expr
  | ExprMissingIndex of HString.t * LustreAst.expr

let error_message = function
  | Unknown e -> e
  | ComplicatedExpr e -> "The expression '"
    ^ (Lib.string_of_t A.pp_print_expr e)
    ^ "' is too complicated for simple syntactic well-foundedness of inductive arrays"
  | ExprNotSmaller e -> "The index expression '"
    ^ (Lib.string_of_t A.pp_print_expr e)
    ^ "' is not strictly smaller"
  | ExprMissingIndex (i, e) -> "The index expression '"
    ^ (Lib.string_of_t A.pp_print_expr e)
    ^ "' must contain the index variable '"
    ^ (HString.string_of_hstring i) ^ "'"


type error = [
  | `LustreArrayDependencies of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreArrayDependencies (pos, kind))

let (let*) = Res.(>>=)
let (>>) = Res.(>>)

let union a b = StringMap.union (fun _ a _ -> Some a) a b

let unwrap result = match result with
  | Ok r -> r
  | Error _ -> assert false

let rec process_items = function
  | (A.Body eqn :: tail) ->
    union (process_equation eqn) (process_items tail)
  | _ :: tail -> process_items tail
  | [] -> StringMap.empty

and process_equation = function
  | A.Equation (_, A.StructDef (_, lhs), expr) ->
    process_lhs 0 expr lhs
  | _ -> StringMap.empty

and process_lhs proj expr = function
  | (A.ArrayDef (_, id, indices) :: tail) ->
    let entry = StringMap.singleton id (indices, expr, proj) in
    union entry (process_lhs (proj + 1) expr tail)
  | _ :: tail -> process_lhs (proj + 1) expr tail
  | [] -> StringMap.empty

let rec extract_indexes expr = List.rev
  (match expr with
  | A.ArrayIndex (_, e1, e2) ->
    e2 :: (extract_indexes e1)
  | e -> [e])

let rec check_inductive_array_dependencies ctx = function
  | (A.NodeDecl (_, decl)) :: tail | (A.FuncDecl (_, decl)) :: tail ->
    check_node_decl ctx decl
    >> check_inductive_array_dependencies ctx tail
  | _ :: tail ->
    check_inductive_array_dependencies ctx tail
  | [] -> Ok ()

and check_node_decl ctx decl =
  let (_, _, _, inputs, outputs, locals, items, _) = decl in
  let array_eqns = process_items items in
    (* Setup the typing context *)
  let constants_ctx = inputs
    |> List.map Ctx.extract_consts
    |> (List.fold_left Ctx.union ctx)
  in
  let input_ctx = inputs
    |> List.map Ctx.extract_arg_ctx
    |> (List.fold_left Ctx.union ctx)
  in
  let output_ctx = outputs
    |> List.map Ctx.extract_ret_ctx
    |> (List.fold_left Ctx.union ctx)
  in
  let ctx = Ctx.union
    (Ctx.union constants_ctx ctx)
    (Ctx.union input_ctx output_ctx)
  in
  let ctx = List.fold_left
    (fun ctx local -> Chk.local_var_binding ctx local |> unwrap)
    ctx
    locals
  in
  let checked = List.map (fun id ->
    let (indices, expr, proj) = StringMap.find id array_eqns in
    check_array_equation ctx array_eqns id indices expr proj)
    (StringMap.keys array_eqns)
  in
  Res.seq_ checked

and check_array_equation ctx eqns id indices expr proj =
  let r expr = check_array_equation ctx eqns id indices expr proj in
  match expr with
  (* Identifiers *)
  | A.Ident _ -> Ok ()
  | ModeRef _ -> Ok ()
  | RecordProject (_, e, _) -> r e
  | TupleProject (_, e, _) -> r e
  (* Values *)
  | Const _ -> Ok ()
  (* Operators *)
  | UnaryOp (_, _, e) -> r e
  | BinaryOp (_, _, e1, e2) -> r e1 >> r e2
  | TernaryOp (_, _, e1, e2, e3) -> r e1 >> r e2 >> r e3
  | NArityOp (_, _, es) -> es |> (List.map r) |> Res.seq_
  | ConvOp (_, _, e) -> r e
  | CompOp (_, _, e1, e2) -> r e1 >> r e2
  (* Structured expressions *)
  | RecordExpr (_, _, es) ->
    es |> (List.map (fun (_, e) -> r e)) |> Res.seq_
  | GroupExpr (_, A.ExprList, es) -> r (List.nth es proj)
  | GroupExpr (_, _, es) -> es |> (List.map r) |> Res.seq_
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) -> r e1 >> r e2
  | ArrayConstr (_, e1, e2) -> r e1 >> r e2
  | ArraySlice (_, e1, (e2, e3)) -> r e1 >> r e2 >> r e3
  | ArrayIndex _ as e ->
    check_array_index ctx eqns id indices e
  | ArrayConcat (_, e1, e2) -> r e1 >> r e2
  (* Quantified expressions *)
  | Quantifier (_, _, vars, e) ->
    let ctx = List.fold_left Ctx.union ctx
      (List.map (fun (_, i, ty) -> Ctx.singleton_ty i ty) vars)
    in
    check_array_equation ctx eqns id indices e proj
  (* Clock operators *)
  | When (_, e, _) -> r e
  | Current (_, e) -> r e
  | Condact (_, e1, e2, _, es1, es2) ->
    r e1 >> r e2
    >> (es1 |> (List.map r) |> Res.seq_)
    >> (es2 |> (List.map r) |> Res.seq_)
  | Activate (_, _, e1, e2, es) ->
    r e1 >> r e2
    >> (es |> (List.map r) |> Res.seq_)
  | Merge (_, _, cases) ->
    cases |> (List.map (fun (_, e) -> r e)) |> Res.seq_
  | RestartEvery (_, _, es, e) ->
    r e >> (es |> (List.map r) |> Res.seq_)
  (* Temporal operators *)
  | Pre _ -> Ok ()
  | Fby (_, e1, _, e2) -> r e1 >> r e2
  | Arrow (_, e1, e2) -> r e1 >> r e2
  (* Node calls *)
  | Call (_, _, es) -> es |> (List.map r) |> Res.seq_
  | CallParam (_, _, _, es) -> es |> (List.map r) |> Res.seq_

and check_array_index ctx eqns id indices expr =
  let exprs = extract_indexes expr in
  let (head, indexes) = (List.hd exprs, List.tl exprs) in
  match head with
  | A.Ident (_, id') ->
    if id = id' then
      let checked = List.map
        (fun (i, e) -> index_expr_is_smaller ctx i e)
        (List.combine indices indexes)
      in
      Res.seq_ checked
    else (match StringMap.find_opt id' eqns with
      | Some (indices, expr, proj) ->
        let expr = List.fold_left
          (fun acc (i, e) -> AH.substitute i e acc)
          expr
          (List.combine indices indexes)
        in
        let expr = AIC.simplify_expr ctx expr in
        check_array_equation ctx eqns id indices expr proj
      | None -> Ok ())
  | Arrow (_, _, e2) ->
    check_array_index ctx eqns id indices e2
  | Pre _ -> Ok ()
  | e -> let vars = AH.vars e in
    if A.SI.mem id vars then
      mk_error (AH.pos_of_expr e) (ComplicatedExpr e)
    else Ok ()

and index_expr_is_smaller ctx index expr =
  let pos = AH.pos_of_expr expr in
  let zero = A.Const (Lib.dummy_pos, Num (HString.mk_hstring "0")) in
  let vars = AH.vars expr in
  if not (A.SI.mem index vars) then
    mk_error pos (ExprMissingIndex (index, expr))
  else
    let expr' = AH.substitute index zero expr in
    let* value = (match AIC.eval_int_expr ctx expr' with
      | Ok e -> Ok e
      | Error _ -> mk_error pos (ComplicatedExpr expr))
    in
    if value >= 0 then mk_error pos (ExprNotSmaller expr)
    else Ok ()
  (* match expr with
  | A.BinaryOp (p, Minus, Ident (_, id), e) as expr ->
    let* value = (match AIC.eval_int_expr ctx e with
      | Ok e -> Ok e
      | Error _ -> mk_error p (ComplicatedExpr expr))
    in
    if id != index then mk_error p (ExprWithWrongIndex (index, expr))
    else if value <= 0 then mk_error p (ExprNotSmaller expr)
    else Ok ()
  | BinaryOp (p, Plus, e, Ident (_, id)) as expr ->
    let* value = (match AIC.eval_int_expr ctx e with
      | Ok e -> Ok e
      | Error _ -> mk_error p (ComplicatedExpr expr))
    in
    if id != index then mk_error p (ExprWithWrongIndex (index, expr))
    else if value >= 0 then mk_error p (ExprNotSmaller expr)
    else Ok ()
  | Ident (p, _) as expr -> mk_error p (ExprNotSmaller expr)
  | e -> mk_error (AH.pos_of_expr e) (ComplicatedExpr e) *)
