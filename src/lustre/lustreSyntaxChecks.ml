(* This file is part of the Kind 2 model checker.

   Copyright (c) 2021 by the Board of Trustees of the University of Iowa

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
(** Check various syntactic properties that do not depend on type information
  
  @author Andrew Marmaduke *)

module LA = LustreAst

module StringSet = Set.Make(
  struct
    let compare = String.compare
    type t = string
  end)

type 'a sc_result = ('a, Lib.position * string) result

type context = {
  types : StringSet.t;
  nodes : StringSet.t;
  functions : StringSet.t;
  contracts : StringSet.t;
  consts : StringSet.t;
  locals : StringSet.t }

(* let (>>=) = Res.(>>=) *)
let (>>) = Res.(>>)

let syntax_error pos msg = Error (pos, msg)

let empty_ctx () = {
    types = StringSet.empty;
    nodes = StringSet.empty;
    functions = StringSet.empty;
    contracts = StringSet.empty;
    consts = StringSet.empty;
    locals = StringSet.empty
  }

let ctx_add_type ctx i = {
    ctx with types = StringSet.add i ctx.types
  }

let ctx_add_node ctx i = {
    ctx with nodes = StringSet.add i ctx.nodes
  }

let ctx_add_contract ctx i = {
    ctx with contracts = StringSet.add i ctx.contracts
  }

let ctx_add_func ctx i = {
    ctx with functions = StringSet.add i ctx.functions
  }

let ctx_add_consts ctx i = {
    ctx with consts = StringSet.add i ctx.consts
  }

let ctx_add_local ctx i = {
    ctx with locals = StringSet.add i ctx.locals
  }

let build_global_ctx (decls:LustreAst.t) =
  let over_decls acc = function
    | LA.TypeDecl (_, AliasType (_, i, _)) -> ctx_add_type acc i
    | TypeDecl (_, FreeType (_, i)) -> ctx_add_type acc i
    | ConstDecl (_, FreeConst (_, i, _)) -> ctx_add_consts acc i
    | ConstDecl (_, UntypedConst (_, i, _)) -> ctx_add_consts acc i
    | ConstDecl (_, TypedConst (_, i, _, _)) -> ctx_add_consts acc i
    | NodeDecl (_, (i, _, _, _, _, _, _, _)) -> ctx_add_node acc i
    | FuncDecl (_, (i, _, _, _, _, _, _, _)) -> ctx_add_func acc i
    | ContractNodeDecl (_, (i, _, _, _, _)) -> ctx_add_contract acc i
    | _ -> acc
  in
  List.fold_left over_decls (empty_ctx ()) decls

let build_local_ctx ctx locals inputs outputs =
  let over_locals acc = function
    | LA.NodeConstDecl (_, FreeConst (_, i, _)) -> ctx_add_local acc i
    | NodeConstDecl (_, UntypedConst (_, i, _)) -> ctx_add_local acc i
    | NodeConstDecl (_, TypedConst (_, i, _, _)) -> ctx_add_local acc i
    | NodeVarDecl (_, (_, i, _, _)) -> ctx_add_local acc i
  in
  let over_inputs acc (_, i, _, _, _) = ctx_add_local acc i in
  let over_outputs acc (_, i, _, _) = ctx_add_local acc i in
  let ctx = List.fold_left over_locals ctx locals in
  let ctx = List.fold_left over_inputs ctx inputs in
  List.fold_left over_outputs ctx outputs

let locals_must_have_definitions locals items =
  let rec find_local_def_lhs id test = function
    | LA.SingleIdent (_, id')
    | TupleSelection (_, id', _)
    | FieldSelection (_, id', _)
    | ArraySliceStructItem (_, id', _)
    | ArrayDef (_, id', _)
      -> test || id = id'
    | TupleStructItem (_, items) ->
      let test_items = items |> List.map (find_local_def_lhs id test)
        |> List.fold_left (fun x y -> x || y) false
      in
      test || test_items
  in
  let find_local_def id = function
    | LA.Body eqn -> (match eqn with
      | LA.Assert _ -> false
      | LA.Equation (_, lhs, _) -> (match lhs with
        | LA.StructDef (_, vars)
          -> List.fold_left (find_local_def_lhs id) false vars)
      | LA.Automaton _ -> false)
    | LA.AnnotMain _ -> false
    | LA.AnnotProperty _ -> false
  in
  let over_locals = function
    | LA.NodeConstDecl _ -> Ok ()
    | LA.NodeVarDecl (_, (pos, id, _, _)) ->
      let test = List.find_opt (fun item -> find_local_def id item) items in
      match test with
      | Some _ -> Ok ()
      | None -> syntax_error pos
        (Format.asprintf "Local variable %s has no definition." id)
  in
  Res.seq (List.map over_locals locals)

let no_dangling_node_calls ctx = function
  | LA.Condact (pos, _, _, i, _, _)
  | Activate (pos, i, _, _, _)
  | Call (pos, i, _) ->
    let check_nodes = StringSet.find_opt i ctx.nodes in
    let check_funcs = StringSet.find_opt i ctx.functions in
    (match check_nodes, check_funcs with
    | Some _, _ -> Ok ()
    | _, Some _ -> Ok ()
    | None, None -> syntax_error pos
      (Format.asprintf "No node with name %s found." i))
  | _ -> Ok ()

let no_dangling_identifiers ctx = function
  | LA.Ident (pos, i) -> 
    let check_consts = StringSet.find_opt i ctx.consts in
    let check_locals = StringSet.find_opt i ctx.locals in
    (match check_consts, check_locals with
    | Some _, _ -> Ok ()
    | _, Some _ -> Ok ()
    | None, None -> syntax_error pos
      (Format.asprintf "No identifier with name %s found." i))
  | _ -> Ok ()

let no_calls_to_node ctx = function
  | LA.Condact (pos, _, _, i, _, _)
  | Activate (pos, i, _, _, _)
  | Call (pos, i, _) ->
    let check_nodes = StringSet.find_opt i ctx.nodes in
    (match check_nodes with
    | Some _ -> syntax_error pos
      (Format.asprintf "Illegal call to node %s, functions can only call other functions, not nodes." i)
    | None -> Ok ())
  | _ -> Ok ()

let no_temporal_operator is_const expr =
  let decl_ctx = if is_const then "constant" else "function" in
  let template = Format.asprintf "Illegal %s in %s definition, %ss cannot have state" in
  match expr with
  | LA.Pre (pos, _) -> syntax_error pos (template "pre" decl_ctx decl_ctx)
  | Arrow (pos, _, _) -> syntax_error pos (template "arrow" decl_ctx decl_ctx)
  | Last (pos, _) -> syntax_error pos (template "last" decl_ctx decl_ctx)
  | Fby (pos, _, _, _) -> syntax_error pos (template "fby" decl_ctx decl_ctx)
  | _ -> Ok ()

let unsupported_expr = function
  | LA.When (pos, _, _) -> syntax_error pos
    (Format.asprintf "Current and when expressions are not supported")
  | LA.Current (pos, _) -> syntax_error pos
      (Format.asprintf "Current expression is not supported")
  | _ -> Ok ()

let rec syntax_check (ast:LustreAst.t) =
  let ctx = build_global_ctx ast in
  Res.seq (List.map (check_declaration ctx) ast)

and check_declaration ctx = function
  | TypeDecl (span, decl) -> Ok (LA.TypeDecl (span, decl))
  | ConstDecl (span, decl) ->
    let check = match decl with
      | LA.FreeConst _ -> Ok ()
      | UntypedConst (_, _, e)
      | TypedConst (_, _, e, _) -> check_const_expr_decl ctx e
    in
    check >> Ok (LA.ConstDecl (span, decl))
  | NodeDecl (span, decl) -> check_node_decl ctx span decl
  | FuncDecl (span, decl) -> check_func_decl ctx span decl
  | ContractNodeDecl (span, decl) -> Ok (LA.ContractNodeDecl (span, decl))
  | NodeParamInst (span, inst) -> Ok (LA.NodeParamInst (span, inst))

and check_const_expr_decl ctx expr =
  let composed_checks e =
    (no_temporal_operator true e)
      >> (no_dangling_identifiers ctx e)
  in
  check_expr composed_checks expr

and check_node_decl ctx span (id, ext, params, inputs, outputs, locals, items, contracts) =
  let ctx = build_local_ctx ctx locals inputs outputs in
  let decl = LA.NodeDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contracts))
  in
  let composed_items_checks e =
    (no_dangling_node_calls ctx e)
      >> (no_dangling_identifiers ctx e)
      >> (unsupported_expr e)
  in
  (locals_must_have_definitions locals items)
    >> (check_items composed_items_checks items)
    >> (Ok decl)

and check_func_decl ctx span (id, ext, params, inputs, outputs, locals, items, contracts) =
  let ctx = build_local_ctx ctx locals inputs outputs in
  let decl = LA.FuncDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contracts))
  in
  let composed_items_checks e =
    (no_dangling_node_calls ctx e)
      >> (no_calls_to_node ctx e)
      >> (no_temporal_operator false e)
      >> (no_dangling_identifiers ctx e)
      >> (unsupported_expr e)
  in
  (check_items composed_items_checks items)
    >> (Ok decl)

and check_items f items =
  let check_item f = function
    | LA.Body (Assert (_, e))
    | Body (Equation (_, _, e))
    | AnnotProperty (_, _, e) -> check_expr f e
    | Body (Automaton _) -> Ok ()
    | AnnotMain _ -> Ok ()
  in
  Res.seqM (fun x _ -> x) () (List.map (check_item f) items)

and check_expr f (expr:LustreAst.expr) =
  let check_list e = Res.seqM (fun x _ -> x) () (List.map (check_expr f) e) in
  let expr' = f expr in
  let r = match expr with
    | LA.RecordProject (_, e, _)
    | TupleProject (_, e, _)
    | UnaryOp (_, _, e)
    | ConvOp (_, _, e)
    | Quantifier (_, _, _, e)
    | When (_, e, _)
    | Current (_, e)
    | Pre (_, e)
      -> check_expr f e
    | BinaryOp (_, _, e1, e2)
    | CompOp (_, _, e1, e2)
    | StructUpdate (_, e1, _, e2)
    | ArrayConstr (_, e1, e2)
    | ArrayIndex (_, e1, e2)
    | ArrayConcat (_, e1, e2)
    | Fby (_, e1, _, e2)
    | Arrow (_, e1, e2)
      -> (check_expr f e1) >> (check_expr f e2)
    | TernaryOp (_, _, e1, e2, e3)
    | ArraySlice (_, e1, (e2, e3))
      -> (check_expr f e1) >> (check_expr f e2) >> (check_expr f e3)
    | NArityOp (_, _, e)
    | GroupExpr (_, _, e)
    | Call (_, _, e)
    | CallParam (_, _, _, e)
      -> check_list e
    | RecordExpr (_, _, e)
    | Merge (_, _, e)
      -> let e = List.map (fun (_, e) -> e) e in check_list e
    | Condact (_, e1, e2, _, e3, e4)
      -> (check_expr f e1) >> (check_expr f e2)
        >> (check_list e3) >> (check_list e4)
    | Activate (_, _, e1, e2, e3)
      -> (check_expr f e1) >> (check_expr f e2) >> (check_list e3)
    | RestartEvery (_, _, e1, e2)
      -> (check_list e1) >> (check_expr f e2)
    | _ -> Ok ()
  in
  expr' >> r