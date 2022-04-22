(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

module R = Res
module A = LustreAst
module AH = LustreAstHelpers
module AD = LustreAstDependencies
module AIC = LustreAstInlineConstants
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

module G = Graph.Make(struct
  type t = A.ident * int

  let compare (id1, idx1) (id2, idx2) =
    match HString.compare id1 id2 with
    | 0 -> idx1 - idx2
    | x -> x

  let pp_print_t = Lib.pp_print_pair
    (A.pp_print_ident)
    (Format.pp_print_int)
    " "
end)

type error_kind = Unknown of string
  | ComplicatedExpr of LustreAst.expr
  | ExprMissingIndex of HString.t * LustreAst.expr
  | Cycle of HString.t list

let error_message = function
  | Unknown e -> e
  | ComplicatedExpr e -> "The expression '"
    ^ (Lib.string_of_t A.pp_print_expr e)
    ^ "' is too complicated in definition of inductive array"
  | Cycle ids -> "Cyclic dependency detected in definition of identifiers: "
    ^ (Lib.string_of_t (Lib.pp_print_list A.pp_print_ident " -> ") ids)
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

let union a b = G.union a b
let union_ a b =
  let* a = a in let* b = b in
  R.ok (union a b)
let empty_ = R.ok G.empty

let zero = A.Const (Lib.dummy_pos, A.Num (HString.mk_hstring "0"))

let unwrap result = match result with
  | Ok r -> r
  | Error _ -> assert false

let rec process_items ctx ns = function
  | (A.Body eqn :: tail) ->
    let* processed_eqn = process_equation ctx ns eqn in
    let* processed_tail = process_items ctx ns tail in
    R.ok (union processed_eqn processed_tail)
  | _ :: tail -> process_items ctx ns tail
  | [] -> empty_

and process_equation ctx ns = function
  | A.Equation (_, A.StructDef (_, lhs), expr) ->
    process_lhs ctx ns 0 expr lhs
  | _ -> empty_

and process_lhs ctx ns proj expr = function
  | (A.ArrayDef (_, id, indices) :: tail) ->
    (* TODO: how to handle multiple indices, substitute 0 for all of them? *)
    let* expr_graph = process_expr (Some (List.hd indices)) ctx ns proj None expr in
    let expr_graph = G.connect expr_graph (id, 0) in
    let* processed_tail = process_lhs ctx ns (proj + 1) expr tail in
    R.ok (union expr_graph processed_tail)
  | (A.SingleIdent (_, id) :: tail) ->
    let* expr_graph = process_expr None ctx ns proj None expr in
    let expr_graph = G.connect expr_graph (id, 0) in
    let* processed_tail = process_lhs ctx ns (proj + 1) expr tail in
    R.ok (union expr_graph processed_tail)
  | _ :: tail -> process_lhs ctx ns (proj + 1) expr tail
  | [] -> empty_

and process_expr ind_var ctx ns proj idx expr =
  let r expr = process_expr ind_var ctx ns proj idx expr in
  match expr with
  (* Identifiers *)
  | A.Ident (_, id) ->
    let idx = match idx with Some idx -> idx | None -> 0 in
    let graph = G.singleton (id, idx) in
    R.ok graph
  | ModeRef _ -> empty_
  | RecordProject (_, e, _) -> r e
  | TupleProject (_, e, _) -> r e
  (* Values *)
  | Const _ -> empty_
  (* Operators *)
  | UnaryOp (_, _, e) -> r e
  | BinaryOp (_, _, e1, e2) -> union_ (r e1) (r e2)
  | TernaryOp (_, _, e1, e2, e3) ->
    union_ (union_ (r e1) (r e2)) (r e3)
  | NArityOp (_, _, es) ->
    es |> (List.map r) |> (List.fold_left union_ empty_)
  | ConvOp (_, _, e) -> r e
  | CompOp (_, _, e1, e2) -> union_ (r e1) (r e2)
  (* Structured expressions *)
  | RecordExpr (_, _, es) ->
    es |> (List.map (fun (_, e) -> r e)) |> (List.fold_left union_ empty_)
  | GroupExpr (_, A.ExprList, es) ->
    (match List.nth_opt es proj with
    | Some e -> r e
    | None -> empty_)
  | GroupExpr (_, _, es) ->
    es |> (List.map r) |> (List.fold_left union_ empty_)
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) -> union_ (r e1) (r e2)
  | ArrayConstr (_, e1, e2) -> union_ (r e1) (r e2)
  | ArraySlice (_, e1, (e2, e3)) ->
    union_ (union_ (r e1) (r e2)) (r e3)
  | ArrayIndex (p, e, idx) ->
    (match ind_var with
    | Some ind_var' ->
      let idx' = AH.substitute ind_var' zero idx in
      (match AIC.eval_int_expr ctx idx' with
      | Ok idx' ->
        let idx_vars = AH.vars idx in
        if A.SI.mem ind_var' idx_vars then
          process_expr ind_var ctx ns proj (Some idx') e
        else mk_error p (ExprMissingIndex (ind_var', idx))
      | Error _ -> mk_error p (ComplicatedExpr idx))
    | None -> r e)
  | ArrayConcat (_, e1, e2) -> union_ (r e1) (r e2)
  (* Quantified expressions *)
  | Quantifier (_, _, vars, e) ->
    let* graph = r e in
    let graph = List.fold_left
      (fun acc (_, id, _) -> G.remove_vertex acc (id, 0))
      graph
      vars
    in
    R.ok graph
  (* Clock operators *)
  | When (_, e, _) -> r e
  | Current (_, e) -> r e
  | Condact (_, e1, e2, _, es1, es2) ->
    let graph1 = union_ (r e1) (r e2) in
    let graph2 = (es1 |> (List.map r) |> (List.fold_left union_ empty_)) in
    let graph3 = (es2 |> (List.map r) |> (List.fold_left union_ empty_)) in
    union_ (union_ graph1 graph2) graph3
  | Activate (_, _, e1, e2, es) ->
    let graph1 = union_ (r e1) (r e2) in
    let graph2 = (es |> (List.map r) |> (List.fold_left union_ empty_)) in
    union_ graph1 graph2
  | Merge (_, _, cases) ->
    cases |> (List.map (fun (_, e) -> r e)) |> (List.fold_left union_ empty_)
  | RestartEvery (_, _, es, e) ->
    let graph = es |> (List.map r) |> (List.fold_left union_ empty_) in
    union_ (r e) graph
  (* Temporal operators *)
  | Pre _ -> empty_
  | Fby (_, e1, _, e2) -> union_ (r e1) (r e2)
  | Arrow (_, e1, e2) -> union_ (r e1) (r e2)
  (* Node calls *)
  | Call (_, i, es) ->
    let arg_vars = List.map r es in
    let node_map = AD.IMap.find i ns in
    let dep_args = AD.IntMap.find proj node_map in
    List.fold_left (fun acc idx ->
        match List.nth_opt arg_vars idx with
        | Some v -> union_ acc v
        | None -> acc)
      empty_
      dep_args
  | CallParam (_, _, _, es) ->
    es |> (List.map r) |> (List.fold_left union_ empty_)

let rec check_inductive_array_dependencies ctx ns = function
  | (A.NodeDecl (_, decl)) :: tail | (A.FuncDecl (_, decl)) :: tail ->
    check_node_decl ctx ns decl
    >> check_inductive_array_dependencies ctx ns tail
  | _ :: tail ->
    check_inductive_array_dependencies ctx ns tail
  | [] -> Ok ()

and check_node_decl ctx ns decl =
  let (_, _, _, inputs, outputs, locals, items, _) = decl in
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
  let* graph = process_items ctx ns items in
  let graph = add_wellfounded_edges graph in
  let graph = add_offset_edges graph in
  (* Format.eprintf "Inductive arrays graph: %a@." G.pp_print_graph graph; *)
  let* _ = (try (Res.ok (G.topological_sort graph)) with
    | Graph.CyclicGraphException ids ->
      let ids = List.map HString.mk_hstring ids in
      mk_error Lib.dummy_pos (Cycle ids))
  in
  R.ok ()

and add_wellfounded_edges graph =
  let vertices = G.get_vertices graph |> G.to_vertex_list in
  let rec partition_by_id vertices =
    if vertices = [] then []
    else
      let (id, idx) = List.hd vertices in
      let vertices = List.tl vertices in
      let (id_vertices, other) = List.partition 
        (fun (id', _) -> HString.equal id id')
        vertices
      in
      let id_verts = (id, idx) :: id_vertices in
      let id_verts = List.sort (fun (_, i1) (_, i2) -> i2 - i1) id_verts in
      [id_verts] @ partition_by_id other
  in
  let rec mk_edges vertices =
    if vertices = [] then G.empty
    else
      let v = List.hd vertices in
      let vertices = List.tl vertices in
      let graph = List.fold_left G.add_vertex G.empty vertices in
      let graph = G.connect graph v in
      union graph (mk_edges vertices)
  in
  let parts = partition_by_id vertices in
  let edges = List.map mk_edges parts in
  List.fold_left union graph edges

and add_offset_edges graph =
  let vertices = G.get_vertices graph |> G.to_vertex_list in
  let non_zero_vertices = List.filter (fun (_, idx) -> idx != 0) vertices in
  let mk_edges ((id, idx) as v) =
    let nhbd = G.children graph (id, 0) in
    let nhbd_offset = List.map (fun (id', idx') -> (id', idx' + idx)) nhbd in
    let graph = List.fold_left G.add_vertex G.empty nhbd_offset in
    let graph = G.connect graph v in
    (* Format.eprintf "graph: %a@." G.pp_print_graph graph; *)
    graph
  in
  List.fold_left (fun acc v -> union acc (mk_edges v)) graph non_zero_vertices
