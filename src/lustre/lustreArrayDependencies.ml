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

module StringMap = HString.HStringMap

let lexiographic_order idx1 idx2 = 
  let idx1_len = List.length idx1 in
  let idx2_len = List.length idx2 in
  if Int.equal idx1_len idx2_len then
    let compared_elements = List.map (fun (i, j) -> i - j) (List.combine idx1 idx2) in
    match (List.filter (fun i -> i != 0) compared_elements) with
    | x :: _ -> x
    | [] -> 0
  else idx1_len - idx2_len

module G = Graph.Make(struct
  type t = A.ident * int list

  let compare (id1, idx1) (id2, idx2) =
    match HString.compare id1 id2 with
    | 0 -> lexiographic_order idx1 idx2
    | x -> x

  let pp_print_t = Lib.pp_print_pair
    (A.pp_print_ident)
    (Lib.pp_print_list Format.pp_print_int " ")
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
  | `LustreArrayDependencies of Position.position * error_kind
]

let mk_error pos kind = Error (`LustreArrayDependencies (pos, kind))

let (let*) = Res.(>>=)
let (>>) = Res.(>>)

let union a b = G.union a b
let union_ a b =
  let* a = a in let* b = b in
  R.ok (union a b)
let empty_ = R.ok G.empty

let zero = A.Const (Position.dummy_pos, A.Num (HString.mk_hstring "0"))

let unwrap result = match result with
  | Ok r -> r
  | Error _ -> assert false

let rec expr_index_layers = function
  | A.ArrayIndex (_, e, _) -> 1 + expr_index_layers e
  | _ -> 0

(** TODO: node summaries need offset information *)
let rec process_items ctx ns = function
  | (A.Body eqn :: tail) ->
    let* (eqn_graph, eqn_pos_map, eqn_count, eqn_len) = process_equation ctx ns eqn in
    let* (tail_graph, tail_pos_map, tail_count, tail_len) = process_items ctx ns tail in
    let graph = union eqn_graph tail_graph in
    let map = StringMap.union (fun _ x _ -> Some x) eqn_pos_map tail_pos_map in
    R.ok (graph, map, eqn_count + tail_count, max eqn_len tail_len)
  | _ :: tail -> process_items ctx ns tail
  | [] -> R.ok (G.empty, StringMap.empty, 0, 0)

and process_equation ctx ns = function
  | A.Equation (_, A.StructDef (_, lhs), expr) ->
    process_lhs ctx ns 0 expr lhs
  | _ -> R.ok (G.empty, StringMap.empty, 0, 0)

and process_lhs ctx ns proj expr = function
  | (A.ArrayDef (pos, id, indices) :: tail) ->
    let zero_list = List.map (fun _ -> 0) indices in
    let* expr_graph = process_expr (Some (List.rev indices)) ctx ns proj [] expr in
    let expr_graph = G.connect expr_graph (id, zero_list) in
    let* (tail_graph, tail_pos_map, count, len) = process_lhs ctx ns (proj + 1) expr tail in
    let graph = union expr_graph tail_graph in
    let map = StringMap.singleton id pos in
    let map = StringMap.union (fun _ x _ -> Some x) map tail_pos_map in
    R.ok (graph, map, count + 1, max len (List.length indices))
  | (A.SingleIdent (pos, id) :: tail) ->
    let* expr_graph = process_expr None ctx ns proj [] expr in
    let expr_graph = G.connect expr_graph (id, 0 :: []) in
    let* (tail_graph, tail_pos_map, count, len)  = process_lhs ctx ns (proj + 1) expr tail in
    let graph = union expr_graph tail_graph in
    let map = StringMap.singleton id pos in
    let map = StringMap.union (fun _ x _ -> Some x) map tail_pos_map in
    R.ok (graph, map, count, len)
  | _ :: tail -> process_lhs ctx ns (proj + 1) expr tail
  | [] -> R.ok (G.empty, StringMap.empty, 0, 0)

and process_expr ind_vars ctx ns proj indices expr =
  let r expr = process_expr ind_vars ctx ns proj indices expr in
  match expr with
  (* Identifiers *)
  | A.Ident (_, id) ->
    R.ok (G.singleton (id, indices))
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
  | GroupExpr (_, A.ExprList, es) -> (
    let g idx exp = process_expr ind_vars ctx ns idx indices exp in
    Ctx.traverse_group_expr_list g ctx proj es
  )
  | GroupExpr (_, _, es) ->
    es |> (List.map r) |> (List.fold_left union_ empty_)
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) -> union_ (r e1) (r e2)
  | ArrayConstr (_, e1, e2) -> union_ (r e1) (r e2)
  | ArraySlice (_, e1, (e2, e3)) ->
    union_ (union_ (r e1) (r e2)) (r e3)
  | ArrayIndex (p, e, idx) ->
    let n = match ind_vars with
      | Some iv -> List.length iv
      | None -> 0
    in
    let index_layers = expr_index_layers e + 1 in
    if n = index_layers then
      (match ind_vars with
      | Some ind_vars' ->
        let ind_var = List.hd ind_vars' in
        let idx' = AH.substitute ind_var zero idx in
        (match AIC.eval_int_expr ctx idx' with
        | Ok idx' ->
          let idx_vars = AH.vars idx in
          if A.SI.cardinal idx_vars = 1 && A.SI.mem ind_var idx_vars then
            let ind_vars = Some (List.tl ind_vars') in
            process_expr ind_vars ctx ns proj (idx' :: indices) e
          else mk_error p (ExprMissingIndex (ind_var, idx))
        | Error _ -> mk_error p (ComplicatedExpr idx))
      | None -> r e)
    else r e
  | ArrayConcat (_, e1, e2) -> union_ (r e1) (r e2)
  (* Quantified expressions *)
  | Quantifier (_, _, vars, e) ->
    let* graph = r e in
    let graph = List.fold_left
      (fun acc (_, id, _) -> G.remove_vertex acc (id, 0 :: []))
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
    let arg_vars = List.map (process_expr ind_vars ctx ns 0 indices) es in
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
  let* (graph, pos_map, count, idx_len) = process_items ctx ns items in
  (* Format.eprintf "Initial graph: %a@." G.pp_print_graph graph; *)
  let graph = add_init_edges idx_len graph in
  (* Format.eprintf "After inits: %a@." G.pp_print_graph graph; *)
  let graph = add_offset_edges count graph  in
  (* Format.eprintf "After offsets: %a@." G.pp_print_graph graph; *)
  let graph = add_wellfounded_edges idx_len graph in
  (* Format.eprintf "After wellfounded: %a@." G.pp_print_graph graph; *)
  let* _ = (try (Res.ok (G.topological_sort graph)) with
    | G.CyclicGraphException ids ->
      let (id, _) = List.hd ids in
      let pos = StringMap.find id pos_map in
      let ids = List.map (fun (id, idx) ->
        let idxs = List.map (fun x -> HString.mk_hstring (string_of_int x)) idx in
        let idxs = HString.concat (HString.mk_hstring " ") idxs in
        HString.concat (HString.mk_hstring " ") [id;idxs])
        ids
      in
      mk_error pos (Cycle ids))
  in
  R.ok ()

(*
  Wellfounded edges prevent larger indexes from being valid.

  For example, the equation A[i] = A[i+1] should be rejected, this equation gives us
  A 0 -> A 1, A 1 -> A 2

  after the init pass and the offset pass, the wellfounded pass will create a new edge
  from every node to every other node whose index value is smaller, thus we get new edges:
  A 2 -> A 1, A 1 -> A 0

  which leads to a cycle
*)
and add_wellfounded_edges idx_len graph =
  let vertices = G.get_vertices graph |> G.to_vertex_list in
  let vertices = List.filter
    (fun (_, offsets) -> List.length offsets = idx_len)
    vertices
  in
  let rec partition_by_id vertices =
    if vertices = [] then [] else
    let (id, indices) = List.hd vertices in
    let vertices = List.tl vertices in
    let (id_vertices, other) = List.partition 
      (fun (id', _) -> HString.equal id id')
      vertices
    in
    let id_verts = (id, indices) :: id_vertices in
    let id_verts = List.sort (fun (_, i1) (_, i2) -> 
        1 - lexiographic_order i1 i2)
      id_verts 
    in
    [id_verts] @ partition_by_id other
  in
  let rec mk_edges vertices =
    if vertices = [] then G.empty else
    let v = List.hd vertices in
    let vertices = List.tl vertices in
    let graph = List.fold_left G.add_vertex G.empty vertices in
    let graph = G.connect graph v in 
    union graph (mk_edges vertices)
  in
  let parts = partition_by_id vertices in
  let edges = List.map mk_edges parts in
  List.fold_left union graph edges

(*
  Adding offset edges recursively adds new edges of an equation at a given instanation
  count number of times.

  For example, given
  A 0 0 -> A -1 -2, B 0 -1

  the first iteration gives the edges:
  A -1 -2 -> A -2 -4, B -1 -3

  the second iteration gives the edges:
  A -2 -4 -> A -3 -6, B -2 -5

  and so on and so forth, for every equation
  Each iteration uses the immediate children of the zeroth node

  At the moment `count` is intialized to the number of equations in a node, it has
  not been proven that this is a sufficient number of iterations to find all possible
  cycles.
*)
and add_offset_edges count graph =
  let vertices = G.get_vertices graph |> G.to_vertex_list in
  let non_zero_vertices = List.filter
    (fun (_, idxs) -> List.fold_left (&&) true (List.map (fun i -> i != 0) idxs))
    vertices
  in
  let mk_edges ((id, offsets) as v) =
    let offsets_len = List.length offsets in
    let nhbd = G.children graph
      (id, List.mapi (fun _ _ -> 0) offsets)
    in
    let nhbd_offset = List.map
      (fun (id', offsets') -> (id', 
        List.mapi (fun i e -> if i < offsets_len then e + (List.nth offsets i) else e) offsets'))
      nhbd
    in
    let graph = List.fold_left G.add_vertex G.empty nhbd_offset in
    let graph = G.connect graph v in
    graph
  in
  let get_new_vertices graph old =
    let vertices = G.get_vertices graph |> G.to_vertex_list in
    List.filter (fun v -> not (List.mem v old)) vertices
  in
  let rec loop n vertices graph =
    if n <= 0 then graph
    else
    let new_edges = List.fold_left
      (fun acc v -> union acc (mk_edges v))
      G.empty 
      vertices
    in
    loop (n - 1) (get_new_vertices new_edges vertices) (union new_edges graph)
  in
  loop count non_zero_vertices graph

(*
  Some edges are created that do not contain all indexes up to the max length.
  For instance, A[i] = B[i][8] + k and B[i][j] = B[i-1][j-1] gives us:
  A 0 -> B 0, B 0 0 -> B -1 -1, A 0 -> k

  This helper function adds fully zero indexed variants to the initial nodes, giving:
  A 0 -> A 0 0, B 0 -> B 0 0, k -> k 0 0
*)
and add_init_edges idx_len graph =
  let vertices = G.get_vertices graph |> G.to_vertex_list in
  let sub_length_vertices = List.filter
    (fun (_, idxs) -> List.length idxs < idx_len)
    vertices
  in
  let parts ((id, offset) as v) =
    let filled_offset = List.init idx_len (fun i ->
      match (List.nth_opt offset i) with
      | Some x -> x
      | None -> 0)
    in
    let filled_graph = G.singleton (id, filled_offset) in
    G.connect filled_graph v 
  in
  List.fold_left (fun acc v -> G.union acc (parts v))
    graph
    sub_length_vertices
