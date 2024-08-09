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

module A = LustreAst
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module AH = LustreAstHelpers

(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let mk_fresh_fn_name: Lib.position -> HString.t -> HString.t = 
fun pos node_name -> 
  i := !i + 1;
  let node_name = HString.concat2 node_name (HString.mk_hstring ".") in
  let pos = Lib.string_of_t Lib.pp_print_line_and_column pos in
  let pos = String.sub pos 1 (String.length pos - 2) |> HString.mk_hstring in
  let name = (HString.mk_hstring "any_") in
  let name = HString.concat2 name pos in
  HString.concat2 node_name name

let rec desugar_expr: Ctx.tc_context -> HString.t -> HString.t list -> A.expr -> A.expr * A.declaration list =
fun ctx node_name fun_ids expr -> 
  let rec_call = desugar_expr ctx node_name fun_ids in
  match expr with
  | A.AnyOp (pos, (_, id, ty), expr1, expr2_opt) -> 
    let span = { A.start_pos = pos; A.end_pos = pos } in
    let contract = match expr2_opt with 
      | None -> [A.Guarantee (AH.pos_of_expr expr1, None, false, expr1)]
      | Some expr2 -> [A.Assume (AH.pos_of_expr expr2, None, false, expr2);
                      A.Guarantee (AH.pos_of_expr expr1, None, false, expr1)] 
    in
    let inputs =
      let vars_of_expr1 = AH.vars_without_node_call_ids expr1 in
      let vars_of_exprs = match expr2_opt with
      | None -> (Ctx.SI.diff vars_of_expr1 (Ctx.SI.singleton id))
      | Some expr2 ->
        let vars_of_expr1_and_expr2 =
          Ctx.SI.union vars_of_expr1 (AH.vars_without_node_call_ids expr2)
        in
        (Ctx.SI.diff vars_of_expr1_and_expr2 (Ctx.SI.singleton id)) in 
      Ctx.SI.union vars_of_exprs (AH.vars_of_type ty) |> Ctx.SI.elements
    in
    (* Global constants don't need to be passed as arguments to generated nodes *)
    let inputs = List.filter (fun i -> 
      match Ctx.lookup_const ctx i with 
        | Some (_, _, Ctx.Global) -> false 
        | _ -> true
    ) inputs in 
    let inputs_call = List.map (fun str -> A.Ident (pos, str)) inputs in
    let ctx = Ctx.add_ty ctx id ty in
    let inputs = List.map (fun input -> (pos, input, Ctx.lookup_ty ctx input, A.ClockTrue)) inputs in
    let inputs = List.map (fun (p, inp, opt, cl) -> match opt with 
      | Some ty -> 
        let is_const = match Ctx.lookup_const ctx inp with | Some _ -> true | None -> false in
        p, inp, ty, cl, is_const 
      | None -> assert false
    ) inputs in
    let name = mk_fresh_fn_name pos node_name in
    (* If the any op expressions are temporal or call a node, we generate an imported node. 
    Otherwise, we generate an imported function. *)
    let has_pre_arrow_or_node_call = match expr2_opt with 
    | Some expr2 -> 
      let node_calls1 = AH.calls_of_expr expr1 |> Ctx.SI.elements |> List.filter (fun i -> not (List.mem i fun_ids)) in 
      let node_calls2 = AH.calls_of_expr expr2 |> Ctx.SI.elements |> List.filter (fun i -> not (List.mem i fun_ids)) in 
      (AH.has_pre_or_arrow expr1 != None) || node_calls1 != [] || 
      (AH.has_pre_or_arrow expr2 != None) || node_calls2 != []
    | None -> 
      let node_calls1 = AH.calls_of_expr expr1 |> Ctx.SI.elements |> List.filter (fun i -> not (List.mem i fun_ids)) in 
      (AH.has_pre_or_arrow expr1 != None) || (node_calls1 != []) 
    in
    (* The generated imported node might be polymorphic, so we find all the needed type variables *)
    let ty_params = 
      Ctx.SI.union (Ctx.ty_vars_of_type ctx node_name ty) 
                   (Ctx.ty_vars_of_expr ctx node_name expr1)
      |> Ctx.SI.elements
    in 
    let ty_params = match expr2_opt with 
    | Some expr2 -> ty_params @ Ctx.SI.elements (Ctx.ty_vars_of_expr ctx node_name expr2)
    | None -> ty_params 
    in
    let ty_vars = List.map (fun id -> A.UserType (pos, [], id)) ty_params in
    let generated_node = 
      if has_pre_arrow_or_node_call then
        A.NodeDecl (span, 
        (name, true, ty_params, inputs, 
        [pos, id, ty, A.ClockTrue], [], [], Some (pos, contract))) 
      else 
        A.FuncDecl (span, 
        (name, true, ty_params, inputs, 
        [pos, id, ty, A.ClockTrue], [], [], Some (pos, contract)))  
    in
    A.Call(pos, ty_vars, name, inputs_call), [generated_node]

  | Ident _ as e -> e, []
  | ModeRef (_, _) as e -> e, []
  | Const (_, _) as e -> e, []
  | RecordProject (pos, e, idx) -> 
    let e, gen_nodes = rec_call e in
    RecordProject (pos, e, idx), gen_nodes
  | TupleProject (pos, e, idx) -> 
    let e, gen_nodes = rec_call e in
    TupleProject (pos, e, idx), gen_nodes
  | UnaryOp (pos, op, e) -> 
    let e, gen_nodes = rec_call e in
    UnaryOp (pos, op, e), gen_nodes
  | BinaryOp (pos, op, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    BinaryOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
  | TernaryOp (pos, op, e1, e2, e3) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    let e3, gen_nodes3 = rec_call e3 in
    TernaryOp (pos, op, e1, e2, e3), gen_nodes1 @ gen_nodes2 @ gen_nodes3
  | ConvOp (pos, op, e) -> 
    let e, gen_nodes = rec_call e in
    ConvOp (pos, op, e), gen_nodes
  | CompOp (pos, op, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    CompOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
  | RecordExpr (pos, ident, expr_list) ->
    let id_list, exprs_gen_nodes = 
      List.map (fun (i, e) -> (i, (rec_call) e)) expr_list |> List.split 
    in
    let expr_list, gen_nodes = List.split exprs_gen_nodes in
    RecordExpr (pos, ident, List.combine id_list expr_list), List.flatten gen_nodes
  | GroupExpr (pos, kind, expr_list) ->
    let expr_list, gen_nodes = List.map (rec_call) expr_list |> List.split in
    GroupExpr (pos, kind, expr_list), List.flatten gen_nodes
  | StructUpdate (pos, e1, idx, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    StructUpdate (pos, e1, idx, e2), gen_nodes1 @ gen_nodes2
  | ArrayConstr (pos, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    ArrayConstr (pos, e1, e2), gen_nodes1 @ gen_nodes2
  | ArrayIndex (pos, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    ArrayIndex (pos, e1, e2), gen_nodes1 @ gen_nodes2
  | Quantifier (pos, kind, idents, e) ->
    let e, gen_nodes = rec_call e in
    Quantifier (pos, kind, idents, e), gen_nodes
  | When (pos, e, clock) -> 
    let e, gen_nodes = rec_call e in
    When (pos, e, clock), gen_nodes
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    let expr_list1, gen_nodes3 = List.map rec_call expr_list1 |> List.split in
    let expr_list2, gen_nodes4 = List.map rec_call expr_list2 |> List.split in
    Condact (pos, e1, e2, id, expr_list1, expr_list2), gen_nodes1 @ gen_nodes2 @ 
                                                      List.flatten gen_nodes3 @ List.flatten gen_nodes4
  | Activate (pos, ident, e1, e2, expr_list) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    Activate (pos, ident, e1, e2, expr_list), gen_nodes1 @ gen_nodes2
  | Merge (pos, ident, expr_list) ->
    let id_list, exprs_gen_nodes = 
      List.map (fun (i, e) -> (i, (rec_call) e)) expr_list |> List.split 
    in
    let expr_list, gen_nodes = List.split exprs_gen_nodes in
    Merge (pos, ident, List.combine id_list expr_list), List.flatten gen_nodes
  | RestartEvery (pos, ident, expr_list, e) ->
    let expr_list, gen_nodes1 = List.map (rec_call) expr_list |> List.split in
    let e, gen_nodes2 = rec_call e in
    RestartEvery (pos, ident, expr_list, e), List.flatten gen_nodes1 @ gen_nodes2
  | Pre (pos, e) -> 
    let e, gen_nodes = rec_call e in
    Pre (pos, e), gen_nodes
  | Arrow (pos, e1, e2) -> 
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    Arrow (pos, e1, e2), gen_nodes1 @ gen_nodes2
  | Call (pos, ty_args, id, expr_list) ->
    let expr_list, gen_nodes = List.map rec_call expr_list |> List.split in
    Call (pos, ty_args, id, expr_list), List.flatten gen_nodes

let desugar_contract_item: Ctx.tc_context -> HString.t -> HString.t list -> A.contract_node_equation -> A.contract_node_equation * A.declaration list =
fun ctx node_name fun_ids ci ->
  let rec_call = desugar_expr ctx node_name fun_ids in
  match ci with
  | A.GhostVars (pos, lhs, e) -> 
    let e, gen_nodes = rec_call e in 
    A.GhostVars (pos, lhs, e), gen_nodes
  | Assume (pos, name, b, e) ->
    let e, gen_nodes = rec_call e in 
    Assume (pos, name, b, e), gen_nodes
  | Guarantee (pos, name, b, e) -> 
    let e, gen_nodes = rec_call e in 
    Guarantee (pos, name, b, e), gen_nodes
  | Mode (pos, i, reqs, enss) ->
    let (reqs, gen_nodes1) = 
      List.map (fun (pos, id, expr) -> (pos, id, rec_call expr)) reqs |> 
      List.map (fun (pos, id, (expr, decls)) -> ((pos, id, expr), decls)) |> 
      List.split in 
    let (enss, gen_nodes2) = 
      List.map (fun (pos, id, expr) -> (pos, id, rec_call expr)) enss |> 
      List.map (fun (pos, id, (expr, decls)) -> ((pos, id, expr), decls)) |> 
      List.split in 
    Mode (pos, i, reqs, enss), (List.flatten gen_nodes1) @ (List.flatten gen_nodes2)
  | ContractCall (pos, i, ty_args, exprs, ids) -> 
    let (exprs, gen_nodes) = List.map rec_call exprs |> List.split in 
    ContractCall (pos, i, ty_args, exprs, ids), List.flatten gen_nodes
  | GhostConst _ 
  | AssumptionVars _ as ci -> ci, []

let desugar_contract: Ctx.tc_context -> HString.t -> HString.t list -> A.contract option -> A.contract option * A.declaration list =
fun ctx node_name fun_ids contract -> 
  match contract with 
  | Some (pos, contract_items) -> 
    let items, gen_nodes = (List.map (desugar_contract_item ctx node_name fun_ids) contract_items) |> List.split in
    Some (pos, items), List.flatten gen_nodes
  | None -> None, []

let rec desugar_node_item: Ctx.tc_context -> HString.t -> HString.t list -> A.node_item -> A.node_item * A.declaration list =
fun ctx node_name fun_ids ni ->
  let rec_call = desugar_node_item ctx node_name fun_ids in
  match ni with
  | A.Body (Equation (pos, lhs, rhs)) -> 
    let rhs, gen_nodes = desugar_expr ctx node_name fun_ids rhs in 
    A.Body (Equation (pos, lhs, rhs)), gen_nodes
  | AnnotProperty (pos, name, e, k) -> 
    let e, gen_nodes = desugar_expr ctx node_name fun_ids e in 
    AnnotProperty(pos, name, e, k), gen_nodes
  | IfBlock (pos, cond, nis1, nis2) -> 
    let nis1, gen_nodes1 = List.map rec_call nis1 |> List.split in
    let nis2, gen_nodes2 = List.map rec_call nis2 |> List.split in
    let cond, gen_nodes3 = desugar_expr ctx node_name fun_ids cond in
    A.IfBlock (pos, cond, nis1, nis2), List.flatten gen_nodes1 @ List.flatten gen_nodes2 @ gen_nodes3
  | FrameBlock (pos, vars, nes, nis) -> 
    let nes = List.map (fun x -> A.Body x) nes in
    let nes, gen_nodes1 = List.map rec_call nes |> List.split in
    let nes = List.map (fun ne -> match ne with
      | A.Body (A.Equation _ as eq) -> eq
      | _ -> assert false
    ) nes in
    let nis, gen_nodes2 = List.map rec_call nis |> List.split in
    FrameBlock(pos, vars, nes, nis), List.flatten gen_nodes1 @ List.flatten gen_nodes2
  | Body (Assert (pos, e)) ->
    let e, gen_nodes = desugar_expr ctx node_name fun_ids e in 
    Body (Assert (pos, e)), gen_nodes
  | AnnotMain _ -> ni, []
    

let desugar_any_ops: Ctx.tc_context -> A.declaration list -> A.declaration list = 
fun ctx decls -> 
  let fun_ids = List.filter_map 
    (fun decl -> match decl with | A.FuncDecl (_, (id, _, _, _, _, _, _, _)) -> Some id | _ -> None) 
    decls 
  in
  let decls =
  List.fold_left (fun decls decl ->
    match decl with
    | A.NodeDecl (span, (id, ext, params, inputs, outputs, locals, items, contract)) -> 
      let ctx = Chk.add_full_node_ctx ctx id params inputs outputs locals in
      let items, gen_nodes = List.map (desugar_node_item ctx id fun_ids) items |> List.split in 
      let contract, gen_nodes2 = desugar_contract ctx id fun_ids contract in
      let gen_nodes = List.flatten gen_nodes in
      decls @ gen_nodes @ gen_nodes2 @ [A.NodeDecl (span, (id, ext, params, inputs, outputs, locals, items, contract))]
    | A.FuncDecl (span, (id, ext, params, inputs, outputs, locals, items, contract)) -> 
      let ctx = Chk.add_full_node_ctx ctx id params inputs outputs locals in
      let items, gen_nodes = List.map (desugar_node_item ctx id fun_ids) items |> List.split in 
      let contract, gen_nodes2 = desugar_contract ctx id fun_ids contract in
      let gen_nodes = List.flatten gen_nodes in
      decls @ gen_nodes @ gen_nodes2 @ [A.FuncDecl (span, (id, ext, params, inputs, outputs, locals, items, contract))]
    | A.ContractNodeDecl (span, (id, params, inputs, outputs, contract)) ->
      let ctx = Chk.add_io_node_ctx ctx id params inputs outputs in
      let contract, gen_nodes = desugar_contract ctx id fun_ids (Some contract) in
      let contract = match contract with
      | Some contract -> contract
      | None -> assert false in (* Must have a contract *)
      decls @ gen_nodes @ [A.ContractNodeDecl (span, (id, params, inputs, outputs, contract))]
    | _ -> decl :: decls
  ) [] decls in 
  decls
