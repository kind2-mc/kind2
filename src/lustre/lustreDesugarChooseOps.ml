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
 
 let mk_fresh_fn_name pos node_name =
   i := !i + 1;
   let node_name = HString.concat2 node_name (HString.mk_hstring ".") in
   let pos = Lib.string_of_t Lib.pp_print_line_and_column pos in
   let pos = String.sub pos 1 (String.length pos - 2) |> HString.mk_hstring in
   let name = (HString.mk_hstring "choose_") in
   let name = HString.concat2 name pos in
   HString.concat2 node_name name
 
 let rec desugar_expr ctx node_name = function
   | A.ChooseOp (pos, (_, id, ty), expr1, expr2_opt) -> 
     let span = { A.start_pos = Lib.dummy_pos; A.end_pos = Lib.dummy_pos } in
     let contract = match expr2_opt with 
      | None -> [A.Guarantee (Lib.dummy_pos, None, false, expr1)]
      | Some expr2 -> [A.Assume (Lib.dummy_pos, None, false, expr2); 
                       A.Guarantee (Lib.dummy_pos, None, false, expr1)] in
     let inputs = Ctx.SI.elements (Ctx.SI.diff (AH.vars expr1) (Ctx.SI.singleton id)) in
     (* Constants don't need to be passed as a parameter to generated node *)
     let inputs = List.filter (fun i -> not (Ctx.member_val ctx i)) inputs in 
     let inputs_call = List.map (fun str -> A.Ident (pos, str)) inputs in
     let ctx = Ctx.add_ty ctx id ty in
     let inputs = List.map (fun input -> (pos, input, Ctx.lookup_ty ctx input, A.ClockTrue)) inputs in
     let inputs = List.map (fun (p, inp, opt, cl) -> match opt with 
       | Some ty -> p, inp, ty, cl, false 
       | None -> assert false
     ) inputs in
     let name = mk_fresh_fn_name pos node_name in
     let generated_node = 
       A.NodeDecl (span, 
       (name, true, [], inputs, 
       [Lib.dummy_pos, id, ty, A.ClockTrue], [], [], Some contract)) 
     in
     A.Call(pos, name, inputs_call), [generated_node]
 
   | Ident _ as e -> e, []
   | ModeRef (_, _) as e -> e, []
   | Const (_, _) as e -> e, []
   | RecordProject (pos, e, idx) -> 
     let e, gen_nodes = desugar_expr ctx node_name e in
     RecordProject (pos, e, idx), gen_nodes
   | TupleProject (pos, e, idx) -> 
     let e, gen_nodes = desugar_expr ctx node_name e in
     TupleProject (pos, e, idx), gen_nodes
   | UnaryOp (pos, op, e) -> 
     let e, gen_nodes = desugar_expr ctx node_name e in
     UnaryOp (pos, op, e), gen_nodes
   | BinaryOp (pos, op, e1, e2) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     BinaryOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
   | TernaryOp (pos, op, e1, e2, e3) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     let e3, gen_nodes3 = desugar_expr ctx node_name e3 in
     TernaryOp (pos, op, e1, e2, e3), gen_nodes1 @ gen_nodes2 @ gen_nodes3
   | NArityOp (pos, op, expr_list) ->
     let expr_list, gen_nodes = List.map (desugar_expr ctx node_name) expr_list |> List.split in
     NArityOp (pos, op, expr_list), List.flatten gen_nodes
   | ConvOp (pos, op, e) -> 
     let e, gen_nodes = desugar_expr ctx node_name e in
     ConvOp (pos, op, e), gen_nodes
   | CompOp (pos, op, e1, e2) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     CompOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
   | RecordExpr (pos, ident, expr_list) ->
     let id_list, exprs_gen_nodes = 
       List.map (fun (i, e) -> (i, (desugar_expr ctx node_name) e)) expr_list |> List.split 
     in
     let expr_list, gen_nodes = List.split exprs_gen_nodes in
     RecordExpr (pos, ident, List.combine id_list expr_list), List.flatten gen_nodes
   | GroupExpr (pos, kind, expr_list) ->
     let expr_list, gen_nodes = List.map (desugar_expr ctx node_name) expr_list |> List.split in
     GroupExpr (pos, kind, expr_list), List.flatten gen_nodes
   | StructUpdate (pos, e1, idx, e2) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     StructUpdate (pos, e1, idx, e2), gen_nodes1 @ gen_nodes2
   | ArrayConstr (pos, e1, e2) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     ArrayConstr (pos, e1, e2), gen_nodes1 @ gen_nodes2
   | ArraySlice (pos, e1, (e2, e3)) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     let e3, gen_nodes3 = desugar_expr ctx node_name e3 in
     ArraySlice (pos, e1, (e2, e3)), gen_nodes1 @ gen_nodes2 @ gen_nodes3
   | ArrayIndex (pos, e1, e2) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     ArrayIndex (pos, e1, e2), gen_nodes1 @ gen_nodes2
   | ArrayConcat (pos, e1, e2) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     ArrayConcat (pos, e1, e2), gen_nodes1 @ gen_nodes2
   | Quantifier (pos, kind, idents, e) ->
     let e, gen_nodes = desugar_expr ctx node_name e in
     Quantifier (pos, kind, idents, e), gen_nodes
   | When (pos, e, clock) -> 
     let e, gen_nodes = desugar_expr ctx node_name e in
     When (pos, e, clock), gen_nodes
   | Current (pos, e) -> 
     let e, gen_nodes = desugar_expr ctx node_name e in
     Current (pos, e), gen_nodes
   | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     let expr_list1, gen_nodes3 = List.map (desugar_expr ctx node_name) expr_list1 |> List.split in
     let expr_list2, gen_nodes4 = List.map (desugar_expr ctx node_name) expr_list2 |> List.split in
     Condact (pos, e1, e2, id, expr_list1, expr_list2), gen_nodes1 @ gen_nodes2 @ 
                                                       List.flatten gen_nodes3 @ List.flatten gen_nodes4
   | Activate (pos, ident, e1, e2, expr_list) ->
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     Activate (pos, ident, e1, e2, expr_list), gen_nodes1 @ gen_nodes2
   | Merge (pos, ident, expr_list) ->
     let id_list, exprs_gen_nodes = 
       List.map (fun (i, e) -> (i, (desugar_expr ctx node_name) e)) expr_list |> List.split 
     in
     let expr_list, gen_nodes = List.split exprs_gen_nodes in
     Merge (pos, ident, List.combine id_list expr_list), List.flatten gen_nodes
   | RestartEvery (pos, ident, expr_list, e) ->
     let expr_list, gen_nodes1 = List.map (desugar_expr ctx node_name) expr_list |> List.split in
     let e, gen_nodes2 = desugar_expr ctx node_name e in
     RestartEvery (pos, ident, expr_list, e), List.flatten gen_nodes1 @ gen_nodes2
   | Pre (pos, e) -> 
     let e, gen_nodes = desugar_expr ctx node_name e in
     Pre (pos, e), gen_nodes
   | Fby (pos, e1, i, e2) -> 
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     Fby (pos, e1, i, e2), gen_nodes1 @ gen_nodes2
   | Arrow (pos, e1, e2) -> 
     let e1, gen_nodes1 = desugar_expr ctx node_name e1 in
     let e2, gen_nodes2 = desugar_expr ctx node_name e2 in
     Arrow (pos, e1, e2), gen_nodes1 @ gen_nodes2
   | Call (pos, id, expr_list) ->
     let expr_list, gen_nodes = List.map (desugar_expr ctx node_name) expr_list |> List.split in
     Call (pos, id, expr_list), List.flatten gen_nodes
   | CallParam (pos, id, types, expr_list) ->
     let expr_list, gen_nodes = List.map (desugar_expr ctx node_name) expr_list |> List.split in
     CallParam (pos, id, types, expr_list), List.flatten gen_nodes

 let desugar_contract_item ctx node_name ci = 
    match ci with 
      | A.GhostVars (pos, lhs, e) -> 
        let e, gen_nodes = desugar_expr ctx node_name e in 
        A.GhostVars (pos, lhs, e), gen_nodes
      | Assume (pos, name, b, e) ->
        let e, gen_nodes = desugar_expr ctx node_name e in 
        Assume (pos, name, b, e), gen_nodes
      | Guarantee (pos, name, b, e) -> 
        let e, gen_nodes = desugar_expr ctx node_name e in 
        Guarantee (pos, name, b, e), gen_nodes
      | GhostConst _ 
      | Mode _ 
      | ContractCall _ 
      | AssumptionVars _ -> ci, []

  let desugar_contract ctx node_name contract = 
    match contract with 
      | Some contract_items -> 
        let items, gen_nodes = (List.map (desugar_contract_item ctx node_name) contract_items) |> List.split in
        Some items, List.flatten gen_nodes
      | None -> None, []
 
 let rec desugar_node_item ctx node_name ni =
   match ni with
     | A.Body (Equation (pos, lhs, rhs)) -> 
       let rhs, gen_nodes = desugar_expr ctx node_name rhs in 
       A.Body (Equation (pos, lhs, rhs)), gen_nodes
     | AnnotProperty (pos, name, e, k) -> 
       let e, gen_nodes = desugar_expr ctx node_name e in 
       AnnotProperty(pos, name, e, k), gen_nodes
     | IfBlock (pos, cond, nis1, nis2) -> 
       let nis1, gen_nodes1 = List.map (desugar_node_item ctx node_name) nis1 |> List.split in
       let nis2, gen_nodes2 = List.map (desugar_node_item ctx node_name) nis2 |> List.split in
       let cond, gen_nodes3 = desugar_expr ctx node_name cond in
       A.IfBlock (pos, cond, nis1, nis2), List.flatten gen_nodes1 @ List.flatten gen_nodes2 @ gen_nodes3
     | FrameBlock (pos, vars, nes, nis) -> 
       let nes = List.map (fun x -> A.Body x) nes in
       let nes, gen_nodes1 = List.map (desugar_node_item ctx node_name) nes |> List.split in
       let nes = List.map (fun ne -> match ne with
         | A.Body (A.Equation _ as eq) -> eq
         | _ -> assert false
       ) nes in
       let nis, gen_nodes2 = List.map (desugar_node_item ctx node_name) nis |> List.split in
       FrameBlock(pos, vars, nes, nis), List.flatten gen_nodes1 @ List.flatten gen_nodes2
     | Body (Assert (pos, e)) ->
       let e, gen_nodes = desugar_expr ctx node_name e in 
       Body (Assert (pos, e)), gen_nodes
     | AnnotMain _ -> ni, []
     
 
 let desugar_choose_ops ctx decls = 
   let decls =
   List.fold_left (fun decls decl ->
     match decl with
      | A.NodeDecl (span, ((id, ext, params, inputs, outputs, locals, items, contract) as d)) -> 
      (
        match Chk.get_node_ctx ctx d with 
          | Ok ctx ->
            let items, gen_nodes = List.map (desugar_node_item ctx id) items |> List.split in 
            let contract, gen_nodes2 = desugar_contract ctx id contract in
            let gen_nodes = List.flatten gen_nodes in
            decls @ gen_nodes @ gen_nodes2 @ [A.NodeDecl (span, (id, ext, params, inputs, outputs, locals, items, contract))]
         (* If there is an error in context collection, it will be detected later in type checking *)
         | Error _ -> decl :: decls
      )
      | A.FuncDecl (span, ((id, ext, params, inputs, outputs, locals, items, contract) as d)) -> 
      (
        match Chk.get_node_ctx ctx d with 
          | Ok ctx -> 
            let items, gen_nodes = List.map (desugar_node_item ctx id) items |> List.split in 
            let contract, gen_nodes2 = desugar_contract ctx id contract in
            let gen_nodes = List.flatten gen_nodes in
            decls @ gen_nodes @ gen_nodes2 @ [A.FuncDecl (span, (id, ext, params, inputs, outputs, locals, items, contract))]
         (* If there is an error in context collection, it will be detected later in type checking *)
          | Error _ -> decl :: decls
      )
       | _ -> decl :: decls
   ) [] decls in 
  decls

