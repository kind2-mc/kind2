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
module Chk = LustreTypeChecker
module Ctx = TypeCheckerContext

let inputs_tag = ".inputs_"
let contract_tag = ".contract_"
let type_tag = ".type_"
let poly_gen_node_tag = ".poly_"

let unwrap = function 
  | Ok x -> x 
  | Error _ -> assert false

let contract_node_decl_to_contracts
= fun ctx (id, params, inputs, outputs, (pos, base_contract)) -> 
  let contract' = List.filter_map (fun ci -> 
    match ci with
    | A.GhostConst _ | GhostVars _ -> Some ci
    | A.Assume (pos, name, b, expr) -> Some (A.Guarantee (pos, name, b, expr))
    | A.ContractCall (pos, name, ty_args, ips, ops) -> 
      let name = HString.concat2 (HString.mk_hstring ".inputs_") name in
      Some (A.ContractCall (pos, name, ty_args, ips, ops))
    | A.Guarantee _ | A.AssumptionVars _ | A.Mode _  -> None
  ) base_contract in
  let gen_node_id = HString.concat2 (HString.mk_hstring inputs_tag) id in
  let inputs2, outputs2 = 
    List.map (fun (p, id, ty, cl) -> (p, id, ty, cl, false)) outputs, 
    List.map (fun (p, id, ty, cl, _) -> (p, id, ty, cl)) inputs 
  in
  (* Since we are omitting assumptions from environment realizability checks,
     we need to chase base types for environment inputs *)
  let inputs2 = List.map (fun (p, id, ty, cl, b) -> 
    let ty = Chk.expand_type_syn_reftype_history_subrange ctx ty |> unwrap in 
    (p, id, ty, cl, b)
  ) inputs2 in
  (* We generate a contract representing this contract's inputs/environment *)
  let environment = gen_node_id, params, inputs2, outputs2, (pos, contract') in
  if Flags.Contracts.check_environment () 
  then 
    (* Update ctx with info about the generated contract *)
    let ctx, _ = LustreTypeChecker.tc_ctx_of_contract_node_decl pos ctx environment |> unwrap in
    [environment], ctx 
  else [], ctx

let node_decl_to_contracts 
= fun pos ctx (id, extern, _, params, inputs, outputs, locals, _, contract) ->
  let base_contract = match contract with | None -> [] | Some (_, contract) -> contract in 
  let contract' = List.filter_map (fun ci -> 
    match ci with
    | A.GhostConst _ | GhostVars _ -> Some ci
    | A.Assume (pos, name, b, expr) -> Some (A.Guarantee (pos, name, b, expr))
    | A.ContractCall (pos, name, ty_args, ips, ops) -> 
      let name = HString.concat2 (HString.mk_hstring ".inputs_") name in
      Some (A.ContractCall (pos, name, ty_args, ips, ops))
    | A.Guarantee _ | A.AssumptionVars _ | A.Mode _  -> None
  ) base_contract in
  let locals_as_outputs = List.map (fun local_decl -> match local_decl with 
    | A.NodeConstDecl (pos, FreeConst (_, id, ty)) 
    | A.NodeConstDecl (pos, TypedConst (_, id, _, ty)) ->  Some (pos, id, ty, A.ClockTrue)
    | A.NodeVarDecl (pos, (_, id, ty, cl)) -> 
      Some (pos, id, ty, cl)
    | _ -> None
  ) locals |> List.filter_map Fun.id in 
  let contract' = if contract' = [] then None else Some (pos, contract') in
  let extern' = true in 
  (* To prevent slicing, we mark generated imported nodes as main nodes *)
  let node_items = [A.AnnotMain(pos, true)] in 
  let gen_node_id = HString.concat2 (HString.mk_hstring inputs_tag) id in
  let gen_node_id2 = HString.concat2 (HString.mk_hstring contract_tag) id in
  let inputs2, outputs2 = 
    List.map (fun (p, id, ty, cl) -> (p, id, ty, cl, false)) outputs, 
    List.map (fun (p, id, ty, cl, _) -> (p, id, ty, cl)) inputs 
  in
  (* Since we are omitting assumptions from environment realizability checks,
     we need to chase base types for environment inputs *)
  let inputs2 = List.map (fun (p, id, ty, cl, b) -> 
    let ty = Chk.expand_type_syn_reftype_history_subrange ctx ty |> unwrap in 
    (p, id, ty, cl, b)
  ) inputs2 in
  (* We potentially generate two imported nodes: One for the input node's contract (w/ type info), and another 
     for the input node's inputs/environment *)
  if extern then 
    let environment = gen_node_id, extern, A.Opaque, params, inputs2, outputs2, [], node_items, contract' in
    if Flags.Contracts.check_environment () then 
      (* Update ctx with info about the generated node *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx environment |> unwrap in
      [environment], ctx
    else [], ctx
  else
    let environment = gen_node_id, extern', A.Opaque, params, inputs2, outputs2, [], node_items, contract' in
    let contract = (gen_node_id2, extern', A.Opaque, params, inputs, locals_as_outputs @ outputs, [], node_items, contract) in
    if Flags.Contracts.check_environment () then 
      (* Update ctx with info about the generated nodes *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx environment |> unwrap in
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx contract |> unwrap in
      [environment; contract], ctx 
    else 
      (* Update ctx with info about the generated node *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx contract |> unwrap in
      [contract], ctx

(* NOTE: Currently, we do not allow global constants to have refinement types. 
   If we decide to support this in the future, then we need to add necessary refinement type information 
   to the generated imported node. For example, if "ty" is a refinement type 
   T = { x: int | x > C }, and C has a refinement type, then C's refinement type needs to be 
   captured as an assumption in the output imported node. *)
let type_to_contract: Lib.position -> HString.t -> A.lustre_type -> HString.t list -> A.declaration option
= fun pos id ty ps -> 
  let span = { A.start_pos = pos; end_pos = pos } in
  let gen_node_id = HString.concat2 (HString.mk_hstring type_tag) id in
  (* To prevent slicing, we mark generated imported nodes as main nodes *)
  let node_items = [A.AnnotMain(pos, true)] in 
  Some (NodeDecl (span, (gen_node_id, true, A.Opaque, ps, [], [(pos, id, ty, A.ClockTrue)], [], node_items, None)))

let gen_imp_nodes: Ctx.tc_context -> A.declaration list -> A.declaration list * Ctx.tc_context 
= fun ctx decls -> 
  let decls, ctx = List.fold_left (fun (acc_decls, acc_ctx) decl -> 
    match decl with 
    | A.ConstDecl (_, FreeConst _)
    | A.ConstDecl (_, TypedConst _) -> acc_decls, acc_ctx
    | A.TypeDecl (_, AliasType (p, id, ps, ty)) -> 
      (match type_to_contract p id ty ps with 
      | Some decl1 -> decl1 :: acc_decls, acc_ctx
      | None -> acc_decls, acc_ctx)
    | A.TypeDecl (_, FreeType _)
    | A.ConstDecl (_, UntypedConst _) -> acc_decls, acc_ctx
    | A.NodeDecl (span, ((p, e, opac, ps, ips, ops, locs, _, c) as node_decl)) ->
      (* Add main annotations to imported nodes *)
      let node_decl = 
        if e then p, e, opac, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c
        else node_decl 
      in
      let decls, acc_ctx = node_decl_to_contracts span.start_pos acc_ctx node_decl in
      let decls = List.map (fun decl -> A.NodeDecl (span, decl)) decls in
      A.NodeDecl(span, node_decl) :: decls @ acc_decls, acc_ctx
    | A.FuncDecl (span, ((p, e, opac, ps, ips, ops, locs, _, c) as func_decl)) ->
      (* Add main annotations to imported functions *)
      let func_decl = 
        if e then p, e, opac, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c
        else func_decl 
      in
      let decls, acc_ctx = node_decl_to_contracts span.start_pos acc_ctx func_decl in
      let decls = List.map (fun decl -> A.FuncDecl (span, decl)) decls in
      A.FuncDecl(span, func_decl) :: decls @ acc_decls, acc_ctx
    | A.ContractNodeDecl (span, contract_node_decl) -> 
      let decls, acc_ctx = contract_node_decl_to_contracts acc_ctx contract_node_decl in 
      let decls = List.map (fun decl -> A.ContractNodeDecl (span, decl)) decls in
      A.ContractNodeDecl (span, contract_node_decl) :: decls @ acc_decls, acc_ctx
    | A.NodeParamInst _ -> decl :: acc_decls, acc_ctx
  ) ([], ctx) decls 
  in 
  List.rev decls, ctx