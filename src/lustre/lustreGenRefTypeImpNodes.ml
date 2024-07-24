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
let poly_gen_node_tag = ".poly"

let unwrap = function 
  | Ok x -> x 
  | Error _ -> assert false

let node_decl_to_contracts 
= fun pos ctx (id, extern, params, inputs, outputs, locals, _, contract) ->
  let base_contract = match contract with | None -> [] | Some (_, contract) -> contract in 
  let contract' = List.filter_map (fun ci -> 
    match ci with 
    | A.Assume (pos, name, b, expr) -> Some (A.Guarantee (pos, name, b, expr))
    | _ -> None
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
  (* We generate two imported nodes: One for the input node's contract (w/ type info), and another 
     for the input node's inputs/environment *)
  if extern then 
    let environment = gen_node_id, extern, params, inputs2, outputs2, [], node_items, contract' in
    if Flags.Contracts.check_environment () then [environment] else []
  else
    let environment = gen_node_id, extern', params, inputs2, outputs2, [], node_items, contract' in 
    let contract = (gen_node_id2, extern', params, inputs, locals_as_outputs @ outputs, [], node_items, contract) in
    if Flags.Contracts.check_environment () then [environment; contract] else [contract]

(* NOTE: Currently, we do not allow global constants to have refinement types. 
   If we decide to support this in the future, then we need to add necessary refinement type information 
   to the generated imported node. For example, if "ty" is a refinement type 
   T = { x: int | x > C }, and C has a refinement type, then C's refinement type needs to be 
   captured as an assumption in the output imported node. *)
let type_to_contract: Lib.position ->HString.t -> A.lustre_type -> A.declaration option
= fun pos id ty -> 
  let span = { A.start_pos = pos; end_pos = pos } in
  let gen_node_id = HString.concat2 (HString.mk_hstring type_tag) id in
  (* To prevent slicing, we mark generated imported nodes as main nodes *)
  let node_items = [A.AnnotMain(pos, true)] in 
  Some (NodeDecl (span, (gen_node_id, true, [], [], [(pos, id, ty, A.ClockTrue)], [], node_items, None)))

let gen_imp_nodes:  Ctx.tc_context -> A.declaration list -> A.declaration list 
= fun ctx decls -> 
  List.fold_left (fun acc decl -> 
    match decl with 
    | A.ConstDecl (_, FreeConst _)
    | A.ConstDecl (_, TypedConst _) -> decl :: acc
    (*!! Make sure type decl params desugared by now *)
    | A.TypeDecl (_, AliasType (p, id, _, ty)) -> 
      (match type_to_contract p id ty with 
      | Some decl1 -> decl :: decl1 :: acc
      | None -> decl :: acc)
    | A.TypeDecl (_, FreeType _)
    | A.ConstDecl (_, UntypedConst _) -> decl :: acc
    | A.NodeDecl (span, ((p, e, ps, ips, ops, locs, _, c) as node_decl)) -> 
      (* Add main annotations to imported nodes *)
      let node_decl = 
        if e then p, e, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c 
        else node_decl 
      in
      let decls = node_decl_to_contracts span.start_pos ctx node_decl in
      let decls = List.map (fun decl -> A.NodeDecl (span, decl)) decls in
      A.NodeDecl(span, node_decl) :: decls @ acc
    | A.FuncDecl (span, ((p, e, ps, ips, ops, locs, _, c) as func_decl)) -> 
      (* Add main annotations to imported functions *)
      let func_decl = 
        if e then p, e, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c 
        else func_decl 
      in
      let decls = node_decl_to_contracts span.start_pos ctx func_decl in
      let decls = List.map (fun decl -> A.FuncDecl (span, decl)) decls in
      A.FuncDecl(span, func_decl) :: decls @ acc
    | A.ContractNodeDecl _ 
    | A.NodeParamInst _ -> decl :: acc
  ) [] decls |> List.rev