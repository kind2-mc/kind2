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

(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let inputs_tag = ".inputs_"
let contract_tag = ".contract_"
let type_tag = ".type_"

let node_decl_to_contracts
= fun (id, _, params, inputs, outputs, locals, _, contract) ->
  let base_contract = match contract with | None -> [] | Some contract -> contract in 
  let contract = List.filter_map (fun ci -> 
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
  let contract = if contract = [] then None else Some contract in
  let span = { A.start_pos = Lib.dummy_pos; end_pos = Lib.dummy_pos } in
  let extern = true in 
  (* To prevent slicing, we mark generated imported nodes as main nodes *)
  let node_items = [A.AnnotMain(Lib.dummy_pos, true)] in 
  let gen_node_id = HString.concat2 (HString.mk_hstring inputs_tag) id in
  let gen_node_id2 = HString.concat2 (HString.mk_hstring contract_tag) id in
  let inputs2, outputs2 = 
    List.map (fun (p, id, ty, cl) -> (p, id, ty, cl, false)) outputs, 
    List.map (fun (p, id, ty, cl, _) -> (p, id, ty, cl)) inputs 
  in
  (* We generate two imported nodes: One for the input node's contract (w/ type info), and another 
     for the input node's inputs/environment *)
  Some (A.NodeDecl (span, (gen_node_id, extern, params, inputs2, outputs2, [], node_items, contract)),
        A.NodeDecl (span, (gen_node_id2, extern, params, inputs, locals_as_outputs @ outputs, [], node_items, Some base_contract)))

(* NOTE: Currently, we do not allow global constants to have refinement types. 
   If we decide to support this in the future, then we need to add necessary refinement type information 
   to the generated imported node. For example, if "ty" is a refinement type 
   T = { x: int | x > C }, and C has a refinement type, then C's refinement type needs to be 
   captured as an assumption in the output imported node. *)
let type_to_contract: HString.t -> A.lustre_type -> A.declaration
= fun id ty -> 
  let span = { A.start_pos = Lib.dummy_pos; end_pos = Lib.dummy_pos } in
  let pos = Lib.dummy_pos in 
  let gen_node_id = HString.concat2 (HString.mk_hstring type_tag) id in
  (* To prevent slicing, we mark generated imported nodes as main nodes *)
  let node_items = [A.AnnotMain(pos, true)] in 
  NodeDecl (span, (gen_node_id, true, [], [], [(pos, id, ty, A.ClockTrue)], [], node_items, None))

let gen_imp_nodes: A.declaration list -> A.declaration list 
= fun decls -> 
  List.fold_left (fun acc decl -> 
    match decl with 
    | A.ConstDecl (_, FreeConst _)
    | A.ConstDecl (_, TypedConst _) -> acc
    | A.TypeDecl (_, AliasType (_, id, ty)) -> type_to_contract id ty :: acc
    | A.TypeDecl (_, FreeType _)
    | A.ConstDecl (_, UntypedConst _) -> decl :: acc
    | A.NodeDecl (span, ((id, extern, params, inputs, outputs, locals, node_items, contract) as decl2)) -> 
      let decl = 
        A.NodeDecl(span, (id, extern, params, inputs, outputs, locals, node_items, contract)) 
      in
      (match node_decl_to_contracts decl2 with 
      | None -> decl :: acc
      | Some (decl2, decl3) -> decl :: decl2 :: decl3 :: acc)
    | A.FuncDecl (span, ((id, extern, params, inputs, outputs, locals, node_items, contract) as decl2)) -> 
      let decl = 
        A.FuncDecl(span, (id, extern, params, inputs, outputs, locals, node_items, contract)) 
      in
      (match node_decl_to_contracts decl2 with 
      | None -> decl :: acc
      | Some (decl2, decl3) -> decl :: decl2 :: decl3 :: acc)
    | A.ContractNodeDecl _ 
    | A.NodeParamInst _ -> decl :: acc
  ) [] decls |> List.rev