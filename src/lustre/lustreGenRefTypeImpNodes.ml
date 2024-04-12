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
module AH = LustreAstHelpers
module Chk = LustreTypeChecker
module Ctx = TypeCheckerContext
module SI = A.SI

(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let inputs_tag = ".inputs_"
let contract_tag = ".contract_"

let unwrap = 
  function 
  | Some v -> v 
  | None -> assert false

let unwrap_res = 
  function 
  | Ok v -> v 
  | Error _ -> assert false

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

let ref_type_to_contract: Ctx.tc_context -> A.lustre_type -> HString.t option -> A.declaration option
= fun ctx ty node_id -> match ty with 
  | RefinementType (pos, (_, id, ty), expr) as ref_type -> 
    let span = { A.start_pos = Lib.dummy_pos; end_pos = Lib.dummy_pos } in
    let ty_str = Lib.string_of_t A.pp_print_lustre_type ref_type |> HString.mk_hstring in
    let gen_node_id = HString.concat2 (HString.mk_hstring (string_of_int !i)) 
                                      ty_str in
    i := !i + 1;
    let is_extern = true in
    let params = [] in 
    let vars = AH.vars_without_node_call_ids expr in
    let inputs = SI.diff vars (SI.singleton id) |> SI.elements in
    let inputs = List.filter_map (fun id -> 
      let ty = Ctx.lookup_ty ctx id |> unwrap in
      let ty = Chk.expand_type_syn_reftype_history ctx ty |> unwrap_res in
      let is_const = Ctx.member_val ctx id in
      let call_params = (match node_id with 
      | Some node_id -> Ctx.lookup_node_param_ids ctx node_id |> unwrap 
      | None -> []
      ) in
      let is_global_const = is_const && not (List.mem id call_params) in
      if is_global_const 
      then None 
      else Some (pos, id, ty, A.ClockTrue, is_const)
    ) inputs in
    let outputs = [(pos, id, ty, A.ClockTrue)] in 
    (* To prevent slicing, we mark generated imported nodes as main nodes *)
    let node_items = [A.AnnotMain(pos, true)] in 
    (* Add assumption for each variable with a refinement type in 'expr' *)
    let assumptions = List.filter_map (fun (_, id, _, _, _) -> 
      let ty = Ctx.lookup_ty ctx id |> unwrap in 
      match ty with 
        | A.RefinementType (_, (_, id2, _), expr) -> 
          let expr =  (AH.substitute_naive id2 (Ident(pos, id)) expr) in
          Some (A.Assume (pos, None, false, expr))
        | _ -> None 
    ) inputs in 
    (* Add guarantee for 'expr' *) 
    let guarantee = A.Guarantee (pos, None, false, expr) in
    let contract = Some (guarantee :: assumptions) in
    Some (NodeDecl (span, (gen_node_id, is_extern, params, inputs, outputs, [], node_items, contract)))
  | _ -> None

let gen_imp_nodes: Ctx.tc_context -> A.declaration list -> A.declaration list 
= fun ctx decls -> 
  List.fold_left (fun acc decl -> 
    match decl with 
    | A.TypeDecl (_, AliasType (_, _, ty))
    | A.ConstDecl (_, FreeConst (_, _, ty))
    | A.ConstDecl (_, TypedConst (_, _, _, ty)) -> 
      (match (ref_type_to_contract ctx ty None) with  
      | None -> decl :: acc
      | Some decl2 -> decl :: decl2 :: acc)
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