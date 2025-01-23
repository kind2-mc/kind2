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
module GI = GeneratedIdentifiers

let inputs_tag = ".inputs_"
let contract_tag = ".contract_"
let type_tag = ".type_"
let poly_gen_node_tag = ".poly_"

let unwrap = function 
  | Ok x -> x 
  | Error _ -> assert false

(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let mk_fresh_ghost_var ty rhs =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_ghost") in
  let gids = { (GI.empty ()) with
    gen_ghost_vars = [name, ty, rhs]; 
  } in 
  name, gids
  
let contract_node_decl_to_contracts
= fun ctx (id, params, inputs, outputs, (pos, base_contract)) -> 
  let contract', gids = List.filter_map (fun ci -> 
    match ci with
    | A.GhostConst _ | GhostVars _ -> Some ([ci], GI.empty ())
    | A.Assume (pos, name, b, expr) -> Some ([A.Guarantee (pos, name, b, expr)], GI.empty ())
    | A.ContractCall (pos, name, ty_args, ips, ops) -> 
      let name = HString.concat2 (HString.mk_hstring ".inputs_") name in
      (* Since we are flipping the inputs and outputs of the generated contract, 
         we also need to flip inputs and outputs of the call *)
      let ips' = List.map (fun id -> A.Ident (pos, id)) ops in
      let ops', gen_ghost_variables, gids = List.mapi (fun i expr -> match expr with 
      | A.Ident (_, id) -> id, [], GI.empty ()
      (* Input is not a simple identifier, so we have to generate a ghost variable 
         to store the output *)
      | expr -> 
        let called_contract_ty = Ctx.lookup_contract_ty ctx name in 
        let ghost_var_ty = match Option.get called_contract_ty with 
        | TArr (_, _, GroupType (_, tys)) -> 
          List.nth tys i  
        | TArr(_, _, ty) when i = 1 -> ty
        | _ -> assert false
        in 
        let gen_ghost_var, gids = mk_fresh_ghost_var ghost_var_ty expr in
        gen_ghost_var,
        [A.GhostVars (pos, (GhostVarDec (pos, [(pos, gen_ghost_var, ghost_var_ty)])), expr)],
        gids
      ) ips |> Lib.split3 in
      Some (
        List.flatten gen_ghost_variables @ [A.ContractCall (pos, name, ty_args, ips', ops')], 
        List.fold_left GI.union ( GI.empty ()) gids
      )
    | A.Guarantee _ | A.AssumptionVars _ | A.Mode _  -> None
  ) base_contract |> List.split in
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
  let contract' = List.flatten contract' in
  (* We generate a contract representing this contract's inputs/environment *)
  let environment = gen_node_id, params, inputs2, outputs2, (pos, contract') in
  let gids = List.fold_left GI.union (GI.empty ()) gids |> GI.StringMap.singleton gen_node_id in
  if Flags.Contracts.check_environment () 
  then 
    (* Update ctx with info about the generated contract *)
    let ctx, _ = LustreTypeChecker.tc_ctx_of_contract_node_decl pos ctx environment |> unwrap in
    [environment], ctx, gids 
  else [], ctx, gids

let node_decl_to_contracts 
= fun pos ctx (id, extern, _, params, inputs, outputs, locals, _, contract) ->
  let base_contract = match contract with | None -> [] | Some (_, contract) -> contract in 
  let contract', gids = List.filter_map (fun ci -> 
    match ci with
    | A.GhostConst _ | GhostVars _ -> Some ([ci], GI.empty ())
    | A.Assume (pos, name, b, expr) -> Some ([A.Guarantee (pos, name, b, expr)], GI.empty ())
    | A.ContractCall (pos, name, ty_args, ips, ops) -> 
      let name = HString.concat2 (HString.mk_hstring ".inputs_") name in
      (* Since we are flipping the inputs and outputs of the generated contract, 
         we also need to flip inputs and outputs of the call *)
      let ips' = List.map (fun id -> A.Ident (pos, id)) ops in
      let ops', gen_ghost_variables, gids = List.mapi (fun i expr -> match expr with 
      | A.Ident (_, id) -> id, [], GI.empty ()
      (* Input is not a simple identifier, so we have to generate a ghost variable 
         to store the output *)
      | expr -> 
        let called_contract_ty = Ctx.lookup_contract_ty ctx name in 
        let ghost_var_ty = match Option.get called_contract_ty with 
        | TArr (_, _, GroupType (_, tys)) -> 
          List.nth tys i  
        | TArr(_, _, ty) when i = 1 -> ty
        | _ -> assert false
        in 
        let gen_ghost_var, gids = mk_fresh_ghost_var ghost_var_ty expr in
        gen_ghost_var,
        (* [A.GhostVars (pos, (GhostVarDec (pos, [(pos, gen_ghost_var, ghost_var_ty)])), expr)], *)
        [],
        gids
      ) ips |> Lib.split3 in
      Some (
        List.flatten gen_ghost_variables @ [A.ContractCall (pos, name, ty_args, ips', ops')], 
        List.fold_left GI.union ( GI.empty ()) gids
      )
    | A.Guarantee _ | A.AssumptionVars _ | A.Mode _  -> None
  ) base_contract |> List.split in
  let locals_as_outputs = List.map (fun local_decl -> match local_decl with 
    | A.NodeConstDecl (pos, FreeConst (_, id, ty)) 
    | A.NodeConstDecl (pos, TypedConst (_, id, _, ty)) ->  Some (pos, id, ty, A.ClockTrue)
    | A.NodeVarDecl (pos, (_, id, ty, cl)) -> 
      Some (pos, id, ty, cl)
    | _ -> None
  ) locals |> List.filter_map Fun.id in 
  let contract' = List.flatten contract' in 
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
  let gids = List.fold_left GI.union (GI.empty ()) gids |> GI.StringMap.singleton gen_node_id in
  (* We potentially generate two imported nodes: One for the input node's contract (w/ type info), and another 
     for the input node's inputs/environment *)
  if extern then 
    let environment = gen_node_id, extern, A.Opaque, params, inputs2, outputs2, [], node_items, contract' in
    if Flags.Contracts.check_environment () then 
      (* Update ctx with info about the generated node *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx environment |> unwrap in
      [environment], ctx, gids
    else [], ctx, gids
  else
    let environment = gen_node_id, extern', A.Opaque, params, inputs2, outputs2, [], node_items, contract' in
    let contract = (gen_node_id2, extern', A.Opaque, params, inputs, locals_as_outputs @ outputs, [], node_items, contract) in
    if Flags.Contracts.check_environment () then 
      (* Update ctx with info about the generated nodes *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx environment |> unwrap in
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx contract |> unwrap in
      [environment; contract], ctx, gids 
    else 
      (* Update ctx with info about the generated node *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx contract |> unwrap in
      [contract], ctx, gids

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

let gen_imp_nodes: Ctx.tc_context -> A.declaration list -> A.declaration list * Ctx.tc_context * GI.t HString.HStringMap.t
= fun ctx decls -> 
  let decls, ctx, gids = List.fold_left (fun (acc_decls, acc_ctx, acc_gids) decl -> 
    match decl with 
    | A.ConstDecl (_, FreeConst _)
    | A.ConstDecl (_, TypedConst _) -> acc_decls, acc_ctx, acc_gids
    | A.TypeDecl (_, AliasType (p, id, ps, ty)) -> 
      (match type_to_contract p id ty ps with 
      | Some decl1 -> decl1 :: acc_decls, acc_ctx, acc_gids
      | None -> acc_decls, acc_ctx, acc_gids)
    | A.TypeDecl (_, FreeType _)
    | A.ConstDecl (_, UntypedConst _) -> acc_decls, acc_ctx, acc_gids
    | A.NodeDecl (span, ((p, e, opac, ps, ips, ops, locs, _, c) as node_decl)) ->
      (* Add main annotations to imported nodes *)
      let node_decl = 
        if e then p, e, opac, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c
        else node_decl 
      in
      let decls, acc_ctx, gids = node_decl_to_contracts span.start_pos acc_ctx node_decl in
      let decls = List.map (fun decl -> A.NodeDecl (span, decl)) decls in
      A.NodeDecl(span, node_decl) :: decls @ acc_decls, acc_ctx, 
      GI.StringMap.merge GI.union_keys2 gids acc_gids
    | A.FuncDecl (span, ((p, e, opac, ps, ips, ops, locs, _, c) as func_decl)) ->
      (* Add main annotations to imported functions *)
      let func_decl = 
        if e then p, e, opac, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c
        else func_decl 
      in
      let decls, acc_ctx, gids = node_decl_to_contracts span.start_pos acc_ctx func_decl in
      let decls = List.map (fun decl -> A.FuncDecl (span, decl)) decls in
      A.FuncDecl(span, func_decl) :: decls @ acc_decls, acc_ctx, 
      GI.StringMap.merge GI.union_keys2 gids acc_gids
    | A.ContractNodeDecl (span, contract_node_decl) -> 
      let decls, acc_ctx, gids = contract_node_decl_to_contracts acc_ctx contract_node_decl in 
      let decls = List.map (fun decl -> A.ContractNodeDecl (span, decl)) decls in
      A.ContractNodeDecl (span, contract_node_decl) :: decls @ acc_decls, acc_ctx, 
      GI.StringMap.merge GI.union_keys2 gids acc_gids
    | A.NodeParamInst _ -> decl :: acc_decls, acc_ctx, acc_gids
  ) ([], ctx, GI.StringMap.empty) decls 
  in 
  List.rev decls, ctx, gids