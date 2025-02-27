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
module R = Res

let (let*) = R.(>>=)

type error_kind = 
  | EnvRealizabilityCheckModeRefAssumption

let error_message error = match error with
  | EnvRealizabilityCheckModeRefAssumption -> "Environment realizability checks do not currently support assumptions containing mode references. To disable environment realizability checking, pass --check_realizability false"

type error = [
  | `LustreGenRefTypeImpNodesError of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreGenRefTypeImpNodesError (pos, kind))

let unwrap = function 
  | Ok x -> x 
  | Error _ -> assert false

(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let mk_fresh_id id = 
  i := !i + 1;
  let prefix = HString.concat2 (HString.mk_hstring (string_of_int !i)) (HString.mk_hstring "_") in
  HString.concat2 prefix id

let mk_fresh_ghost_var pos ty rhs =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_ghost") in
  let gids = { (GI.empty ()) with
    locals = GI.StringMap.singleton name ty; 
    (* No contract scope is given because we are currently disallowing mode references in contract 
       assumptions during environment realizability checks. *)
    equations = [([], [], A.StructDef(pos, [SingleIdent (pos, name)]), rhs, Some GI.Ghost)];
  } in 
  name, gids

let rec expr_contains_mode_ref expr = 
  let r = expr_contains_mode_ref in 
  match expr with 
  | A.ModeRef (_, _) -> true
  | Ident (_, _) 
  | Const (_, _) -> false
  | RecordProject (_, e, _) | TupleProject (_, e, _) | UnaryOp (_, _, e)
  | ConvOp (_, _, e) | Quantifier (_, _, _, e) | When (_, e, _)
  | Pre (_, e) 
    -> r e
  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) | StructUpdate (_, e1, _, e2)
  | ArrayConstr (_, e1, e2) | ArrayIndex (_, e1, e2)
  | Arrow (_, e1, e2)
    -> r e1 || r e2
  | TernaryOp (_, _, e1, e2, e3)
    -> r e1 || r e2 || r e3
  | GroupExpr (_, _, expr_list)
    -> List.fold_left (fun acc x -> acc || r x) false expr_list
  | RecordExpr (_, _, _, expr_list) | Merge (_, _, expr_list)
    -> List.fold_left (fun acc (_, e) -> acc || r e) false expr_list
  | Activate (_, _, e1, e2, expr_list) -> 
    r e1 || r e2
    || List.fold_left (fun acc x -> acc || r x) false expr_list
  | Call (_, _, _, _) | Condact (_, _, _, _, _, _) | RestartEvery (_, _, _, _) | AnyOp (_, _, _, _)
    -> false

let mk_generated_env_contract_eqs ctx base_contract = 
  let* res = R.seq (List.map (fun ci -> 
    match ci with
    | A.GhostConst _ | GhostVars _ -> R.ok (Some (ci, GI.empty ()))
    | A.Assume (pos, name, b, expr) ->
      if expr_contains_mode_ref expr then mk_error pos EnvRealizabilityCheckModeRefAssumption else
      R.ok (Some (A.Guarantee (pos, name, b, expr), GI.empty ()))
    | A.ContractCall (pos, (name, _, _), ty_args, ips, ops) ->
      if Flags.Contracts.check_environment () then ( 
        let name = name, Some A.Environment, None in
        (* Since we are flipping the inputs and outputs of the generated contract, 
          we also need to flip inputs and outputs of the call *)
        let ips' = List.map (fun id -> A.Ident (pos, id)) ops in
        let ops', gids = List.mapi (fun i expr -> match expr with 
        | A.Ident (_, id) -> id, GI.empty ()
        (* Input is not a simple identifier, so we have to generate a ghost variable 
          to store the output *)
        | expr -> 
          let called_contract_ty = Ctx.lookup_contract_ty ctx name in 
          (* Option.get should not fail because we know the check_environment flag is enabled *)
          let ghost_var_ty = match Option.get called_contract_ty with 
          | TArr (_, _, GroupType (_, tys)) -> 
            List.nth tys i  
          | TArr(_, _, ty) when i = 0 -> ty
          | _ -> assert false
          in 
          let gen_ghost_var, gids = mk_fresh_ghost_var pos ghost_var_ty expr in
          gen_ghost_var,
          gids
        ) ips |> List.split in
        R.ok (Some (
          A.ContractCall (pos, name, ty_args, ips', ops'), 
          List.fold_left GI.union ( GI.empty ()) gids
        )))
      else R.ok None
    | A.Guarantee _ | A.AssumptionVars _ | A.Mode _  -> R.ok None
  ) base_contract) in
  let contract', gids = List.filter_map (fun x -> x) res |> List.split in
  R.ok (contract', gids)

let mk_swapped_inputs_and_outputs ctx inputs outputs = 
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
  inputs2, outputs2

let contract_node_decl_to_contracts
= fun ctx ((id, _, _), params, inputs, outputs, (pos, base_contract)) -> 
  let* contract', gids = mk_generated_env_contract_eqs ctx base_contract in
  let gen_node_id = id, Some A.Environment, None in
  let inputs2, outputs2 = mk_swapped_inputs_and_outputs ctx inputs outputs in
  (* We generate a contract representing this contract's inputs/environment *)
  let environment = gen_node_id, params, inputs2, outputs2, (pos, contract') in
  let gids = List.fold_left GI.union (GI.empty ()) gids |> A.NodeNameMap.singleton gen_node_id in
  if Flags.Contracts.check_environment () 
  then 
    (* Update ctx with info about the generated contract *)
    let ctx, _ = LustreTypeChecker.tc_ctx_of_contract_node_decl pos ctx environment |> unwrap in
    R.ok ([environment], ctx, gids)
  else R.ok ([], ctx, gids)

let node_decl_to_contracts 
= fun pos ctx ((id, _, _), extern, _, params, inputs, outputs, locals, _, contract) ->
  let base_contract = match contract with | None -> [] | Some (_, contract) -> contract in 
  let* contract', gids = mk_generated_env_contract_eqs ctx base_contract in
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
  let gen_node_id = id, Some A.Environment, None in
  let gen_node_id2 = id, Some A.Contract, None in
  let inputs2, outputs2 = mk_swapped_inputs_and_outputs ctx inputs outputs in
  let gids = List.fold_left GI.union (GI.empty ()) gids |> A.NodeNameMap.singleton gen_node_id in
  (* We potentially generate two imported nodes: One for the input node's contract (w/ type info), and another 
     for the input node's inputs/environment *)
  if extern then 
    let environment = gen_node_id, extern, A.Opaque, params, inputs2, outputs2, [], node_items, contract' in
    if Flags.Contracts.check_environment () then 
      (* Update ctx with info about the generated node *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx environment |> unwrap in
      R.ok ([environment], ctx, gids)
    else R.ok([], ctx, gids)
  else
    let environment = gen_node_id, extern', A.Opaque, params, inputs2, outputs2, [], node_items, contract' in
    let contract = (gen_node_id2, extern', A.Opaque, params, inputs, locals_as_outputs @ outputs, [], node_items, contract) in
    if Flags.Contracts.check_environment () then 
      (* Update ctx with info about the generated nodes *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx environment |> unwrap in
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx contract |> unwrap in
      R.ok ([environment; contract], ctx, gids)
    else 
      (* Update ctx with info about the generated node *)
      let ctx, _ = LustreTypeChecker.tc_ctx_of_node_decl pos ctx contract |> unwrap in
      R.ok ([contract], ctx, gids)

(* NOTE: If "ty" is a refinement type that includes a constant with
   its own refinement type, e.g., T = { x: int | x > C }, where
   C has a refinement type, there is no need to capture C's refinement type as
   an assumption. This is because C's constraints are handled separately
   (see commit 6ac7eee).
*)
let type_to_contract: Lib.position -> HString.t -> A.lustre_type -> HString.t list -> A.declaration option
= fun pos id ty ps -> 
  let span = { A.start_pos = pos; end_pos = pos } in
  let gen_node_id = (id, Some A.Type, None) in
  (* To prevent slicing, we mark generated imported nodes as main nodes *)
  let node_items = [A.AnnotMain(pos, true)] in 
  (* Avoid name clashes (e.g., with enum constants) *)
  let id = mk_fresh_id id in
  Some (NodeDecl (span, (gen_node_id, true, A.Opaque, ps, [], [(pos, id, ty, A.ClockTrue)], [], node_items, None)))

let gen_imp_nodes: Ctx.tc_context -> A.declaration list -> (A.declaration list * Ctx.tc_context * GI.t A.NodeNameMap.t, [> error]) result
= fun ctx decls -> 
  let* decls, ctx, gids = R.seq_chain (fun (acc_decls, acc_ctx, acc_gids) decl -> 
    match decl with 
    | A.ConstDecl (_, FreeConst _)
    | A.ConstDecl (_, TypedConst _) -> R.ok (acc_decls, acc_ctx, acc_gids)
    | A.TypeDecl (_, AliasType (p, id, ps, ty)) -> 
      (match type_to_contract p id ty ps with 
      | Some decl1 -> R.ok (decl1 :: acc_decls, acc_ctx, acc_gids)
      | None -> R.ok (acc_decls, acc_ctx, acc_gids))
    | A.TypeDecl (_, FreeType _)
    | A.ConstDecl (_, UntypedConst _) -> R.ok (acc_decls, acc_ctx, acc_gids)
    | A.NodeDecl (span, ((p, e, opac, ps, ips, ops, locs, _, c) as node_decl)) ->
      (* Add main annotations to imported nodes *)
      let node_decl = 
        if e then p, e, opac, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c
        else node_decl 
      in
      let* decls, acc_ctx, gids = node_decl_to_contracts span.start_pos acc_ctx node_decl in
      let decls = List.map (fun decl -> A.NodeDecl (span, decl)) decls in
      R.ok (
        A.NodeDecl(span, node_decl) :: decls @ acc_decls, acc_ctx, 
        A.NodeNameMap.merge GI.union_keys2 gids acc_gids
      )
    | A.FuncDecl (span, ((p, e, opac, ps, ips, ops, locs, _, c) as func_decl)) ->
      (* Add main annotations to imported functions *)
      let func_decl = 
        if e then p, e, opac, ps, ips, ops, locs, [A.AnnotMain (span.start_pos, true)], c
        else func_decl 
      in
      let* decls, acc_ctx, gids = node_decl_to_contracts span.start_pos acc_ctx func_decl in
      let decls = List.map (fun decl -> A.FuncDecl (span, decl)) decls in
      R.ok (
        A.FuncDecl(span, func_decl) :: decls @ acc_decls, acc_ctx, 
        A.NodeNameMap.merge GI.union_keys2 gids acc_gids
      )
    | A.ContractNodeDecl (span, contract_node_decl) -> 
      let* decls, acc_ctx, gids = contract_node_decl_to_contracts acc_ctx contract_node_decl in 
      let decls = List.map (fun decl -> A.ContractNodeDecl (span, decl)) decls in
      R.ok (
        A.ContractNodeDecl (span, contract_node_decl) :: decls @ acc_decls, acc_ctx, 
        A.NodeNameMap.merge GI.union_keys2 gids acc_gids
      )
    | A.NodeParamInst _ -> R.ok (decl :: acc_decls, acc_ctx, acc_gids)
  ) ([], ctx, A.NodeNameMap.empty) decls 
  in 
  R.ok (List.rev decls, ctx, gids)