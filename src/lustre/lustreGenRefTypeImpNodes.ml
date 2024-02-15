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

let unwrap = 
  function 
  | Some v -> v 
  | None -> assert false

let unwrap_res = 
  function 
  | Ok v -> v 
  | Error _ -> assert false

let ref_type_to_contract: Ctx.tc_context -> A.lustre_type -> HString.t option -> A.declaration option
= fun ctx ty node_id -> match ty with 
  | RefinementType (pos, (_, id, ty), expr) as ref_type -> 
    (* Only generate contracts if realizability checking is enabled *)
    if not (List.mem `CONTRACTCK (Flags.enabled ())) then None else
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
      let ty = Chk.expand_type ctx ty |> unwrap_res in
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
    let locals = [] in 
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
    Some (NodeDecl (span, (gen_node_id, is_extern, params, inputs, outputs, locals, node_items, contract)))
  | _ -> None

let handle_inputs: Ctx.tc_context -> HString.t -> A.const_clocked_typed_decl -> A.declaration option 
= fun ctx node_id (_, _, ty, _, _) ->
  ref_type_to_contract ctx ty (Some node_id)

let handle_outputs: Ctx.tc_context -> HString.t -> A.clocked_typed_decl -> A.declaration option 
= fun ctx node_id (_, _, ty, _) ->
  ref_type_to_contract ctx ty (Some node_id)

let handle_locals: Ctx.tc_context -> HString.t -> A.node_local_decl -> A.declaration option 
= fun ctx node_id -> function 
  | A.NodeVarDecl (_, (_, _, ty, _)) 
  | A.NodeConstDecl (_, TypedConst (_, _, _, ty))
  | A.NodeConstDecl (_, FreeConst (_, _, ty)) -> ref_type_to_contract ctx ty (Some node_id)
  | A.NodeConstDecl (_, UntypedConst _) -> None

let gen_imp_nodes: Ctx.tc_context -> A.declaration list -> A.declaration list 
= fun ctx decls -> 
  let gen_decls =
    List.map (fun decl -> 
      match decl with 
      | A.TypeDecl (_, AliasType (_, _, ty))
      | A.ConstDecl (_, FreeConst (_, _, ty))
      | A.ConstDecl (_, TypedConst (_, _, _, ty)) -> [(ref_type_to_contract ctx ty None)]
      | A.TypeDecl (_, FreeType _)
      | A.ConstDecl (_, UntypedConst _) -> []
      | A.NodeDecl (_, ((id, _, _, inputs, outputs, locals, _, _) as decl))
      | A.FuncDecl (_, ((id, _, _, inputs, outputs, locals, _, _) as decl)) -> 
        let ctx = Chk.get_node_ctx ctx decl |> unwrap_res in
        List.map (handle_inputs ctx id) inputs @ List.map (handle_outputs ctx id) outputs @ List.map (handle_locals ctx id) locals
      | A.ContractNodeDecl _ 
      | A.NodeParamInst _ -> [] (*TODO*)
    ) decls |> List.flatten |> List.filter_map Fun.id
  in
  decls @ gen_decls