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

let unwrap = 
  function 
  | Some v -> v 
  | None -> assert false

let unwrap_res = 
  function 
  | Ok v -> v 
  | Error _ -> assert false

let ref_type_to_contract: A.lustre_type -> Ctx.tc_context -> HString.t -> HString.t -> A.declaration option
= fun ty ctx ty_name node_id -> match ty with 
  | RefinementType (pos, (_, id, ty), expr) -> 
    let span = { A.start_pos = Lib.dummy_pos; end_pos = Lib.dummy_pos } in
    let gen_node_id = HString.concat2 ty_name (HString.mk_hstring "_node") in
    let is_extern = true in
    let params = [] in 
    let vars = AH.vars_without_node_call_ids expr in
    let inputs = SI.diff vars (SI.singleton id) |> SI.elements in
    let inputs = List.filter_map (fun id -> 
      let ty = Ctx.lookup_ty ctx id |> unwrap in
      let ty = Chk.expand_type ctx ty |> unwrap_res in
      let is_const = Ctx.member_val ctx id in
      let call_params = Ctx.lookup_node_param_ids ctx node_id |> unwrap in
      let is_global_const = is_const && not (List.mem id call_params) in
      if is_global_const 
      then None 
      else Some (pos, id, ty, A.ClockTrue, is_const)
    ) inputs in
    let outputs = [(pos, id, ty, A.ClockTrue)] in
    let locals = [] in 
    let node_items = [] in 
    (* Add assumption for each variable with a refinement type in 'expr' *)
    let assumptions = List.filter_map (fun (_, id, _, _, _) -> 
      let ty = Ctx.lookup_ty ctx id |> unwrap in 
      match ty with 
        | A.RefinementType (_, (_, id2, _), expr) -> 
          let expr =  (AH.substitute_naive id2 (Ident(pos, id)) expr) in
          Some (A.Assume (pos, None, true, expr)) (*!! Same issue as below *)
        | _ -> None 
    ) inputs in 
    (* Add guarantee for 'expr' *) 
    (*!! Soft vs weak guarantee (3rd element)? *)
    let guarantee = A.Guarantee (pos, None, true, expr) in
    let contract = Some (guarantee :: assumptions) in
    Some (NodeDecl (span, (gen_node_id, is_extern, params, inputs, outputs, locals, node_items, contract)))
  | _ -> None