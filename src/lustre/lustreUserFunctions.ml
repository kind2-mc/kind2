(* This file is part of the Kind 2 model checker.

   Copyright (c) 2024 by the Board of Trustees of the University of Iowa

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
module NI = NodeId
module AH = LustreAstHelpers
module Ctx = TypeCheckerContext

let valid_outputs ctx = function
  | [(_, _, ty, _)] -> ( (* single output variable *)
    not (Ctx.type_contains_array ctx ty)
  )
  | _ -> false

let valid_locals ctx locals =
  locals |> List.for_all (function
  | A.NodeConstDecl (_, TypedConst (_,_,_,ty)) ->
    not (Ctx.type_contains_array ctx ty)
  | A.NodeConstDecl _ -> true
  | NodeVarDecl (_, (_, _, ty, _)) ->
    not (Ctx.type_contains_array ctx ty)
  )

let valid_items set items =
  items |> List.for_all (function
    | A.Body (Equation (_, StructDef (_, [A.SingleIdent _]), rhs)) ->
      NI.Set.subset (AH.calls_of_expr rhs) set
    | AnnotProperty _ -> true
    | A.Body (Equation (_, _, _))
    | Body (Assert _)
    | AnnotMain _ -> false
    | Auto _ -> true (* no-op, removed earlier in pipeline *)
    | FrameBlock _
    | IfBlock _
    | WhenBlock _ -> assert false (* desugared earlier in pipeline *)
  )

let is_output_defined outputs items =
  let output_id =
    match outputs with
    | [(_, id, _, _)] -> id
    | _ -> assert false
  in
  items |> List.exists (function
    | A.Body (Equation (_, StructDef (_, [A.SingleIdent (_, id)]), _)) ->
      HString.equal id output_id
    | _ -> false
  )

let have_ref_type ctx outputs =
  outputs |> List.exists (fun (_, _, ty, _) ->
    Ctx.type_contains_ref ctx ty
  )

let rec can_be_abstracted' ctx contracts (_, items) =
  items |> List.exists (function
    | A.Guarantee _ | Mode _ -> true
    | ContractCall (_, id, _, _, _) -> (
        match NI.Map.find_opt id contracts with
        | None -> assert false
        | Some (_, _, _, outputs, contract) ->
          have_ref_type ctx outputs
          || can_be_abstracted' ctx contracts contract
    )
    | _ -> false
  )

let can_be_abstracted ctx contracts outputs contract =
  have_ref_type ctx outputs
  ||
  match contract with
  | None -> false
  | Some contract -> can_be_abstracted' ctx contracts contract

(* [true] if the contract of the function, if any, is never used in place of
   its body: there is nothing to abstract its calls with, or it is transparent.
   This is [LustreNode.has_effective_contract] at the level of the AST. *)
let has_no_effective_contract ctx contracts opac contract outputs =
  opac = A.Transparent || not (can_be_abstracted ctx contracts outputs contract)

let is_inlinable (set: NI.Set.t) contracts ctx opac contract outputs locals items =
  has_no_effective_contract ctx contracts opac contract outputs &&
  valid_outputs ctx outputs &&
  valid_locals ctx locals &&
  valid_items set items &&
  is_output_defined outputs items

(* The recursive functions whose functional symbols are given a definition at
   the SMT level (see [LustreFunDefs]), and which a call applied to quantified
   variables can therefore be compiled to an application of (see
   [LustreAstNormalizer.mk_fresh_qcall]).

   A function a contract abstracts is left out: its symbol is uninterpreted,
   constrained by the contract at the arguments of its instances only, so under
   a quantifier it would be an arbitrary function and a property that does hold
   of it could be reported falsifiable.

   The remaining conditions [LustreFunDefs] puts on a definition -- the body is
   a total function of the inputs, the solver defines recursive functions --
   are not known at this point. A call to a function that fails them is
   accepted here, and [LustreTransSys] warns about it. *)
let uf_callable_functions: Ctx.tc_context -> A.declaration list -> NI.Set.t
= fun ctx decls ->
  List.fold_left (fun (set, contracts) dcl ->
    match dcl with
    | A.ContractNodeDecl (_, contract_node_decl) -> (
      let (id, _, _, _, _) = contract_node_decl in
      set, NI.Map.add id contract_node_decl contracts
    )
    (* A non-imported recursive function *)
    | A.FuncDecl
        (_, (id, false, opac, _, _, outputs, _, _, contract), { A.is_rec = true; _ })
      -> (
      if has_no_effective_contract ctx contracts opac contract outputs then
        NI.Set.add id set, contracts
      else
        set, contracts
    )
    | _ -> set, contracts
  )
  (NI.Set.empty, NI.Map.empty)
  decls
  |> fst

let inlinable_functions: Ctx.tc_context -> A.declaration list -> NI.Set.t 
= fun ctx decls ->
  List.fold_left (fun (set, contracts) dcl ->
    match dcl with
    | A.ContractNodeDecl (_, contract_node_decl) -> (
      let (id, _, _, _, _) = contract_node_decl in
      set, NI.Map.add id contract_node_decl contracts
    )
    (* A non-imported non-recursive function *)
    | A.FuncDecl (_, (id, false, opac, [], _, outputs, locals, items, contract), { is_lemma = false; is_rec = false }) -> (
      if is_inlinable set contracts ctx opac contract outputs locals items then
        NI.Set.add id set, contracts
      else
        set, contracts
    )
    (* A type ascription *) 
    | A.NodeDecl (_, (id, _, _, _, _, _, _, _, _)) -> 
      if NI.get_node_type id = NI.TypeAscription then
        NI.Set.add id set, contracts 
      else 
        set, contracts
    | _ -> set, contracts
  )
  (NI.Set.empty, NI.Map.empty)
  decls
  |> fst
