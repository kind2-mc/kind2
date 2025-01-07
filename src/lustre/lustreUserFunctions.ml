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
module AH = LustreAstHelpers
module Ctx = TypeCheckerContext

module IdSet = A.SI
module StringMap = HString.HStringMap

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
      IdSet.subset (AH.calls_of_expr rhs) set
    | AnnotProperty _ -> true
    | A.Body (Equation (_, _, _))
    | Body (Assert _)
    | AnnotMain _ -> false
    | FrameBlock _
    | IfBlock _ -> assert false (* desugared earlier in pipeline *)
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

let have_ref_type_or_subrange ctx outputs =
  outputs |> List.exists (fun (_, _, ty, _) ->
    Ctx.type_contains_ref_or_subrange ctx ty
  )

let rec can_be_abstracted' ctx contracts (_, items) =
  items |> List.exists (function
    | A.Guarantee _ | Mode _ -> true
    | ContractCall (_, id, _, _, _) -> (
        match StringMap.find_opt id contracts with
        | None -> assert false
        | Some (_, _, _, outputs, contract) ->
          have_ref_type_or_subrange ctx outputs
          || can_be_abstracted' ctx contracts contract
    )
    | _ -> false
  )

let can_be_abstracted ctx contracts outputs contract =
  have_ref_type_or_subrange ctx outputs
  ||
  match contract with
  | None -> false
  | Some contract -> can_be_abstracted' ctx contracts contract

let is_inlinable set contracts ctx opac contract outputs locals items =
  (opac = A.Transparent || not (can_be_abstracted ctx contracts outputs contract)) &&
  valid_outputs ctx outputs &&
  valid_locals ctx locals &&
  valid_items set items &&
  is_output_defined outputs items

let inlinable_functions ctx decls =
  List.fold_left (fun (set, contracts) dcl ->
    match dcl with
    | A.ContractNodeDecl (_, contract_node_decl) -> (
      let (id, _, _, _, _) = contract_node_decl in
      set, StringMap.add id contract_node_decl contracts
    )
    (* A non-imported function *)
    | A.FuncDecl (_, (id, false, opac, [], _, outputs, locals, items, contract)) -> (
      if is_inlinable set contracts ctx opac contract outputs locals items then
        IdSet.add id set, contracts
      else
        set, contracts
    )
    | _ -> set, contracts
  )
  (IdSet.empty, StringMap.empty)
  decls
  |> fst