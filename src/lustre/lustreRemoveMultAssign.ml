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
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module GI = GeneratedIdentifiers

(** [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref (0)

(* This looks unsafe, but we only apply unwrap when we know from earlier stages
   in the pipeline that an error is not possible. *)
let unwrap result = match result with
  | Ok r -> r
  | Error _ -> assert false

let split_and_flatten3 xs =
  let ls = List.map (fun (l, _, _) -> l) xs |> List.flatten in
  let ms = List.map (fun (_, m, _) -> m) xs |> List.flatten in
  let ns = List.map (fun (_, _, n) -> n) xs |> List.flatten in
  ls, ms, ns

(** Create a new fresh temporary variable name. *)
let mk_fresh_temp_var ty =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "temp") in
  let gids2 = { (GI.empty ()) with 
    locals = GI.StringMap.singleton name (false, ty);
  } in
  name, gids2
  

(** When pulling out temp variables for recursive array definitions,
   we also have to modify the RHS to match the temp variable.
   For example, we want equations of the form
   'temp[i] = if i = 0 then 0 else temp[i-1] + 1' rather than
   'temp[i] = if i = 0 then 0 else y[i-1] + 1', where 'y' was
   the original LHS variable name.
*)
let rec modify_arraydefs_in_expr array_assoc_list = function
    (* Replace all oracles with 'fill' *)
    | A.Ident (pos, i1) -> (
      let update = List.assoc_opt i1 array_assoc_list in
      match update with 
      | Some id -> A.Ident(pos, id)
      | None -> A.Ident(pos, i1)
    )
    (* Everything else is just recursing to find Idents *)
    | Pre (a, e) -> Pre (a, (modify_arraydefs_in_expr array_assoc_list e))  
    | Arrow (a, e1, e2) -> Arrow (a, (modify_arraydefs_in_expr array_assoc_list e1), (modify_arraydefs_in_expr array_assoc_list e2))
    | Const _ as e -> e
    | ModeRef _ as e -> e
    | RecordProject (a, e, b) -> RecordProject (a, (modify_arraydefs_in_expr array_assoc_list e), b)
    | ConvOp (a, b, e) -> ConvOp (a, b, (modify_arraydefs_in_expr array_assoc_list e))
    | UnaryOp (a, b, e) -> UnaryOp (a, b, (modify_arraydefs_in_expr array_assoc_list e))
    | Current (a, e) -> Current (a, (modify_arraydefs_in_expr array_assoc_list e))
    | When (a, e, b) -> When (a, (modify_arraydefs_in_expr array_assoc_list e), b)
    | TupleProject (a, e, b) -> TupleProject (a, (modify_arraydefs_in_expr array_assoc_list e), b)
    | Quantifier (a, b, c, e) -> Quantifier (a, b, c, (modify_arraydefs_in_expr array_assoc_list e))
    | BinaryOp (a, b, e1, e2) -> BinaryOp (a, b, (modify_arraydefs_in_expr array_assoc_list e1), (modify_arraydefs_in_expr array_assoc_list e2))
    | CompOp (a, b, e1, e2) -> CompOp (a, b, (modify_arraydefs_in_expr array_assoc_list e1), (modify_arraydefs_in_expr array_assoc_list e2))
    | ArrayConcat (a, e1, e2) -> ArrayConcat (a, (modify_arraydefs_in_expr array_assoc_list e1), (modify_arraydefs_in_expr array_assoc_list e2))
    | ArrayIndex (a, e1, e2) -> ArrayIndex (a, (modify_arraydefs_in_expr array_assoc_list e1), (modify_arraydefs_in_expr array_assoc_list e2))
    | ArrayConstr (a, e1, e2)  -> ArrayConstr (a, (modify_arraydefs_in_expr array_assoc_list e1), (modify_arraydefs_in_expr array_assoc_list e2))
    | Fby (a, e1, b, e2) -> Fby (a, (modify_arraydefs_in_expr array_assoc_list e1), b, (modify_arraydefs_in_expr array_assoc_list e2))
    | TernaryOp (a, b, e1, e2, e3) -> TernaryOp (a, b, (modify_arraydefs_in_expr array_assoc_list e1), (modify_arraydefs_in_expr array_assoc_list e2), (modify_arraydefs_in_expr array_assoc_list e3))
    | ArraySlice (a, e1, (e2, e3)) -> ArraySlice (a, (modify_arraydefs_in_expr array_assoc_list e1), ((modify_arraydefs_in_expr array_assoc_list e2), (modify_arraydefs_in_expr array_assoc_list e3)))
    
    | GroupExpr (a, b, l) -> GroupExpr (a, b, List.map (modify_arraydefs_in_expr array_assoc_list) l)
    | NArityOp (a, b, l) -> NArityOp (a, b, List.map (modify_arraydefs_in_expr array_assoc_list) l) 
    | Call (a, b, l) -> Call (a, b, List.map (modify_arraydefs_in_expr array_assoc_list) l)
    | CallParam (a, b, c, l) -> CallParam (a, b, c, List.map (modify_arraydefs_in_expr array_assoc_list) l)

    | Merge (a, b, l) -> Merge (a, b, 
      List.combine
      (List.map fst l)
      (List.map (modify_arraydefs_in_expr array_assoc_list) (List.map snd l)))
    
    | RecordExpr (a, b, l) -> RecordExpr (a, b,     
      List.combine
      (List.map fst l)
      (List.map (modify_arraydefs_in_expr array_assoc_list) (List.map snd l)))
    
    | RestartEvery (a, b, l, e) -> 
      RestartEvery (a, b, List.map (modify_arraydefs_in_expr array_assoc_list) l, modify_arraydefs_in_expr array_assoc_list e)
    | Activate (a, b, e, r, l) ->
      Activate (a, b, (modify_arraydefs_in_expr array_assoc_list) e, (modify_arraydefs_in_expr array_assoc_list) r, List.map (modify_arraydefs_in_expr array_assoc_list) l)
    | Condact (a, e, r, b, l1, l2) ->
      Condact (a, (modify_arraydefs_in_expr array_assoc_list) e, (modify_arraydefs_in_expr array_assoc_list) r, b, 
              List.map (modify_arraydefs_in_expr array_assoc_list) l1, List.map (modify_arraydefs_in_expr array_assoc_list) l2)

    | StructUpdate (a, e1, li, e2) -> 
      A.StructUpdate (a, modify_arraydefs_in_expr array_assoc_list e1, 
      List.map (function
                | A.Label (a, b) -> A.Label (a, b)
                | Index (a, e) -> Index (a, modify_arraydefs_in_expr array_assoc_list e)
              ) li, 
      modify_arraydefs_in_expr array_assoc_list e2) 


(** Takes in an equation LHS and returns 
    * updated gids with temp variables,
    * equations setting original variable equal to temp variables, 
    * updated context
   *)
let create_new_eqs ctx lhs expr = 
  let rhs_pos = AH.pos_of_expr expr in
  let convert_struct_item = (function
    | A.SingleIdent (p, i) as si -> 
      let ty = (match Ctx.lookup_ty ctx i with 
        | Some ty -> ty 
        (* Type error, shouldn't be possible *)
        | None -> assert false) in
      let temp, gids = mk_fresh_temp_var ty in
      (
        [gids], 
        [A.SingleIdent(p, temp)],
        [(A.Equation(p, StructDef(p, [si]), Ident(rhs_pos, temp)))]
      )

    (*
    y, A[i] = (7, if i = 0 then 0 else A[i-1] + 1); 
    -->
    t1, t2[i] = (7, if i = 0 then 0 else A[i-1] + 1); 
    y = t1;
    A = t2;
    *)
    | ArrayDef (p, i, js) as si -> 
      
      let ty = (match Ctx.lookup_ty ctx i with 
        | Some ty -> ty 
        (* Type error, shouldn't be possible *)
        | None -> assert false) in
      let temp, gids = mk_fresh_temp_var ty in
      let array_index = List.fold_left (fun expr j -> A.ArrayIndex(rhs_pos, expr, A.Ident(rhs_pos, j))) (A.Ident(rhs_pos, temp)) js in
      (
        [gids],
        [A.ArrayDef(p, temp, js)],
        [(A.Equation(p, StructDef(p, [si]), array_index))]
      )
    | _ ->
      (* Other types of LHS are not supported *)
      assert false
  ) in
  match lhs with
    | A.StructDef (pos, ss) -> 
      let res = (List.map convert_struct_item ss) in
      let gids, sis, eqs = split_and_flatten3 res in
      
      let get_array_ids =
        List.filter_map (function
          | A.ArrayDef (_, id, _) -> Some id
          | _ -> None)
      in
      let array_assoc_list =
        let arrayids_original = get_array_ids ss in
        let arrayids_new = get_array_ids sis in
        List.combine arrayids_original arrayids_new
      in
      let expr = modify_arraydefs_in_expr array_assoc_list expr in
      let gids2 = { (GI.empty ()) with 
        equations = [([], [], A.StructDef(pos, sis), expr)];
      } in
      let eqs = List.map (fun x -> A.Body x) eqs in
        (
          (* modify expr if we have an ArrayDef in temp_lhs *)
          eqs, 
          gids2::gids
        )

let remove_mult_assign_from_ni ctx ni = 
  let rec helper ctx ni = (
    match ni with 
      | A.Body (Equation (_, lhs, expr)) -> 
        let lhs_vars = AH.defined_vars_with_pos ni in
        (* If there is no multiple assignment, we don't alter the node item,
          otherwise, we must remove the multiple assignment. *)
        if (List.length lhs_vars = 1) 
        then [ni], []
        else create_new_eqs ctx lhs expr
      
      | IfBlock (pos, e, l1, l2) -> 
        let nis1, gids1 = List.map (helper ctx) l1 |> List.split in
        let nis2, gids2 = List.map (helper ctx) l2 |> List.split in
        (* nis1 and nis3 are the temp variables need to get pulled outside the if block *)
        [A.IfBlock (pos, e, List.flatten nis1, List.flatten nis2)], List.flatten gids1 @ List.flatten gids2

      | FrameBlock (pos, vars, nes, nis) -> 
        let nes = List.map (fun x -> A.Body x) nes in 
        let nis1, gids1 = List.map (helper ctx) nes |> List.split in
        let nis2, gids2 = List.map (helper ctx) nis |> List.split in
        let nis1 = nis1 |> List.flatten |> List.map 
          (fun x -> match x with | A.Body (Equation _ as e) -> e | _ -> assert false) in
        (* nis1 and nis3 are the temp variables need to get pulled outside the if block *)
        [A.FrameBlock (pos, vars, nis1, List.flatten nis2)], List.flatten gids1 @ List.flatten gids2
      
      (* Don't need to alter these node items as they are not allowed in if
         and frame blocks. If they are present anyway, it will be caught in
         lustreDesugarIfBlocks.ml *)
      | A.Body (Assert _) 
      | A.AnnotProperty _
      | A.AnnotMain _ -> [ni], []
  ) in
  let (nis, gids) = helper ctx ni in
  let gids = List.fold_left GI.union (GI.empty ()) gids in
  (* Calling 'remove_mult_assign_from_ib' on an if or frame block (which is always
     the case) will mean that nis2 will always have length 1. *)
  let ni = List.hd nis in
  ni, gids

let desugar_node_item ctx ni = match ni with
  | A.IfBlock _ 
  | A.FrameBlock _ -> 
    remove_mult_assign_from_ni ctx ni 
  | _ -> ni, GI.empty ()

(** Remove multiple assignment from if and frame blocks in a single declaration. *)
let desugar_node_decl ctx decl = match decl with
  | A.FuncDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) ->
    let ctx = Chk.get_node_ctx ctx d |> unwrap in
    let res = List.map (desugar_node_item ctx) nis in
    let nis, gids = List.split res in
    let gids = List.fold_left GI.union (GI.empty ()) gids in
    A.FuncDecl (s, (node_id, b, nps, cctds, ctds, nlds, nis, co)), GI.StringMap.singleton node_id gids
  | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) -> 
    let ctx = Chk.get_node_ctx ctx d |> unwrap in
    let res = List.map (desugar_node_item ctx) nis in
    let nis, gids = List.split res in
    let gids = List.fold_left GI.union (GI.empty ()) gids in
    A.NodeDecl (s, (node_id, b, nps, cctds, ctds, nlds, nis, co)), GI.StringMap.singleton node_id gids
  | _ -> decl, GI.StringMap.empty
  
(** Desugars a declaration list to remove multiple assignment from if blocks and frame
    blocks. *)
let remove_mult_assign ctx sorted_node_contract_decls = 
  let decls, gids = List.map (desugar_node_decl ctx) sorted_node_contract_decls |> List.split in
  let gids = List.fold_left (GI.StringMap.merge GI.union_keys2) GI.StringMap.empty gids in
  decls, gids