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
module R = Res
module GI = GeneratedIdentifiers
module AH = LustreAstHelpers
module NI = NodeId

let (let*) = R.(>>=)

type error_kind = 
  | MisplacedNodeItemError of A.node_item
  | MisplacedFrameBlockError of A.node_item

let error_message error = match error with
  | MisplacedNodeItemError ni -> (match ni with
    | Body (Assert _) -> "Asserts are not allowed inside frame blocks."
    | FrameBlock _ -> "Frame blocks are not allowed inside other frame blocks."
    | AnnotMain _ -> "Main annotations are not allowed inside frame blocks."
    | AnnotProperty _ -> "Property annotations are not allowed inside frame blocks."
    (* Other node items are allowed *)
    | _ -> assert false
    )
  | MisplacedFrameBlockError _ -> "Frame blocks are not allowed in functions."

type error = [
  | `LustreDesugarFrameBlocksError of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreDesugarFrameBlocksError (pos, kind))
 
type warning_kind = 
  | UninitializedVariableWarning of HString.t

let warning_message warning = match warning with
  | UninitializedVariableWarning id -> "Uninitialized frame block variable " ^ HString.string_of_hstring id

let error_if_lus_strict = function
  | UninitializedVariableWarning _ -> true

type warning = [
  | `LustreDesugarFrameBlocksWarning of Lib.position * warning_kind
]

let mk_warning pos kind = `LustreDesugarFrameBlocksWarning (pos, kind)

type eq_or_framecond =
  | Eq of A.eq_lhs
  | FCond of A.eq_lhs

(* First position is frame block header, second position is of the specific equation *)
let pos_list_map : (Lib.position * eq_or_framecond) list NI.Hashtbl.t = 
  NI.Hashtbl.create 20

let i = ref 0

let mk_fresh_indices inds =
  List.fold_left (fun acc _ ->
    let new_name = (string_of_int !i) ^ "_ind" in 
    i := !i + 1; 
    (HString.mk_hstring new_name) :: acc
  ) [] inds

let warn_unguarded_pres nis pos = 
  List.map (fun ni -> match ni with
    | A.Body (Equation (_, StructDef(_, [SingleIdent(_, id)]), expr)) -> 
      if AH.has_unguarded_pre_no_warn expr then [(mk_warning pos (UninitializedVariableWarning id))] else []
    | A.Body (Equation (_, StructDef(_, [ArrayDef(_, id, _)]), expr)) -> 
      if AH.has_unguarded_pre_no_warn expr then [(mk_warning pos (UninitializedVariableWarning id))] else []
    | _ -> []
  ) nis

(** Parses an expression and replaces any ITE oracles with the 'fill'
    expression (which is stuttering, ie, 'pre variable').
*)
let rec fill_ite_helper frame_pos node_id lhs fill e = 
  let r = fill_ite_helper frame_pos node_id lhs fill in 
  match e with
  (* Replace all oracles with 'fill' *)
  | A.Ident (pos, i) -> 
    (* See if 'i' is of the form "n_iboracle" *)
    if GI.var_is_iboracle i 
    then (
      (* First, record that frame var "i" was actually used for stuttering *)
      let frame_info = [(frame_pos, FCond lhs)] in
      (* If there is already a binding, we want to retain the old 'frame_info' *)
      let frame_info = match NI.Hashtbl.find_opt pos_list_map node_id with
        | Some frame_info2 -> frame_info @ frame_info2
        | None -> frame_info 
      in
      NI.Hashtbl.add pos_list_map node_id frame_info;
      
      fill
    )
    else A.Ident(pos, i)

  (* Everything else is just recursing to find Idents *)
  | Pre (p, e) -> Pre (p, r e)
  | Arrow (p, e1, e2) -> Arrow (p, r e1, r e2)
  | TypeAscription (p, e, ty) -> TypeAscription (p, r e, ty)
  | Const _ as e -> e
  | ModeRef _ as e -> e
  | Last _ as e -> e
  | EmptyMap _ as e -> e
  | EmptySet _ as e -> e
  | RecordProject (p, e, id) -> RecordProject (p, r e, id)
  | ConvOp (p, b, e) -> ConvOp (p, b, r e)
  | Extract (p, e, b, c) -> Extract (p, r e, b, c)
  | UnaryOp (p, b, e) -> UnaryOp (p, b, r e)
  | When (p, e, b) -> When (p, r e, b)
  | Quantifier (p, b, c, e) -> Quantifier (p, b, c, r e)
  | BinaryOp (p, b, e1, e2) -> BinaryOp (p, b, r e1, r e2)
  | CompOp (p, b, e1, e2) -> CompOp (p, b, r e1, r e2)
  | AnyOp _ -> assert false (* desugared in lustreDesugarAnyChooseOps *)
  | ChooseOp _ -> assert false (* desugared in lustreDesugarAnyChooseOps *)
  | IndexAccess (p, e1, e2, k) -> IndexAccess (p, r e1, r e2, k)
  | ArrayConstr (p, e1, e2) -> ArrayConstr (p, r e1, r e2)
  | TernaryOp (p, b, e1, e2, e3) -> TernaryOp (p, b, r e1, r e2, r e3)
  
  | GroupExpr (p, b, l) -> GroupExpr (p, b, List.map r l)
  | Call (p, b, c, l) -> Call (p, b, c, List.map r l)

  | Merge (p, b, l) -> Merge (p, b, 
    List.combine
    (List.map fst l)
    (List.map r (List.map snd l)))
  
  | RecordExpr (p, b, c, l) -> RecordExpr (p, b, c,
    List.combine
    (List.map fst l)
    (List.map r (List.map snd l)))
  
  | RestartEvery (p, b, l, e) -> 
    RestartEvery (p, b, List.map r l, r e)
  | Activate (p, b, e1, e2, l) ->
    Activate (p, b, r e1, r e2, List.map r l)
  | Condact (p, e1, e2, b, l1, l2) ->
    Condact (p, r e1, r e2, b, 
             List.map r l1, List.map r l2)

  | StructUpdate (p, e1, li, e2) -> 
    let e2 = match e2 with 
    | Some e2 -> Some (r e2)
    | None -> None 
    in
    A.StructUpdate (p, r e1,
    List.map (function
              | A.Label (a, b) -> A.Label (a, b)
              | MapIndex (a, e) -> MapIndex (a, r e)
              | SetIndex (a, e) -> SetIndex (a, r e)
              | Index (a, e) -> Index (a, r e)
              | GenericIndex (a, e) -> GenericIndex (a, r e)
             ) li, 
    e2)
  | A.Match (p, e, arms, ty_opt) ->
    A.Match (p, r e,
      List.combine
        (List.map fst arms)
        (List.map r (List.map snd arms)),
      ty_opt)
  | A.ADTTerm (p, ty_args, ctor, args) ->
    A.ADTTerm (p, ty_args, ctor, List.map r args)

(** Helper function to generate node equations when an initialized variable in the
    frame block is left undefined in the frame block body. *)
let generate_undefined_nes f_pos node_id nis ne = match ne with
  | A.Equation (pos, (StructDef(_, [SingleIdent(_, id)]) as lhs), init) -> 
    (* Find the corresponding node item in frame block body. *)
    let res = List.find_opt (fun ni -> match ni with
      | A.Body (A.Equation (_, StructDef(_, [SingleIdent(_, i)]), _)) when id = i -> true
      | A.Body (A.Equation (_, StructDef(_, [ArrayDef(_, i, _)]), _)) when id = i -> true
      | _ -> false
    ) nis in 
    let pos2 = AH.pos_of_expr init in (
    match res with
      (* Already defined in frame block *)
      | Some _ -> R.ok []
      (* Fill in equation in frame block body *)
      | None -> 
        (* First, record that frame var "id" was actually used for stuttering *)
        let frame_info = [(f_pos, FCond lhs)] in
        (* If there is already a binding, we want to retain the old 'frame_info' *)
        let frame_info = match NI.Hashtbl.find_opt pos_list_map node_id with
          | Some frame_info2 -> frame_info @ frame_info2
          | None -> frame_info 
        in
        NI.Hashtbl.add pos_list_map node_id frame_info;

        R.ok [A.Body(A.Equation(pos, lhs, Arrow(pos2, init, Pre(pos2, Ident (pos2, id)))))]
    )
  | A.Equation (pos, (StructDef(_, [ArrayDef(_, id1, id2)]) as lhs), init) -> 
    (* Find the corresponding node item in frame block body. *)
    let res = List.find_opt (fun ni -> match ni with
      | A.Body (A.Equation (_, StructDef(_, [ArrayDef(_, i, _)]), _)) when id1 = i -> true
      | A.Body (A.Equation (_, StructDef(_, [SingleIdent(_, i)]), _)) when id1 = i -> true
      | _ -> false
    ) nis in 
    let pos2 = AH.pos_of_expr init in 
    let rec build_array_index js = (match js with
      | [j] -> A.IndexAccess(pos2, A.Ident(pos2, id1), A.Ident(pos2, j), Array)
      | j :: js -> IndexAccess(pos2, build_array_index js, A.Ident(pos2, j), Array)
      | [] -> assert false (* not possible *)
    ) in
    (match res with
      (* Already defined in frame block *)
      | Some _ -> R.ok []
      (* Fill in equation in frame block body *)
      | None -> 
        (* First, record that frame var "id1" was actually used for stuttering *)
        let frame_info = [(f_pos, FCond lhs)] in
        (* If there is already a binding, we want to retain the old 'frame_info' *)
        let frame_info = match NI.Hashtbl.find_opt pos_list_map node_id with
          | Some frame_info2 -> frame_info @ frame_info2
          | None -> frame_info 
        in
        NI.Hashtbl.add pos_list_map node_id frame_info;

        R.ok [A.Body(A.Equation(pos, lhs, Arrow(pos2, init, Pre(pos2, build_array_index (List.rev id2)))))]
    )
  (* Assert in frame block guard *)
  | A.Assert(pos, _) -> mk_error pos (MisplacedNodeItemError (A.Body ne))
  (* Equations with multiple assignments have already been desugared, so this
     case is not possible *)
  | A.Equation _ -> assert false

(* Helper function to "push indices" further inside ITEs, e.g. 
   (if c then arr1 else arr2)[i][j] --> if c then arr1[i][j] else arr2[i][j]. 
   This is a necessary normalization step for fill_ite_helper, 
   as the initialization itself may contain indices.
   For example, consider the array equation 
     A[i] = (if c then ib_oracle else arr2)[i], with initialization 
     A[i] = i. 
   Without this step, fill_ite_helper will generate the malformed equation
     A[i] = (if c then i -> pre A[i] else arr2)[i].
   But, if we push indices first, we convert equation 
     A[i] = (if c then ib_oracle else arr2)[i] to  
     A[i] = if c then ib_oracle else arr2[i], and then to  
     A[i] = if c then i -> pre A[i] else arr2[i], which is well-formed. 
*)
let rec push_indices indices e =
  let r = push_indices indices in
  match e with
  | (A.Ident (pos, id) as e) -> 
    if GI.var_is_iboracle id then e else 
      List.fold_left (fun acc ind -> 
        A.IndexAccess (pos, acc, Ident (pos, ind), Array)
      ) e indices 
  | TernaryOp (p, Ite, e1, e2, e3) -> TernaryOp (p, Ite, e1, r e2, r e3)
  | e ->  
    let p = AH.pos_of_expr e in
    List.fold_left (fun acc ind -> 
      A.IndexAccess (p, acc, Ident (p, ind), Array)
    ) e indices 

(** Helper function to generate node equations when a variable in the 
    frame block var list is left undefined in the frame block body AND has 
    no initialization. *)
let generate_undefined_nes_no_init node_id pos nes nis var = 
    (* Find var's corresponding node item in frame block body *)
    match (List.find_opt (fun ni -> match ni with
      | A.Body (A.Equation (_, StructDef(_, [SingleIdent(_, i)]), _)) when i = var -> true
      | A.Body (A.Equation (_, StructDef(_, [ArrayDef(_, i, _)]), _)) when i = var -> true
      | _ -> false) nis)
    with
      (* Already defined in frame block body *)
      | Some _ -> R.ok []
      | _ -> 
    (* If not found, find var's corresponding initialization *)
    match (List.find_opt (fun ne -> match ne with
        | (A.Equation (_, StructDef(_, [SingleIdent(_, i)]), _)) when i = var -> true
        | (A.Equation (_, StructDef(_, [ArrayDef(_, i, _)]), _)) when i = var -> true
        | _ -> false
    ) nes)
    with
      (* Already defined in frame block initialization *)
      | Some _ -> R.ok []
      | None -> 
        let lhs = A.StructDef(pos, [SingleIdent (pos, var)]) in
        (* First, record that frame var "var" was actually used for stuttering *)
        let frame_info = [(pos, FCond lhs)] in
        (* If there is already a binding, we want to retain the old 'frame_info' *)
        let frame_info = match NI.Hashtbl.find_opt pos_list_map node_id with
          | Some frame_info2 -> frame_info @ frame_info2
          | None -> frame_info 
        in
        NI.Hashtbl.add pos_list_map node_id frame_info;

        R.ok [A.Body(A.Equation(pos, lhs, Pre(pos, Ident (pos, var))))]

(** Helper function to fill in ITE oracles. 
    For variable v, fill each ITE oracle with `init_v -> pre v` if an initialization exists, 
    and `pre v` otherwise. *) 
let fill_ite_oracles f_pos node_id nes ni = 
match ni with
  | A.Body (Equation (pos, (StructDef(_, [SingleIdent(_, i)]) as lhs), rhs_expr)) -> 
    (* Find initialization value *)
    let exprs = List.find_map (fun ne -> match ne with 
      | A.Equation (_, StructDef(_, [SingleIdent(_, id)]), init_expr) when id = i  -> 
        let pre_expr = A.Pre (pos, Ident (pos, i)) in 
        Some (lhs, init_expr, rhs_expr, pre_expr)
      (* In this case, the initialization is a recursive array definition, but 
         the body equation is not. So, we have to make the whole desugared equation recursive. *)
      | A.Equation (_, StructDef(p1, [ArrayDef(p2, id, inds1)]), init_expr) when id = i  -> 
        (* Substitute fresh variables for inds1 in lhs and init_expr to avoid name clash issues *)
        let fresh = mk_fresh_indices inds1 in
        let lhs = A.StructDef(p1, [ArrayDef(p2, id, fresh)]) in
        let init_expr = AH.replace_idents inds1 fresh init_expr in
        let pos = AH.pos_of_expr init_expr in
        let rhs_expr = push_indices fresh rhs_expr in
        let pre_expr = List.fold_left (fun expr j -> 
          A.IndexAccess (pos, expr, A.Ident(pos, j), Array)
        ) (A.Pre (pos, Ident (pos, i))) fresh 
        in 
        Some (lhs, init_expr, rhs_expr, pre_expr)
      | _ -> None
    ) nes in
    (match exprs with
      | Some (lhs, init, rhs_expr, pre_expr) ->     
        let pos2 = AH.pos_of_expr rhs_expr in 
        let rhs = 
          fill_ite_helper f_pos node_id lhs 
            (A.Arrow (pos2, init, pre_expr)) rhs_expr
        in
        R.ok (A.Body (Equation (pos, lhs, rhs))) 
      | None -> 
        let pos2 = AH.pos_of_expr rhs_expr in 
        let rhs = 
          fill_ite_helper f_pos node_id lhs 
            (A.Pre (pos2, Ident(pos2, i))) rhs_expr
        in
        R.ok (A.Body (Equation (pos, lhs, rhs))))
  | A.Body (Equation (pos, StructDef(p1, [ArrayDef(p2, i1, inds1)]), rhs_expr)) ->
    (* Substitute fresh variables for inds1 in lhs and init_expr to avoid name clash issues *)
    let fresh = mk_fresh_indices inds1 in
    let lhs = A.StructDef (p1, [ArrayDef(p2, i1, fresh)]) in
    let rhs_expr = AH.replace_idents inds1 fresh rhs_expr in
    let pos2 = AH.pos_of_expr rhs_expr in 
    (* Find initialization value *)
    let array_index = List.fold_left (fun expr j ->
      A.IndexAccess(pos2, expr, A.Ident(pos2, j), Array)) (A.Ident(pos2, i1)) fresh
    in
    let init = List.find_map (fun ne -> match ne with 
      | A.Equation (_, StructDef(_, [ArrayDef(_, id, inds2)]), expr) when id = i1  -> 
        Some (AH.replace_idents inds2 fresh expr)
      (* In this case, the body equation is a recursive array definition, but 
         the initialization is not. So, we have to make the whole desugared equation recursive. *)
      | A.Equation (_, StructDef(_, [SingleIdent(_, id)]), expr) when id = i1  -> 
        let pos = AH.pos_of_expr expr in
        let expr = List.fold_left (fun acc ind -> 
          A.IndexAccess (pos, acc, Ident (pos, ind), Array)  
        ) expr fresh in
        Some expr
      | _ -> None
    ) nes in 
    (match init with
      | Some init -> 
        let rhs = 
          fill_ite_helper f_pos node_id lhs 
            (A.Arrow (pos2, init, (A.Pre (pos2, array_index)))) rhs_expr
        in
        R.ok (A.Body (Equation (pos, lhs, rhs)))
      | None -> 
        let rhs = 
          fill_ite_helper f_pos node_id lhs 
            (A.Pre (pos2, array_index)) rhs_expr 
        in
        R.ok (A.Body (Equation (pos, lhs, rhs))))
    (* The following node items should not be in frame blocks. In particular,
      if blocks should have been desugared earlier in the pipeline. *)
  | A.IfBlock (pos, _, _, _)
  | A.WhenBlock (pos, _, _, _)
  | A.FrameBlock (pos, _, _, _) 
  | A.Body (Assert (pos, _)) 
  | A.AnnotProperty (pos, _, _, _)
  | A.Body (Equation (pos, _, _))
  | A.Auto pos
  | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)



(**
  For each node item in frame block body:
    Fill in ITE oracles (for variable v, fill with `init_v -> pre v` if an initialization 
    exists, and `pre v` otherwise).  
  For each initialization:
    Fill in an equation if one doesn't exist.
  For each variable that is neither initialized nor defined:
    Fill in an equation of the form 'y = pre y' (initially undefined)
*)
let desugar_node_item (node_id: NI.t) ni = match ni with
    (* All multiple assignment is removed in lustreRemoveMultAssign.ml *)
  | A.FrameBlock (pos, vars, nes, nis) ->
    let vars = List.map snd vars in
    let* nis = R.seq (List.map (fill_ite_oracles pos node_id nes) nis) in
    let* nis2 = R.seq (List.map (generate_undefined_nes pos node_id nis) nes) in
    let nis2 = List.flatten nis2 in 
    let* nis3 = R.seq (List.map (generate_undefined_nes_no_init node_id pos nes nis) vars) in
    let nis3 = List.flatten nis3 in
    let warnings = warn_unguarded_pres (nis @ nis3) pos |> List.flatten in
    (* Frame block header info *)
    let frame_info = (List.map (fun ne -> match ne with
        | A.Equation (_, lhs, expr) -> (AH.pos_of_expr expr, Eq lhs)
        | _ -> assert false) nes) in
    (* If there is already a binding, we want to retain the old 'frame_info' *)
    let frame_info = match NI.Hashtbl.find_opt pos_list_map node_id with
      | Some frame_info2 -> frame_info @ frame_info2
      | None -> frame_info 
    in
    (* Record node equation LHSs so we can add state var defs later *)
    NI.Hashtbl.add pos_list_map node_id frame_info;

    R.ok ([], nis @ nis2 @ nis3, warnings)
  | _ -> R.ok ([], [ni], []) 

(** Desugars a declaration list to remove frame blocks. 
    If a frame block node equation has if statements with undefined branches, it fills the branches in by setting
    the variable v equal to `init_v -> pre v` (or, if no initialization is provided, just `pre v`) *)
let desugar_frame_blocks sorted_node_contract_decls = 
  NI.Hashtbl.clear pos_list_map ;
  let desugar_node_decl decl = (match decl with
    | A.NodeDecl (s, ((node_id, b, o, nps, cctds, ctds, nlds, nis2, co))) ->
      let* res = R.seq (List.map (desugar_node_item node_id) nis2) in
      let decls, nis, warnings = Lib.split3 res in
      let warnings = List.flatten warnings in 
      R.ok (A.NodeDecl (s, (node_id, b, o, nps, cctds, ctds,
                       (List.flatten decls) @ nlds, List.flatten nis, co)), warnings) 
                      
    (* Make sure there are no frame blocks in functions *)
    | A.FuncDecl (_, ((_, _, _, _, _, _, _, nis, _)), _) -> (
      let contains_frame_block = List.find_opt (fun ni -> match ni with | A.FrameBlock _ -> true | _ -> false) nis in
      match contains_frame_block with
        | Some (FrameBlock (pos, _, _, _) as fb) -> mk_error pos (MisplacedFrameBlockError fb)
        | _ -> R.ok (decl, [])
      )
    | _ -> R.ok (decl, [])
  ) in
  let* res = R.seq (List.map desugar_node_decl sorted_node_contract_decls) in
  let decls, warnings = List.split res in
  let warnings = List.flatten warnings in
  R.ok (decls, warnings)
