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

(** 
   The following code desugars frame blocks into a list of node items
   (equations), completing two major steps:
   1. Fill in any oracles within the frame block (for unguarded pres or 
      undefined variables in if blocks).
   2. Generate node equations for variables left completely undefined in frame 
      blocks.

   @author Rob Lorch
 *)

module A = LustreAst
module R = Res
module LDI = LustreDesugarIfBlocks
module Chk = LustreTypeChecker

let (let*) = R.(>>=)

type error_kind = Unknown of string
  | MisplacedNodeItemError of A.node_item
  | MisplacedFrameBlockError of A.node_item

let error_message error = match error with
  | Unknown s -> s
  | MisplacedNodeItemError ni -> (match ni with
    | Body (Assert _) -> "Asserts are not allowed inside frame blocks."
    | FrameBlock _ -> "Frame blocks are not allowed inside other frame blocks."
    | AnnotMain _ -> "Main annotations are not allowed inside frame blocks."
    | AnnotProperty _ -> "Property annotations are not allowed inside frame blocks."
    (* Other node items are allowed *)
    | _ -> assert false
    )
  | MisplacedFrameBlockError _ -> "FrameBlocks are not allowed in functions."

type error = [
  | `LustreDesugarFrameBlocksError of Lib.position * error_kind
  | `LustreDesugarIfBlocksError of Lib.position * LDI.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
]

let mk_error pos kind = Error (`LustreDesugarFrameBlocksError (pos, kind))

(** Parses an expression and replaces any ITE oracles with the 'fill'
    expression (which is stuttering, ie, 'pre variable').
*)
let rec fill_ite_helper fill = function
  (* Replace all oracles with 'fill' *)
  | A.Ident (pos, i) -> 
    (* See if 'i' is of the form "n_iboracle" *)
    let str = String.split_on_char '_' (HString.string_of_hstring i) |>
      List.rev |> List.hd
    in
    if (str = "iboracle") then fill else A.Ident(pos, i)

  (* Everything else is just recursing to find Idents *)
  | Pre (a, e) -> Pre (a, fill_ite_helper fill e)
  | Arrow (a, e1, e2) -> Arrow (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | Const _ as e -> e
  | ModeRef _ as e -> e
    
  | RecordProject (a, e, b) -> RecordProject (a, fill_ite_helper fill e, b)
  | ConvOp (a, b, e) -> ConvOp (a, b, fill_ite_helper fill e)
  | UnaryOp (a, b, e) -> UnaryOp (a, b, fill_ite_helper fill e)
  | Current (a, e) -> Current (a, fill_ite_helper fill e)
  | When (a, e, b) -> When (a, fill_ite_helper fill e, b)
  | TupleProject (a, e, b) -> TupleProject (a, fill_ite_helper fill e, b)
  | Quantifier (a, b, c, e) -> Quantifier (a, b, c, fill_ite_helper fill e)
  | BinaryOp (a, b, e1, e2) -> BinaryOp (a, b, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | CompOp (a, b, e1, e2) -> CompOp (a, b, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | ArrayConcat (a, e1, e2) -> ArrayConcat (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | ArrayIndex (a, e1, e2) -> ArrayIndex (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | ArrayConstr (a, e1, e2)  -> ArrayConstr (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | Fby (a, e1, b, e2) -> Fby (a, fill_ite_helper fill e1, b, fill_ite_helper fill e2)
  | TernaryOp (a, b, e1, e2, e3) -> TernaryOp (a, b, fill_ite_helper fill e1, fill_ite_helper fill e2, fill_ite_helper fill e3)
  | ArraySlice (a, e1, (e2, e3)) -> ArraySlice (a, fill_ite_helper fill e1, (fill_ite_helper fill e2, fill_ite_helper fill e3))
  
  | GroupExpr (a, b, l) -> GroupExpr (a, b, List.map (fill_ite_helper fill) l)
  | NArityOp (a, b, l) -> NArityOp (a, b, List.map (fill_ite_helper fill) l) 
  | Call (a, b, l) -> Call (a, b, List.map (fill_ite_helper fill) l)
  | CallParam (a, b, c, l) -> CallParam (a, b, c, List.map (fill_ite_helper fill) l)

  | Merge (a, b, l) -> Merge (a, b, 
    List.combine
    (List.map fst l)
    (List.map (fill_ite_helper fill) (List.map snd l)))
  
  | RecordExpr (a, b, l) -> RecordExpr (a, b,     
    List.combine
    (List.map fst l)
    (List.map (fill_ite_helper fill) (List.map snd l)))
  
  | RestartEvery (a, b, l, e) -> 
    RestartEvery (a, b, List.map (fill_ite_helper fill) l, fill_ite_helper fill e)
  | Activate (a, b, e, r, l) ->
    Activate (a, b, (fill_ite_helper fill) e, (fill_ite_helper fill) r, List.map (fill_ite_helper fill) l)
  | Condact (a, e, r, b, l1, l2) ->
    Condact (a, (fill_ite_helper fill) e, (fill_ite_helper fill) r, b, 
             List.map (fill_ite_helper fill) l1, List.map (fill_ite_helper fill) l2)

  | StructUpdate (a, e1, li, e2) -> 
    A.StructUpdate (a, fill_ite_helper fill e1, 
    List.map (function
              | A.Label (a, b) -> A.Label (a, b)
              | Index (a, e) -> Index (a, fill_ite_helper fill e)
             ) li, 
    fill_ite_helper fill e2)

(** Helper function to generate node equations when an initialized variable in the 
    frame block is left undefined in the frame block body. *)
let generate_undefined_nes nis ne = match ne with
  | A.Equation (pos, (StructDef(_, [SingleIdent(_, id)]) as lhs), init) -> 
    (* Find the corresponding node item in frame block body. *)
    let res = List.find_opt (fun ni -> match ni with
      | A.Body (A.Equation (_, StructDef(_, [SingleIdent(_, i)]), _)) when id = i -> true
      | _ -> false
    ) nis in (
    match res with
      (* Already defined in frame block *)
      | Some _ -> R.ok []
      (* Fill in equation in frame block body *)
      | None -> R.ok [A.Body(A.Equation(pos, lhs, Arrow(pos, init, Pre(pos, Ident (pos, id)))))]
    )
  | A.Equation (pos, (StructDef(_, [ArrayDef(_, id1, id2)]) as lhs), init) -> 
    (* Find the corresponding node item in frame block body. *)
    let res = List.find_opt (fun ni -> match ni with
      | A.Body (A.Equation (_, StructDef(_, [ArrayDef(_, i, _)]), _)) when id1 = i -> true
      | _ -> false
    ) nis in 
    let rec build_array_index js = (match js with
      | [j] -> A.ArrayIndex(pos, A.Ident(pos, id1), A.Ident(pos, j))
      | j :: js -> ArrayIndex(pos, build_array_index js, A.Ident(pos, j))
      | [] -> assert false (* not possible *)
    ) in

    (match res with
      (* Already defined in frame block *)
      | Some _ -> R.ok []
      (* Fill in equation in frame block body *)
      | None -> R.ok [A.Body(A.Equation(pos, lhs, Arrow(pos, init, Pre(pos, build_array_index (List.rev id2)))))]
    )
  (* Assert in frame block guard *)
  | A.Equation(pos, _, _) -> mk_error pos (MisplacedNodeItemError (A.Body ne))
  | A.Assert(pos, _) -> mk_error pos (MisplacedNodeItemError (A.Body ne))


(** Helper function to generate node equations when a variable in the 
    frame block var list is left undefined in the frame block body AND has 
    no initialization. *)
let generate_undefined_nes_no_init pos nes nis var = 
    (* Find var's corresponding node item in frame block body. *)
    let res = List.find_opt (fun ni -> match ni with
      | A.Body (A.Equation (_, StructDef(_, [SingleIdent(_, i)]), _)) when i = var -> true
      | A.Body (A.Equation (_, StructDef(_, [ArrayDef(_, i, _)]), _)) when i = var -> true
      (* Check to see if var has an initialization*)
      | _ -> match (List.find_opt (fun ne -> match ne with
        | (A.Equation (_, StructDef(_, [SingleIdent(_, i)]), _)) when i = var -> true
        | (A.Equation (_, StructDef(_, [ArrayDef(_, i, _)]), _)) when i = var -> true
        | _ -> false
      ) nes) with | Some _ -> true | None -> false
    ) nis in (
    match res with
      (* Already defined in frame block body or initialization*)
      | Some _ -> R.ok []
      (* Fill in equation in frame block body *)
      | None -> R.ok [A.Body(A.Equation(pos, StructDef(pos, [SingleIdent (pos, var)]), Pre(pos, Ident (pos, var))))]
    )


(** Helper function to fill in ITE oracles and guard equations with specified
    initialization values (if present). *)
let fill_ite_oracles nes ni = 
match ni with
  | A.Body (Equation (pos, (StructDef(_, [SingleIdent(pos2, i)]) as lhs), e)) -> 
    (* Find initialization value *)
    let init = Lib.find_map (fun ne -> match ne with 
      | A.Equation (_, StructDef(_, [SingleIdent(_, id)]), expr) when id = i  -> Some expr
      | _ -> None
    ) nes in
    (match init with
      | Some init ->     
        R.ok (A.Body (Equation (pos, lhs, (A.Arrow (pos, init, 
                                                    fill_ite_helper (A.Pre (pos2, Ident(pos2, i))) e)))))
      | None -> 
        R.ok (A.Body (Equation (pos, lhs, fill_ite_helper 
                                (A.Pre (pos2, Ident(pos2, i)))
                                e))))
  | A.Body (Equation (pos, (StructDef(_, [ArrayDef(pos2, i1, i2)]) as lhs), e)) ->
  (* Find initialization value *)
  let array_index = List.fold_left (fun expr j -> A.ArrayIndex(pos, expr, A.Ident(pos, j))) (A.Ident(pos, i1)) i2 in
  let init = Lib.find_map (fun ne -> match ne with 
    | A.Equation (_, StructDef(_, [ArrayDef(_, id, _)]), expr) when id = i1  -> Some expr
    | _ -> None
  ) nes in 
  (match init with
    | Some init -> 
      R.ok (A.Body (Equation (pos, lhs, (A.Arrow (pos, init, 
                                                  fill_ite_helper (A.Pre (pos2, array_index)) e)))))
    | None -> 
      R.ok (A.Body (Equation (pos, lhs, fill_ite_helper 
                         (A.Pre (pos2, array_index))
                         e))))
  (* The following node items should not be in frame blocks. In particular,
     if blocks should have been desugared earlier in the pipeline. *)
  | A.IfBlock (pos, _, _, _) 
  | A.FrameBlock (pos, _, _, _) 
  | A.Body (Assert (pos, _)) 
  | A.AnnotProperty (pos, _, _)
  | A.Body (Equation (pos, _, _))
  | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
  


(**
  For each node item in frame block body:
    Fill in ITE oracles and initialize equations (RHS) when an initialization
    value is specified.
  For each initialization:
    Fill in an equation if one doesn't exist.
  For each variable that is neither initialized nor defined:
    Fill in an equation of the form 'y = pre y' (initially undefined)
*)
let desugar_node_item _ ni = match ni with
    (* All multiple assignment is removed in lustreDesugarIfBlocks.ml *)
  | A.FrameBlock (pos, vars, nes, nis) ->
    let* nis = R.seq (List.map (fill_ite_oracles nes) nis) in
    let* nis2 = R.seq (List.map (generate_undefined_nes nis) nes) in
    let nis2 = List.flatten nis2 in 
    let* nis3 = R.seq (List.map (generate_undefined_nes_no_init pos nes nis) vars) in
    let nis3 = List.flatten nis3 in
    R.ok ([], nis @ nis2 @ nis3)
  | _ -> R.ok ([], [ni])



(** Desugars a declaration list to remove frame blocks. Node equations
    in the body are initialized with the provided initializations. If a frame block 
    node equation has if statements with undefined branches, it fills the branches in by setting
    the variable equal to its value in the previous timestep. *)
let desugar_frame_blocks ctx sorted_node_contract_decls = 
  let desugar_node_decl decl = (match decl with
    | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis2, co) as d)) -> 
      let* ctx = Chk.get_node_ctx ctx d in
      let* res = R.seq (List.map (desugar_node_item ctx) nis2) in
      let decls, nis = List.split res in
      R.ok (A.NodeDecl (s, (node_id, b, nps, cctds, ctds, 
                       (List.flatten decls) @ nlds, List.flatten nis, co))) 
                      
    (* Make sure there are no frame blocks in functions *)
    | A.FuncDecl (_, ((_, _, _, _, _, _, nis, _))) -> (
      let contains_frame_block = List.find_opt (fun ni -> match ni with | A.FrameBlock _ -> true | _ -> false) nis in
      match contains_frame_block with
        | Some (FrameBlock (pos, _, _, _) as fb) -> mk_error pos (MisplacedFrameBlockError fb)
        | _ -> R.ok decl
      )
    | _ -> R.ok decl
  ) in
  R.seq (List.map desugar_node_decl sorted_node_contract_decls)