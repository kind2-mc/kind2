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

let (let*) = R.(>>=)

type error_kind = Unknown of string
  | MisplacedNodeItemError of A.node_item
  | InitializationNotFoundError of A.node_item
  | MisplacedFrameBlockError of A.node_item

let error_message error = match error with
  | Unknown s -> s
  | MisplacedNodeItemError ni -> "Node item " ^ Lib.string_of_t A.pp_print_node_item ni ^ " is not allowed in frame block."
  | MisplacedFrameBlockError ni -> "FrameBlock " ^ Lib.string_of_t A.pp_print_node_item ni ^ " is not allowed in function."
  | InitializationNotFoundError ni -> "Node item " ^ Lib.string_of_t A.pp_print_node_item ni ^ " does not have a corresponding initialization in the frame block."

type error = [
  | `LustreDesugarFrameBlocksError of Lib.position * error_kind
  | `LustreDesugarIfBlocksError of Lib.position * LDI.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
]

let mk_error pos kind = Error (`LustreDesugarFrameBlocksError (pos, kind))

(** Parses an expression and replaces any ITE oracles with the 'fill'
    expression (which is stuttering, ie, 'init -> pre variable').
    Also guards unguarded pres with 'init'. 
*)
let rec fill_ite_helper init fill ung = function
  (* Replace all oracles with 'fill' *)
  | A.Ident (pos, i) -> 
    (* See if 'i' is of the form "n_iboracle" *)
    let str = String.split_on_char '_' (HString.string_of_hstring i) |>
      List.rev |> List.hd
    in
    if (str = "iboracle") then fill else A.Ident(pos, i)

  (* Guard unguarded pres *)
  | Pre (a, e) -> 
    if ung
    then Arrow(a, init, Pre (a, (fill_ite_helper init fill true) e))
    else Pre (a, (fill_ite_helper init fill true) e)  
  | Arrow (a, e1, e2) -> Arrow (a, fill_ite_helper init fill ung e1, fill_ite_helper init fill false e2)


  (* Everything else is just recursing to find Idents and unguarded pres *)
  | Const _ as e -> e
  | ModeRef _ as e -> e
    
  | RecordProject (a, e, b) -> RecordProject (a, fill_ite_helper init fill ung e, b)
  | ConvOp (a, b, e) -> ConvOp (a, b, fill_ite_helper init fill ung e)
  | UnaryOp (a, b, e) -> UnaryOp (a, b, fill_ite_helper init fill ung e)
  | Current (a, e) -> Current (a, fill_ite_helper init fill ung e)
  | When (a, e, b) -> When (a, fill_ite_helper init fill ung e, b)
  | TupleProject (a, e, b) -> TupleProject (a, fill_ite_helper init fill ung e, b)
  | Quantifier (a, b, c, e) -> Quantifier (a, b, c, fill_ite_helper init fill ung e)
  | BinaryOp (a, b, e1, e2) -> BinaryOp (a, b, fill_ite_helper init fill ung e1, fill_ite_helper init fill ung e2)
  | CompOp (a, b, e1, e2) -> CompOp (a, b, fill_ite_helper init fill ung e1, fill_ite_helper init fill ung e2)
  | ArrayConcat (a, e1, e2) -> ArrayConcat (a, fill_ite_helper init fill ung e1, fill_ite_helper init fill ung e2)
  | ArrayIndex (a, e1, e2) -> ArrayIndex (a, fill_ite_helper init fill ung e1, fill_ite_helper init fill ung e2)
  | ArrayConstr (a, e1, e2)  -> ArrayConstr (a, fill_ite_helper init fill ung e1, fill_ite_helper init fill ung e2)
  | Fby (a, e1, b, e2) -> Fby (a, fill_ite_helper init fill ung e1, b, fill_ite_helper init fill ung e2)
  | TernaryOp (a, b, e1, e2, e3) -> TernaryOp (a, b, fill_ite_helper init fill ung e1, fill_ite_helper init fill ung e2, fill_ite_helper init fill ung e3)
  | ArraySlice (a, e1, (e2, e3)) -> ArraySlice (a, fill_ite_helper init fill ung e1, (fill_ite_helper init fill ung e2, fill_ite_helper init fill ung e3))
  
  | GroupExpr (a, b, l) -> GroupExpr (a, b, List.map (fill_ite_helper init fill ung) l)
  | NArityOp (a, b, l) -> NArityOp (a, b, List.map (fill_ite_helper init fill ung) l) 
  | Call (a, b, l) -> Call (a, b, List.map (fill_ite_helper init fill ung) l)
  | CallParam (a, b, c, l) -> CallParam (a, b, c, List.map (fill_ite_helper init fill ung) l)

  | Merge (a, b, l) -> Merge (a, b, 
    List.combine
    (List.map fst l)
    (List.map (fill_ite_helper init fill ung) (List.map snd l)))
  
  | RecordExpr (a, b, l) -> RecordExpr (a, b,     
    List.combine
    (List.map fst l)
    (List.map (fill_ite_helper init fill ung) (List.map snd l)))
  
  | RestartEvery (a, b, l, e) -> 
    RestartEvery (a, b, List.map (fill_ite_helper init fill ung) l, fill_ite_helper init fill ung e)
  | Activate (a, b, e, r, l) ->
    Activate (a, b, (fill_ite_helper init fill ung) e, (fill_ite_helper init fill ung) r, List.map (fill_ite_helper init fill ung) l)
  | Condact (a, e, r, b, l1, l2) ->
    Condact (a, (fill_ite_helper init fill ung) e, (fill_ite_helper init fill ung) r, b, 
             List.map (fill_ite_helper init fill ung) l1, List.map (fill_ite_helper init fill ung) l2)

  | StructUpdate (a, e1, li, e2) -> 
    A.StructUpdate (a, fill_ite_helper init fill ung e1, 
    List.map (function
              | A.Label (a, b) -> A.Label (a, b)
              | Index (a, e) -> Index (a, fill_ite_helper init fill ung e)
             ) li, 
    fill_ite_helper init fill ung e2)

(** Helper function to generate node equations when a variable in the 
    frame block guard is left undefined in the frame block body. *)
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

(** Helper function to fill in ITE oracles and guard unguarded pres. *)
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
        R.ok (A.Body (Equation (pos, lhs, fill_ite_helper 
                                init
                                (A.Arrow (pos, init, (A.Pre (pos2, Ident(pos2, i)))))
                                true
                                e)))
      | None -> mk_error pos (InitializationNotFoundError ni))
  | A.Body (Equation (pos, (StructDef(_, [ArrayDef(pos2, i1, i2)]) as lhs), e)) ->
  (* Find initialization value *)
  let array_index = List.fold_left (fun expr j -> A.ArrayIndex(pos, expr, A.Ident(pos, j))) (A.Ident(pos, i1)) i2 in
  let init = Lib.find_map (fun ne -> match ne with 
    | A.Equation (_, StructDef(_, [ArrayDef(_, id, _)]), expr) when id = i1  -> Some expr
    | _ -> None
  ) nes in 
  (match init with
    | Some init -> R.ok (A.Body (Equation (pos, lhs, fill_ite_helper 
                         init
                        (A.Arrow (pos, init, (A.Pre (pos2, array_index))))
                         true
                         e)))
    | None -> mk_error pos (InitializationNotFoundError ni))
  (* The following node items should not be in frame blocks. In particular,
     if blocks should have been desugared earlier in the pipeline. *)
  | A.IfBlock (pos, _, _, _) 
  | A.FrameBlock (pos, _, _) 
  | A.Body (Assert (pos, _)) 
  | A.AnnotProperty (pos, _, _)
  | A.Body (Equation (pos, _, _)) -> mk_error pos (MisplacedNodeItemError ni)
  | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
  


(**
  For each node item in frame block body:
    Fill in ITE oracles and guard the generated pres.
  For each definition in frame block guard:
    Fill in an equation if one doesn't exist.
*)
let desugar_node_item _ ni = match ni with
    (* All multiple assignment is removed in lustreDesugarIfBlocks.ml *)
  | A.FrameBlock (_, nes, nis) ->
    let* nis = R.seq (List.map (fill_ite_oracles nes) nis) in
    let* nis2 = R.seq (List.map (generate_undefined_nes nis) nes) in
    let nis2 = List.flatten nis2 in 
    R.ok ([], nis @ nis2)
  | _ -> R.ok ([], [ni])



(** Desugars a declaration list to remove frame blocks. If a frame block has
    if statements with undefined branches, it fills the branches in by setting
    the variable equal to its previous value (and initialing the 'pre' with the
    given init value). *)
let desugar_frame_blocks ctx normalized_nodes_and_contracts = 
  let desugar_node_decl decl = (match decl with
    | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis2, co) as d)) -> 
      let* ctx = LDI.get_node_ctx ctx d in
      let* res = R.seq (List.map (desugar_node_item ctx) nis2) in
      let decls, nis = List.split res in
      R.ok (A.NodeDecl (s, (node_id, b, nps, cctds, ctds, 
                       (List.flatten decls) @ nlds, List.flatten nis, co))) 
                      
    (* Make sure there are no frame blocks in functions *)
    | A.FuncDecl (_, ((_, _, _, _, _, _, nis, _))) -> (
      let contains_frame_block = List.find_opt (fun ni -> match ni with | A.FrameBlock _ -> true | _ -> false) nis in
      match contains_frame_block with
        | Some (FrameBlock (pos, _, _) as fb) -> mk_error pos (MisplacedFrameBlockError fb)
        | _ -> R.ok decl
      )
    | _ -> R.ok decl
  ) in
  R.seq (List.map desugar_node_decl normalized_nodes_and_contracts)