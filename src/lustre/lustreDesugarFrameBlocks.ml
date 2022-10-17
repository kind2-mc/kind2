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
   @author Rob Lorch
 *)

module A = LustreAst
module R = Res

let (let*) = R.(>>=)

type error_kind = Unknown of string
  | StubError

let error_message error = match error with
  | Unknown s -> s
  | StubError -> "Stub error"

type error = [
  | `LustreDesugarFrameBlocksError of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreDesugarFrameBlocksError (pos, kind))

(** Parses an expression and replaces any ITE oracles with the 'fill'
    expression (which is stuttering, ie, 'init -> pre variable') *)
let rec fill_ite_helper fill = function
  (* Base case-- replace all oracles with 'fill' *)
  | A.Ident (pos, i) -> 
    (* See if 'i' is of the form "n_iboracle"*)
    let str = String.split_on_char '_' (HString.string_of_hstring i) |>
      List.rev |> List.hd
    in
    if (str = "iboracle") then fill else A.Ident(pos, i)

  (* Everything else is just recursing to find Idents *)
  | Const _ as e -> e
  | ModeRef _ as e -> e
    
  | RecordProject (a, e, b) -> RecordProject (a, fill_ite_helper fill e, b)
  | ConvOp (a, b, e) -> ConvOp (a, b, fill_ite_helper fill e)
  | UnaryOp (a, b, e) -> UnaryOp (a, b, fill_ite_helper fill e)
  | Current (a, e) -> Current (a, fill_ite_helper fill e)
  | When (a, e, b) -> When (a, fill_ite_helper fill e, b)
  | TupleProject (a, e, b) -> TupleProject (a, fill_ite_helper fill e, b)
  | Quantifier (a, b, c, e) -> Quantifier (a, b, c, fill_ite_helper fill e)
  | Pre (a, e) -> Pre (a, fill_ite_helper fill e)
  | BinaryOp (a, b, e1, e2) -> BinaryOp (a, b, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | CompOp (a, b, e1, e2) -> CompOp (a, b, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | ArrayConcat (a, e1, e2) -> ArrayConcat (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | ArrayIndex (a, e1, e2) -> ArrayIndex (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | ArrayConstr (a, e1, e2)  -> ArrayConstr (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | Arrow (a, e1, e2) -> Arrow (a, fill_ite_helper fill e1, fill_ite_helper fill e2)
  | Fby (a, e1, b, e2) -> Fby (a, fill_ite_helper fill e1, b, fill_ite_helper fill e2)
  | TernaryOp (a, b, e1, e2, e3) -> TernaryOp (a, b, fill_ite_helper fill e1, e2, fill_ite_helper fill e3)
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

(** Helper function to generate node equations when a variable in the 
    frame block guard is left undefined in the frame block body. *)
let add_undefined_nes nis ne = match ne with
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
  (* Assert in frame block guard *)
  | _ -> mk_error Lib.dummy_pos StubError 

(* What about ArrayDef? *)
(** Helper function to fill in ITE oracles. *)
let fill_ite_oracles nes ni = 
match ni with
  | A.Body (Equation (pos, (StructDef(_, [SingleIdent(pos2, i)]) as lhs), e)) -> 
    (* Find initialization value *)
    let init = List.find_opt (fun ne -> match ne with 
      | A.Equation (_, StructDef(_, [SingleIdent(_, id)]), _) when id = i  -> true
      | _ -> false
    ) nes in 
    let init = (match init with
      | Some (A.Equation (_, StructDef(_, [SingleIdent(_, _)]), expr)) -> expr
      (* shouldn't be possible*)
      | _ -> assert false) in
    (* Fill in oracles *)
    A.Body (Equation (pos, lhs, fill_ite_helper 
                     (A.Arrow (pos, init, (A.Pre (pos2, Ident(pos2, i)))))
                     e))
  | A.FrameBlock _ -> failwith "stub"
  (* shouldn't be possible *)
  | A.IfBlock _ -> assert false
  (* other stuff in frame block body *)
  | _ -> failwith "stub" (* mk_error Lib.dummy_pos StubError *)
  


(**
  For each node item in frame block body:
    Fill in ITE oracles and guard the generated pres.
  For each definition in frame block guard:
    Fill in an equation if one doesn't exist.
*)
let desugar_node_item ni = match ni with
  | A.FrameBlock (_, nes, nis) -> 
    let nis = List.map (fill_ite_oracles nes) nis in
    let* nis2 = R.seq (List.map (add_undefined_nes nis) nes) in
    let nis2 = List.flatten nis2 in 
    R.ok (nis @ nis2)
  | _ -> R.ok [ni]



(** Desugars a declaration list to remove frame blocks. If a frame block has
    if statements with undefined branches, it fills the branches in by setting
    the variable equal to its previous value (and initialing the 'pre' with the
    given init value). *)
let desugar_frame_blocks normalized_nodes_and_contracts = 
  let desugar_node_decl decl = (match decl with
    | A.NodeDecl (s, (node_id, b, nps, cctds, ctds, nlds, nis, co)) -> 
      let* nis = R.seq (List.map desugar_node_item nis) in
      let nis = List.flatten nis in
      (* List.iter (A.pp_print_node_item Format.std_formatter) nis; *)
      R.ok (A.NodeDecl (s, (node_id, b, nps, cctds, ctds, nlds, nis, co)))
    | _ -> R.ok decl
  ) in
  R.seq (List.map desugar_node_decl normalized_nodes_and_contracts)