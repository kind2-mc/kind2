(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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
@author Rob Lorch *)

module A = LustreAst
module Chk = LustreTypeChecker
module Ctx = TypeCheckerContext

(* This looks unsafe, but we only apply unwrap when we know from earlier stages
   in the pipeline that an error is not possible. *)
let unwrap result = match result with
  | Ok r -> r
  | Error _ -> assert false

let rec ni_add_array_constraints ctx acc = function
  | A.Body (Equation (pos, StructDef(_, [SingleIdent(_, i)]), rhs)) -> 
    let ty = (match Ctx.lookup_ty ctx i with 
      | Some ty -> ty 
      (* Type error, shouldn't be possible *)
      | None -> assert false
    ) in 
    (match ty with 
      | ArrayType (_, (_, expr1)) -> (match rhs with 
        | ArrayConstr(_, _, expr2) -> 
          Format.fprintf Format.std_formatter "Got here!\n";
          A.Guarantee (pos, None, false, CompOp(pos, Eq, expr1, expr2)) :: acc
        | _ -> acc
      )
      | _ -> acc
    ) 
  | A.Body (Assert _) -> acc
  | A.IfBlock (_, _, nis1, nis2) -> 
    let cons1 = List.fold_left (ni_add_array_constraints ctx) acc nis1 in 
    let cons2 = List.fold_left (ni_add_array_constraints ctx) acc nis2 in 
    cons1 @ cons2 @ acc
  | A.FrameBlock (_, _, nes, nis) -> 
    let cons1 = 
      List.map (fun eq -> A.Body eq) nes |> 
      List.fold_left (ni_add_array_constraints ctx) acc
    in
    let cons2 = List.fold_left (ni_add_array_constraints ctx) acc nis in 
    cons1 @ cons2 @ acc
  | A.AnnotMain _ -> acc
  | A.AnnotProperty _ -> acc
  | _ -> acc (*!! Remove this! !!*)

(** Add array length constraints to AST *)
let add_array_constraints ctx decls = 
  List.map (fun decl -> match decl with
    | A.FuncDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) -> 
      let ctx = Chk.get_node_ctx ctx d |> unwrap in
      let constraints = List.fold_left (ni_add_array_constraints ctx) [] nis in
      let co = match co with 
        | None -> Some constraints 
        | Some co -> Some (constraints @ co)
      in
      A.FuncDecl (s, (node_id, b, nps, cctds, ctds, nlds, nis, co))
    | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) -> 
      let ctx = Chk.get_node_ctx ctx d |> unwrap in
      let constraints = List.fold_left (ni_add_array_constraints ctx) [] nis in
      let co = match co with 
        | None -> Some constraints 
        | Some co -> Some (constraints @ co)
      in
      A.NodeDecl (s, (node_id, b, nps, cctds, ctds, nlds, nis, co))
    | _ -> decl
  ) decls

let add_array_constraints2 ctx ((_, _, _, _, _, _, items, contract) as d) = 
  let ctx = Chk.get_node_ctx ctx d |> unwrap in
  let constraints = List.fold_left (ni_add_array_constraints ctx) [] items in
  match contract with 
    | None -> Some constraints 
    | Some co -> Some (constraints @ co)