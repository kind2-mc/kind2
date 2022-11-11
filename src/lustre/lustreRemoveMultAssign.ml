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

(** @author Rob Lorch *)

(** Removes multiple assignment from an if block by pulling out equations
   with multiple assignment and using temp variables. 
  Example: 
   if cond
   then 
      y1, y2 = node(expr1);
   else
      y1 = expr2;
      y2 = expr3;
   fi
  -->
   t1, t2 = node(expr1);
   if cond
   then 
      y1 = t1;
      y2 = t2;
   else
      y1 = expr2;
      y2 = expr3;
   fi

  For each temp variable, we also generate a new declaration.
*)

module R = Res
module A = LustreAst
module AH = LustreAstHelpers
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

let (let*) = R.(>>=)

type error_kind = Unknown of string
  | MisplacedNodeItemError of A.node_item

let error_message error = match error with
  | Unknown s -> s
  | MisplacedNodeItemError ni -> "Node item " ^ Lib.string_of_t A.pp_print_node_item ni ^ " is not allowed in if block"

type error = [
  | `LustreRemoveMultAssignError of Lib.position * error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
]

let mk_error pos kind = Error (`LustreRemoveMultAssignError (pos, kind))

(** [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref (0)

let split_and_flatten4 ls =
  let xs = List.map (fun (x, _, _, _) -> x) ls |> List.flatten in
  let ys = List.map (fun (_, y, _, _) -> y) ls |> List.flatten in
  let zs = List.map (fun (_, _, z, _) -> z) ls |> List.flatten in
  let ws = List.map (fun (_, _, _, w) -> w) ls |> List.flatten in
  xs, ys, zs, ws

(** Create a new fresh temporary variable name. *)
let mk_fresh_temp_name _ =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  HString.concat2 prefix (HString.mk_hstring "_temp") 

(** When pulling out temp variables for recursive array definitions,
   we also have to modify the RHS to match the temp variable.
   For example, we want equations of the form
   'temp[i] = if i = 0 then 0 else temp[i-1] + 1' rather than
   'temp[i] = if i = 0 then 0 else y[i-1] + 1', where 'y' was
   the original LHS variable name.
*)
let rec modify_arraydefs_in_expr arraydefs_original arraydefs_new = function
    (* Replace all oracles with 'fill' *)
    | A.Ident (pos, i1) -> 
      let comb = List.combine arraydefs_original arraydefs_new in
      let update = Lib.find_map (fun pair -> match pair with 
        | (A.ArrayDef(_, i2, _), A.ArrayDef (_, i3, _)) when i1 = i2 -> 
          Some (A.Ident(pos, i3))
        | _ -> None
      ) comb in (match update with 
        | Some value -> value 
        | None -> A.Ident(pos, i1)
      )
    (* Everything else is just recursing to find Idents *)
    | Pre (a, e) -> Pre (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e))  
    | Arrow (a, e1, e2) -> Arrow (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2))
    | Const _ as e -> e
    | ModeRef _ as e -> e
    | RecordProject (a, e, b) -> RecordProject (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e), b)
    | ConvOp (a, b, e) -> ConvOp (a, b, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e))
    | UnaryOp (a, b, e) -> UnaryOp (a, b, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e))
    | Current (a, e) -> Current (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e))
    | When (a, e, b) -> When (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e), b)
    | TupleProject (a, e, b) -> TupleProject (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e), b)
    | Quantifier (a, b, c, e) -> Quantifier (a, b, c, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e))
    | BinaryOp (a, b, e1, e2) -> BinaryOp (a, b, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2))
    | CompOp (a, b, e1, e2) -> CompOp (a, b, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2))
    | ArrayConcat (a, e1, e2) -> ArrayConcat (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2))
    | ArrayIndex (a, e1, e2) -> ArrayIndex (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2))
    | ArrayConstr (a, e1, e2)  -> ArrayConstr (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2))
    | Fby (a, e1, b, e2) -> Fby (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), b, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2))
    | TernaryOp (a, b, e1, e2, e3) -> TernaryOp (a, b, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e2), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e3))
    | ArraySlice (a, e1, (e2, e3)) -> ArraySlice (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new e1), ((modify_arraydefs_in_expr arraydefs_original arraydefs_new e2), (modify_arraydefs_in_expr arraydefs_original arraydefs_new e3)))
    
    | GroupExpr (a, b, l) -> GroupExpr (a, b, List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l)
    | NArityOp (a, b, l) -> NArityOp (a, b, List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l) 
    | Call (a, b, l) -> Call (a, b, List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l)
    | CallParam (a, b, c, l) -> CallParam (a, b, c, List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l)

    | Merge (a, b, l) -> Merge (a, b, 
      List.combine
      (List.map fst l)
      (List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) (List.map snd l)))
    
    | RecordExpr (a, b, l) -> RecordExpr (a, b,     
      List.combine
      (List.map fst l)
      (List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) (List.map snd l)))
    
    | RestartEvery (a, b, l, e) -> 
      RestartEvery (a, b, List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l, modify_arraydefs_in_expr arraydefs_original arraydefs_new e)
    | Activate (a, b, e, r, l) ->
      Activate (a, b, (modify_arraydefs_in_expr arraydefs_original arraydefs_new) e, (modify_arraydefs_in_expr arraydefs_original arraydefs_new) r, List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l)
    | Condact (a, e, r, b, l1, l2) ->
      Condact (a, (modify_arraydefs_in_expr arraydefs_original arraydefs_new) e, (modify_arraydefs_in_expr arraydefs_original arraydefs_new) r, b, 
              List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l1, List.map (modify_arraydefs_in_expr arraydefs_original arraydefs_new) l2)

    | StructUpdate (a, e1, li, e2) -> 
      A.StructUpdate (a, modify_arraydefs_in_expr arraydefs_original arraydefs_new e1, 
      List.map (function
                | A.Label (a, b) -> A.Label (a, b)
                | Index (a, e) -> Index (a, modify_arraydefs_in_expr arraydefs_original arraydefs_new e)
              ) li, 
      modify_arraydefs_in_expr arraydefs_original arraydefs_new e2) 


(** Takes in an equation LHS and returns 
    * updated LHS with temp variables,
    * equations setting original variable equal to temp variables, 
    * new declarations, and
    * updated context
   *)
let create_new_eqs ctx lhs expr = 
  let convert_struct_item = (function
    | A.SingleIdent (p, i) as si -> 
      let temp = mk_fresh_temp_name i in
      (* Type error, shouldn't be possible *)
      let ty = (match Ctx.lookup_ty ctx i with 
        | Some ty -> ty 
        | None -> assert false) in
      let ctx = Ctx.add_ty ctx temp ty in
      (
        [A.SingleIdent(p, temp)],
        [A.Body (A.Equation(p, StructDef(p, [si]), Ident(p, temp)))],
        [A.NodeVarDecl(p, (p, temp, ty, ClockTrue))],
        [ctx]
      )

    (*
    y, A[i] = (7, if i = 0 then 0 else A[i-1] + 1); 
    -->
    t1, t2[i] = (7, if i = 0 then 0 else A[i-1] + 1); 
    y = t1;
    A = t2;
    *)
    | ArrayDef (p, i, js) as si -> 
      let temp = mk_fresh_temp_name i in
      let array_index = List.fold_left (fun expr j -> A.ArrayIndex(p, expr, A.Ident(p, j))) (A.Ident(p, temp)) js in
      (* Type error, shouldn't be possible *)
      let ty = (match Ctx.lookup_ty ctx i with 
        | Some ty -> ty 
        | None -> assert false (* Not possible *)) in
      let ctx = Ctx.add_ty ctx temp ty in
      (
        [A.ArrayDef(p, temp, js)],
        [A.Body (A.Equation(p, StructDef(p, [si]), array_index))],
        [A.NodeVarDecl(p, (p, temp, ty, ClockTrue))],
        [ctx]
      )
    | _ ->
      (* Other types of LHS are not supported *)
      assert false
  ) in
  match lhs with
    | A.StructDef (pos, ss) -> 
      let res = (List.map convert_struct_item ss) in
      let sis, eqs, decls, ctx = split_and_flatten4 res in
      let arraydefs_original = List.filter (fun x -> match x with | A.ArrayDef _ -> true | _ -> false) ss in
      let arraydefs_new = List.filter (fun x -> match x with | A.ArrayDef _ -> true | _ -> false) sis in
      let expr = modify_arraydefs_in_expr arraydefs_original arraydefs_new expr in
      (
        (* modify expr if we have an ArrayDef in temp_lhs *)
        [A.Body (Equation (pos, A.StructDef(pos, sis), expr))],
        eqs,
        decls,
        ctx
      )

let remove_mult_assign_from_ni ctx ni = 
  let rec helper ctx ni = (
    match ni with 
      | A.Body (Equation (_, lhs, expr)) -> 
        let lhs_vars = AH.defined_vars_with_pos ni in
        (* If there is no multiple assignment, we don't alter the node item,
          otherwise, we must remove the multiple assignment. The first node item
          list in the return value represents node items we "pull out" of the if block
          (ie, we define those before generating the ITEs). *)
        if (List.length lhs_vars = 1) 
        then R.ok([], [ni], [], [ctx])
        else (
          R.ok (create_new_eqs ctx lhs expr)
        )
      
      | IfBlock (pos, e, l1, l2) -> 
        let* res1 = R.seq (List.map (helper ctx) l1) in
        let nis1, nis2, decls1, ctx1 = split_and_flatten4 res1 in
        let* res2 = R.seq (List.map (helper ctx) l2) in
        let nis3, nis4, decls2, ctx2 = split_and_flatten4 res2 in
        (* nis1 and nis3 are the temp variables need to get pulled outside the if block *)
        R.ok (nis1 @ nis3, [A.IfBlock (pos, e, nis2, nis4)], decls1 @ decls2, ctx1 @ ctx2)

      | FrameBlock (pos, vars, nes, nis) -> 
        let nes = List.map (fun x -> A.Body x) nes in 
        let* res1 = R.seq (List.map (helper ctx) nes) in
        let nis1, nis2, decls1, ctx1 = split_and_flatten4 res1 in
        let* res2 = R.seq (List.map (helper ctx) nis) in
        let nis3, nis4, decls2, ctx2 = split_and_flatten4 res2 in     
        let nis2 = List.map 
          (fun x -> match x with | A.Body (Equation _ as e) -> e | _ -> assert false) 
          nis2 in
        (* nis1 and nis3 are the temp variables need to get pulled outside the if block *)
        R.ok (nis1 @ nis3, [A.FrameBlock (pos, vars, nis2, nis4)], decls1 @ decls2, ctx1 @ ctx2)
      
      (* Misplaced assert, annotmain, annotproperty in if block*)
      | A.Body (Assert (pos, _)) 
      | A.AnnotProperty (pos, _, _)
      | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
  ) in
  let* (nis, nis2, new_decls, ctx) = helper ctx ni in
  let ctx = List.fold_left Ctx.union Ctx.empty_tc_context ctx in
  (* Calling 'remove_mult_assign_from_ib' on an if or frame block (which is always
     the case) will mean that nis2 will always have length 1. *)
  let ni = List.hd nis2 in
  R.ok (nis, ni, new_decls, ctx)

let desugar_node_item ctx ni = match ni with
  | A.IfBlock _ -> 
    let* (nis, ib, decls1, _) = remove_mult_assign_from_ni ctx ni in 
    R.ok (decls1, nis @ [ib])
  | A.FrameBlock _ -> 
    let* (nis2, fb, decls1, _) = remove_mult_assign_from_ni ctx ni in 
    R.ok (decls1, nis2 @ [fb])
  | _ -> R.ok ([], [ni])

(** Desugars an individual node declaration (removing IfBlocks). *)
let desugar_node_decl ctx decl = match decl with
  | A.FuncDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) ->
    let* ctx = Chk.get_node_ctx ctx d in
    let* res = R.seq (List.map (desugar_node_item ctx) nis) in
    let (new_decls, nis) = List.split res in
    R.ok (A.FuncDecl (s, (node_id, b, nps, cctds, ctds, (List.flatten new_decls) @ nlds, (List.flatten nis), co))) 
  | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) -> 
    let* ctx = Chk.get_node_ctx ctx d in
    let* res = R.seq (List.map (desugar_node_item ctx) nis) in
    let (new_decls, nis) = List.split res in
    R.ok (A.NodeDecl (s, (node_id, b, nps, cctds, ctds, (List.flatten new_decls) @ nlds, (List.flatten nis), co))) 
  | _ -> R.ok (decl)


(** Desugars a declaration list to remove IfBlocks. Converts IfBlocks to
    declarative ITEs, filling in oracles if branches are undefined. *)
let remove_mult_assign ctx sorted_node_contract_decls = 
  let* decls = R.seq (List.map (desugar_node_decl ctx) sorted_node_contract_decls) in
  R.ok decls