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
module NI = NodeId
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module AH = LustreAstHelpers

let mk_fresh_fn_name: Lib.position -> NI.t -> NI.node_type -> NI.t = 
fun pos node_name node_type -> 
  let pos = Lib.string_of_t Lib.pp_print_line_and_column pos in
  let pos = String.sub pos 1 (String.length pos - 2) |> HString.mk_hstring in
  let name = match node_type with 
  | Any -> HString.mk_hstring ".any_"
  | Choose -> HString.mk_hstring ".choose_"
  | TypeAscription -> HString.mk_hstring ".type_ascription_"
  | _ -> assert false
  in
  let name = HString.concat2 name pos |> HString.concat2 (NI.get_name node_name)  in
  NI.mk_node_id ~node_type ~user_name:name name

let rec desugar_type: Ctx.tc_context -> NI.t -> NI.t list -> A.lustre_type -> A.lustre_type * A.declaration list =
fun ctx node_name fun_ids ty -> 
  let r = desugar_type ctx node_name fun_ids in 
  match ty with 
  | Int _ | Bool _ | Real _ | SBitVector _ | UBitVector _ 
  | EnumType _ | AbstractType _ 
  | UserType _ | History _ -> ty, [] 
  | Map (p, kt, vt) -> 
    let kt, gen_nodes1 = r kt in 
    let vt, gen_nodes2 = r vt in
    Map (p, kt, vt), gen_nodes1 @ gen_nodes2
  | Set (p, ty) ->
    let ty, gen_nodes = r ty in
    Set (p, ty), gen_nodes  
  | ArrayType (p, (ty, len)) ->
    let ty, gen_nodes1 = r ty in
    let len, gen_nodes2 = desugar_expr ctx node_name fun_ids len in
    ArrayType (p, (ty, len)), gen_nodes1 @ gen_nodes2
  | TArr (p, ty1, ty2) ->
    let ty1, gen_nodes1 = r ty1 in
    let ty2, gen_nodes2 = r ty2 in
    TArr (p, ty1, ty2), gen_nodes1 @ gen_nodes2
  | GroupType (p, tys) ->
    let tys, gen_nodes = List.map r tys |> List.split in
    GroupType (p, tys), List.flatten gen_nodes 
  | TupleType (p, tys) ->
    let tys, gen_nodes = List.map r tys |> List.split in
    TupleType (p, tys), List.flatten gen_nodes 
  | RecordType (p, id, tis) ->
    let tis, gen_nodes = List.map (fun (p, id, ty) -> let ty, d = r ty in (p, id, ty), d) tis |> List.split in
    RecordType (p, id, tis), List.flatten gen_nodes
  | RefinementType (p1, (p2, id, ty), e) ->
    let ty, gen_nodes1 = r ty in
    let e, gen_nodes2 = desugar_expr ctx node_name fun_ids e in
    RefinementType (p1, (p2, id, ty), e), gen_nodes1 @ gen_nodes2

and desugar_expr: Ctx.tc_context -> NI.t -> NI.t list -> A.expr -> A.expr * A.declaration list =
fun ctx node_name fun_ids expr -> 
  let rec_call = desugar_expr ctx node_name fun_ids in
  match expr with
  | TypeAscription (pos, e, ty) ->
    let e, gen_nodes1 = rec_call e in
    let ty, gen_nodes2 = desugar_type ctx node_name fun_ids ty in
    let span = { A.start_pos = pos; A.end_pos = pos; } in
    let node_id = mk_fresh_fn_name pos node_name TypeAscription in
    let ip_id = HString.mk_hstring Lib.StringValues.type_ascription_input_name in 
    let op_id = HString.mk_hstring Lib.StringValues.type_ascription_output_name in
    let ip = pos, ip_id, ty, A.ClockTrue, false in
    let mono = Chk.expand_type_syn_reftype_history ctx ty |> Result.get_ok in
    let op = pos, op_id, mono, A.ClockTrue in
    let eq = A.Body (A.Equation (pos, A.StructDef (pos, [A.SingleIdent (pos, op_id)]), A.Ident (pos, ip_id))) in
    (* The generated function might be polymorphic, so we find all the needed type variables *)
    let ty_params = 
      Ctx.SI.union (Ctx.ty_vars_of_type ctx node_name ty) 
                   (Ctx.ty_vars_of_expr ctx node_name e)
      |> Ctx.SI.elements
    in 
    let ty_args = List.map (fun id -> A.UserType (pos, [], id)) ty_params in
    let ty = Ctx.expand_type_syn ctx ty in
    let inputs = AH.vars_of_type ty |> Ctx.SI.elements in
    (* Global constants don't need to be passed as arguments to generated nodes *)
    let inputs = List.filter (fun i -> 
      match Ctx.lookup_const ctx i with 
        | Some (_, _, Ctx.Global) -> false 
        | _ -> true
    ) inputs in 
    let inputs_call = List.map (fun str -> A.Ident (pos, str)) inputs in
    let inputs = List.map (fun input -> (pos, input, Ctx.lookup_ty ctx input, A.ClockTrue)) inputs in
    let inputs = List.map (fun (p, inp, opt, cl) -> match opt with 
      | Some ty -> 
        let is_const = match Ctx.lookup_const ctx inp with | Some _ -> true | None -> false in
        p, inp, ty, cl, is_const 
      | None -> assert false
    ) inputs in
    let decl =
        A.NodeDecl (span, (node_id, false, Transparent, ty_params, ip :: inputs, [op], [], [eq], None)) 
    in 
    Call (pos, ty_args, node_id, e :: inputs_call), decl :: gen_nodes1 @ gen_nodes2 
  | A.ChooseOp (pos, (_, id, ty), expr1)
  | A.AnyOp (pos, (_, id, ty), expr1) -> 
    let expr1, gen_nodes = rec_call expr1 in
    let ty, ty_gen_nodes = desugar_type ctx node_name fun_ids ty in
    let span = { A.start_pos = pos; A.end_pos = pos } in
    let contract = 
      [A.Guarantee (AH.pos_of_expr expr1, None, false, expr1)] 
    in
    let inputs =
      let vars_of_expr1 = AH.vars_without_node_call_ids expr1 in
      let vars_of_exprs =
        Ctx.SI.diff vars_of_expr1 (Ctx.SI.singleton id)
      in 
      Ctx.SI.union vars_of_exprs (AH.vars_of_type ty) |> Ctx.SI.elements
    in
    (* Global constants don't need to be passed as arguments to generated nodes *)
    let inputs = List.filter (fun i -> 
      match Ctx.lookup_const ctx i with 
        | Some (_, _, Ctx.Global) -> false 
        | _ -> true
    ) inputs in 
    let inputs_call = List.map (fun str -> A.Ident (pos, str)) inputs in
    let ctx = Ctx.add_ty ctx id ty in
    let inputs = List.map (fun input -> (pos, input, Ctx.lookup_ty ctx input, A.ClockTrue)) inputs in
    let inputs = List.map (fun (p, inp, opt, cl) -> match opt with 
      | Some ty -> 
        let is_const = match Ctx.lookup_const ctx inp with | Some _ -> true | None -> false in
        p, inp, ty, cl, is_const 
      | None -> assert false
    ) inputs in
    (* The generated imported node might be polymorphic, so we find all the needed type variables *)
    let ty_params = 
      Ctx.SI.union (Ctx.ty_vars_of_type ctx node_name ty) 
                   (Ctx.ty_vars_of_expr ctx node_name expr1)
      |> Ctx.SI.elements
    in 
    let ty_vars = List.map (fun id -> A.UserType (pos, [], id)) ty_params in
    let generated_node, name = match expr with 
    | AnyOp _ -> 
        (* `any` operators are nondeterministic *)
        let name = mk_fresh_fn_name pos node_name Any in
        A.NodeDecl (span, 
        (name, true, A.Opaque, ty_params, inputs,
        [pos, id, ty, A.ClockTrue], [], [], Some (pos, contract))), 
        name
    | ChooseOp _ -> 
        (* `choose` operators are deterministic *)
        let name = mk_fresh_fn_name pos node_name Choose in
        A.FuncDecl (span, 
        (name, true, A.Opaque, ty_params, inputs,
        [pos, id, ty, A.ClockTrue], [], [], Some (pos, contract)), { is_lemma = false; is_rec = false }), 
        name
    | _ -> assert false
    in
    A.Call(pos, ty_vars, name, inputs_call), gen_nodes @ ty_gen_nodes @ [generated_node]

  | Ident _ as e -> e, []
  | ModeRef (_, _) as e -> e, []
  | A.EmptySet (pos, None) -> A.EmptySet (pos, None), []
  | A.EmptySet (pos, Some ty) ->
    let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
    A.EmptySet (pos, Some ty), gen_nodes
  | A.EmptyMap (pos, None) -> A.EmptyMap (pos, None), []
  | A.EmptyMap (pos, Some (kt, vt)) ->
    let kt', gen_nodes1 = desugar_type ctx node_name fun_ids kt in
    let vt', gen_nodes2 = desugar_type ctx node_name fun_ids vt in
    A.EmptyMap (pos, Some (kt', vt')), gen_nodes1 @ gen_nodes2
  | Const (_, _) as e -> e, []
  | RecordProject (pos, e, idx) -> 
    let e, gen_nodes = rec_call e in
    RecordProject (pos, e, idx), gen_nodes
  | UnaryOp (pos, op, e) -> 
    let e, gen_nodes = rec_call e in
    UnaryOp (pos, op, e), gen_nodes
  | BinaryOp (pos, op, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    BinaryOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
  | TernaryOp (pos, op, e1, e2, e3) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    let e3, gen_nodes3 = rec_call e3 in
    TernaryOp (pos, op, e1, e2, e3), gen_nodes1 @ gen_nodes2 @ gen_nodes3
  | ConvOp (pos, op, e) -> 
    let e, gen_nodes = rec_call e in
    ConvOp (pos, op, e), gen_nodes
  | CompOp (pos, op, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    CompOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
  | Extract (pos, e, ub, lb) -> 
    let e, gen_nodes = rec_call e in 
    Extract (pos, e, ub, lb), gen_nodes
  | RecordExpr (pos, ident, ps, expr_list) ->
    let ps, gen_nodes_ty = List.map (desugar_type ctx node_name fun_ids) ps |> List.split in
    let id_list, exprs_gen_nodes = 
      List.map (fun (i, e) -> (i, (rec_call) e)) expr_list |> List.split 
    in
    let expr_list, gen_nodes = List.split exprs_gen_nodes in
    RecordExpr (pos, ident, ps, List.combine id_list expr_list), List.flatten gen_nodes_ty @ List.flatten gen_nodes
  | GroupExpr (pos, kind, expr_list) ->
    let expr_list, gen_nodes = List.map (rec_call) expr_list |> List.split in
    GroupExpr (pos, kind, expr_list), List.flatten gen_nodes
  | StructUpdate (pos, e1, idx, Some e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    StructUpdate (pos, e1, idx, Some e2), gen_nodes1 @ gen_nodes2
  | StructUpdate (pos, e, idx, None) ->
    let e, gen_nodes = rec_call e in
    StructUpdate (pos, e, idx, None), gen_nodes 
  | ArrayConstr (pos, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    ArrayConstr (pos, e1, e2), gen_nodes1 @ gen_nodes2
  | IndexAccess (pos, e1, e2, kind) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    IndexAccess (pos, e1, e2, kind), gen_nodes1 @ gen_nodes2
  | Quantifier (pos, kind, tis , e) ->
    let tis, gen_nodes_ty = List.map (fun (p, id, ty) ->
      let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
      (p, id, ty), gen_nodes
    ) tis |> List.split in
    let e, gen_nodes = rec_call e in
    Quantifier (pos, kind, tis, e), List.flatten gen_nodes_ty @ gen_nodes
  | When (pos, e, clock) -> 
    let e, gen_nodes = rec_call e in
    When (pos, e, clock), gen_nodes
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    let expr_list1, gen_nodes3 = List.map rec_call expr_list1 |> List.split in
    let expr_list2, gen_nodes4 = List.map rec_call expr_list2 |> List.split in
    Condact (pos, e1, e2, id, expr_list1, expr_list2), gen_nodes1 @ gen_nodes2 @ 
                                                      List.flatten gen_nodes3 @ List.flatten gen_nodes4
  | Activate (pos, ident, e1, e2, expr_list) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    Activate (pos, ident, e1, e2, expr_list), gen_nodes1 @ gen_nodes2
  | Merge (pos, ident, expr_list) ->
    let id_list, exprs_gen_nodes = 
      List.map (fun (i, e) -> (i, (rec_call) e)) expr_list |> List.split 
    in
    let expr_list, gen_nodes = List.split exprs_gen_nodes in
    Merge (pos, ident, List.combine id_list expr_list), List.flatten gen_nodes
  | RestartEvery (pos, ident, expr_list, e) ->
    let expr_list, gen_nodes1 = List.map (rec_call) expr_list |> List.split in
    let e, gen_nodes2 = rec_call e in
    RestartEvery (pos, ident, expr_list, e), List.flatten gen_nodes1 @ gen_nodes2
  | Pre (pos, e) -> 
    let e, gen_nodes = rec_call e in
    Pre (pos, e), gen_nodes
  | Arrow (pos, e1, e2) -> 
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    Arrow (pos, e1, e2), gen_nodes1 @ gen_nodes2
  | Call (pos, ty_args, id, expr_list) ->
    let ty_args, gen_nodes_ty = List.map (desugar_type ctx node_name fun_ids) ty_args |> List.split in
    let expr_list, gen_nodes = List.map rec_call expr_list |> List.split in
    Call (pos, ty_args, id, expr_list), List.flatten gen_nodes_ty @ List.flatten gen_nodes

let desugar_contract_item: Ctx.tc_context -> NI.t -> NI.t list -> A.contract_node_equation -> A.contract_node_equation * A.declaration list =
fun ctx node_name fun_ids ci ->
  let rec_call = desugar_expr ctx node_name fun_ids in
  match ci with
  | A.GhostVars (pos, lhs, e) ->
    let lhs, gen_nodes_ty = match lhs with
      | A.GhostVarDec (p, tis) ->
          let tis, gen_nodes_ty = List.map (fun (p, id, ty) ->
            let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
            (p, id, ty), gen_nodes
          ) tis |> List.split in
          A.GhostVarDec (p, tis), List.flatten gen_nodes_ty
    in
    let e, gen_nodes = rec_call e in
    A.GhostVars (pos, lhs, e), gen_nodes_ty @ gen_nodes
  | Assume (pos, name, b, e) ->
    let e, gen_nodes = rec_call e in 
    Assume (pos, name, b, e), gen_nodes
  | Guarantee (pos, name, b, e) -> 
    let e, gen_nodes = rec_call e in 
    Guarantee (pos, name, b, e), gen_nodes
  | Decreases (pos, e) ->
    let e, gen_nodes = rec_call e in
    Decreases (pos, e), gen_nodes
  | Mode (pos, i, reqs, enss) ->
    let (reqs, gen_nodes1) = 
      List.map (fun (pos, id, expr) -> (pos, id, rec_call expr)) reqs |> 
      List.map (fun (pos, id, (expr, decls)) -> ((pos, id, expr), decls)) |> 
      List.split in 
    let (enss, gen_nodes2) = 
      List.map (fun (pos, id, expr) -> (pos, id, rec_call expr)) enss |> 
      List.map (fun (pos, id, (expr, decls)) -> ((pos, id, expr), decls)) |> 
      List.split in 
    Mode (pos, i, reqs, enss), (List.flatten gen_nodes1) @ (List.flatten gen_nodes2)
  | ContractCall (pos, i, ty_args, exprs, ids) ->
    let ty_args, gen_nodes_ty = List.map (desugar_type ctx node_name fun_ids) ty_args |> List.split in
    let (exprs, gen_nodes) = List.map rec_call exprs |> List.split in
    ContractCall (pos, i, ty_args, exprs, ids), List.flatten gen_nodes_ty @ List.flatten gen_nodes
  | A.GhostConst (A.FreeConst (pos, id, ty)) ->
    let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
    A.GhostConst (A.FreeConst (pos, id, ty)), gen_nodes
  | A.GhostConst (A.TypedConst (pos, id, e, ty)) ->
    let ty, gen_nodes_ty = desugar_type ctx node_name fun_ids ty in
    let e, gen_nodes = rec_call e in
    A.GhostConst (A.TypedConst (pos, id, e, ty)), gen_nodes_ty @ gen_nodes
  | A.GhostConst (A.UntypedConst (pos, id, e)) ->
    let e, gen_nodes = rec_call e in
    A.GhostConst (A.UntypedConst (pos, id, e)), gen_nodes
  | AssumptionVars _ as ci -> ci, []

let desugar_contract: Ctx.tc_context -> NI.t -> NI.t list -> A.contract option -> A.contract option * A.declaration list =
fun ctx node_name fun_ids contract -> 
  match contract with 
  | Some (pos, contract_items) -> 
    let items, gen_nodes = (List.map (desugar_contract_item ctx node_name fun_ids) contract_items) |> List.split in
    Some (pos, items), List.flatten gen_nodes
  | None -> None, []

let rec desugar_node_item: Ctx.tc_context -> NI.t -> NI.t list -> A.node_item -> A.node_item * A.declaration list =
fun ctx node_name fun_ids ni ->
  let rec_call = desugar_node_item ctx node_name fun_ids in
  match ni with
  | A.Body (Equation (pos, lhs, rhs)) -> 
    let rhs, gen_nodes = desugar_expr ctx node_name fun_ids rhs in 
    A.Body (Equation (pos, lhs, rhs)), gen_nodes
  | AnnotProperty (pos, name, e, k) -> 
    let e, gen_nodes = desugar_expr ctx node_name fun_ids e in 
    AnnotProperty(pos, name, e, k), gen_nodes
  | IfBlock (pos, cond, nis1, nis2) -> 
    let nis1, gen_nodes1 = List.map rec_call nis1 |> List.split in
    let nis2, gen_nodes2 = List.map rec_call nis2 |> List.split in
    let cond, gen_nodes3 = desugar_expr ctx node_name fun_ids cond in
    A.IfBlock (pos, cond, nis1, nis2), List.flatten gen_nodes1 @ List.flatten gen_nodes2 @ gen_nodes3
  | WhenBlock (pos, cond, nis1, nis2) ->
    let nis1, gen_nodes1 = List.map rec_call nis1 |> List.split in
    let nis2, gen_nodes2 = List.map rec_call nis2 |> List.split in
    let cond, gen_nodes3 = desugar_expr ctx node_name fun_ids cond in
    A.WhenBlock (pos, cond, nis1, nis2), List.flatten gen_nodes1 @ List.flatten gen_nodes2 @ gen_nodes3
  | FrameBlock (pos, vars, nes, nis) -> 
    let nes = List.map (fun x -> A.Body x) nes in
    let nes, gen_nodes1 = List.map rec_call nes |> List.split in
    let nes = List.map (fun ne -> match ne with
      | A.Body (A.Equation _ as eq) -> eq
      | _ -> assert false
    ) nes in
    let nis, gen_nodes2 = List.map rec_call nis |> List.split in
    FrameBlock(pos, vars, nes, nis), List.flatten gen_nodes1 @ List.flatten gen_nodes2
  | Body (Assert (pos, e)) ->
    let e, gen_nodes = desugar_expr ctx node_name fun_ids e in 
    Body (Assert (pos, e)), gen_nodes
  | AnnotMain _ -> ni, []
    

let gen_nodes: Ctx.tc_context -> A.declaration list -> A.declaration list = 
fun ctx decls -> 
  let fun_ids = List.filter_map 
    (fun decl -> match decl with | A.FuncDecl (_, (id, _, _, _, _, _, _, _, _), _) -> Some id | _ -> None)
    decls 
  in
  let decls =
  List.fold_left (fun decls decl ->
    match decl with
    | A.NodeDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract)) ->
      let ctx = Chk.add_full_node_ctx ctx id params inputs outputs locals in
      let inputs, gen_nodes_in = List.map (fun (p, id', ty, c, b) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c, b), gen_nodes
      ) inputs |> List.split in
      let outputs, gen_nodes1 = List.map (fun (p, id', ty, c) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c), gen_nodes
      ) outputs |> List.split in
      let locals, gen_nodes_loc = List.map (function
        | A.NodeVarDecl (pos, (p, id', ty, c)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeVarDecl (pos, (p, id', ty, c)), gen_nodes
        | A.NodeConstDecl (pos, A.FreeConst (_, id', ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.FreeConst (pos, id', ty)), gen_nodes
        | A.NodeConstDecl (pos, A.TypedConst (_, id', e, ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.TypedConst (pos, id', e, ty)), gen_nodes
        | A.NodeConstDecl (pos, (A.UntypedConst _ as cd)) ->
            A.NodeConstDecl (pos, cd), []
      ) locals |> List.split in
      let items, gen_nodes2 = List.map (desugar_node_item ctx id fun_ids) items |> List.split in
      let contract, gen_nodes3 = desugar_contract ctx id fun_ids contract in
      let gen_nodes = List.flatten gen_nodes_in @ List.flatten gen_nodes1 @ List.flatten gen_nodes_loc @ List.flatten gen_nodes2 @ gen_nodes3 in
      decls @ gen_nodes @ [A.NodeDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract))] 
    | A.FuncDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract), is_rec) ->
      let ctx = Chk.add_full_node_ctx ctx id params inputs outputs locals in
      let inputs, gen_nodes_in = List.map (fun (p, id', ty, c, b) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c, b), gen_nodes
      ) inputs |> List.split in
      let outputs, gen_nodes_out = List.map (fun (p, id', ty, c) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c), gen_nodes
      ) outputs |> List.split in
      let locals, gen_nodes_loc = List.map (function
        | A.NodeVarDecl (pos, (p, id', ty, c)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeVarDecl (pos, (p, id', ty, c)), gen_nodes
        | A.NodeConstDecl (pos, A.FreeConst (_, id', ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.FreeConst (pos, id', ty)), gen_nodes
        | A.NodeConstDecl (pos, A.TypedConst (_, id', e, ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.TypedConst (pos, id', e, ty)), gen_nodes
        | A.NodeConstDecl (pos, (A.UntypedConst _ as cd)) ->
            A.NodeConstDecl (pos, cd), []
      ) locals |> List.split in
      let items, gen_nodes = List.map (desugar_node_item ctx id fun_ids) items |> List.split in
      let contract, gen_nodes2 = desugar_contract ctx id fun_ids contract in
      let gen_nodes = 
        List.flatten gen_nodes_in @ List.flatten gen_nodes_out @ List.flatten gen_nodes_loc @ List.flatten gen_nodes 
      in
      decls @ gen_nodes @ gen_nodes2 @
      [A.FuncDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract), is_rec)]
    | A.ContractNodeDecl (span, (id, params, inputs, outputs, contract)) ->
      let ctx = Chk.add_io_node_ctx ctx id params inputs outputs in
      let inputs, gen_nodes_in = List.map (fun (p, id', ty, c, b) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c, b), gen_nodes
      ) inputs |> List.split in
      let outputs, gen_nodes_out = List.map (fun (p, id', ty, c) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c), gen_nodes
      ) outputs |> List.split in
      let contract, gen_nodes = desugar_contract ctx id fun_ids (Some contract) in
      let contract = match contract with
      | Some contract -> contract
      | None -> assert false in (* Must have a contract *)
      let gen_nodes = List.flatten gen_nodes_in @ List.flatten gen_nodes_out @ gen_nodes in
      decls @ gen_nodes @ [A.ContractNodeDecl (span, (id, params, inputs, outputs, contract))] 
    | decl -> decl :: decls
  ) [] decls in 
  decls
