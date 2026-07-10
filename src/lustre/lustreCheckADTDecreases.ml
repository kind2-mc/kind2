(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(* Static termination check for functions with ADT decreases clauses.
   For each recursive call f(args) inside such a function, we verify that
   t_callee[callee_formals := args] is a strict syntactic subterm of t,
   where t is the caller's decreases expression. This check runs after Match
   desugaring so pattern variables have already been expanded to selector
   chains (FieldProject nodes). *)

module LA = LustreAst
module LH = LustreAstHelpers
module Chk = LustreTypeChecker
module LDAT = LustreDesugarADTs
module HStringMap = HString.HStringMap
module NI = NodeId

let (let*) = Res.(>>=)

type error_kind =
  | NotAStructuralSubterm of LA.expr * LA.expr
  (* (substituted callee measure, caller measure) *)

type error = [`LustreCheckADTDecreasesError of Lib.position * error_kind]

let error_message = function
  | NotAStructuralSubterm (callee_m, caller_m) ->
    Format.asprintf
      "Recursive call does not structurally decrease the measure: \
       '%a' is not a strict subterm of '%a'"
      LA.pp_print_expr callee_m LA.pp_print_expr caller_m

let check_error pos kind = Error (`LustreCheckADTDecreasesError (pos, kind))

(* Position-independent expression equality via string rendering. *)
let expr_equal e1 e2 = LA.string_of_expr e1 = LA.string_of_expr e2

(* t' ⊏ t: t' is a strict syntactic subterm of t.
   Strips FieldProject layers from t'; true iff the chain ends exactly at t. *)
let rec is_strict_subterm base t' =
  match t' with
  | LA.FieldProject (_, inner, _, _) ->
    expr_equal inner base || is_strict_subterm base inner
  | _ -> false

(* Extract the decreases expression from a contract, if any. *)
let get_decreases = function
  | None -> None
  | Some (_, items) ->
    List.fold_left (fun acc item ->
      match item with
      | LA.Decreases (_, e) -> Some e
      | _ -> acc
    ) None items

(* Check whether the type of e is a recursive ADT according to adt_map. *)
let is_adt_decreases ctx adt_map e =
  match Chk.infer_type_expr ctx None e with
  | Error _ -> false
  | Ok (ty, _, _) ->
    match Chk.expand_type_syn_reftype_history ctx ty with
    | Error _ -> false
    | Ok ty_exp ->
      let name_opt = match ty_exp with
        | LA.UserType (_, _, n) | LA.ADT (_, n, _) -> Some n
        | _ -> None
      in
      match name_opt with
      | Some n ->
        (match HStringMap.find_opt n adt_map with
        | Some info -> info.LDAT.is_recursive
        | None -> false)
      | None -> false

(* Collect all (pos, callee_id, args) for calls in the same SCC as
   caller_scc, by walking all sub-expressions. *)
let rec collect_rec_calls scc_map caller_scc expr =
  let go = collect_rec_calls scc_map caller_scc in
  let go_list es = List.concat_map go es in
  match expr with
  | LA.Call (pos, _ty_args, callee_id, args) ->
    let callee_name = NI.get_internal_name callee_id in
    let in_scc = match HStringMap.find_opt callee_name scc_map with
      | Some id -> id = caller_scc
      | None -> false
    in
    let sub = go_list args in
    if in_scc then (pos, callee_id, args) :: sub else sub
  | LA.Ident _ | LA.ModeRef _ | LA.Const _
  | LA.Last _ | LA.EmptySet _ | LA.EmptyMap _ -> []
  | LA.Pre (_, e) | LA.UnaryOp (_, _, e) | LA.ConvOp (_, _, e)
  | LA.TypeAscription (_, e, _) | LA.When (_, e, _)
  | LA.FieldProject (_, e, _, _) | LA.ADTTester (_, e, _)
  | LA.AnyOp (_, _, e) | LA.ChooseOp (_, _, e)
  | LA.Quantifier (_, _, _, e) | LA.Extract (_, e, _, _) -> go e
  | LA.Arrow (_, e1, e2) | LA.BinaryOp (_, _, e1, e2)
  | LA.CompOp (_, _, e1, e2) | LA.ArrayConstr (_, e1, e2) -> go_list [e1; e2]
  | LA.TernaryOp (_, _, e1, e2, e3) -> go_list [e1; e2; e3]
  | LA.GroupExpr (_, _, es) | LA.ADTTerm (_, _, _, es) -> go_list es
  | LA.RecordExpr (_, _, _, flds) -> go_list (List.map snd flds)
  | LA.StructUpdate (_, e, _, Some e2) -> go_list [e; e2]
  | LA.StructUpdate (_, e, _, None) -> go e
  | LA.IndexAccess (_, e1, e2, _) -> go_list [e1; e2]
  | LA.Condact (_, e1, e2, _, es1, es2) -> go_list ([e1; e2] @ es1 @ es2)
  | LA.Activate (_, _, e1, e2, es) -> go_list ([e1; e2] @ es)
  | LA.Merge (_, _, cases) -> go_list (List.map snd cases)
  | LA.RestartEvery (_, _, es, e) -> go_list (e :: es)
  | LA.Match (_, e, arms, _) -> go_list (e :: List.map snd arms)

let rec collect_rec_calls_items scc_map caller_scc items =
  let go_items = collect_rec_calls_items scc_map caller_scc in
  let go_expr = collect_rec_calls scc_map caller_scc in
  List.concat_map (fun item -> match item with
    | LA.Body (LA.Assert (_, e)) -> go_expr e
    | LA.Body (LA.Equation (_, _, e)) -> go_expr e
    | LA.AnnotProperty _ -> []
    | LA.IfBlock (_, e, items1, items2) ->
      go_expr e @ go_items items1 @ go_items items2
    | LA.WhenBlock (_, e, items1, items2) ->
      go_expr e @ go_items items1 @ go_items items2
    | LA.FrameBlock (_, _, eqs, sub_items) ->
      let eq_calls = List.concat_map (fun eq -> match eq with
        | LA.Equation (_, _, e) -> go_expr e
        | LA.Assert (_, e) -> go_expr e) eqs in
      eq_calls @ go_items sub_items
    | LA.AnnotMain _ | LA.Auto _ -> []
  ) items

(* Build a map from function name → (formals, contract) for all FuncDecls. *)
let build_func_map decls =
  List.fold_left (fun m decl ->
    match decl with
    | LA.FuncDecl (_, (fname, _, _, _, inputs, _, _, _, contract), _) ->
      let formals = List.map (fun ip -> LH.extract_ip_ty ip |> fst) inputs in
      HStringMap.add (NI.get_internal_name fname) (formals, contract) m
    | _ -> m
  ) HStringMap.empty decls

(* Substitute callee_formals with actuals in expr, using intermediate
   placeholders to avoid variable-capture in simultaneous substitution. *)
let substitute_formals callee_formals actuals expr =
  let placeholders = List.mapi
    (fun i _ -> HString.mk_hstring (Format.sprintf ".adt_rec_%d" i))
    callee_formals
  in
  let to_placeholders =
    List.fold_left2
      (fun e formal ph -> LH.substitute_naive formal (LA.Ident (Lib.dummy_pos, ph)) e)
      expr callee_formals placeholders
  in
  List.fold_left2
    (fun e ph actual -> LH.substitute_naive ph actual e)
    to_placeholders placeholders actuals

(* Check one recursive FuncDecl. *)
let check_func_decl ctx adt_map scc_map func_map decl =
  match decl with
  | LA.FuncDecl (_, (fname_id, _, _, ty_params, inputs, outputs, locals, items, contract), { LA.is_rec = true; _ }) -> (
    let fname = NI.get_internal_name fname_id in
    (* Build a context that includes this function's parameters so that
       infer_type_expr can type-check the decreases expression. *)
    let local_ctx =
      Chk.add_full_node_ctx ctx fname_id ty_params inputs outputs locals
    in
    match get_decreases contract with
    | None -> Ok ()
    | Some t ->
      if not (is_adt_decreases local_ctx adt_map t) then Ok ()
      else
        let caller_scc = match HStringMap.find_opt fname scc_map with
          | Some id -> id
          | None -> assert false
        in
        let rec_calls = collect_rec_calls_items scc_map caller_scc items in
        let check_call (pos, callee_id, args) =
          let callee_name = NI.get_internal_name callee_id in
          match HStringMap.find_opt callee_name func_map with
          | None -> Ok ()
          | Some (callee_formals, callee_contract) ->
            match get_decreases callee_contract with
            | None -> Ok ()
            | Some t_callee ->
              let substituted = substitute_formals callee_formals args t_callee in
              if is_strict_subterm t substituted then Ok ()
              else check_error pos (NotAStructuralSubterm (substituted, t))
        in
        let* _ = Res.seq (List.map check_call rec_calls) in
        Ok ()
  )
  | _ -> Ok ()

let check ctx adt_map scc_map decls =
  let func_map = build_func_map decls in
  let* _ = Res.seq (List.map (check_func_decl ctx adt_map scc_map func_map) decls) in
  Ok decls
