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
   where t is the caller's decreases expression. *)

module LA = LustreAst
module LH = LustreAstHelpers
module Chk = LustreTypeChecker
module LDAT = LustreDesugarADTs
module HStringMap = HString.HStringMap
module HStringSet = HString.HStringSet
module NI = NodeId

let (let*) = Res.(>>=)

type error_kind =
  | NotAStructuralSubterm of LA.expr * LA.expr
  (* (substituted callee measure, caller measure) *)
  | MixedDecreasesKindsInScc of LA.ident list

type error = [`LustreCheckADTDecreasesError of Lib.position * error_kind]

let error_message = function
  | NotAStructuralSubterm (callee_m, caller_m) ->
    Format.asprintf
      "Recursive call does not structurally decrease the measure: \
       '%a' is not a strict subterm of '%a' (only a variable bound by an \
       enclosing match's constructor pattern can witness a structural \
       decrease; a bare field selector cannot)"
      LA.pp_print_expr callee_m LA.pp_print_expr caller_m
  | MixedDecreasesKindsInScc ids ->
    "Mutually recursive functions "
    ^ (Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids)
    ^ " must all use the same kind of decreases measure (either all integer, \
       or all algebraic data type); mixing kinds within one mutually \
       recursive group is not supported"

let check_error pos kind = Error (`LustreCheckADTDecreasesError (pos, kind))

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
let is_adt_decreases ctx adt_map nname e =
  match Chk.infer_type_expr ctx (Some nname) e with
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

(* All variable names a pattern binds, at any depth (both a top-level
   VarPat's own name and every name nested inside a constructor Pat). *)
let rec pattern_bound_vars pat =
  match pat with
  | LA.VarPat (_, id) -> [id]
  | LA.Pat (_, _, subpats) -> List.concat_map pattern_bound_vars subpats

(* Whether it's safe to match on `scrut` and trust its pattern's bindings:
   true when `scrut` is caller_measure `t` itself (the base case), or when
   `scrut` is already in `safe_env`, i.e. previously established as a
   strict subterm of `t` by an earlier match. *)
let scrutinee_is_safe caller_measure shadowed safe_env scrut =
  ((LH.syn_expr_equal None scrut caller_measure |> Result.get_ok)
   && not (LA.SI.exists (fun v -> HStringSet.mem v shadowed)
             (LH.vars_without_node_call_ids caller_measure)))
  || (match scrut with
      | LA.Ident (_, v) -> HStringSet.mem v safe_env
      | _ -> false)

(* Collect all (pos, callee_id, args, safe_env) for calls in the same SCC as
   caller_scc, by walking all sub-expressions. `safe_env` is the set of
   variables, in scope at each point, known to be strict structural subterms
   of `caller_measure`. `shadowed` is the set of variable names rebound by
   any enclosing pattern so far, safe or not -- used only to invalidate
   scrutinee_is_safe's "is t itself" case when t's own name has been
   shadowed. *)
let rec collect_rec_calls scc_map caller_scc caller_measure shadowed safe_env expr =
  let go = collect_rec_calls scc_map caller_scc caller_measure shadowed safe_env in
  let go_list es = List.concat_map go es in
  match expr with
  | LA.Call (pos, _ty_args, callee_id, args) ->
    let callee_name = NI.get_internal_name callee_id in
    let in_scc = match HStringMap.find_opt callee_name scc_map with
      | Some id -> id = caller_scc
      | None -> false
    in
    let sub = go_list args in
    if in_scc then (pos, callee_id, args, safe_env) :: sub else sub
  | LA.Match (_, scrut, arms, _) ->
    let scrut_calls = go scrut in
    let scrut_safe = scrutinee_is_safe caller_measure shadowed safe_env scrut in
    (* Whether scrut is itself already an established strict subterm *)
    let scrut_is_safe_alias =
      match scrut with
      | LA.Ident (_, v) -> HStringSet.mem v safe_env
      | _ -> false
    in
    let arm_calls = List.concat_map (fun (pat, body) ->
      let bound = pattern_bound_vars pat in
      let arm_shadowed =
        List.fold_left (fun s v -> HStringSet.add v s) shadowed bound
      in
      let arm_env =
        match pat with
        | LA.VarPat (_, x) ->
          if scrut_is_safe_alias then HStringSet.add x safe_env
          else HStringSet.remove x safe_env
        | LA.Pat (_, _, _) ->
          if scrut_safe then
            List.fold_left (fun s v -> HStringSet.add v s) safe_env bound
          else
            (* The pattern's own bindings are not safe here (the scrutinee
               isn't), and may shadow a same-named variable that *is* safe
               in the outer scope. *)
            List.fold_left (fun s v -> HStringSet.remove v s) safe_env bound
      in
      collect_rec_calls scc_map caller_scc caller_measure arm_shadowed arm_env body
    ) arms in
    scrut_calls @ arm_calls
  | LA.Ident _ | LA.ModeRef _ | LA.Const _
  | LA.Last _ | LA.EmptySet _ | LA.EmptyMap _ | LA.AbstractSymConst _ -> []
  | LA.Pre (_, e) | LA.UnaryOp (_, _, e) | LA.ConvOp (_, _, e)
  | LA.TypeAscription (_, e, _) | LA.When (_, e, _)
  | LA.FieldProject (_, e, _, _) | LA.ADTTester (_, e, _)
  | LA.AnyOp (_, _, e) | LA.ChooseOp (_, _, e)
  | LA.Extract (_, e, _, _) -> go e
  | LA.Quantifier (_, _, qs, e) ->
    (* The quantifier's own bound names shadow any same-named outer
       binding, exactly as a match arm's pattern bindings do (see the
       Match case above): they must be added to shadowed and removed from
       safe_env before recursing into the body. *)
    let bound = List.map (fun (_, i, _) -> i) qs in
    let shadowed = List.fold_left (fun s v -> HStringSet.add v s) shadowed bound in
    let safe_env = List.fold_left (fun s v -> HStringSet.remove v s) safe_env bound in
    collect_rec_calls scc_map caller_scc caller_measure shadowed safe_env e
  | LA.Arrow (_, e1, e2) | LA.BinaryOp (_, _, e1, e2)
  | LA.CompOp (_, _, e1, e2) | LA.ArrayConstr (_, e1, e2) -> go_list [e1; e2]
  | LA.TernaryOp (_, _, e1, e2, e3) -> go_list [e1; e2; e3]
  | LA.GroupExpr (_, _, es) | LA.ADTTerm (_, _, _, es) -> go_list es
  | LA.RecordExpr (_, _, _, flds) -> go_list (List.map snd flds)
  | LA.StructUpdate (_, e, idx, e2_opt) ->
    let idx_calls = LH.fold_label_or_index [] (@) go idx in
    let rest = match e2_opt with
      | Some e2 -> go_list [e; e2]
      | None -> go e
    in
    idx_calls @ rest
  | LA.IndexAccess (_, e1, e2, _) -> go_list [e1; e2]
  | LA.Condact (_, e1, e2, _, es1, es2) -> go_list ([e1; e2] @ es1 @ es2)
  | LA.Activate (_, _, e1, e2, es) -> go_list ([e1; e2] @ es)
  | LA.Merge (_, _, cases) -> go_list (List.map snd cases)
  | LA.RestartEvery (_, _, es, e) -> go_list (e :: es)

let rec collect_rec_calls_items scc_map caller_scc caller_measure shadowed safe_env items =
  let go_items = collect_rec_calls_items scc_map caller_scc caller_measure shadowed safe_env in
  let go_expr = collect_rec_calls scc_map caller_scc caller_measure shadowed safe_env in
  List.concat_map (fun item -> match item with
    | LA.Body (LA.Assert (_, e)) -> go_expr e
    | LA.Body (LA.Equation (_, _, e)) -> go_expr e
    | LA.AnnotProperty (_, _, e, kind) ->
      go_expr e @ (match kind with
        | LA.Provided e2 -> go_expr e2
        | LA.Invariant | LA.Reachable _ -> [])
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

(* Whether decl's decreases measure is ADT-typed; None if decl is not a
   rec FuncDecl with a decreases clause. *)
let adt_decreases_kind ctx adt_map decl =
  match decl with
  | LA.FuncDecl (_, (fname_id, _, _, ty_params, inputs, outputs, locals, _, contract),
                 { LA.is_rec = true; _ }) -> (
    match get_decreases contract with
    | None -> None
    | Some t ->
      let local_ctx = Chk.add_full_node_ctx ctx fname_id ty_params inputs outputs locals in
      Some (is_adt_decreases local_ctx adt_map fname_id t)
  )
  | _ -> None

(* Reject a mutually recursive group (SCC) whose members don't all use the
   same kind of decreases measure. Mixing an integer measure (verified
   dynamically, as an SMT proof obligation) with an ADT measure (verified
   statically, see above) in one SCC would leave the edge from an
   integer-measured caller into an ADT-measured callee unchecked by either
   mechanism. *)
let check_consistent_scc_kinds ctx adt_map scc_map decls =
  let entries = List.filter_map (fun decl ->
    match decl, adt_decreases_kind ctx adt_map decl with
    | LA.FuncDecl (span, (fname_id, _, _, _, _, _, _, _, _), _), Some is_adt ->
      let fname = NI.get_internal_name fname_id in
      (match HStringMap.find_opt fname scc_map with
      | Some scc_id -> Some (scc_id, (span.LA.start_pos, NI.get_user_name fname_id, is_adt))
      | None -> None)
    | _ -> None
  ) decls in
  let groups = List.fold_left (fun acc (scc_id, entry) ->
    let prev = match List.assoc_opt scc_id acc with Some l -> l | None -> [] in
    (scc_id, entry :: prev) :: List.remove_assoc scc_id acc
  ) [] entries in
  Res.seq_ (List.map (fun (_, members) ->
    match members with
    | [] | [_] -> Ok ()
    | (_, _, k0) :: _ ->
      if List.for_all (fun (_, _, k) -> k = k0) members then Ok ()
      else
        let pos, _, _ = List.hd members in
        let ids = List.map (fun (_, id, _) -> id) members in
        check_error pos (MixedDecreasesKindsInScc ids)
  ) groups)

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
   placeholders to avoid variable-capture in simultaneous substitution.
   Caller must ensure callee_formals and actuals have equal length. *)
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

(* Positionally align callee_formals against the syntactic call args,
   accounting for a single argument expanding to several formals (e.g. a
   call to a multi-output node passed directly as one argument). *)
let rec align_formals_to_args ctx formals args =
  match formals, args with
  | [], _ -> []
  | _, [] -> assert false
  | _, arg :: rest_args ->
    let arity = TypeCheckerContext.arity_of_expr ctx arg in
    let taken, remaining_formals = Lib.list_split arity formals in
    let mapped = List.map (fun f -> (f, arg, arity = 1)) taken in
    mapped @ align_formals_to_args ctx remaining_formals rest_args

(* Whether `e`, once the callee's decreases measure has been substituted with
   the caller's actual arguments, witnesses a genuine structural decrease:
   exactly a variable bound (transitively) by an enclosing match's
   constructor pattern -- never a bare field projection or any other shape,
   which could be unconstrained in SMT if the guard doesn't actually hold. *)
let is_strict_decrease safe_env = function
  | LA.Ident (_, v) -> HStringSet.mem v safe_env
  | _ -> false

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
    | None -> assert false
    | Some t ->
      if not (is_adt_decreases local_ctx adt_map fname_id t) then Ok ()
      else
        match HStringMap.find_opt fname scc_map with
        | None -> Ok ()
        | Some caller_scc ->
          let rec_calls =
            collect_rec_calls_items scc_map caller_scc t HStringSet.empty HStringSet.empty items
          in
          let check_call (pos, callee_id, args, safe_env) =
            let callee_name = NI.get_internal_name callee_id in
            match HStringMap.find_opt callee_name func_map with
            | None -> assert false
            | Some (callee_formals, callee_contract) ->
              match get_decreases callee_contract with
              | None -> assert false
              | Some t_callee ->
                (* Only the formals t_callee actually mentions in its decreases
                   clause need a substitution at all. The type checker already
                   guarantees t_callee mentions nothing but the callee's own
                   formals (LustreTypeChecker.NonInputInADTDecreasesMeasure),
                   so every relevant name is guaranteed to align to some arg
                   below. *)
                let relevant = LH.vars_without_node_call_ids t_callee in
                let aligned = align_formals_to_args local_ctx callee_formals args in
                let relevant_aligned =
                  List.filter (fun (f, _, _) -> LA.SI.mem f relevant) aligned
                in
                if List.exists (fun (_, _, precise) -> not precise) relevant_aligned then
                  (* No precise per-formal value exists for a multi-output
                     argument (e.g. N(f()) where f() has 2+ outputs). *)
                  let (_, arg, _) =
                    List.find (fun (_, _, precise) -> not precise) relevant_aligned
                  in
                  check_error pos (NotAStructuralSubterm (arg, t))
                else
                  let relevant_formals, relevant_args =
                    List.map (fun (f, arg, _) -> (f, arg)) relevant_aligned |> List.split
                  in
                  let substituted = substitute_formals relevant_formals relevant_args t_callee in
                  if is_strict_decrease safe_env substituted then Ok ()
                  else check_error pos (NotAStructuralSubterm (substituted, t))
          in
          let* _ = Res.seq (List.map check_call rec_calls) in
          Ok ()
  )
  | _ -> Ok ()

let check ctx adt_map scc_map decls =
  let* () = check_consistent_scc_kinds ctx adt_map scc_map decls in
  let func_map = build_func_map decls in
  let* _ = Res.seq (List.map (check_func_decl ctx adt_map scc_map func_map) decls) in
  Ok decls
