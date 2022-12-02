(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

(** Normalize a Lustre AST to ease in translation to a transition system

  The two main requirements of this normalization are to:
    1. Guard any unguarded pre expressions 
    2. Generate any needed local identifiers or oracles

  Identifiers are constructed with a numeral prefix followed by a type suffix.
  e.g. 2_glocal or 6_oracle. These are not valid lustre identifiers and are
  expected to be transformed into indexes with the numeral as a branch and the
  suffix type as the leaf.

  Generated locals/oracles are referenced inside the AST via an Ident expression
  but the actual definition is not added to the AST. Instead it is recoreded in
  the generated_identifiers record.

  pre operators are explicitly guarded in the AST by an oracle variable
  if they were originally unguarded
    e.g. pre expr => oracle -> pre expr

  The following parts of the AST are abstracted by locals:

  1. Arguments to node calls that are not identifiers
    e.g.
      Node expr1 expr2 ... exprn
      =>
      Node l1 l2 ... ln
    where each li is a local variable and li = expri

  2. Arguments to the pre operator that are not identifiers
    e.g.
      pre expr => pre l
    where l = expr

  3. Node calls
    e.g.
      x1, ..., xn = ... op node_call(a, b, c) op ...
      => x1, ..., xn = ... op (l1, ..., ln) op ...
    where (l1, ..., ln) is a group (list) expression
      and each li corresponds to an output of the node_call
      If node_call has only one output, it is instead just an ident expression
    (Note that there is no generated equality here, how the node call is
      referenced at the stage of a LustreNode is by the node_call record where
      the output holds the state variables produced by the node call)

  4. Properties checked expression
  5. Assertions checked expression
  6. Condition of node calls (if it is not equivalent to true)
  7. Restarts of node calls (if it is not a constant)

     @author Andrew Marmaduke *)

open Lib
open GeneratedIdentifiers

module A = LustreAst
module AH = LustreAstHelpers
module AIC = LustreAstInlineConstants
module AI = LustreAbstractInterpretation
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

type error = [
  | `LustreAstNormalizerError
]

let (>>=) = Res.(>>=)
let unwrap result = match result with
  | Ok r -> r
  | Error e ->
    let msg = LustreErrors.error_message e in
    Log.log L_debug "(Lustre AST Normalizer Internal Error: %s)" msg;
    assert false


module AstCallHash = struct
  type t = A.ident (* node name *)
    * A.expr (* cond *)
    * A.expr (* restart *)
    * A.expr list (* arguments (which are already abstracted) *)
    * A.expr list option (* defaults *)
  let equal (xi, xc, xr, xa, xd) (yi, yc, yr, ya, yd) =
    let compare_list x y = if List.length x = List.length y then
        List.map2 (AH.syn_expr_equal None) x y
      else [Ok false]
    in
    let join l = List.fold_left
      (fun a x -> a >>= fun a -> x >>= fun x -> Ok (a && x))
      (Ok (true))
      l
    in
    let i = HString.equal xi yi in
    let c = AH.syn_expr_equal None xc yc in
    let r = AH.syn_expr_equal None xr yr in
    let a = compare_list xa ya |> join in
    let d = match xd, yd with
      | Some xd, Some yd -> compare_list xd yd |> join
      | None, None -> Ok true
      | _ -> Ok false
    in
    match i, c, r, a, d with
    | true, Ok true, Ok true, Ok true, Ok true -> true
    | _ -> false

  let hash (i, c, r, a, d) =
    let c_hash = AH.hash (Some 6) c in
    let r_hash = AH.hash (Some 6) r in
    let a_hash = List.map (AH.hash (Some 6)) a in
    let d_hash = match d with
      | Some l -> List.map (AH.hash (Some 6)) l
      | None -> [0]
    in
    Hashtbl.hash (HString.hash i, c_hash, r_hash, a_hash, d_hash)
end

module CallCache = Hashtbl.Make(AstCallHash)

module LocalHash = struct
  type t = A.expr
  let equal x y = (match AH.syn_expr_equal (Some 6) x y with
    | Ok true -> true
    | _ -> false)
  
  let hash = AH.hash (Some 6)
end

module LocalCache = Hashtbl.Make(LocalHash)

module NodeArgHash = struct
  type t = A.expr
  let equal x y = (match AH.syn_expr_equal None x y with
    | Ok true -> true
    | _ -> false)
  
  let hash = AH.hash (Some 6)
end

module NodeArgCache = Hashtbl.Make(NodeArgHash)

let force_fresh = true
  (*
  As of today, this flag should be true when the condition below holds
  (IVC, MCS and CONTRACTCK use modelElement which assumes it is the case)
  The flag is always set to true because it is safe to do so and in this way
  we don't need to worry about keeping the condition up-to-date:

  Flags.IVC.compute_ivc () ||
  (match Flags.enabled () with
   | modules when List.mem `MCS modules -> true
   | modules when List.mem `CONTRACTCK modules -> true
   | _ -> false
  )*)

let call_cache = CallCache.create 20
let local_cache = LocalCache.create 20
let node_arg_cache = NodeArgCache.create 20

let clear_cache () =
  CallCache.clear call_cache;
  LocalCache.clear local_cache;
  NodeArgCache.clear node_arg_cache;

type info = {
  context : Ctx.tc_context;
  abstract_interp_context : LustreAbstractInterpretation.context;
  inductive_variables : LustreAst.lustre_type StringMap.t;
  quantified_variables : LustreAst.typed_ident list;
  node_is_input_const : (bool list) StringMap.t;
  contract_calls : LustreAst.contract_node_decl StringMap.t;
  contract_scope : (Lib.position * HString.t) list;
  contract_ref : HString.t;
  interpretation : HString.t StringMap.t;
  local_group_projection : int
}

let get_warnings map = map
  |> StringMap.bindings
  |> List.map (fun (_, { warnings }) -> warnings)
  |> List.flatten
  |> List.sort (fun (p1, _) (p2, _) -> compare_pos p1 p2)

let pp_print_generated_identifiers ppf gids =
  let locals_list = StringMap.bindings gids.locals 
    |> List.map (fun (x, (y, z, w, _)) -> x, y, z, w)
  in
  let array_ctor_list = StringMap.bindings gids.array_constructors
    |> List.map (fun (x, (y, z, w)) -> x, y, z, w)
  in
  let contract_calls_list = StringMap.bindings gids.contract_calls
    |> List.map (fun (x, (y, z, w)) -> x, y, z, w)
  in
  let pp_print_local ppf (id, b, ty, e) = Format.fprintf ppf "(%a, %b, %a, %a)"
    HString.pp_print_hstring id
    b
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_array_ctor ppf (id, ty, e, s) = Format.fprintf ppf "(%a, %a, %a, %a)"
    HString.pp_print_hstring id
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
    LustreAst.pp_print_expr s
  in
  let pp_print_node_arg ppf (id, b, ty, e) = Format.fprintf ppf "(%a, %b, %a, %a)"
    HString.pp_print_hstring id
    b
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_oracle ppf (id, ty, e) = Format.fprintf ppf "(%a, %a, %a)"
    HString.pp_print_hstring id
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_call = (fun ppf (pos, output, cond, restart, ident, args, defaults) ->
    Format.fprintf ppf 
      "%a: %a = call(%a,(restart %a every %a)(%a),%a)"
      pp_print_position pos
      HString.pp_print_hstring output
      A.pp_print_expr cond
      HString.pp_print_hstring ident
      A.pp_print_expr restart
      (pp_print_list A.pp_print_expr ",@ ") args
      (pp_print_option (pp_print_list A.pp_print_expr ",@")) defaults)
  in
  let pp_print_source ppf source = Format.fprintf ppf (match source with
    | Local -> "local"
    | Input -> "input"
    | Output -> "output"
    | Ghost -> "ghost")
  in
  let pp_print_subrange_constraint ppf (source, is_original, pos, id, rexpr) =
    Format.fprintf ppf "(%a, %b, %a, %a, %a)"
      pp_print_source source
      is_original
      Lib.pp_print_position pos
      HString.pp_print_hstring id
      A.pp_print_expr rexpr
  in
  let pp_print_contract_call ppf (ref, pos, scope, decl) = Format.fprintf ppf "%a := (%a, %a): %a"
    HString.pp_print_hstring ref
    pp_print_position pos
    (pp_print_list (pp_print_pair Lib.pp_print_position HString.pp_print_hstring ":") "::") scope
    (pp_print_list A.pp_print_contract_item ";") decl
  in
  Format.fprintf ppf "%a\n%a\n%a\n%a\n%a\n%a\n%a\n"
    (pp_print_list pp_print_oracle "\n") gids.oracles
    (pp_print_list pp_print_array_ctor "\n") array_ctor_list
    (pp_print_list pp_print_local "\n") locals_list
    (pp_print_list pp_print_node_arg "\n") gids.node_args
    (pp_print_list pp_print_call "\n") gids.calls
    (pp_print_list pp_print_subrange_constraint "\n") gids.subrange_constraints
    (pp_print_list pp_print_contract_call "\n") contract_calls_list

let compute_node_input_constant_mask decls =
  let over_decl map = function
  | A.NodeDecl (_, (id, _, _, inputs, _, _, _, _)) ->
    let is_consts = List.map (fun (_, _, _, _, c) -> c) inputs in
    StringMap.add id is_consts map
  | FuncDecl (_, (id, _, _, inputs, _, _, _, _)) ->
    let is_consts = List.map (fun (_, _, _, _, c) -> c) inputs in
    StringMap.add id is_consts map
  | _ -> map
  in List.fold_left over_decl StringMap.empty decls

let collect_contract_node_decls decls =
  let over_decl map = function
  | A.ContractNodeDecl (_, (id, params, inputs, outputs, equations)) ->
    StringMap.add id (id, params, inputs, outputs, equations) map
  | _ -> map
  in List.fold_left over_decl StringMap.empty decls


(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let contract_ref = ref 0

let dpos = Lib.dummy_pos

let union_list ids =
  List.fold_left (fun x y -> union x y ) (empty ()) ids

let expr_has_inductive_var ind_vars expr =
  let vars = AH.vars expr in
  let ind_vars = List.map (fun (i, _) -> i) (StringMap.bindings ind_vars) in
  let ind_vars = List.filter (fun x -> A.SI.mem x vars) ind_vars in
  match ind_vars with
  | [] -> None
  | h :: _ -> Some h

let new_contract_reference () =
  contract_ref := ! contract_ref + 1;
  HString.mk_hstring (string_of_int !contract_ref)

let extract_array_size = function
  | A.ArrayType (_, (_, size)) -> (match size with
    | A.Const (_, Num x) -> x |> HString.string_of_hstring |> int_of_string
    | _ -> assert false)
  | _ -> assert false

let generalize_to_array_expr name ind_vars expr nexpr = 
  let vars = AH.vars expr in
  let ind_vars = List.map (fun (i, _) -> i) (StringMap.bindings ind_vars) in
  let ind_vars = List.filter (fun x -> A.SI.mem x vars) ind_vars in
  let (eq_lhs, nexpr) = if List.length ind_vars = 0
    then A.StructDef (dpos, [SingleIdent (dpos, name)]), nexpr
    else A.StructDef (dpos, [ArrayDef (dpos, name, ind_vars)]),
      A.ArrayIndex (dpos, nexpr, A.Ident (dpos, List.hd ind_vars))
  in eq_lhs, nexpr

let mk_fresh_local force info pos is_ghost ind_vars expr_type expr oexpr =
  match (LocalCache.find_opt local_cache expr, force) with
  | Some nexpr, false -> nexpr, empty ()
  | _ ->
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_glocal") in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    locals = StringMap.singleton name (is_ghost, expr_type, expr, oexpr);
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr)]; }
  in
  LocalCache.add local_cache expr nexpr;
  nexpr, gids

let mk_fresh_array_ctor info pos ind_vars expr_type expr size_expr =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_varray") in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    array_constructors = StringMap.singleton name (expr_type, expr, size_expr);
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr)]; }
  in nexpr, gids

let mk_fresh_node_arg_local info pos is_const ind_vars expr_type expr =
  match NodeArgCache.find_opt node_arg_cache expr with
  | Some nexpr -> nexpr, empty ()
  | None ->
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_gklocal") in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    node_args = [(name, is_const, expr_type, expr)];
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr)]; }
  in
  NodeArgCache.add node_arg_cache expr nexpr;
  nexpr, gids

let mk_range_expr ctx expr_type expr = 
  let rec mk ctx n expr_type expr = 
    let expr_type = Ctx.expand_nested_type_syn ctx expr_type in
    match expr_type with
    | A.IntRange (_, l, u) ->
      let original_ty = Chk.infer_type_expr ctx expr |> unwrap in
      let original_ty = Ctx.expand_nested_type_syn ctx original_ty in
      let user_prop, is_original = match original_ty with
        | A.IntRange (_, l', u') ->
          let is_original =
            let (l, u) = AIC.eval_int_expr ctx l, AIC.eval_int_expr ctx u in
            let (l', u') = AIC.eval_int_expr ctx l', AIC.eval_int_expr ctx u' in
            (match (l, u, l', u') with
            | Ok l, Ok u, Ok l', Ok u' -> l = l' && u = u'
            | _ -> false)
          in
          let user_prop = if is_original then []
            else
              let l' = A.CompOp (dpos, A.Lte, l', expr) in
              let u' = A.CompOp (dpos, A.Lte, expr, u') in
              [A.BinaryOp (dpos, A.And, l', u'), true]
          in
          user_prop, is_original
        | A.Int _ -> [], false
        | _ -> assert false
      in
      let l = A.CompOp (dpos, A.Lte, l, expr) in
      let u = A.CompOp (dpos, A.Lte, expr, u) in
      [A.BinaryOp (dpos, A.And, l, u), is_original] @ user_prop
    | A.ArrayType (_, (ty, upper_bound)) ->
      let id_str = HString.concat2 (HString.mk_hstring "x") (HString.mk_hstring (string_of_int n)) in
      let id = A.Ident (dpos, id_str) in
      let ctx = Ctx.add_ty ctx id_str (A.Int dpos) in
      let expr = A.ArrayIndex (dpos, expr, id) in
      let rexpr = mk ctx (succ n) ty expr in
      let l = A.CompOp (dpos, A.Lte, A.Const (dpos, A.Num (HString.mk_hstring "0")), id) in
      let u = A.CompOp (dpos, A.Lt, id, upper_bound) in
      let assumption = A.BinaryOp (dpos, A.And, l, u) in
      let var = dpos, id_str, (A.Int dpos) in
      let body = fun e -> A.BinaryOp (dpos, A.Impl, assumption, e) in
      List.map (fun (e, is_original) -> A.Quantifier (dpos, A.Forall, [var], body e), is_original) rexpr
    | TupleType (_, tys) ->
      let mk_proj i = A.TupleProject (dpos, expr, i) in
      let tys = List.filter (fun ty -> AH.type_contains_subrange ty) tys in
      let tys = List.mapi (fun i ty -> mk ctx n ty (mk_proj i)) tys in
      List.fold_left (@) [] tys
    | RecordType (_, _, tys) ->
      let mk_proj i = A.RecordProject (dpos, expr, i) in
      let tys = List.filter (fun (_, _, ty) -> AH.type_contains_subrange ty) tys in
      let tys = List.map (fun (_, i, ty) -> mk ctx n ty (mk_proj i)) tys in
      List.fold_left (@) [] tys
    | _ -> assert false
  in
  mk ctx 0 expr_type expr

let mk_fresh_subrange_constraint source info pos constrained_name expr_type =
  let expr = A.Ident (pos, constrained_name) in
  let range_exprs = mk_range_expr info.context expr_type expr in
  let gids = List.map (fun (range_expr, is_original) ->
    i := !i + 1;
    let output_expr = AH.rename_contract_vars range_expr in
    let prefix = HString.mk_hstring (string_of_int !i) in
    let name = HString.concat2 prefix (HString.mk_hstring "_subrange") in
    let nexpr = A.Ident (pos, name) in
    let (eq_lhs, _) = generalize_to_array_expr name StringMap.empty range_expr nexpr in
    let gids = { (empty ()) with
      subrange_constraints = [(source, is_original, pos, name, output_expr)];
      equations = [(info.quantified_variables, info.contract_scope, eq_lhs, range_expr)]; }
    in
    gids)
    range_exprs
  in
  List.fold_left union (empty ()) gids

let mk_fresh_oracle expr_type expr =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_oracle") in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let gids = { (empty ()) with
    oracles = [name, expr_type, expr]; }
  in nexpr, gids

let record_warning pos original =
  { (empty ()) with  warnings = [(pos, original)]; }

let mk_fresh_call info id map pos cond restart args defaults =
  let called_node = StringMap.find id map in
  let has_oracles = List.length called_node.oracles > 0 in
  let check_cache = CallCache.find_opt
    call_cache
    (id, cond, restart, args, defaults)
  in
  match check_cache, has_oracles with
  | Some nexpr, false -> nexpr, empty ()
  | _ ->
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix  (HString.mk_hstring "_call") in
  let proj = if info.local_group_projection < 0 then (HString.mk_hstring "")
    else HString.concat2
      (HString.mk_hstring (string_of_int info.local_group_projection))
      (HString.mk_hstring "proj_")
  in
  let nexpr = A.Ident (pos, HString.concat2 proj name) in
  let call = (pos, name, cond, restart, id, args, defaults) in
  let gids = { (empty ()) with calls = [call] } in
  CallCache.add call_cache (id, cond, restart, args, defaults) nexpr;
  nexpr, gids

let get_type_of_id info node_id id =
  let ty = (match AI.get_type info.abstract_interp_context node_id id with
  | Some ty -> ty
  | None -> let ty = Ctx.lookup_ty info.context id |> get in ty)
  in
  Ctx.expand_nested_type_syn info.context ty

(* If [expr] is already an id then we don't create a fresh local *)
let should_not_abstract force expr = not force && AH.expr_is_id expr

let normalize_list f list =
  let over_list (nitems, gids) item =
    let (normal_item, ids) = f item in
    normal_item :: nitems, union ids gids
  in let list, gids = List.fold_left over_list ([], empty ()) list in
  List.rev list, gids

let rec normalize ctx ai_ctx (decls:LustreAst.t) =
  let info = { context = ctx;
    abstract_interp_context = ai_ctx;
    inductive_variables = StringMap.empty;
    quantified_variables = [];
    node_is_input_const = compute_node_input_constant_mask decls;
    contract_calls = collect_contract_node_decls decls;
    contract_ref = HString.mk_hstring "";
    contract_scope = [];
    interpretation = StringMap.empty;
    local_group_projection = -1 }
  in let over_declarations (nitems, accum) item =
    clear_cache ();
    let (normal_item, map) =
      normalize_declaration info accum item in
    (match normal_item with 
      | Some ni -> ni :: nitems
      | None -> nitems),
    StringMap.merge union_keys map accum
  in let ast, map = List.fold_left over_declarations
    ([], StringMap.empty) decls
  in let ast = List.rev ast in
  
  Debug.parse ("===============================================\n"
    ^^ "Generated Identifiers:\n%a\n\n"
    ^^ "Normalized lustre AST:\n%a\n"
    ^^ "===============================================\n")
    (pp_print_list
      (pp_print_pair
        HString.pp_print_hstring
        pp_print_generated_identifiers
        ":")
      "\n")
      (StringMap.bindings map)
    A.pp_print_program ast;

  Res.ok (ast, map)

and normalize_declaration info map = function
  | NodeDecl (span, decl) ->
    let normal_decl, map = normalize_node info map decl in
    Some (A.NodeDecl(span, normal_decl)), map
  | FuncDecl (span, decl) ->
    let normal_decl, map = normalize_node info map decl in
    Some (A.FuncDecl (span, normal_decl)), map
  | ContractNodeDecl (_, _) -> None, StringMap.empty
  | decl -> Some decl, StringMap.empty

and normalize_node_contract info map cref inputs outputs (id, _, ivars, ovars, body) =
  let contract_ref = cref in
  let ivars_names = List.map (fun (_, id, _, _, _) -> id) ivars in
  let ovars_names = List.map (fun (_, id, _, _) -> id) ovars in
  let input_interp = List.fold_left (fun acc (i, e) ->
      StringMap.merge union_keys acc (StringMap.singleton i e))
    StringMap.empty
    (List.combine ivars_names inputs)
  in
  let output_interp = List.fold_left (fun acc (i, e) ->
      StringMap.merge union_keys acc (StringMap.singleton i e))
    StringMap.empty
    (List.combine ovars_names outputs)
  in
  let interp = StringMap.merge union_keys input_interp output_interp in
  let type_exports = Ctx.lookup_contract_exports info.context id |> get in
  let ctx = List.fold_left (fun c (id, ty) -> Ctx.add_ty c id ty)
    info.context
    (Ctx.IMap.bindings type_exports) in
  let ctx = List.fold_left (fun c (_, id, ty, _, _) -> Ctx.add_ty c id ty)
    ctx ivars in
  let ctx = List.fold_left (fun c (_, id, ty, _) -> Ctx.add_ty c id ty)
    ctx ovars in
  let info = { info with
    context = ctx;
    interpretation = interp;
    contract_ref; }
  in
  let nbody, gids = normalize_contract info map id body in
  nbody, gids, StringMap.empty

(*
and normalize_const_declaration info map = function
  | A.UntypedConst (pos, id, expr) ->
    let nexpr, gids = normalize_expr ?guard:None false info map expr in
    A.UntypedConst (pos, id, nexpr), gids
  | TypedConst (pos, id, expr, ty) ->
    let nexpr, gids = normalize_expr ?guard:None false info map expr in
    A.TypedConst (pos, id, nexpr, ty), gids
  | e -> e, empty ()
*)

and normalize_ghost_declaration info map = function
  | A.UntypedConst (pos, id, expr) ->
    let new_id = StringMap.find id info.interpretation in
    let nexpr, gids = normalize_expr ?guard:None info map expr in
    A.UntypedConst (pos, new_id, nexpr), gids
  | TypedConst (pos, id, expr, ty) ->
    let new_id = StringMap.find id info.interpretation in
    let nexpr, gids = normalize_expr ?guard:None info map expr in
    A.TypedConst (pos, new_id, nexpr, ty), gids
  | e -> e, empty ()

and normalize_node info map
    (node_id, is_extern, params, inputs, outputs, locals, items, contracts) =
  (* Setup the typing context *)
  let constants_ctx = inputs
    |> List.map Ctx.extract_consts
    |> (List.fold_left Ctx.union info.context)
  in
  let input_ctx = inputs
    |> List.map Ctx.extract_arg_ctx
    |> (List.fold_left Ctx.union info.context)
  in
  let output_ctx = outputs
    |> List.map Ctx.extract_ret_ctx
    |> (List.fold_left Ctx.union info.context)
  in
  let ctx = Ctx.union
    (Ctx.union constants_ctx info.context)
    (Ctx.union input_ctx output_ctx)
  in
  let info = { info with context = ctx } in
  (* Record subrange constraints on inputs, outputs *)
  let gids1 = inputs
    |> List.filter (fun (_, id, _, _, _) -> 
      let ty = get_type_of_id info node_id id in
      AH.type_contains_subrange ty)
    |> List.fold_left (fun acc (p, id, _, _, _) ->
      let ty = get_type_of_id info node_id id in
      let ty = AIC.inline_constants_of_lustre_type info.context ty in
      union acc (mk_fresh_subrange_constraint Input info p id ty))
      (empty ())
  in
  let gids2 = outputs
    |> List.filter (fun (_, id, _, _) -> 
      let ty = get_type_of_id info node_id id in
      AH.type_contains_subrange ty)
    |> List.fold_left (fun acc (p, id, _, _) ->
      let ty = get_type_of_id info node_id id in
      let ty = AIC.inline_constants_of_lustre_type info.context ty in
      union acc (mk_fresh_subrange_constraint Output info p id ty))
      (empty ())
  in
  (* We have to handle contracts before locals
    Otherwise the typing contexts collide *)
  let ncontracts, gids5 = match contracts with
    | Some contracts ->
      let ctx = Chk.tc_ctx_of_contract info.context contracts |> unwrap
      in
      let contract_ref = new_contract_reference () in
      let info = { info with context = ctx; contract_ref } in
      let ncontracts, gids = normalize_contract info map node_id
        contracts in
      (Some ncontracts), gids
    | None -> None, empty ()
  in
  (* Record subrange constraints on locals
    and finish setting up the typing context for the node body *)
  let ctx = List.fold_left
    (fun ctx local -> Chk.local_var_binding ctx local |> unwrap)
    ctx
    locals
  in
  let info = { info with context = ctx } in
  let gids3 = locals
    |> List.filter (function
      | A.NodeVarDecl (_, (_, id, _, _)) -> 
        let ty = get_type_of_id info node_id id in
        AH.type_contains_subrange ty
      | _ -> false)
    |> List.fold_left (fun acc l -> match l with
      | A.NodeVarDecl (p, (_, id, _, _)) -> 
        let ty = get_type_of_id info node_id id in
        let ty = AIC.inline_constants_of_lustre_type info.context ty in
        union acc (mk_fresh_subrange_constraint Local info p id ty)
      | _ -> assert false)
      (empty ())
  in
  (* Normalize equations and the contract *)
  let nitems, gids4 = normalize_list (normalize_item info map) items in
  let gids = union_list [gids1; gids2; gids3; gids4; gids5] in
  let map = StringMap.singleton node_id gids in
  (node_id, is_extern, params, inputs, outputs, locals, nitems, ncontracts), map

and normalize_item info map = function
  | Body equation ->
    let nequation, gids = normalize_equation info map equation in
    Body nequation, gids
  | AnnotMain b -> AnnotMain b, empty ()
  | AnnotProperty (pos, name, expr) ->
    let name' =
      match name with
      | None -> (
        let hs_expr =
          Format.asprintf "@[<h>%a@]" A.pp_print_expr expr
          |> HString.mk_hstring
        in
        Some hs_expr
      )
      | Some _ as n -> n
    in
    let nexpr, gids = abstract_expr false info map false expr in
    AnnotProperty (pos, name', nexpr), gids

and rename_ghost_variables info node_id contract =
  let sep = HString.mk_hstring "_contract_" in
  match contract with
  | [] -> [StringMap.empty], info
  | (A.GhostConst (UntypedConst (_, id, _))
  | GhostConst (TypedConst (_, id, _, _))) :: t ->
    let ty = Ctx.lookup_ty info.context id |> get in
    let ty = Ctx.expand_nested_type_syn info.context ty in
    let new_id = HString.concat sep [info.contract_ref;id] in
    let info = { info with context = Ctx.add_ty info.context new_id ty } in
    let tail, info = rename_ghost_variables info node_id t in
    (StringMap.singleton id new_id) :: tail, info
  (* Recurse through each declaration one at a time *)
  | GhostVars (pos1, A.GhostVarDec(pos2, (_, id, _)::tis), e) :: t -> 
    let ty = Ctx.lookup_ty info.context id |> get in
    let ty = Ctx.expand_nested_type_syn info.context ty in
    let new_id = HString.concat sep [info.contract_ref;id] in
    let info = { info with context = Ctx.add_ty info.context new_id ty } in
    let tail, info = rename_ghost_variables info node_id (A.GhostVars (pos1, A.GhostVarDec(pos2, tis), e) :: t) in
    (StringMap.singleton id new_id) :: tail, info
  | _ :: t -> rename_ghost_variables info node_id t

and normalize_contract info map node_id items =
  let gids = ref (empty ()) in
  let result = ref [] in
  let ghost_interp, info = rename_ghost_variables info node_id items in
  let ghost_interp = List.fold_left (StringMap.merge union_keys)
    StringMap.empty ghost_interp
  in
  let interp = StringMap.merge union_keys ghost_interp info.interpretation in
  let interpretation = ref interp in

  for j = 0 to (List.length items) - 1 do
    let info = { info with interpretation = !interpretation } in
    let item = List.nth items j in
    let nitem, gids', interpretation' = match item with
      | Assume (pos, name, soft, expr) ->
        let nexpr, gids = abstract_expr force_fresh info map true expr in
        A.Assume (pos, name, soft, nexpr), gids, StringMap.empty
      | Guarantee (pos, name, soft, expr) -> 
        let nexpr, gids = abstract_expr force_fresh info map true expr in
        Guarantee (pos, name, soft, nexpr), gids, StringMap.empty
      | Mode (pos, name, requires, ensures) ->
(*         let new_name = info.contract_ref ^ "_contract_" ^ name in
        let interpretation = StringMap.singleton name new_name in
        let info = { info with interpretation } in *)
        let over_property info map (pos, name, expr) =
          let nexpr, gids = abstract_expr true info map true expr in
          (pos, name, nexpr), gids
        in
        let nrequires, gids1 = normalize_list (over_property info map) requires in
        let nensures, gids2 = normalize_list (over_property info map) ensures in
        Mode (pos, name, nrequires, nensures), union gids1 gids2, StringMap.empty
      | ContractCall (pos, name, inputs, outputs) ->
        let ninputs, gids1 = normalize_list (abstract_expr false info map false) inputs in
        let noutputs = List.map
          (fun id -> match StringMap.find_opt id info.interpretation with
            | Some new_id -> new_id
            | None -> id)
          outputs
        in
        let ninputs = List.map (fun e -> 
          match e with
          | A.Ident (_, i) -> i
          | _ -> assert false)
          ninputs
        in
        let cref = new_contract_reference () in
        let info = { info with
            contract_scope = info.contract_scope @ [(pos, name)];
            contract_ref = cref;
          }
        in
        let called_node = StringMap.find name info.contract_calls in
        let normalized_call, gids2, interp = 
          normalize_node_contract info map cref ninputs noutputs called_node
        in
        let gids = union gids1 gids2 in
        let gids = { gids with
          contract_calls = StringMap.add info.contract_ref
            (pos, info.contract_scope, normalized_call)
            gids.contract_calls
          }
        in
        ContractCall (pos, cref, inputs, outputs), gids, interp
      | GhostConst decl ->
        let ndecl, gids= normalize_ghost_declaration info map decl in
        GhostConst ndecl, gids, StringMap.empty
      | GhostVars (pos, ((GhostVarDec (pos2, tis)) as lhs), expr) ->
        let items = match lhs with | A.GhostVarDec (_, items) -> items in
        let lhs_arity = List.length items in
        let rhs_arity = match expr with
          | A.GroupExpr(_, A.ExprList, expr_list) -> List.length expr_list
          | _ -> 1
        in
        let vars_of_calls = AH.vars_of_node_calls expr in

        (* Currently, parallel ghost variable assignment is not supported with 
           arrays (only simple typed identifiers). But, the following code with
           "has_inductive" is included because we plan on offering this functionality
           in the future.*)
        let has_inductive = vars_of_calls
          |> A.SI.to_seq
          |> Seq.fold_left
            (fun acc v -> acc || StringMap.mem v info.inductive_variables)
            false
        in
        let (nexpr, gids1), expanded = (
          if has_inductive && lhs_arity <> rhs_arity then
            (match StringMap.choose_opt info.inductive_variables with
            | Some (ivar, ty) ->
              let size = extract_array_size ty in
              let expanded_expr = expand_node_calls_in_place info ivar size expr in
              let exprs, gids = List.split (List.init lhs_arity
                (
                  fun i -> 
                  let info = { info with local_group_projection = i } in
                  normalize_expr ?guard:None info map expanded_expr
                )
              ) 
              in
              let gids = List.fold_left (fun acc g -> union g acc) (empty ()) gids in
            (A.GroupExpr (dpos, A.ExprList, exprs), gids), true
            | None -> normalize_expr ?guard:None info map expr, false)
            
          else if has_inductive && lhs_arity = rhs_arity then
            let expanded_expr = List.fold_left
              (fun acc (v, ty) -> 
                let size = extract_array_size ty in
                expand_node_calls_in_place info v size acc)
              expr
              (StringMap.bindings info.inductive_variables)
            in
            normalize_expr ?guard:None info map expanded_expr, true
          else normalize_expr ?guard:None info map expr, false
        )
        in
        let gids2 = (
          if expanded then
          let items = match lhs with | GhostVarDec (_, items) -> items in
          let ids = List.map (function (_, i, _) -> i) items
          in
          { (empty ()) with  expanded_variables = StringSet.of_list ids }
          else empty ()
        )
        in
        let gids3 = (
          let gids_list = (
            List.map (
              fun (_, i, ty) -> 
              let new_id = StringMap.find i info.interpretation in
              if AH.type_contains_subrange ty then
                mk_fresh_subrange_constraint Ghost info pos new_id ty
              else empty ()
            )
            tis
          ) in
          List.fold_left union (empty ()) gids_list
        ) in

        (* Get new identifiers for LHS *)
        let new_tis = List.map (fun (p, id, e) -> 
          (p, StringMap.find id info.interpretation, e)) tis in
        GhostVars (pos, GhostVarDec(pos2, new_tis), nexpr), union (union gids1 gids2) gids3, StringMap.empty
      
      | AssumptionVars decl ->
        AssumptionVars decl, empty (), StringMap.empty
    in
    interpretation := StringMap.merge union_keys !interpretation interpretation';
    result := nitem :: !result;
    gids := union !gids gids';
  done;
  !result, !gids


and normalize_equation info map = function
  | Assert (pos, expr) ->
    let nexpr, gids = abstract_expr true info map true expr in
    Assert (pos, nexpr), gids
  | Equation (pos, lhs, expr) ->
    (* Need to track array indexes of the left hand side if there are any *)
    let items = match lhs with | A.StructDef (_, items) -> items in
    let info = List.fold_left (fun info item -> match item with
      | A.ArrayDef (pos, v, is) ->
        let info = List.fold_left (fun info i -> { info with
          context = Ctx.add_ty info.context i (A.Int pos); })
          info
          is
        in
        let ty = match Ctx.lookup_ty info.context v with 
          | Some t -> t | None -> assert false
        in
        let ivars = List.fold_left (fun m i -> StringMap.add i ty m)
          StringMap.empty
          is
        in { info with inductive_variables = ivars}
      | _ -> info)
      info
      items
    in
    let lhs_arity = List.length items in
    let rhs_arity = match expr with
      | A.GroupExpr(_, A.ExprList, expr_list) -> List.length expr_list
      | _ -> 1
    in
    let vars_of_calls = AH.vars_of_node_calls expr in
    let has_inductive = vars_of_calls
      |> A.SI.to_seq
      |> Seq.fold_left
        (fun acc v -> acc || StringMap.mem v info.inductive_variables)
        false
    in
    let (nexpr, gids1), expanded = (
      if has_inductive && lhs_arity <> rhs_arity then
        (match StringMap.choose_opt info.inductive_variables with
        | Some (ivar, ty) ->
          let size = extract_array_size ty in
          let expanded_expr = expand_node_calls_in_place info ivar size expr in
          let exprs, gids = List.split (List.init lhs_arity
            (fun i -> 
              let info = { info with local_group_projection = i } in
              normalize_expr info map expanded_expr))
          in
          let gids = List.fold_left (fun acc g -> union g acc) (empty ()) gids in
        (A.GroupExpr (dpos, A.ExprList, exprs), gids), true
        | None -> normalize_expr info map expr, false)
      else if has_inductive && lhs_arity = rhs_arity then
        let expanded_expr = List.fold_left
          (fun acc (v, ty) -> 
            let size = extract_array_size ty in
            expand_node_calls_in_place info v size acc)
          expr
          (StringMap.bindings info.inductive_variables)
        in
        normalize_expr info map expanded_expr, true
      else normalize_expr info map expr, false)
    in
    let gids2 = if expanded then
      let items = match lhs with | StructDef (_, items) -> items in
      let ids = List.map (function
        | A.SingleIdent (_, i) | ArrayDef (_, i, _) -> i
        | _ -> assert false)
        items
      in
      { (empty ()) with  expanded_variables = StringSet.of_list ids }
      else empty ()
    in
    Equation (pos, lhs, nexpr), union gids1 gids2

and rename_id info = function
  | A.Ident (pos, id) ->
    (match (StringMap.find_opt id info.interpretation) with
      | Some new_id -> A.Ident (pos, new_id)
      | None -> A.Ident (pos, id))
  | _ -> assert false

and abstract_expr ?guard force info map is_ghost expr = 
  let nexpr, gids1 = normalize_expr ?guard info map expr in
  if should_not_abstract force nexpr then
    nexpr, gids1
  else
    let ivars = info.inductive_variables in
    let pos = AH.pos_of_expr expr in
    let ty = if expr_has_inductive_var ivars expr |> is_some then
      (StringMap.choose_opt info.inductive_variables) |> get |> snd
    else Chk.infer_type_expr info.context expr |> unwrap
    in
    let iexpr, gids2 = mk_fresh_local force info pos is_ghost ivars ty nexpr expr in
    iexpr, union gids1 gids2

and expand_node_call info expr var count =
  let ty = Chk.infer_type_expr info.context expr |> unwrap in
  let mk_index i = A.Const (dpos, Num (HString.mk_hstring (string_of_int i))) in
  let expr_array = List.init count (fun i -> AH.substitute var (mk_index i) expr) in
  match ty with
  | A.ArrayType _ -> A.GroupExpr (dpos, ArrayExpr, expr_array)
  | _ -> List.fold_left
    (fun acc (i, e) ->
      let pos = Lib.dummy_pos in
      let i = HString.mk_hstring (Int.to_string i) in
      let cond = A.CompOp (pos, A.Eq, A.Ident (pos, var), A.Const (pos, A.Num i)) in
      A.TernaryOp (pos, A.Ite, cond, e, acc))
    (List.nth expr_array 0)
    (List.tl (List.init count (fun i -> i, List.nth expr_array i)))

and combine_args_with_const info args flags =
  let output_arity = List.map (fun e -> match e with
    | A.Call (_, i, _) ->
      (* This node type is guaranteed to exist by type checking *)
      let node_type = Ctx.lookup_node_ty info.context i |> get in
      (match node_type with
      | TArr (_, _, GroupType (_, es)) -> List.length es
      | _ -> 1)
    | _ -> 1)
    args
  in
  let over_args_arity (i, acc) (e, arity) =
    if arity > 1 then
      i + arity, (e, false) :: acc
    else
      succ i, (e, List.nth flags i) :: acc
  in
  List.fold_left over_args_arity (0, []) (List.combine args output_arity)
  |> snd |> List.rev
 
and normalize_expr ?guard info map =
  let abstract_node_arg ?guard force is_const info map expr =
    let nexpr, gids1 = normalize_expr ?guard info map expr in
    if should_not_abstract force nexpr then
      nexpr, gids1
    else
      let ivars = info.inductive_variables in
      let pos = AH.pos_of_expr expr in
      let ty = if expr_has_inductive_var ivars expr |> is_some then
        (StringMap.choose_opt info.inductive_variables) |> get |> snd
      else Chk.infer_type_expr info.context expr |> unwrap
      in
      let iexpr, gids2 = mk_fresh_node_arg_local info pos is_const ivars ty nexpr in
      iexpr, union gids1 gids2
  in function
  (* ************************************************************************ *)
  (* Node calls                                                               *)
  (* ************************************************************************ *)
  | Call (pos, id, args) ->
    let flags = StringMap.find id info.node_is_input_const in
    let cond = A.Const (Lib.dummy_pos, A.True) in
    let restart =  A.Const (Lib.dummy_pos, A.False) in
    let nargs, gids1 = normalize_list
      (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
      (combine_args_with_const info args flags)
    in
    let nexpr, gids2 = mk_fresh_call info id map pos cond restart nargs None in
    nexpr, union gids1 gids2
  | Condact (pos, cond, restart, id, args, defaults) ->
    let flags = StringMap.find id info.node_is_input_const in
    let ncond, gids1 = if AH.expr_is_true cond then cond, empty ()
      else abstract_expr ?guard true info map false cond in
    let nrestart, gids2 = if AH.expr_is_const restart then restart, empty ()
      else abstract_expr ?guard true info map false restart
    in let nargs, gids3 = normalize_list
      (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
      (combine_args_with_const info args flags)
    in
    let ndefaults, gids4 = normalize_list
      (normalize_expr ?guard info map)
      defaults in
    let nexpr, gids5 = mk_fresh_call info id map pos ncond nrestart nargs (Some ndefaults) in
    let gids = union_list [gids1; gids2; gids3; gids4; gids5] in
    nexpr, gids
  | RestartEvery (pos, id, args, restart) ->
    let flags = StringMap.find id info.node_is_input_const in
    let cond = A.Const (dummy_pos, A.True) in
    let nrestart, gids1 = if AH.expr_is_const restart then restart, empty ()
      else abstract_expr ?guard true info map false restart
    in let nargs, gids2 = normalize_list
      (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
      (combine_args_with_const info args flags)
    in
    let nexpr, gids3 = mk_fresh_call info id map pos cond nrestart nargs None in
    let gids = union_list [gids1; gids2; gids3] in
    nexpr, gids
  | Merge (pos, clock_id, cases) ->
    let normalize' info map ?guard = function
      | clock_value, A.Activate (pos, id, cond, restart, args) ->
        let flags = StringMap.find id info.node_is_input_const in
        let ncond, gids1 = if AH.expr_is_true cond then cond, empty ()
          else abstract_expr ?guard false info map false cond in
        let nrestart, gids2 = if AH.expr_is_const restart then restart, empty ()
          else abstract_expr ?guard false info map false restart in
        let nargs, gids3 = normalize_list
          (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
          (combine_args_with_const info args flags)
        in
        let nexpr, gids4 = mk_fresh_call info id map pos ncond nrestart nargs None in
        let gids = union_list [gids1; gids2; gids3; gids4] in
        (clock_value, nexpr), gids
      | clock_value, A.Call (pos, id, args) ->
        let flags = StringMap.find id info.node_is_input_const in
        let cond_expr = match HString.string_of_hstring clock_value with
          | "true" -> A.Ident (pos, clock_id)
          | "false" -> A.UnaryOp (pos, A.Not, A.Ident (pos, clock_id))
          | _ -> A.CompOp (pos, A.Eq, A.Ident (pos, clock_id), A.Ident (pos, clock_value))
        in let ncond, gids1 = abstract_expr ?guard false info map false cond_expr in
        let restart =  A.Const (Lib.dummy_pos, A.False) in
        let nargs, gids2 = normalize_list
          (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
          (combine_args_with_const info args flags)
        in
        let nexpr, gids3 = mk_fresh_call info id map pos ncond restart nargs None in
        let gids = union_list [gids1; gids2; gids3] in
        (clock_value, nexpr), gids
      | clock_value, expr ->
        let nexpr, gids = normalize_expr ?guard info map expr in
        (clock_value, nexpr), gids
    in let ncases, gids = normalize_list (normalize' ?guard info map) cases in
    Merge (pos, clock_id, ncases), gids
  (* ************************************************************************ *)
  (* Guarding and abstracting pres                                            *)
  (* ************************************************************************ *)
  | Arrow (pos, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard:(Some nexpr1) info map expr2 in
    let gids = union gids1 gids2 in
    Arrow (pos, nexpr1, nexpr2), gids
   | Pre (pos1, ArrayIndex (pos2, expr1, expr2)) ->
    let expr = A.ArrayIndex (pos2, Pre (pos1, expr1), expr2) in
    normalize_expr ?guard info map expr
  | Pre (pos, expr) as p ->
    let ivars = info.inductive_variables in
    let ty = if expr_has_inductive_var ivars expr |> is_some then
        (StringMap.choose_opt info.inductive_variables) |> get |> snd
      else Chk.infer_type_expr info.context expr |> unwrap
      in
    let nexpr, gids1 = abstract_expr ?guard:None false info map false expr in
    let guard, gids2, previously_guarded = match guard with
      | Some guard -> guard, empty (), true
      | None ->
        let guard, gids1 = mk_fresh_oracle ty nexpr in
        let gids2 = record_warning pos p in
        guard, union gids1 gids2, false
    in
    let gids = union gids1 gids2 in
    let nexpr' = match nexpr with
      | A.ArrayIndex (pos2, expr1, expr2) ->
        A.ArrayIndex (pos2, Pre (pos, expr1), expr2)
      | e -> Pre (pos, e)
    in
    if previously_guarded then nexpr', gids
    else Arrow (pos, guard, nexpr'), gids
  (* ************************************************************************ *)
  (* Misc. abstractions                                                       *)
  (* ************************************************************************ *)
  | ArrayConstr (pos, expr, size_expr) ->
    let ivars = info.inductive_variables in
    let ty = if expr_has_inductive_var ivars expr |> is_some then
      (StringMap.choose_opt info.inductive_variables) |> get |> snd
    else Chk.infer_type_expr info.context expr |> unwrap
    in
    let nexpr, gids1 = normalize_expr ?guard info map expr in
    let ivars = info.inductive_variables in
    let iexpr, gids2 = mk_fresh_array_ctor info pos ivars ty nexpr size_expr in
    ArrayConstr (pos, iexpr, size_expr), union gids1 gids2
  (* ************************************************************************ *)
  (* Variable renaming to ease handling contract scopes                       *)
  (* ************************************************************************ *)
  | Ident _ as e -> rename_id info e, empty ()
  (* ************************************************************************ *)
  (* The remaining expr kinds are all just structurally recursive             *)
  (* ************************************************************************ *)
  | ModeRef _ as expr -> expr, empty ()
  | RecordProject (pos, expr, i) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    RecordProject (pos, nexpr, i), gids
  | TupleProject (pos, expr, i) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    TupleProject (pos, nexpr, i), gids
  | Const _ as expr -> expr, empty ()
  | UnaryOp (pos, op, expr) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    UnaryOp (pos, op, nexpr), gids
  | BinaryOp (pos, op, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    BinaryOp (pos, op, nexpr1, nexpr2), union gids1 gids2
  | TernaryOp (pos, op, expr1, expr2, expr3) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    let nexpr3, gids3 = normalize_expr ?guard info map expr3 in
    let gids = union (union gids1 gids2) gids3 in
    TernaryOp (pos, op, nexpr1, nexpr2, nexpr3), gids
  | NArityOp (pos, op, expr_list) ->
    let nexpr_list, gids = normalize_list
      (normalize_expr ?guard info map)
      expr_list in
    NArityOp (pos, op, nexpr_list), gids
  | ConvOp (pos, op, expr) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    ConvOp (pos, op, nexpr), gids
  | CompOp (pos, op, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    CompOp (pos, op, nexpr1, nexpr2), union gids1 gids2
  | RecordExpr (pos, id, id_expr_list) ->
    let normalize' info map ?guard (id, expr) =
      let nexpr, gids = normalize_expr ?guard info map expr in
      (id, nexpr), gids
    in 
    let nid_expr_list, gids = normalize_list 
      (normalize' ?guard info map)
      id_expr_list in
    RecordExpr (pos, id, nid_expr_list), gids
  | GroupExpr (pos, kind, expr_list) ->
    let nexpr_list, gids = normalize_list
      (normalize_expr ?guard info map)
      expr_list in
    GroupExpr (pos, kind, nexpr_list), gids
  | StructUpdate (pos, expr1, i, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    StructUpdate (pos, nexpr1, i, nexpr2), union gids1 gids2
  | ArraySlice (pos, expr1, (expr2, expr3)) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    let nexpr3, gids3 = normalize_expr ?guard info map expr3 in
    let gids = union (union gids1 gids2) gids3 in
    ArraySlice (pos, nexpr1, (nexpr2, nexpr3)), gids
  | ArrayIndex (pos, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    ArrayIndex (pos, nexpr1, nexpr2), union gids1 gids2
  | ArrayConcat (pos, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    ArrayConcat (pos, nexpr1, nexpr2), union gids1 gids2
  | Quantifier (pos, kind, vars, expr) ->
    let ctx = List.fold_left Ctx.union info.context
      (List.map (fun (_, i, ty) -> Ctx.singleton_ty i ty) vars)
    in
    let info = { 
      info with context = ctx;
        quantified_variables = info.quantified_variables @ vars }
    in
    let nexpr, gids = normalize_expr ?guard info map expr in
    Quantifier (pos, kind, vars, nexpr), gids
  | When (pos, expr, clock_expr) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    When (pos, nexpr, clock_expr), gids
  | Current (pos, expr) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    Current (pos, nexpr), gids
  | Activate (pos, id, expr1, expr2, expr_list) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    let nexpr_list, gids3 = normalize_list
      (normalize_expr ?guard info map)
      expr_list in
    let gids = union (union gids1 gids2) gids3 in
    Activate (pos, id, nexpr1, nexpr2, nexpr_list), gids
  | Fby (pos, expr1, i, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    Fby (pos, nexpr1, i, nexpr2), union gids1 gids2
  | CallParam (pos, id, type_list, expr_list) ->
    let nexpr_list, gids = normalize_list
      (normalize_expr ?guard info map)
      expr_list in
    CallParam (pos, id, type_list, nexpr_list), gids

and expand_node_calls_in_place info var count expr =
  let r = expand_node_calls_in_place info var count in
  match expr with
  | A.RecordProject (p, e, i) -> A.RecordProject (p, r e, i)
  | TupleProject (p, e, i) -> A.TupleProject (p, r e, i)
  | UnaryOp (p, op, e) -> A.UnaryOp (p, op, r e)
  | ConvOp (p, op, e) -> A.ConvOp (p, op, r e)
  | Quantifier (p, k, ids, e) -> A.Quantifier (p, k, ids, r e)
  | When (p, e, c) -> A.When (p, r e, c)
  | Current (p, e) -> A.Current (p, r e)
  | Pre (p, e) -> A.Pre (p, r e)
  | BinaryOp (p, op, e1, e2) -> A.BinaryOp (p, op, r e1, r e2)
  | CompOp (p, op, e1, e2) -> A.CompOp (p, op, r e1, r e2)
  | StructUpdate (p, e1, u, e2) -> A.StructUpdate (p, r e1, u, r e2)
  | ArrayConstr (p, e1, e2) -> A.ArrayConstr (p, r e1, r e2)
  | ArrayIndex (p, e1, e2) -> A.ArrayIndex (p, r e1, r e2)
  | ArrayConcat (p, e1, e2) -> A.ArrayConcat (p, r e1, r e2)
  | Fby (p, e1, i, e2) -> A.Fby (p, r e1, i, r e2)
  | Arrow (p, e1, e2) -> A.Arrow (p, r e1, r e2)
  | TernaryOp (p, op, e1, e2, e3) -> A.TernaryOp (p, op, r e1, r e2, r e3)
  | ArraySlice (p, e1, (e2, e3)) -> A.ArraySlice (p, r e1, (r e2, r e3))
  | NArityOp (p, op, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    A.NArityOp (p, op, expr_list)
  | GroupExpr (p, k, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    A.GroupExpr (p, k, expr_list)
  | CallParam (p, n, t, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    A.CallParam (p, n, t, expr_list)
  | RecordExpr (p, n, expr_list) ->
    let expr_list = List.map (fun (i, e) -> (i, r e)) expr_list in
    A.RecordExpr (p, n, expr_list)
  | Merge (p, n, expr_list) ->
    let expr_list = List.map (fun (i, e) -> (i, r e)) expr_list in
    A.Merge (p, n, expr_list)
  | Activate (p, n, e1, e2, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    A.Activate (p, n, r e1, r e2, expr_list)
  | Call (p, n, expr_list) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    expand_node_call info (A.Call (p, n, expr_list)) var count
  | Condact (p, e1, e2, id, expr_list1, expr_list2) ->
    let expr_list1 = List.map (fun e -> r e) expr_list1 in
    let expr_list2 = List.map (fun e -> r e) expr_list2 in
    let e = A.Condact (p, r e1, r e2, id, expr_list1, expr_list2) in
    expand_node_call info e var count
  | RestartEvery (p, id, expr_list, e) ->
    let expr_list = List.map (fun e -> r e) expr_list in
    let e = A.RestartEvery (p, id, expr_list, r e) in
    expand_node_call info e var count
  | e -> e
