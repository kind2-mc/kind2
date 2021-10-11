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
  Note that oracles are _propagated_ in node calls. If a node `n1` has an oracle
  and is called by another node `n2`, then `n2` will inherit a propagated oracle

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

module A = LustreAst
module AH = LustreAstHelpers
module AIC = LustreAstInlineConstants
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

let (>>=) = Res.(>>=)

module StringMap = struct
  include Map.Make(struct
    type t = string
    let compare i1 i2 = String.compare i1 i2
  end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end

module CallCache = struct
  include Map.Make(struct
    type t = string (* node name *)
      * A.expr (* cond *)
      * A.expr (* restart *)
      * A.expr list (* arguments (which are already abstracted) *)
      * A.expr list option (* defaults *)
    let compare (xi, xc, xr, xa, xd) (yi, yc, yr, ya, yd) =
      let compare_list x y = if List.length x = List.length y then
          List.map2 (AH.syn_expr_equal (Some 6)) x y
        else [Ok false]
      in
      let join l = List.fold_left
        (fun a x -> a >>= fun a -> x >>= fun x -> Ok (a && x))
        (Ok (true))
        l
      in
      let i = String.equal xi yi in
      let c = AH.syn_expr_equal (Some 6) xc yc in
      let r = AH.syn_expr_equal (Some 6) xr yr in
      let a = compare_list xa ya |> join in
      let d = match xd, yd with
        | Some xd, Some yd -> compare_list xd yd |> join
        | None, None -> Ok true
        | _ -> Ok false
      in
      match i, c, r, a, d with
      | true, Ok true, Ok true, Ok true, Ok true -> 0
      | _ -> 1
  end)
end

module LocalCache = struct
  include Map.Make(struct
    type t = A.expr
    let compare x y = match AH.syn_expr_equal (Some 6) x y with
      | Ok true -> 0
      | _ -> 1
  end)
end

let call_cache = ref CallCache.empty
let local_cache = ref LocalCache.empty
let node_arg_cache = ref LocalCache.empty

let clear_cache () =
  call_cache := CallCache.empty;
  local_cache := LocalCache.empty;
  node_arg_cache := LocalCache.empty;

type source = Local | Input | Output | Ghost

type generated_identifiers = {
  node_args : (string (* abstracted variable name *)
    * bool (* whether the variable is constant *)
    * LustreAst.lustre_type
    * LustreAst.expr)
    list;
  array_constructors :
    (LustreAst.lustre_type
    * LustreAst.expr
    * LustreAst.expr)
    StringMap.t;
  locals : (bool (* whether the variable is ghost *)
    * string list (* scope *)
    * LustreAst.lustre_type
    * LustreAst.expr (* abstracted expression *)
    * LustreAst.expr) (* original expression *)
    StringMap.t;
  contract_calls :
    (Lib.position
    * string list (* contract scope *)
    * LustreAst.contract_node_equation list)
    StringMap.t;
  warnings : (Lib.position * LustreAst.expr) list;
  oracles : (string * LustreAst.lustre_type * LustreAst.expr) list;
  propagated_oracles : (string * string) list;
  calls : (Lib.position (* node call position *)
    * (string list) (* oracle inputs *)
    * string (* abstracted output *)
    * LustreAst.expr (* condition expression *)
    * LustreAst.expr (* restart expression *)
    * string (* node name *)
    * (LustreAst.expr list) (* node arguments *)
    * (LustreAst.expr list option)) (* node argument defaults *)
    list;
  subrange_constraints : (source
    * Lib.position
    * string (* Generated name for Range Expression *)
    * string) (* Original name that is constrained *)
    list;
  equations :
    (LustreAst.typed_ident list (* quantified variables *)
    * string list (* contract scope  *)
    * LustreAst.eq_lhs
    * LustreAst.expr)
    list;
}

type info = {
  context : Ctx.tc_context;
  inductive_variables : LustreAst.lustre_type StringMap.t;
  quantified_variables : LustreAst.typed_ident list;
  node_is_input_const : (bool list) StringMap.t;
  contract_calls : LustreAst.contract_node_decl StringMap.t;
  contract_scope : string list;
  contract_ref : string;
  interpretation : string StringMap.t;
}

let get_warnings map = map
  |> StringMap.bindings
  |> List.map (fun (_, { warnings }) -> warnings)
  |> List.flatten
  |> List.sort (fun (p1, _) (p2, _) -> compare_pos p1 p2)

let pp_print_generated_identifiers ppf gids =
  let locals_list = StringMap.bindings gids.locals 
    |> List.map (fun (x, (y, _, z, w, _)) -> x, y, z, w)
  in
  let array_ctor_list = StringMap.bindings gids.array_constructors
    |> List.map (fun (x, (y, z, w)) -> x, y, z, w)
  in
  let contract_calls_list = StringMap.bindings gids.contract_calls
    |> List.map (fun (x, (y, z, w)) -> x, y, z, w)
  in
  let pp_print_local ppf (id, b, ty, e) = Format.fprintf ppf "(%a, %b, %a, %a)"
    Format.pp_print_string id
    b
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_array_ctor ppf (id, ty, e, s) = Format.fprintf ppf "(%a, %a, %a, %a)"
    Format.pp_print_string id
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
    LustreAst.pp_print_expr s
  in
  let pp_print_node_arg ppf (id, b, ty, e) = Format.fprintf ppf "(%a, %b, %a, %a)"
    Format.pp_print_string id
    b
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_oracle ppf (id, ty, e) = Format.fprintf ppf "(%a, %a, %a)"
    Format.pp_print_string id
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in
  let pp_print_call = (fun ppf (pos, oracles, output, cond, restart, ident, args, defaults) ->
    Format.fprintf ppf 
      "%a: %a = call(%a,(restart %a every %a)(%a;%a),%a)"
      pp_print_position pos
      Format.pp_print_string output
      A.pp_print_expr cond
      Format.pp_print_string ident
      A.pp_print_expr restart
      (pp_print_list A.pp_print_expr ",@ ") args
      (pp_print_list Format.pp_print_string ",@ ") oracles
      (pp_print_option (pp_print_list A.pp_print_expr ",@")) defaults)
  in
  let pp_print_source ppf source = Format.fprintf ppf (match source with
    | Local -> "local"
    | Input -> "input"
    | Output -> "output"
    | Ghost -> "ghost")
  in
  let pp_print_subrange_constraint ppf (source, pos, id, oid) =
    Format.fprintf ppf "(%a, %a, %s, %s)"
      pp_print_source source
      Lib.pp_print_position pos
      id oid
  in
  let pp_print_contract_call ppf (ref, pos, scope, decl) = Format.fprintf ppf "%a := (%a, %a): %a"
    Format.pp_print_string ref
    pp_print_position pos
    (pp_print_list Format.pp_print_string "::") scope
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

let empty () = {
    locals = StringMap.empty;
    warnings = [];
    array_constructors = StringMap.empty;
    node_args = [];
    oracles = [];
    propagated_oracles = [];
    calls = [];
    contract_calls = StringMap.empty;
    subrange_constraints = [];
    equations = [];
  }

let union_keys key id1 id2 = match key, id1, id2 with
  | _, None, None -> None
  | _, (Some v), None -> Some v
  | _, None, (Some v) -> Some v
  (* Identifiers are guaranteed to be unique making this branch impossible *)
  | _, (Some _), (Some _) -> assert false

let union ids1 ids2 = {
    locals = StringMap.merge union_keys ids1.locals ids2.locals;
    array_constructors = StringMap.merge union_keys
      ids1.array_constructors ids2.array_constructors;
    warnings = ids1.warnings @ ids2.warnings;
    node_args = ids1.node_args @ ids2.node_args;
    oracles = ids1.oracles @ ids2.oracles;
    propagated_oracles = ids1.propagated_oracles @ ids2.propagated_oracles;
    calls = ids1.calls @ ids2.calls;
    contract_calls = StringMap.merge union_keys
      ids1.contract_calls ids2.contract_calls;
    subrange_constraints = ids1.subrange_constraints @ ids2.subrange_constraints;
    equations = ids1.equations @ ids2.equations;
  }

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
  string_of_int !contract_ref

let extract_array_size = function
  | A.ArrayType (_, (_, size)) -> (match size with
    | A.Const (_, Num x) -> int_of_string x
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

let mk_fresh_local info pos is_ghost ind_vars expr_type expr oexpr =
  match LocalCache.find_opt expr !local_cache with
  | Some nexpr -> nexpr, empty ()
  | None ->
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_glocal" in
  let scope = info.contract_scope in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    locals = StringMap.singleton name (is_ghost, scope, expr_type, expr, oexpr);
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr)]; }
  in
  local_cache := LocalCache.add expr nexpr !local_cache;
  nexpr, gids

let mk_fresh_array_ctor info pos ind_vars expr_type expr size_expr =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_varray" in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    array_constructors = StringMap.singleton name (expr_type, expr, size_expr);
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr)]; }
  in nexpr, gids

let mk_fresh_node_arg_local info pos is_const ind_vars expr_type expr =
  match LocalCache.find_opt expr !node_arg_cache with
  | Some nexpr -> nexpr, empty ()
  | None ->
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_gklocal" in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { (empty ()) with
    node_args = [(name, is_const, expr_type, expr)];
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, expr)]; }
  in
  node_arg_cache := LocalCache.add expr nexpr !node_arg_cache;
  nexpr, gids

let mk_range_expr expr_type expr = 
  let mk_and tys =
    List.fold_left (fun acc e -> A.BinaryOp (dpos, A.And, acc, e))
      (A.Const (dpos, A.True)) tys
  in
  let rec mk n expr_type expr = match expr_type with
    | A.IntRange (_, l, u) -> 
      let l = A.CompOp (dpos, A.Lte, l, expr) in
      let u = A.CompOp (dpos, A.Lte, expr, u) in
      A.BinaryOp (dpos, A.And, l, u)
    | A.ArrayType (_, (ty, upper_bound)) ->
      let id_str = "x" ^ (string_of_int n) in
      let id = A.Ident (dpos, id_str) in
      let expr = A.ArrayIndex (dpos, expr, id) in
      let rexpr = mk (succ n) ty expr in
      let l = A.CompOp (dpos, A.Lte, A.Const (dpos, A.Num "0"), id) in
      let u = A.CompOp (dpos, A.Lt, id, upper_bound) in
      let assumption = A.BinaryOp (dpos, A.And, l, u) in
      let var = dpos, id_str, (A.Int dpos) in
      let body = A.BinaryOp (dpos, A.Impl, assumption, rexpr) in
      A.Quantifier (dpos, A.Forall, [var], body)
    | TupleType (_, tys) ->
      let mk_proj i = A.TupleProject (dpos, expr, i) in
      let tys = List.filter (fun ty -> AH.type_contains_subrange ty) tys in
      let tys = List.mapi (fun i ty -> mk n ty (mk_proj i)) tys in
      mk_and tys
    | RecordType (_, tys) ->
      let mk_proj i = A.RecordProject (dpos, expr, i) in
      let tys = List.filter (fun (_, _, ty) -> AH.type_contains_subrange ty) tys in
      let tys = List.map (fun (_, i, ty) -> mk n ty (mk_proj i)) tys in
      mk_and tys
    | _ -> assert false
  in
  mk 0 expr_type expr

let mk_fresh_subrange_constraint source info pos constrained_name expr_type =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_subrange" in
  let expr = A.Ident (pos, constrained_name) in
  let nexpr = A.Ident (pos, name) in
  let range_expr = mk_range_expr expr_type expr in
  let (eq_lhs, _) = generalize_to_array_expr name StringMap.empty range_expr nexpr in
  let gids = { (empty ()) with
    subrange_constraints = [(source, pos, name, constrained_name)];
    equations = [(info.quantified_variables, info.contract_scope, eq_lhs, range_expr)]; }
  in
  gids

let mk_fresh_oracle expr_type expr =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_oracle" in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let gids = { (empty ()) with
    oracles = [name, expr_type, expr]; }
  in nexpr, gids

let record_warning pos original =
  { (empty ()) with  warnings = [(pos, original)]; }

let mk_fresh_call id map pos cond restart args defaults =
  let called_node = StringMap.find id map in
  let has_oracles = List.length called_node.oracles > 0 in
  let check_cache = CallCache.find_opt
    (id, cond, restart, args, defaults)
    !call_cache
  in
  match check_cache, has_oracles with
  | Some nexpr, false -> nexpr, empty ()
  | _ ->
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_call" in
  let nexpr = A.Ident (pos, name) in
  let propagated_oracles = 
    let called_oracles = called_node.oracles |> List.map (fun (id, _, _) -> id) in
    let called_poracles = called_node.propagated_oracles |> List.map fst in
    List.map (fun n ->
      (i := !i + 1;
      let prefix = string_of_int !i in
      prefix ^ "_poracle", n))
      (called_oracles @ called_poracles)
  in
  let oracle_args = List.map (fun (p, _) -> p) propagated_oracles in
  let call = (pos, oracle_args, name, cond, restart, id, args, defaults) in
  let gids = { (empty ()) with
    propagated_oracles = propagated_oracles;
    calls = [call];}
  in
  call_cache := CallCache.add (id, cond, restart, args, defaults) nexpr !call_cache;
  nexpr, gids

let normalize_list f list =
  let over_list (nitems, gids) item =
    let (normal_item, ids) = f item in
    normal_item :: nitems, union ids gids
  in let list, gids = List.fold_left over_list ([], empty ()) list in
  List.rev list, gids

let rec normalize ctx (decls:LustreAst.t) =
  let info = { context = ctx;
    inductive_variables = StringMap.empty;
    quantified_variables = [];
    node_is_input_const = compute_node_input_constant_mask decls;
    contract_calls = collect_contract_node_decls decls;
    contract_ref = "";
    contract_scope = [];
    interpretation = StringMap.empty; }
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
  
  Log.log L_trace ("===============================================\n"
    ^^ "Generated Identifiers:\n%a\n\n"
    ^^ "Normalized lustre AST:\n%a\n"
    ^^ "===============================================\n")
    (pp_print_list
      (pp_print_pair
        Format.pp_print_string
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
  let nbody, gids = normalize_contract info map body in
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
    (id, is_extern, params, inputs, outputs, locals, items, contracts) =
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
  let ctx = List.fold_left
    (fun ctx local -> Chk.local_var_binding ctx local
      |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
      |> Res.unwrap)
    ctx
    locals
  in
  let info = { info with context = ctx } in
  (* Record subrange constraints on inputs, outputs, and locals *)
  let gids1 = inputs
    |> List.filter (fun (_, i, _, _, _) -> 
        let ty = Ctx.lookup_ty info.context i |> get in
        let ty = Ctx.expand_nested_type_syn ctx ty in
        AH.type_contains_subrange ty)
    |> List.fold_left (fun acc (p, i, _, _, _) ->
        let ty = Ctx.lookup_ty info.context i |> get in
        let ty = Ctx.expand_nested_type_syn ctx ty in
        (* This inlining step will become unnecessary when the backend no
          longer demands constants in the integer range bounds *)
        let ty = AIC.inline_constants_of_lustre_type info.context ty in
        union acc (mk_fresh_subrange_constraint Input info p i ty))
        (empty ())
  in
  let gids2 = locals
    |> List.filter (function
      | A.NodeVarDecl (_, (_, i, _, _)) -> 
        let ty = Ctx.lookup_ty info.context i |> get in
        let ty = Ctx.expand_nested_type_syn ctx ty in
        AH.type_contains_subrange ty
      | _ -> false)
    |> List.fold_left (fun acc l -> match l with
      | A.NodeVarDecl (p, (_, i, _, _)) -> 
          let ty = Ctx.lookup_ty info.context i |> get in
          let ty = Ctx.expand_nested_type_syn ctx ty in
          (* This inlining step will become unnecessary when the backend no
            longer demands constants in the integer range bounds *)
          let ty = AIC.inline_constants_of_lustre_type info.context ty in
          union acc (mk_fresh_subrange_constraint Local info p i ty)
      | _ -> assert false)
      (empty ())
  in
  let gids3 = outputs
    |> List.filter (fun (_, i, _, _) -> 
        let ty = Ctx.lookup_ty info.context i |> get in
        let ty = Ctx.expand_nested_type_syn ctx ty in
        AH.type_contains_subrange ty)
    |> List.fold_left (fun acc (p, i, _, _) ->
        let ty = Ctx.lookup_ty info.context i |> get in
        let ty = Ctx.expand_nested_type_syn ctx ty in
        (* This inlining step will become unnecessary when the backend no
          longer demands constants in the integer range bounds *)
        let ty = AIC.inline_constants_of_lustre_type info.context ty in
        union acc (mk_fresh_subrange_constraint Output info p i ty))
        (empty ())
  in
  (* Normalize equations and the contract *)
  let nitems, gids4 = normalize_list (normalize_item info map) items in
  let ncontracts, gids5 = match contracts with
    | Some contracts ->
      let ctx = Chk.tc_ctx_of_contract info.context contracts
        |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
        |> Res.unwrap in
      let contract_ref = new_contract_reference () in
      let info = { info with context = ctx; contract_ref } in
      let ncontracts, gids = normalize_contract info map
        contracts in
      (Some ncontracts), gids
    | None -> None, empty ()
  in
  let gids = union_list [gids1; gids2; gids3; gids4; gids5] in
  let map = StringMap.singleton id gids in
  (id, is_extern, params, inputs, outputs, locals, nitems, ncontracts), map

and normalize_item info map = function
  | Body equation ->
    let nequation, gids = normalize_equation info map equation in
    Body nequation, gids
  | AnnotMain b -> AnnotMain b, empty ()
  | AnnotProperty (pos, name, expr) ->
    let nexpr, gids = abstract_expr false info map false expr in
    AnnotProperty (pos, name, nexpr), gids

and rename_ghost_variables info = function
  | [] -> [StringMap.empty]
  | (A.GhostConst (UntypedConst (_, id, _))
  | GhostConst (TypedConst (_, id, _, _))) :: t ->
    let new_id = info.contract_ref ^ "_contract_" ^ id in
    (StringMap.singleton id new_id) :: rename_ghost_variables info t
  | (A.GhostVar (UntypedConst (_, id, _))
  | GhostVar (TypedConst (_, id, _, _))) :: t ->
    let new_id = info.contract_ref ^ "_contract_" ^ id in
    (StringMap.singleton id new_id) :: rename_ghost_variables info t
  | _ :: t -> rename_ghost_variables info t

and normalize_contract info map items =
  let gids = ref (empty ()) in
  let result = ref [] in
  let ghost_interp = rename_ghost_variables info items in
  let ghost_interp = List.fold_left (StringMap.merge union_keys)
    StringMap.empty ghost_interp in
  let interp = StringMap.merge union_keys ghost_interp info.interpretation in
  let interpretation = ref interp in

  for j = 0 to (List.length items) - 1 do
    let info = { info with interpretation = !interpretation } in
    let item = List.nth items j in
    let nitem, gids', interpretation' = match item with
      | Assume (pos, name, soft, expr) ->
        let nexpr, gids = abstract_expr false info map true expr in
        A.Assume (pos, name, soft, nexpr), gids, StringMap.empty
      | Guarantee (pos, name, soft, expr) -> 
        let nexpr, gids = abstract_expr false info map true expr in
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
        let ninputs = List.map (fun e -> 
          match e with
          | A.Ident (_, i) -> i
          | _ -> assert false)
          ninputs
        in
        let cref = new_contract_reference () in
        let info = { info with
          contract_scope = name :: info.contract_scope;
          contract_ref = cref;
          } in
        let called_node = StringMap.find name info.contract_calls in
        let normalized_call, gids2, interp = 
          normalize_node_contract info map cref ninputs outputs called_node
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
      | GhostVar decl ->
        let gids1 = match decl with
          | UntypedConst (pos, i, _)
          | FreeConst (pos, i, _)
          | TypedConst (pos, i, _, _) ->
            let ty = Ctx.lookup_ty info.context i |> get in
            let ty = Ctx.expand_nested_type_syn info.context ty in
            (* This inlining step will become unnecessary when the backend no
              longer demands constants in the integer range bounds *)
            let ty = AIC.inline_constants_of_lustre_type info.context ty in
            if AH.type_contains_subrange ty then
              mk_fresh_subrange_constraint Ghost info pos i ty
            else empty ()
        in
        let ndecl, gids2 = normalize_ghost_declaration info map decl in
        GhostVar ndecl, union gids1 gids2, StringMap.empty
    in
(*     Format.eprintf "accum interp: %a\n\n"
      (pp_print_list
        (pp_print_pair
          Format.pp_print_string
          Format.pp_print_string
          ":")
        "\n")
      (StringMap.bindings !interpretation);
    Format.eprintf "new interp: %a\n\n"
      (pp_print_list
        (pp_print_pair
          Format.pp_print_string
          Format.pp_print_string
          ":")
        "\n")
      (StringMap.bindings interpretation'); *)
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
        in let ty = match Ctx.lookup_ty info.context v with 
          | Some t -> t | None -> assert false
        in let ivars = List.fold_left (fun m i -> StringMap.add i ty m)
          StringMap.empty
          is
        in { info with inductive_variables = ivars}
      | _ -> info)
      info
      items
    in
    let nexpr, gids = normalize_expr info map expr in
    Equation (pos, lhs, nexpr), gids
  | Automaton _ -> Lib.todo __LOC__

and rename_id info = function
  | A.Ident (pos, id) ->
    (match (StringMap.find_opt id info.interpretation) with
      | Some new_id -> A.Ident (pos, new_id)
      | None -> A.Ident (pos, id))
  | _ -> assert false

and abstract_expr ?guard force info map is_ghost expr = 
  let ivars = info.inductive_variables in
  (* If [expr] is already an id or const then we don't create a fresh local *)
  if AH.expr_is_id expr && not force then
    rename_id info expr, empty ()
  else
    let pos = AH.pos_of_expr expr in
    let ty = if expr_has_inductive_var ivars expr |> is_some then
      (StringMap.choose_opt info.inductive_variables) |> get |> snd
    else Chk.infer_type_expr info.context expr
      |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
      |> Res.unwrap in
    let nexpr, gids1 = normalize_expr ?guard info map expr in
    let iexpr, gids2 = mk_fresh_local info pos is_ghost ivars ty nexpr expr in
    iexpr, union gids1 gids2

and expand_node_call expr var count =
  let mk_index i = A.Const (dpos, Num (string_of_int i)) in
  let array = List.init count (fun i -> AH.substitute var (mk_index i) expr) in
  A.GroupExpr (dpos, ArrayExpr, array)

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
    if AH.expr_is_id expr && not force then
      rename_id info expr, empty ()
    else
      let ivars = info.inductive_variables in
      let pos = AH.pos_of_expr expr in
      let ty = if expr_has_inductive_var ivars expr |> is_some then
        (StringMap.choose_opt info.inductive_variables) |> get |> snd
      else Chk.infer_type_expr info.context expr
        |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
        |> Res.unwrap in
      let nexpr, gids1 = normalize_expr ?guard info map expr in
      let iexpr, gids2 = mk_fresh_node_arg_local info pos is_const ivars ty nexpr in
      iexpr, union gids1 gids2
  in function
  (* ************************************************************************ *)
  (* Node calls                                                               *)
  (* ************************************************************************ *)
  | Call (pos, id, args) as e ->
    let ivars = info.inductive_variables in
    let ivar = List.map (fun a -> expr_has_inductive_var ivars a) args in
    let ivar = List.nth_opt ivar 0 |> join in
    if is_some ivar then
      let _, size = StringMap.choose ivars in
      let size = extract_array_size size in
      let expr = expand_node_call e (get ivar) size in
      normalize_expr ?guard info map expr
    else
      let flags = StringMap.find id info.node_is_input_const in
      let cond = A.Const (Lib.dummy_pos, A.True) in
      let restart =  A.Const (Lib.dummy_pos, A.False) in
      let nargs, gids1 = normalize_list
        (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
        (combine_args_with_const info args flags)
      in
      let nexpr, gids2 = mk_fresh_call id map pos cond restart nargs None in
      nexpr, union gids1 gids2
  | Condact (pos, cond, restart, id, args, defaults) as e ->
    let ivars = info.inductive_variables in
    let ivar = List.map (fun a -> expr_has_inductive_var ivars a) args in
    let ivar = List.nth_opt ivar 0 |> join in
    if is_some ivar then
      let _, size = StringMap.choose ivars in
      let size = extract_array_size size in
      let expr = expand_node_call e (get ivar) size in
      normalize_expr ?guard info map expr
    else
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
      let nexpr, gids5 = mk_fresh_call id map pos ncond nrestart nargs (Some ndefaults) in
      let gids = union_list [gids1; gids2; gids3; gids4; gids5] in
      nexpr, gids
  | RestartEvery (pos, id, args, restart) as e ->
    let ivars = info.inductive_variables in
    let ivar = List.map (fun a -> expr_has_inductive_var ivars a) args in
    let ivar = List.nth_opt ivar 0 |> join in
    if is_some ivar then
      let _, size = StringMap.choose ivars in
      let size = extract_array_size size in
      let expr = expand_node_call e (get ivar) size in
      normalize_expr ?guard info map expr
    else
      let flags = StringMap.find id info.node_is_input_const in
      let cond = A.Const (dummy_pos, A.True) in
      let nrestart, gids1 = if AH.expr_is_const restart then restart, empty ()
        else abstract_expr ?guard true info map false restart
      in let nargs, gids2 = normalize_list
        (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
        (combine_args_with_const info args flags)
      in
      let nexpr, gids3 = mk_fresh_call id map pos cond nrestart nargs None in
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
        let nexpr, gids4 = mk_fresh_call id map pos ncond nrestart nargs None in
        let gids = union_list [gids1; gids2; gids3; gids4] in
        (clock_value, nexpr), gids
      | clock_value, A.Call (pos, id, args) ->
        let flags = StringMap.find id info.node_is_input_const in
        let cond_expr = match clock_value with
          | "true" -> A.Ident (pos, clock_id)
          | "false" -> A.UnaryOp (pos, A.Not, A.Ident (pos, clock_id))
          | _ -> A.CompOp (pos, A.Eq, A.Ident (pos, clock_id), A.Ident (pos, clock_value))
        in let ncond, gids1 = abstract_expr ?guard false info map false cond_expr in
        let restart =  A.Const (Lib.dummy_pos, A.False) in
        let nargs, gids2 = normalize_list
          (fun (arg, is_const) -> abstract_node_arg ?guard:None false is_const info map arg)
          (combine_args_with_const info args flags)
        in
        let nexpr, gids3 = mk_fresh_call id map pos ncond restart nargs None in
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
      else Chk.infer_type_expr info.context expr
        |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
        |> Res.unwrap in
    let nexpr, gids1 = abstract_expr ?guard false info map false expr in
    let guard, gids2, previously_guarded = match guard with
      | Some guard -> guard, empty (), true
      | None ->
        let guard, gids1 = mk_fresh_oracle ty nexpr in
        let gids2 = record_warning pos p in
        guard, union gids1 gids2, false
    in let gids = union gids1 gids2 in
    let nexpr' = match nexpr with
      | A.ArrayIndex (pos2, expr1, expr2) ->
        A.ArrayIndex (pos2, Pre (pos, expr1), expr2)
      | e -> Pre (pos, e)
    in if previously_guarded then nexpr', gids
    else Arrow (Lib.dummy_pos, guard, nexpr'), gids
  (* ************************************************************************ *)
  (* Misc. abstractions                                                       *)
  (* ************************************************************************ *)
  | ArrayConstr (pos, expr, size_expr) ->
    let ivars = info.inductive_variables in
    let ty = if expr_has_inductive_var ivars expr |> is_some then
      (StringMap.choose_opt info.inductive_variables) |> get |> snd
    else Chk.infer_type_expr info.context expr
      |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
      |> Res.unwrap in
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
  | Last _ as expr -> expr, empty ()
  | Fby (pos, expr1, i, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    Fby (pos, nexpr1, i, nexpr2), union gids1 gids2
  | CallParam (pos, id, type_list, expr_list) ->
    let nexpr_list, gids = normalize_list
      (normalize_expr ?guard info map)
      expr_list in
    CallParam (pos, id, type_list, nexpr_list), gids
