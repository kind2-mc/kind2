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
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker

module StringMap = struct
  include Map.Make(struct
    type t = string
    let compare i1 i2 = String.compare i1 i2
  end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end

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
    * LustreAst.lustre_type
    * LustreAst.expr)
    StringMap.t;
  warnings : (Lib.position * LustreAst.expr) list;
  oracles : (string * LustreAst.expr) list;
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
  equations : (LustreAst.eq_lhs
    * LustreAst.expr)
    list
}

type info = {
  context : Ctx.tc_context;
  inductive_variables : LustreAst.lustre_type StringMap.t;
  node_is_input_const : (bool list) StringMap.t
}

let get_warnings map = map
  |> StringMap.bindings
  |> List.map (fun (_, { warnings }) -> warnings)
  |> List.flatten
  |> List.sort (fun (p1, _) (p2, _) -> compare_pos p1 p2)

let pp_print_generated_identifiers ppf gids =
  let locals_list = StringMap.bindings gids.locals 
    |> List.map (fun (x, (y, z, w)) -> x, y, z, w)
  in let array_ctor_list = StringMap.bindings gids.array_constructors
    |> List.map (fun (x, (y, z, w)) -> x, y, z, w)
  in let pp_print_local ppf (id, b, ty, e) = Format.fprintf ppf "(%a, %b, %a, %a)"
    Format.pp_print_string id
    b
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in let pp_print_array_ctor ppf (id, ty, e, s) = Format.fprintf ppf "(%a, %a, %a, %a)"
    Format.pp_print_string id
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
    LustreAst.pp_print_expr s
  in let pp_print_node_arg ppf (id, b, ty, e) = Format.fprintf ppf "(%a, %b, %a, %a)"
    Format.pp_print_string id
    b
    LustreAst.pp_print_lustre_type ty
    LustreAst.pp_print_expr e
  in let pp_print_oracle = pp_print_pair
    Format.pp_print_string
    LustreAst.pp_print_expr
    ":"
  in let pp_print_call = (fun ppf (pos, oracles, output, cond, restart, ident, args, defaults) ->
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
  in Format.fprintf ppf "%a\n%a\n%a\n%a\n%a\n"
    (pp_print_list pp_print_oracle "\n") gids.oracles
    (pp_print_list pp_print_array_ctor "\n") array_ctor_list
    (pp_print_list pp_print_local "\n") locals_list
    (pp_print_list pp_print_node_arg "\n") gids.node_args
    (pp_print_list pp_print_call "\n") gids.calls

let compute_node_input_constant_mask decls =
  let over_decl map = function
  | A.NodeDecl (pos, (id, _, _, inputs, _, _, _, _)) ->
    let is_consts = List.map (fun (_, _, _, _, c) -> c) inputs in
    StringMap.add id is_consts map
  | FuncDecl (pos, (id, _, _, inputs, _, _, _, _)) ->
    let is_consts = List.map (fun (_, _, _, _, c) -> c) inputs in
    StringMap.add id is_consts map
  | decl -> map
  in List.fold_left over_decl StringMap.empty decls

(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let dpos = Lib.dummy_pos

let empty = {
    locals = StringMap.empty;
    warnings = [];
    array_constructors = StringMap.empty;
    node_args = [];
    oracles = [];
    propagated_oracles = [];
    calls = [];
    equations = [];
  }

let union_keys key id1 id2 = match key, id1, id2 with
  | key, None, None -> None
  | key, (Some v), None -> Some v
  | key, None, (Some v) -> Some v
  (* Identifiers are guaranteed to be unique making this branch impossible *)
  | key, (Some v1), (Some v2) -> assert false

let union ids1 ids2 = {
    locals = StringMap.merge union_keys ids1.locals ids2.locals;
    array_constructors = StringMap.merge union_keys
      ids1.array_constructors ids2.array_constructors;
    warnings = ids1.warnings @ ids2.warnings;
    node_args = ids1.node_args @ ids2.node_args;
    oracles = ids1.oracles @ ids2.oracles;
    propagated_oracles = ids1.propagated_oracles @ ids2.propagated_oracles;
    calls = ids1.calls @ ids2.calls;
    equations = ids1.equations @ ids2.equations;
  }

let union_list ids =
  List.fold_left (fun x y -> union x y ) empty ids

let expr_has_inductive_var ind_vars expr =
  let vars = AH.vars expr in
  let ind_vars = List.map (fun (i, _) -> i) (StringMap.bindings ind_vars) in
  let ind_vars = List.filter (fun x -> A.SI.mem x vars) ind_vars in
  match ind_vars with
  | [] -> None
  | h :: t -> Some h

let extract_array_size expr = function
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

let mk_fresh_local pos is_ghost ind_vars expr_type expr =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_glocal" in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = {
    locals = StringMap.singleton name (is_ghost, expr_type, expr);
    array_constructors = StringMap.empty;
    warnings = [];
    node_args = [];
    oracles = [];
    propagated_oracles = [];
    calls = []; 
    equations = [(eq_lhs, expr)] }
  in nexpr, gids

let mk_fresh_array_ctor pos ind_vars expr_type expr size_expr =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_varray" in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { locals = StringMap.empty;
    array_constructors = StringMap.singleton name (expr_type, expr, size_expr);
    warnings = [];
    node_args = [];
    oracles = [];
    propagated_oracles = [];
    calls = []; 
    equations = [(eq_lhs, expr)] }
  in nexpr, gids

let mk_fresh_node_arg_local pos is_const ind_vars expr_type expr =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_gklocal" in
  let nexpr = A.Ident (pos, name) in
  let (eq_lhs, nexpr) = generalize_to_array_expr name ind_vars expr nexpr in
  let gids = { locals = StringMap.empty;
    array_constructors = StringMap.empty;
    warnings = [];
    node_args = [(name, is_const, expr_type, expr)];
    oracles = [];
    propagated_oracles = [];
    calls = [];
    equations = [(eq_lhs, expr)] }
  in nexpr, gids

let mk_fresh_oracle expr =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_oracle" in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let gids = { locals = StringMap.empty;
    array_constructors = StringMap.empty;
    warnings = [];
    node_args = [];
    oracles = [name, expr];
    propagated_oracles = [];
    calls = [];
    equations = [] }
  in nexpr, gids

let record_warning pos original =
  { locals = StringMap.empty;
    array_constructors = StringMap.empty;
    warnings = [(pos, original)];
    node_args = [];
    oracles = [];
    propagated_oracles = [];
    calls = [];
    equations = [] }

let mk_fresh_call id map pos cond restart args defaults =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_call" in
  let nexpr = A.Ident (pos, name)
  in let propagated_oracles = 
    let called_node = StringMap.find id map in
    let called_oracles = called_node.oracles |> List.map fst in
    let called_poracles = called_node.propagated_oracles |> List.map fst in
    List.map (fun n ->
      (i := !i + 1;
      let prefix = string_of_int !i in
      prefix ^ "_poracle", n))
      (called_oracles @ called_poracles)
  in let oracle_args = List.map (fun (p, o) -> p) propagated_oracles
  in let call = (pos, oracle_args, name, cond, restart, id, args, defaults) in
  let gids = { locals = StringMap.empty;
    array_constructors = StringMap.empty;
    warnings = [];
    node_args = [];
    oracles = [];
    propagated_oracles = propagated_oracles;
    calls = [call];
    equations = [] }
  in nexpr, gids

let normalize_list f list =
  let over_list (nitems, gids) item =
    let (normal_item, ids) = f item in
    normal_item :: nitems, union ids gids
  in let list, gids = List.fold_left over_list ([], empty) list in
  List.rev list, gids

let rec normalize ctx (decls:LustreAst.t) =
  let info = { context = ctx;
    inductive_variables = StringMap.empty;
    node_is_input_const = compute_node_input_constant_mask decls }
  in let over_declarations (nitems, node_maps) item =
    let (normal_item, node_map) = normalize_declaration info node_maps item in
    normal_item :: nitems, StringMap.merge union_keys node_map node_maps
  in let ast, node_map = List.fold_left over_declarations ([], StringMap.empty) decls
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
      (StringMap.bindings node_map)
    A.pp_print_program ast;

  Res.ok (ast, node_map)

and normalize_declaration ctx map = function
  | NodeDecl (pos, decl) ->
    let normal_decl, node_map = normalize_node ctx map decl in
    A.NodeDecl(pos, normal_decl), node_map
  | FuncDecl (pos, decl) ->
    let normal_decl, node_map = normalize_node ctx map decl in
    A.FuncDecl (pos, normal_decl), node_map
  | decl -> decl, StringMap.empty

and normalize_node info map
    (id, is_func, params, inputs, outputs, locals, items, contracts) =
  (* It would be better if the type checker was elaborating
    (i.e. tracking the types associated with identifiers) so that
    reconstructing types didn't require rebuilding contexts and retype
    checking *)
  let constants_ctx = inputs
    |> List.map Ctx.extract_consts
    |> (List.fold_left Ctx.union info.context) in
  let input_ctx = inputs
    |> List.map Ctx.extract_arg_ctx
    |> (List.fold_left Ctx.union info.context)
  in let output_ctx = outputs
    |> List.map Ctx.extract_ret_ctx
    |> (List.fold_left Ctx.union info.context)
  in let ctx = Ctx.union
    (Ctx.union constants_ctx info.context)
    (Ctx.union input_ctx output_ctx)
  in let ctx = List.fold_left
    (fun ctx local -> Chk.local_var_binding ctx local
      |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
      |> Res.unwrap)
    ctx
    locals
  in let info = { info with context = ctx } in
  let nitems, gids1 = normalize_list (normalize_item info map) items in
  let ncontracts, gids2 = match contracts with
    | Some contracts ->
      let ncontracts, gids = normalize_list
        (normalize_contract info map)
        contracts in
      (Some ncontracts), gids
    | None -> None, empty
  in let gids = union gids1 gids2 in
  let node_map = StringMap.singleton id gids in
  (id, is_func, params, inputs, outputs, locals, nitems, ncontracts), node_map

and normalize_item info map = function
  | Body equation ->
    let nequation, gids = normalize_equation info map equation in
    Body nequation, gids
  | AnnotMain b -> AnnotMain b, empty
  | AnnotProperty (pos, name, expr) ->
    let nexpr, gids = abstract_expr info map false expr in
    AnnotProperty (pos, name, nexpr), gids

and normalize_contract info map = function
  | Assume (pos, name, soft, expr) ->
    let nexpr, gids = normalize_expr info map expr in
    Assume (pos, name, soft, nexpr), gids
  | Guarantee (pos, name, soft, expr) -> 
    let nexpr, gids = normalize_expr info map expr in
    Guarantee (pos, name, soft, nexpr), gids
  | Mode (pos, name, requires, ensures) ->
    let over_property info map (pos, name, expr) =
      let nexpr, gids = normalize_expr info map expr in
      (pos, name, nexpr), gids
    in
    let nrequires, gids1 = normalize_list (over_property info map) requires in
    let nensures, gids2 = normalize_list (over_property info map) ensures in
    Mode (pos, name, nrequires, nensures), union gids1 gids2
  | ContractCall (pos, name, inputs, outputs) ->
    let ninputs, gids = normalize_list (normalize_expr info map) inputs in
    ContractCall (pos, name, ninputs, outputs), gids
  | decl -> decl, empty

and normalize_equation info map = function
  | Assert (pos, expr) ->
    let nexpr, gids = abstract_expr info map true expr in
    Assert (pos, nexpr), gids
  | Equation (pos, lhs, expr) ->
    (* Need to track array indexes of the left hand side if there are any *)
    let items = match lhs with | A.StructDef (pos, items) -> items in
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
  | Automaton (pos, id, states, auto) -> Lib.todo __LOC__

and abstract_expr ?guard info map is_ghost expr = 
  let ivars = info.inductive_variables in
  (* If [expr] is already an id or const then we don't create a fresh local *)
  if AH.expr_is_id expr then
    expr, empty
  else
    let pos = AH.pos_of_expr expr in
    let ty = if expr_has_inductive_var ivars expr |> is_some then
      (StringMap.choose_opt info.inductive_variables) |> get |> snd
    else Chk.infer_type_expr info.context expr
      |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
      |> Res.unwrap in
    let nexpr, gids1 = normalize_expr ?guard info map expr in
    let iexpr, gids2 = mk_fresh_local pos is_ghost ivars ty nexpr in
    iexpr, union gids1 gids2

and expand_node_call expr var count =
  let mk_index i = A.Const (dpos, Num (string_of_int i)) in
  let array = List.init count (fun i -> AH.substitute var (mk_index i) expr) in
  A.GroupExpr (dpos, ArrayExpr, array)

and normalize_expr ?guard info map =
  let abstract_node_arg ?guard is_const info map expr = 
    let ivars = info.inductive_variables in
    if AH.expr_is_id expr then
      expr, empty
    else
      let pos = AH.pos_of_expr expr in
      let ty = if expr_has_inductive_var ivars expr |> is_some then
        (StringMap.choose_opt info.inductive_variables) |> get |> snd
      else Chk.infer_type_expr info.context expr
        |> Res.map_err (fun (_, s) -> fun ppf -> Format.pp_print_string ppf s)
        |> Res.unwrap in
      let nexpr, gids1 = normalize_expr ?guard info map expr in
      let iexpr, gids2 = mk_fresh_node_arg_local pos is_const ivars ty nexpr in
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
      let (var, size) = StringMap.choose ivars in
      let size = extract_array_size var size in
      let expr = expand_node_call e (get ivar) size in
      normalize_expr ?guard info map expr
    else
      let cond = A.Const (Lib.dummy_pos, A.True) in
      let restart =  A.Const (Lib.dummy_pos, A.False) in
      let nargs, gids1 = normalize_list
        (fun (arg, is_const) -> abstract_node_arg ?guard is_const info map arg)
        (List.combine args (StringMap.find id info.node_is_input_const)) in
      let nexpr, gids2 = mk_fresh_call id map pos cond restart nargs None in
      nexpr, union gids1 gids2
  | Condact (pos, cond, restart, id, args, defaults) as e ->
    let ivars = info.inductive_variables in
    let ivar = List.map (fun a -> expr_has_inductive_var ivars a) args in
    let ivar = List.nth_opt ivar 0 |> join in
    if is_some ivar then
      let (var, size) = StringMap.choose ivars in
      let size = extract_array_size var size in
      let expr = expand_node_call e (get ivar) size in
      normalize_expr ?guard info map expr
    else
      let ncond, gids1 = if AH.expr_is_true cond then cond, empty
        else abstract_expr ?guard info map false cond in
      let nrestart, gids2 = if AH.expr_is_const restart then restart, empty
        else abstract_expr ?guard info map false restart
      in let nargs, gids3 = normalize_list
        (fun (arg, is_const) -> abstract_node_arg ?guard is_const info map arg)
        (List.combine args (StringMap.find id info.node_is_input_const)) in
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
      let (var, size) = StringMap.choose ivars in
      let size = extract_array_size var size in
      let expr = expand_node_call e (get ivar) size in
      normalize_expr ?guard info map expr
    else
      let cond = A.Const (dummy_pos, A.True) in
      let nrestart, gids1 = if AH.expr_is_const restart then restart, empty
        else abstract_expr ?guard info map false restart
      in let nargs, gids2 = normalize_list
        (fun (arg, is_const) -> abstract_node_arg ?guard is_const info map arg)
        (List.combine args (StringMap.find id info.node_is_input_const)) in
      let nexpr, gids3 = mk_fresh_call id map pos cond nrestart nargs None in
      let gids = union_list [gids1; gids2; gids3] in
      nexpr, gids
  | Merge (pos, clock_id, cases) ->
    let normalize' info map ?guard = function
      | clock_value, A.Activate (pos, id, cond, restart, args) ->
        let ncond, gids1 = if AH.expr_is_true cond then cond, empty
          else abstract_expr ?guard info map false cond in
        let nrestart, gids2 = if AH.expr_is_const restart then restart, empty
          else abstract_expr ?guard info map false restart in
        let nargs, gids3 = normalize_list
          (fun (arg, is_const) -> abstract_node_arg ?guard is_const info map arg)
          (List.combine args (StringMap.find id info.node_is_input_const)) in
        let nexpr, gids4 = mk_fresh_call id map pos ncond nrestart nargs None in
        let gids = union_list [gids1; gids2; gids3; gids4] in
        (clock_value, nexpr), gids
      | clock_value, A.Call (pos, id, args) ->
        let cond_expr = match clock_value with
          | "true" -> A.Ident (pos, clock_id)
          | "false" -> A.UnaryOp (pos, A.Not, A.Ident (pos, clock_id))
          | _ -> A.CompOp (pos, A.Eq, A.Ident (pos, clock_id), A.Ident (pos, clock_value))
        in let ncond, gids1 = abstract_expr ?guard info map false cond_expr in
        let restart =  A.Const (Lib.dummy_pos, A.False) in
        let nargs, gids2 = normalize_list
          (fun (arg, is_const) -> abstract_node_arg ?guard is_const info map arg)
          (List.combine args (StringMap.find id info.node_is_input_const)) in
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
    let nexpr, gids1 = abstract_expr ?guard info map false expr in
    let guard, gids2, previously_guarded = match guard with
      | Some guard -> guard, empty, true
      | None -> let guard, gids1 = mk_fresh_oracle nexpr in
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
    let iexpr, gids2 = mk_fresh_array_ctor pos ivars ty nexpr size_expr in
    ArrayConstr (pos, iexpr, size_expr), union gids1 gids2
  (* ************************************************************************ *)
  (* The remaining expr kinds are all just structurally recursive             *)
  (* ************************************************************************ *)
  | Ident _ as expr -> expr, empty
  | ModeRef _ as expr -> expr, empty
  | RecordProject (pos, expr, i) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    RecordProject (pos, nexpr, i), gids
  | TupleProject (pos, expr, i) ->
    let nexpr, gids = normalize_expr ?guard info map expr in
    TupleProject (pos, nexpr, i), gids
  | Const _ as expr -> expr, empty
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
  | Last _ as expr -> expr, empty
  | Fby (pos, expr1, i, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard info map expr1 in
    let nexpr2, gids2 = normalize_expr ?guard info map expr2 in
    Fby (pos, nexpr1, i, nexpr2), union gids1 gids2
  | CallParam (pos, id, type_list, expr_list) ->
    let nexpr_list, gids = normalize_list
      (normalize_expr ?guard info map)
      expr_list in
    CallParam (pos, id, type_list, nexpr_list), gids
