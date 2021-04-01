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

     @author Andrew Marmaduke *)

open Lib

module A = LustreAst

(** Map for types with identifiers as keys *)
module IMap = struct
  include Map.Make(struct
    type t = LustreAst.ident
    let compare i1 i2 = Stdlib.compare i1 i2
  end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end

type generated_identifiers = {
    locals : LustreAst.expr IMap.t;
    oracles : LustreAst.ident list
}

let pp_print_generated_identifiers ppf gids =
  let locals_list = IMap.bindings gids.locals |> List.rev in
  let pp_print_local = pp_print_pair
    Format.pp_print_string
    A.pp_print_expr
    " = "
  in
  let pp_print_oracle = Format.pp_print_string in
  Format.fprintf ppf "%a\n%a"
    (pp_print_list pp_print_oracle "\n") gids.oracles
    (pp_print_list pp_print_local "\n") locals_list


(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref 0

let empty = {
    locals = IMap.empty;
    oracles = []
  }

let union ids1 ids2 =
  let f key id1 id2 = match key, id1, id2 with
    | key, None, None -> None
    | key, (Some v), None -> Some v
    | key, None, (Some v) -> Some v
    (* Identifiers are guaranteed to be unique making this branch impossible *)
    | key, (Some v1), (Some v2) -> assert false
  in {
    locals = IMap.merge f ids1.locals ids2.locals;
    oracles = ids1.oracles @ ids2.oracles
  }

let mk_fresh_local expr =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_glocal" in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let glocal = IMap.singleton name expr in
  let gids = { locals = glocal; oracles = [] } in
  nexpr, gids

let mk_fresh_oracle () =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_oracle" in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let gids = { locals = IMap.empty; oracles = [name] } in
  nexpr, gids

let expr_is_id : A.expr -> bool = function
  | Ident (_, _) -> true
  | _ -> false

let expr_is_const : A.expr -> bool = function
  | Const (_, _) -> true
  | _ -> false

let normalize_list f list =
  let over_list (nitems, gids) item =
    let (normal_item, ids) = f item in
    normal_item :: nitems, union ids gids
  in List.fold_left over_list ([], empty) list

let rec normalize (decls:LustreAst.t) =
  let ast, gids = normalize_list normalize_declaration decls in
  Log.log L_trace ("===============================================\n"
    ^^ "Generated Identifiers:\n%a\n\n"
    ^^ "Normalized lustre AST:\n%a\n"
    ^^ "===============================================\n")
    pp_print_generated_identifiers gids
    A.pp_print_program ast;
  Res.ok (ast, gids)

and normalize_declaration = function
  | NodeDecl (pos, decl) ->
    let normal_decl, gids = normalize_node decl in
    A.NodeDecl(pos, normal_decl), gids
  | FuncDecl (pos, decl) ->
    let normal_decl, gids = normalize_node decl in
    A.FuncDecl (pos, normal_decl), gids
  | decl -> decl, empty

and normalize_node
    (id, is_func, params, inputs, outputs, locals, items, contracts) =
  let nitems, gids1 = normalize_list normalize_item items in
  let ncontracts, gids2 = match contracts with
    | Some contracts ->
      let ncontracts, gids = normalize_list normalize_contract contracts in
      (Some ncontracts), gids
    | None -> None, empty
  in let gids = union gids1 gids2 in
  (id, is_func, params, inputs, outputs, locals, nitems, ncontracts), gids

and normalize_item = function
  | Body equation ->
    let nequation, gids = normalize_equation equation in
    Body nequation, gids
  | AnnotMain b -> AnnotMain b, empty
  | AnnotProperty (pos, name, expr) ->
    let nexpr, gids = normalize_expr expr in
    AnnotProperty (pos, name, nexpr), gids

and normalize_contract = function
  | Assume (pos, name, soft, expr) ->
    let nexpr, gids = normalize_expr expr in
    Assume (pos, name, soft, nexpr), gids
  | Guarantee (pos, name, soft, expr) -> 
    let nexpr, gids = normalize_expr expr in
    Guarantee (pos, name, soft, nexpr), gids
  | Mode (pos, name, requires, ensures) ->
    let over_property (pos, name, expr) =
      let nexpr, gids = normalize_expr expr in
      (pos, name, nexpr), gids
    in
    let nrequires, gids1 = normalize_list over_property requires in
    let nensures, gids2 = normalize_list over_property ensures in
    Mode (pos, name, nrequires, nensures), union gids1 gids2
  | ContractCall (pos, name, inputs, outputs) ->
    let ninputs, gids = normalize_list normalize_expr inputs in
    ContractCall (pos, name, ninputs, outputs), gids
  | decl -> decl, empty

and normalize_equation = function
  | Assert (pos, expr) ->
    let nexpr, gids = normalize_expr expr in
    Assert (pos, nexpr), gids
  | Equation (pos, lhs, expr) ->
    let nexpr, gids = normalize_expr expr in
    Equation (pos, lhs, nexpr), gids
  | Automaton (pos, id, states, auto) ->
    A.Automaton (pos, id, states, auto), empty

and normalize_expr ?guard =
  let generate_fresh_ids ?guard expr =
    (* If [expr] is already an id then we don't create a fresh local *)
    if expr_is_id expr then
      expr, empty
    else
      let nexpr, gids1 = normalize_expr ?guard expr in
      let iexpr, gids2 = mk_fresh_local nexpr in
      iexpr, union gids1 gids2
  in function
  (* ************************************************************************ *)
  (* Node calls                                                               *)
  (* ************************************************************************ *)
  | Call (pos, id, args) ->
    let nargs, gids = normalize_list (generate_fresh_ids ?guard) args in
    Call (pos, id, nargs), gids
  | Condact (pos, cond, restart, id, args, defaults) ->
    let ncond, gids1 = normalize_expr ?guard cond in
    let nrestart, gids2 = normalize_expr ?guard restart in
    let nargs, gids3 = normalize_list (generate_fresh_ids ?guard) args in
    let ndefaults, gids4 = normalize_list (normalize_expr ?guard) defaults in
    let gids = union (union gids1 gids2) (union gids3 gids4) in
    Condact (pos, ncond, nrestart, id, nargs, ndefaults), gids
  | RestartEvery (pos, id, args, cond) ->
    let ncond, gids1 = normalize_expr ?guard cond in
    let nargs, gids2 = normalize_list (generate_fresh_ids ?guard) args in
    RestartEvery (pos, id, nargs, ncond), union gids1 gids2
  (* ************************************************************************ *)
  (* Guarding and abstracting pres                                            *)
  (* ************************************************************************ *)
  | Arrow (pos, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard:(Some nexpr1) expr2 in
    let gids = union gids1 gids2 in
    Arrow (pos, nexpr1, nexpr2), gids
  | Pre (pos, expr) ->
    let guard, gids1, previously_guarded = match guard with
      | Some guard -> guard, empty, true
      | None -> let guard, gids = mk_fresh_oracle () in
          guard, gids, false
    in
    (* If [expr] is an id then we don't create a fresh local *)
    let nexpr, gids2 = generate_fresh_ids ?guard:(Some guard) expr in
    let gids = union gids1 gids2 in
    if previously_guarded then Pre (pos, nexpr), gids
    else Arrow (Lib.dummy_pos, guard, Pre (pos, nexpr)), gids
  (* ************************************************************************ *)
  (* The remaining expr kinds are all just structurally recursive             *)
  (* ************************************************************************ *)
  | Ident _ as expr -> expr, empty
  | ModeRef _ as expr -> expr, empty
  | RecordProject (pos, expr, i) ->
    let nexpr, gids = normalize_expr ?guard expr in
    RecordProject (pos, nexpr, i), gids
  | TupleProject (pos, expr, i) ->
    let nexpr, gids = normalize_expr ?guard expr in
    TupleProject (pos, nexpr, i), gids
  | Const _ as expr -> expr, empty
  | UnaryOp (pos, op, expr) ->
    let nexpr, gids = normalize_expr ?guard expr in
    UnaryOp (pos, op, nexpr), gids
  | BinaryOp (pos, op, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    BinaryOp (pos, op, nexpr1, nexpr2), union gids1 gids2
  | TernaryOp (pos, op, expr1, expr2, expr3) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    let nexpr3, gids3 = normalize_expr ?guard expr3 in
    let gids = union (union gids1 gids2) gids3 in
    TernaryOp (pos, op, nexpr1, nexpr2, nexpr3), gids
  | NArityOp (pos, op, expr_list) ->
    let nexpr_list, gids = normalize_list (normalize_expr ?guard) expr_list in
    NArityOp (pos, op, nexpr_list), gids
  | ConvOp (pos, op, expr) ->
    let nexpr, gids = normalize_expr ?guard expr in
    ConvOp (pos, op, nexpr), gids
  | CompOp (pos, op, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    CompOp (pos, op, nexpr1, nexpr2), union gids1 gids2
  | RecordExpr (pos, id, id_expr_list) ->
    let normalize' ?guard (id, expr) =
      let nexpr, gids = normalize_expr ?guard expr in
      (id, nexpr), gids
    in 
    let nid_expr_list, gids = normalize_list (normalize' ?guard) id_expr_list in
    RecordExpr (pos, id, nid_expr_list), gids
  | GroupExpr (pos, kind, expr_list) ->
    let nexpr_list, gids = normalize_list (normalize_expr ?guard) expr_list in
    GroupExpr (pos, kind, nexpr_list), gids
  | StructUpdate (pos, expr1, i, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    StructUpdate (pos, nexpr1, i, nexpr2), union gids1 gids2
  | ArrayConstr (pos, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    ArrayConstr (pos, nexpr1, nexpr2), union gids1 gids2
  | ArraySlice (pos, expr1, (expr2, expr3)) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    let nexpr3, gids3 = normalize_expr ?guard expr3 in
    let gids = union (union gids1 gids2) gids3 in
    ArraySlice (pos, nexpr1, (nexpr2, nexpr3)), gids
  | ArrayIndex (pos, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    ArrayIndex (pos, nexpr1, nexpr2), union gids1 gids2
  | ArrayConcat (pos, expr1, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    ArrayConcat (pos, nexpr1, nexpr2), union gids1 gids2
  | Quantifier (pos, kind, vars, expr) ->
    let nexpr, gids = normalize_expr ?guard expr in
    Quantifier (pos, kind, vars, nexpr), gids
  | When (pos, expr, clock_expr) ->
    let nexpr, gids = normalize_expr ?guard expr in
    When (pos, nexpr, clock_expr), gids
  | Current (pos, expr) ->
    let nexpr, gids = normalize_expr ?guard expr in
    Current (pos, nexpr), gids
  | Activate (pos, id, expr1, expr2, expr_list) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    let nexpr_list, gids3 = normalize_list (normalize_expr ?guard) expr_list in
    let gids = union (union gids1 gids2) gids3 in
    Activate (pos, id, nexpr1, nexpr2, nexpr_list), gids
  | Merge (pos, id, id_expr_list) ->
    let normalize' ?guard (id, expr) =
    let nexpr, gids = normalize_expr ?guard expr in
      (id, nexpr), gids
    in 
    let nid_expr_list, gids = normalize_list (normalize' ?guard) id_expr_list in
    Merge (pos, id, nid_expr_list), gids
  | Last _ as expr -> expr, empty
  | Fby (pos, expr1, i, expr2) ->
    let nexpr1, gids1 = normalize_expr ?guard expr1 in
    let nexpr2, gids2 = normalize_expr ?guard expr2 in
    Fby (pos, nexpr1, i, nexpr2), union gids1 gids2
  | CallParam (pos, id, type_list, expr_list) ->
    let nexpr_list, gids = normalize_list (normalize_expr ?guard) expr_list in
    CallParam (pos, id, type_list, nexpr_list), gids
