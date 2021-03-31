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

  3. Guards of the arrow operator that are not constant or identifiers
    e.g.
      expr1 -> expr2 => l1 -> expr2
    where l1 = expr1

     @author Andrew Marmaduke *)

module A = LustreAst
module AH = LustreAstHelpers

module IMap = struct
  include Map.Make(struct
    type t = LustreAst.ident
    let compare i1 i2 = Stdlib.compare i1 i2
  end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end
(** Map for types with identifiers as keys *)

type generated_identifiers = {
    locals : LustreAst.expr IMap.t;
    oracles : LustreAst.ident list
}

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

let mk_fresh_local (expr:A.expr) =
  i := !i + 1;
  let prefix = string_of_int !i in
  let name = prefix ^ "_glocal" in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let glocal = IMap.singleton name expr in
  let gids = { locals = glocal; oracles = [] } in
  nexpr, gids

let mk_fresh_oracle =
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
  normalize_list normalize_declaration decls |> Result.ok

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

and normalize_expr ?guard = function
  | Call (pos, id, exprs) ->
    let generate_fresh_ids expr =
      (* If [expr] is already an id then we don't create a fresh local *)
      if expr_is_id expr then
        expr, empty
      else
        let pos = AH.pos_of_expr expr in
        let iexpr, gids =
          let guard, gids1 = match guard with
            | Some guard -> guard, empty
            | None -> mk_fresh_oracle
          in
          let nexpr, gids2 = normalize_expr ?guard:(Some guard) expr in
          let gexpr = A.Arrow (pos, guard, nexpr) in
          let iexpr, gids3 = mk_fresh_local gexpr in
          iexpr, union (union gids1 gids2) gids3
      in iexpr, gids
    in let nexprs, gids = normalize_list generate_fresh_ids exprs in
    Call (pos, id, nexprs), gids
  | Arrow (pos, expr1, expr2) ->
    (* If [expr1] is an id or a constant then we don't create a fresh local *)
    let nexpr1, gids1 = if expr_is_id expr1 || expr_is_const expr1 then
        expr1, empty
      else
        let expr1', gids1 = normalize_expr ?guard expr1 in
        let nexpr1, gids2 = mk_fresh_local expr1' in
        nexpr1, union gids1 gids2
    in
    let nexpr2, gids2 = normalize_expr ?guard:(Some nexpr1) expr2 in
    let gids = union gids1 gids2 in
    Arrow (pos, nexpr1, nexpr2), gids
  | Pre (pos, expr) ->
    let guard, gids1, previously_guarded = match guard with
      | Some guard -> guard, empty, true
      | None -> let guard, gids = mk_fresh_oracle in
          guard, gids, false
    in
    (* If [expr] is an id then we don't create a fresh local *)
    let nexpr, gids = if expr_is_id expr then
        expr, empty
      else
        let gexpr, gids1 = normalize_expr ?guard:(Some guard) expr in
        let nexpr, gids2 = mk_fresh_local gexpr in
        nexpr, union gids1 gids2
    in if previously_guarded then Pre (pos, nexpr), gids
    else Arrow (Lib.dummy_pos, guard, Pre (pos, nexpr)), gids
  | expr -> normalize_expr ?guard expr
