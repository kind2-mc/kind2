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

module R = Res
module A = LustreAst
module NI = NodeId
module AH = LustreAstHelpers
module GI = GeneratedIdentifiers
module Chk = LustreTypeChecker
module Ctx = TypeCheckerContext


type error_kind = 
  | MisplacedNodeItemError of A.node_item
  | MissingDefinitionInBranchError of HString.t

let error_message error = match error with
  | MisplacedNodeItemError ni -> (match ni with
    | Body (Assert _) -> "Asserts are not allowed inside if blocks."
    | FrameBlock _ -> "Frame blocks are not allowed inside if blocks."
    | AnnotMain _ -> "Main annotations are not allowed inside if blocks."
    | AnnotProperty _ -> "Property annotations are not allowed inside if blocks."
    | WhenBlock _ -> "When blocks are not allowed inside if blocks."
    | IfBlock _ -> "If blocks are not allowed inside when blocks."
    (* Other node items are allowed *)
    | _ -> assert false
  )
  | MissingDefinitionInBranchError id ->
    "Variable '" ^ HString.string_of_hstring id ^ "' must be defined in every branch, including implicit ones."

type error = [
  | `LustreDesugarIfBlocksError of Lib.position * error_kind
]

let ib_oracle_tree = HString.mk_hstring "ib_oracle" 

(** [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref (0)

module LhsMap = struct
  include Map.Make (struct
    (* LHS and its corresponding position on the RHS *)
    type t = (A.eq_lhs * Lib.position)
    let compare lhs1 lhs2 = 
      let (A.StructDef (_, ss1)), _ = lhs1 in
      let (A.StructDef (_, ss2)), _ = lhs2 in
      let vars1 = A.SI.flatten (List.map AH.vars_of_struct_item ss1) in
      let vars2 = A.SI.flatten (List.map AH.vars_of_struct_item ss2) in 
      compare vars1 vars2
  end)
end

type cond_tree =
	| Leaf of A.expr option
	| Node of cond_tree * A.expr * cond_tree

let pos_list_map : (Lib.position * A.eq_lhs) list NI.Hashtbl.t = 
  NI.Hashtbl.create 20

let (let*) = R.(>>=)

let mk_error pos kind = Error (`LustreDesugarIfBlocksError (pos, kind))

let unwrap = function 
| Ok r -> r 
| Error _ -> assert false

(** Checks whether a cond_tree contains any Leaf None (undefined branch). *)
let rec has_leaf_none = function
  | Leaf None -> true
  | Leaf (Some _) -> false
  | Node (l, _, r) -> has_leaf_none l || has_leaf_none r

(** Extracts the variable name and position from an equation LHS. *)
let get_lhs_var lhs = match lhs with
  | A.StructDef (pos, [SingleIdent (_, i)]) -> (i, pos)
  | A.StructDef (pos, [ArrayDef (_, i, _)]) -> (i, pos)
  | _ -> assert false

(** Fresh local variables introduced to capture the discarded results of a call
    statement (e.g. a lemma call like 'double(n-1);', see lustreNameCalls.ml)
    are not required to be defined in every branch. *)
let is_discarded_lhs lhs =
  let (var, _) = get_lhs_var lhs in
  GI.var_is_discarded_output var

(** Create a new oracle for use with if blocks. *)
let mk_fresh_ib_oracle pos expr_type =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring ("_" ^ GI.iboracle)) in
  let nexpr = A.Ident (pos, name) in
  let gids = { (GI.empty ()) with
    ib_oracles = [name, expr_type]; }
  in nexpr, gids

let rec update_if_position_info node_id ni = match ni with
  | A.IfBlock (_, _, nis1, nis2)
  | A.WhenBlock (_, _, nis1, nis2) ->
    List.iter (update_if_position_info node_id) nis1;
    List.iter (update_if_position_info node_id) nis2;
  | Body (Equation (_, lhs, expr)) ->
    (* If there is already a binding, we want to retain the old 'if_info' *)
    let if_info = match NI.Hashtbl.find_opt pos_list_map node_id with
      | Some if_info2 -> (AH.pos_of_expr expr, lhs) :: if_info2
      | None -> [(AH.pos_of_expr expr, lhs)] 
    in
    NI.Hashtbl.add pos_list_map node_id if_info;
  | _ -> ()

(** Updates a tree (modeling an ITE structure) with a new equation. *)
let rec add_eq_to_tree conds rhs node = 
  (* let ppf = Format.std_formatter in *)
  match conds with
    | [] -> node
    | [(b, cond)] -> (
      match node with
        | Leaf (Some _) -> 
          (* shouldn't be possible *)
          assert false 
        | Leaf None -> 
          if b then (Node (Leaf (Some rhs), cond, Leaf None))
          else      (Node (Leaf None, cond, Leaf (Some rhs)))
        | Node (l, c, r) -> 
          if b then (Node (Leaf (Some rhs), c, r))
          else      (Node (l, c, Leaf (Some rhs)))
    )
    | (b, cond)::conds -> (
      match node with
        | Leaf (Some _) -> 
          (* shouldn't be possible *)
          assert false
        | Leaf None -> 
          if b then (Node (add_eq_to_tree conds rhs (Leaf None), cond, Leaf None))
          else (Node (Leaf None, cond, add_eq_to_tree conds rhs (Leaf None)))
        | Node (l, c, r) -> 
          if b then (Node (add_eq_to_tree conds rhs l, c, r))
          else (Node (l, c, add_eq_to_tree conds rhs r))
    )


(* If there are multiple recursive array definitions for the same array that use
   different locals, we need to translate to using only one set of locals for desugaring.
   For example,
   if c
   then 
     array[i] = expr1
   else
     array[j] = expr2
  
    desugars to array[i] = if c then expr1 else expr2. In this function, we update expr2
    to use the local "i" rather than "j".   *)
let update_recursive_array_locals map lhs expr = 
  match lhs with
    | A.StructDef (_, [ArrayDef (_, var1, inds1)]) -> (
      let matching_lhs = LhsMap.bindings map |> List.map fst |> List.map fst
      |> List.find_opt 
        (fun x -> (match x with 
          | A.StructDef (_, [ArrayDef (_, var2, _)]) when var1 = var2 -> true 
          | _ -> false)
        ) in 
      match matching_lhs with
        | Some (A.StructDef (_, [ArrayDef (_, _, inds2)]) as lhs2) -> 
        (* Replace instances with "inds1" with "inds2" *)
        lhs2, AH.replace_idents inds1 inds2 expr
        | _ -> lhs, expr
      ) 
    | _ -> lhs, expr


(** Converts an if block to a map of trees (creates a tree for each equation LHS) *)
let if_block_to_trees ib =
  let rec helper ib trees conds = (
    match ib with 
      | A.IfBlock (pos, cond, ni::nis, nis') -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) -> 
          let lhs, expr = update_recursive_array_locals trees lhs expr in
          (* Update corresponding tree (or add new tree if it doesn't exist) *)
          let trees = LhsMap.update (lhs, AH.pos_of_expr expr) 
            (fun tree -> match tree with
              | Some tree -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr tree)
              | None -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr (Leaf None)))
            trees 
          in
          (helper (A.IfBlock (pos, cond, nis, nis')) trees conds)
          (* A no-op item contributes no equations to any tree. *)
          | A.Auto _ -> (helper (A.IfBlock (pos, cond, nis, nis')) trees conds)
          (* Recurse, keeping track of our location within the if blocks using the
             'conds' list. *)
          | A.IfBlock _ ->
            let* res = (helper ni trees (conds @ [(true, cond)])) in
            (helper (A.IfBlock (pos, cond, nis, nis'))
                   res
                   conds)
          (* Misplaced frame block, annot main, or annot property *)
          | A.Body (Assert (pos, _))
          | A.FrameBlock (pos, _, _, _)
          | A.AnnotProperty (pos, _, _, _)
          | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
          | A.WhenBlock (pos, _, _, _) -> mk_error pos (MisplacedNodeItemError ni)
        )
      | A.IfBlock (pos, cond, [], ni::nis) -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) -> 
            let lhs, expr = update_recursive_array_locals trees lhs expr in
            (* Update corresponding tree (or add new tree if it doesn't exist) *)
            let trees = LhsMap.update (lhs, AH.pos_of_expr expr) 
              (fun tree -> match tree with
                | Some tree -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr tree)
                | None -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr (Leaf None))) 
              trees 
            in
            (helper (A.IfBlock (pos, cond, [], nis)) trees conds)
          (* A no-op item contributes no equations to any tree. *)
          | A.Auto _ -> (helper (A.IfBlock (pos, cond, [], nis)) trees conds)
          (* Recurse, keeping track of our location within the if blocks using the
             'conds' list. *)
          | A.IfBlock _ ->
            let* res = (helper ni trees (conds @ [(false, cond)])) in
            (helper (A.IfBlock (pos, cond, [], nis))
                   res
                   conds)
          (* Misplaced frame block, annot main, or annot property *)
          | A.FrameBlock (pos, _, _, _)
          | A.Body (Assert (pos, _))
          | A.AnnotProperty (pos, _, _, _)
          | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
          | A.WhenBlock (pos, _, _, _) -> mk_error pos (MisplacedNodeItemError ni)
        )
      (* We've processed everything in the if block. *)
      | A. IfBlock (_, _, [], []) -> R.ok (trees)
      (* shouldn't be possible *)
      | _ -> assert false
  ) in
  (helper ib LhsMap.empty [])

(** Converts a when block to a map of trees (like if_block_to_trees but for WhenBlock). *)
let when_block_to_trees wb =
  let rec helper wb trees conds = (
    match wb with
      | A.WhenBlock (pos, cond, ni::nis, nis') -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) ->
          let lhs, expr = update_recursive_array_locals trees lhs expr in
          let trees = LhsMap.update (lhs, AH.pos_of_expr expr)
            (fun tree -> match tree with
              | Some tree -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr tree)
              | None -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr (Leaf None)))
            trees
          in
          (helper (A.WhenBlock (pos, cond, nis, nis')) trees conds)
          (* A no-op item contributes no equations to any tree. *)
          | A.Auto _ -> (helper (A.WhenBlock (pos, cond, nis, nis')) trees conds)
          | A.WhenBlock _ ->
            let* res = (helper ni trees (conds @ [(true, cond)])) in
            (helper (A.WhenBlock (pos, cond, nis, nis'))
                   res
                   conds)
          | A.IfBlock (pos, _, _, _) -> mk_error pos (MisplacedNodeItemError ni)
          | A.Body (Assert (pos, _))
          | A.FrameBlock (pos, _, _, _)
          | A.AnnotProperty (pos, _, _, _)
          | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
        )
      | A.WhenBlock (pos, cond, [], ni::nis) -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) ->
            let lhs, expr = update_recursive_array_locals trees lhs expr in
            let trees = LhsMap.update (lhs, AH.pos_of_expr expr)
              (fun tree -> match tree with
                | Some tree -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr tree)
                | None -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr (Leaf None)))
              trees
            in
            (helper (A.WhenBlock (pos, cond, [], nis)) trees conds)
          (* A no-op item contributes no equations to any tree. *)
          | A.Auto _ -> (helper (A.WhenBlock (pos, cond, [], nis)) trees conds)
          | A.WhenBlock _ ->
            let* res = (helper ni trees (conds @ [(false, cond)])) in
            (helper (A.WhenBlock (pos, cond, [], nis))
                   res
                   conds)
          | A.IfBlock (pos, _, _, _) -> mk_error pos (MisplacedNodeItemError ni)
          | A.FrameBlock (pos, _, _, _)
          | A.Body (Assert (pos, _))
          | A.AnnotProperty (pos, _, _, _)
          | A.AnnotMain (pos, _) -> mk_error pos (MisplacedNodeItemError ni)
        )
      | A.WhenBlock (_, _, [], []) -> R.ok (trees)
      | _ -> assert false
  ) in
  (helper wb LhsMap.empty [])
  
(** Converts a tree of conditions/expressions to an ITE expression. *)
let rec tree_to_ite pos node =
  match node with
    | Leaf Some expr -> expr
    | Leaf None -> A.Ident(pos, ib_oracle_tree)
    | Node (left, cond, right) -> 
      let left = tree_to_ite pos left in
      let right = tree_to_ite pos right in
      let pos = AH.pos_of_expr left in
      TernaryOp (pos, Ite, cond, left, right)

(** Converts a tree of conditions/expressions to a lazy ITE expression. *)
let rec tree_to_lazy_ite pos node =
  match node with
    | Leaf Some expr -> expr
    | Leaf None -> A.Ident(pos, ib_oracle_tree)
    | Node (left, cond, right) ->
      let left = tree_to_lazy_ite pos left in
      let right = tree_to_lazy_ite pos right in
      let pos = AH.pos_of_expr left in
      TernaryOp (pos, LazyIte, cond, left, right)

(** Returns the type associated with a tree. *)
let get_tree_type ctx lhs = 
  match lhs with
    | A.StructDef(_, [SingleIdent(_, i)]) -> (Ctx.lookup_ty ctx i) 
    | A.StructDef(_, [ArrayDef(_, i, _)]) -> (
      match (Ctx.lookup_ty ctx i) with
        (* Assignment in the form of A[i] = f(i), so the RHS type is no
           longer an array *)
        | Some (ArrayType (_, (ty, _))) -> Some ty
        | _ -> None
      )
    (* Other cases not possible *)
    | _ -> assert false

(** Fills empty spots in an ITE with oracles. *)
let rec fill_ite_with_oracles ctx expr ty =
  match expr with
    | A.TernaryOp (pos, Ite, cond, e1, e2) -> 
      let e1, gids1, decls1 = fill_ite_with_oracles ctx e1 ty in
      let e2, gids2, decls2 = fill_ite_with_oracles ctx e2 ty in
      A.TernaryOp (pos, Ite, cond, e1, e2), GI.union gids1 gids2, decls1 @ decls2
    | A.TernaryOp (pos, LazyIte, cond, e1, e2) ->
      let e1, gids1, decls1 = fill_ite_with_oracles ctx e1 ty in
      let e2, gids2, decls2 = fill_ite_with_oracles ctx e2 ty in
      A.TernaryOp (pos, LazyIte, cond, e1, e2), GI.union gids1 gids2, decls1 @ decls2
    | Ident(p, s) when s = ib_oracle_tree -> 
      (* We convert ty to its base type
         because oracles should not fulfill type-related proof obligations *)
      let ty = Chk.expand_type_syn_reftype_history ctx ty |> unwrap in
      let (expr, gids) = (mk_fresh_ib_oracle p ty) in
      (match expr with
        (* Clocks are unsupported, so the clock value is hardcoded to ClockTrue *)
        | A.Ident (_, name) ->  expr, gids, [A.NodeVarDecl(p, (p, name, ty, ClockTrue))]
        | _ -> assert false (* not possible *))
    | _ -> expr, GI.empty (), []

(** Helper function to determine if two trees are equal *)
let rec trees_eq node1 node2 = match node1, node2 with
  | Leaf (Some i), Leaf (Some j) -> (match (AH.syn_expr_equal None i j) with
    | Ok n -> n
    | Error _ -> false
  )
  | Node (l1, _, r1), Node (l2, _, r2) -> 
    trees_eq l1 l2 && trees_eq r1 r2
  | _ -> false

  
(** Removes redundancy from a binary tree. *)
   let rec simplify_tree node = 
    match node with
      | Leaf _ -> node
      | Node (i, str, j) -> 
        let i = simplify_tree i in
        let j = simplify_tree j in
        if trees_eq i j then i else
        Node (i, str, j)


let split_and_flatten3 ls =
  let xs = List.map (fun (x, _, _) -> x) ls |> List.flatten in
  let ys = List.map (fun (_, y, _) -> y) ls |> List.flatten in
  let zs = List.map (fun (_, _, z) -> z) ls |> List.flatten in
  xs, ys, zs


(** Helper function for 'desugar_node_item' that converts IfBlocks to a list
    of ITEs. There are a number of steps in this process.

    Precondition: Multiple assignment has been removed from if blocks.

    Steps:
    1. Converting the if block to a list of trees modeling the ITEs.
    2. Doing any possible simplication on the above trees.
    3. Converting the trees to ITE expressions.
    4. Filling in the ITE expressions with oracles where variables are undefined.
    5. Returning lists of new local declarations, generated equations, and gids
    *)
let extract_equations_from_if node_id ctx ib in_frame_block =
  (* Keep track of where the if block variables are defined so that the position can
     be displayed in post analysis, eg ivcMcs.ml *)
  update_if_position_info node_id ib;
  let* tree_map = if_block_to_trees ib in
  let (lhss_poss, trees) = LhsMap.bindings (tree_map) |> List.split in
  let trees = List.map simplify_tree trees in  
  (* When outside a frame block, every variable defined in any branch must be
     defined in all branches (no Leaf None allowed). *)
  let* () =
    if in_frame_block then R.ok ()
    else
      let lhss = List.map fst lhss_poss in
      R.seq_ (List.map2 (fun lhs tree ->
        if has_leaf_none tree && not (is_discarded_lhs lhs) then
          let (var, pos) = get_lhs_var lhs in
          mk_error pos (MissingDefinitionInBranchError var)
        else R.ok ()
      ) lhss trees)
  in
  let lhs_poss = List.map (fun (A.StructDef (pos, _), _) -> pos) lhss_poss in
  let rhs_poss = List.map snd lhss_poss in
  let lhss = List.map fst lhss_poss in
  let ites = List.map2 tree_to_ite rhs_poss trees in
  let tys = (List.map (get_tree_type ctx) lhss) in 
  let tys = (List.map (fun x -> match x with | Some y -> y | None -> assert false (* not possible *)) 
                       tys) in
  let res = List.map2 (fill_ite_with_oracles ctx) ites tys in
  let ites = List.map (fun (x, _, _) -> x) res in
  let gids = List.map (fun (_, y, _) -> y) res in
  let new_decls = List.map (fun (_, _, z) -> z) res |> List.flatten in

  let gids = List.fold_left GI.union (GI.empty ()) gids in
  (* Combine poss, lhss, and ites into a list of equations *)
  let eqs = (List.map2 (fun (a, b) c -> (A.Body (A.Equation (a, b, c)))) (List.combine lhs_poss lhss) ites) in
  R.ok (new_decls, eqs, [gids])


(* ********************************************************************** *)
(* When-block clocked-call consistency ties                               *)
(* ********************************************************************** *)

(* Returns the defining expression of [id], looking first among the node's
   top-level equations, and then among the generated equations of [gids],
   where [id] may be bound as a component of a pulled-out group equation
   (see lustreRemoveMultAssign.ml). *)
let find_def_of_ident gids nis id =
  let from_items =
    List.find_map (function
      | A.Body (A.Equation (_, A.StructDef (_, [A.SingleIdent (_, x)]), rhs))
        when HString.equal x id -> Some rhs
      | _ -> None
    ) nis
  in
  match from_items with
  | Some _ -> from_items
  | None ->
    List.find_map (fun (_, _, lhs, rhs, _) ->
      match lhs, rhs with
      | A.StructDef (_, [A.SingleIdent (_, x)]), _ when HString.equal x id ->
        Some rhs
      | A.StructDef (_, sis), A.GroupExpr (_, A.ExprList, es)
        when List.length sis = List.length es ->
        List.find_map (fun (si, e) -> match si with
          | A.SingleIdent (_, x) when HString.equal x id -> Some e
          | _ -> None
        ) (List.combine sis es)
      | _ -> None
    ) gids.GI.equations

(* Checks whether [e] denotes the previous value of [x] (i.e. 'last x'),
   possibly through locals such as the ones introduced by
   lustreDesugarLast.ml or lustreRemoveMultAssign.ml. Returns [None] if it
   does not, and [Some init_opt] if it does, where [init_opt] is the
   initialization expression of [x] found along the way, if any. *)
let rec held_expr_init gids nis x depth e =
  match e with
  | A.Pre (_, A.Ident (_, y)) when HString.equal y x -> Some None
  | A.Arrow (_, init, A.Pre (_, A.Ident (_, y))) when HString.equal y x ->
    Some (Some init)
  | A.Ident (_, g) when depth > 0 -> (
    match find_def_of_ident gids nis g with
    | Some rhs -> held_expr_init gids nis x (depth - 1) rhs
    | None -> None)
  | _ -> None

(* Returns the initialization expression of [x] in the frame block equations
   [frame_nes], if any. *)
let frame_init_of frame_nes x =
  List.find_map (function
    | A.Equation (_, A.StructDef (_, [A.SingleIdent (_, y)]), init)
      when HString.equal y x -> Some init
    | _ -> None
  ) frame_nes

let syn_equal e1 e2 =
  match AH.syn_expr_equal None e1 e2 with
  | Ok b -> b
  | Error _ -> false

(* If [e] is (bound to) the output of a node call activated on the when-block
   guard [cond], return the identifier bound to that output: either [e] is an
   identifier defined by a pulled-out clocked call equation, or [e] is a
   direct node call, in which case it is pulled out into a fresh local defined
   by a clocked generated equation (returned in the gids, together with the
   replacement expression for the branch). *)
let call_output_of_expr gids ctx cond ty_opt e =
  match e with
  | A.Ident (_, t) ->
    let is_clocked_output =
      List.exists (fun (_, _, lhs, rhs, src) ->
        match src, lhs, rhs with
        | Some (GI.ClockedOutput g), A.StructDef (_, sis), A.Call (_, _, f, _) ->
          syn_equal g cond &&
          Ctx.node_id_is_node ctx f &&
          List.exists
            (function A.SingleIdent (_, y) -> HString.equal y t | _ -> false)
            sis
        | _ -> false
      ) gids.GI.equations
    in
    if is_clocked_output then Some (t, GI.empty (), None) else None
  | A.Call (pos, _, f, _) when Ctx.node_id_is_node ctx f -> (
    match ty_opt with
    | None -> None
    | Some ty ->
      (* Use the base type so the fresh local does not have to fulfill
         type-related proof obligations while the clock is off. *)
      match Chk.expand_type_syn_reftype_history ctx ty with
      | Error _ -> None
      | Ok ty ->
        i := !i + 1;
        let name =
          HString.mk_hstring (string_of_int !i ^ "_" ^ GI.clocked_call_output)
        in
        let gids = { (GI.empty ()) with
          GI.locals = GI.StringMap.singleton name ty;
          GI.equations =
            [([], [], A.StructDef (pos, [A.SingleIdent (pos, name)]),
              e, Some (GI.ClockedOutput cond))];
        } in
        Some (name, gids, Some (A.Ident (pos, name))))
  | _ -> None

(* For each variable [x] defined by this when-block as
     x = when c then <output of node call> else <last x>
   (or with the else branch omitted inside a frame block, which also holds the
   previous value), generate a boolean local [tie = (x = t)], where [t] is the
   local bound to the output of the activated call, and, when the initial
   value [init] of [x] is available, a boolean local [init_tie = (x = init)].
   The tuple [(tie, init_tie, t, x)] is recorded in the gids. LustreTransSys
   turns each tuple into candidate invariants expressing that, once the clock
   has ticked, the held variable and the (frozen) call output agree, and that,
   before the first tick, the held variable still has its initial value; this
   makes the hold semantics of the activation encoding visible to
   k-induction. *)
let mk_clocked_call_ties ctx gids nis frame_nes in_frame_block lhss_poss trees =
  let mk_bool_local pos suffix eq_expr =
    i := !i + 1;
    let name = HString.mk_hstring (string_of_int !i ^ "_" ^ suffix) in
    let gids = { (GI.empty ()) with
      GI.locals = GI.StringMap.singleton name (A.Bool pos);
      GI.equations =
        [([], [], A.StructDef (pos, [A.SingleIdent (pos, name)]),
          eq_expr, Some GI.Local)];
    } in
    name, gids
  in
  let tied =
    List.map2 (fun (lhs, _) tree ->
      match tree, lhs with
      | Node (Leaf (Some then_e), cond, else_leaf),
        A.StructDef (_, [A.SingleIdent (pos, x)]) ->
        let held = (match else_leaf with
          | Leaf None -> if in_frame_block then Some None else None
          | Leaf (Some e) -> held_expr_init gids nis x 3 e
          | Node _ -> None)
        in (
        match held with
        | None -> tree, None
        | Some init_opt ->
          let init_opt = (match init_opt with
            | Some _ -> init_opt
            | None -> frame_init_of frame_nes x)
          in
          let ty_opt = get_tree_type ctx lhs in
          match call_output_of_expr gids ctx cond ty_opt then_e with
          | Some (t, call_gids, new_then) ->
            let tree = match new_then with
              | Some e -> Node (Leaf (Some e), cond, else_leaf)
              | None -> tree
            in
            let tie, tie_gids =
              mk_bool_local pos GI.clocked_call_tie
                (A.CompOp (pos, A.Eq, A.Ident (pos, x), A.Ident (pos, t)))
            in
            let init_tie, init_gids = (match init_opt with
              | Some init ->
                let init_tie, init_gids =
                  mk_bool_local pos GI.clocked_call_tie
                    (A.CompOp (pos, A.Eq, A.Ident (pos, x), init))
                in
                Some init_tie, init_gids
              | None -> None, GI.empty ())
            in
            tree,
            Some ((tie, init_tie, t, x),
                  GI.union call_gids (GI.union tie_gids init_gids))
          | None -> tree, None)
      | _ -> tree, None
    ) lhss_poss trees
  in
  let trees = List.map fst tied in
  let ties, tie_gids = List.filter_map snd tied |> List.split in
  let tie_gids = List.fold_left GI.union (GI.empty ()) tie_gids in
  let tie_gids =
    { tie_gids with GI.clocked_call_ties = ties @ tie_gids.GI.clocked_call_ties }
  in
  trees, tie_gids

(** Helper function for 'desugar_node_item' that converts WhenBlocks to a list
    of lazy ITEs (if-then-otherwise). Same steps as extract_equations_from_if
    but uses tree_to_lazy_ite to produce LazyIte expressions. *)
let extract_equations_from_when node_id ctx gids nis frame_nes wb in_frame_block =
  update_if_position_info node_id wb;
  let* tree_map = when_block_to_trees wb in
  let (lhss_poss, trees) = LhsMap.bindings (tree_map) |> List.split in
  let trees = List.map simplify_tree trees in
  (* Outside a frame block, every variable defined in any branch must be defined
     in all branches. Inside a frame block, an omitted definition is filled with
     an oracle (later guarded by 'last x', i.e. 'init_x -> pre x'), so undefined
     branches are allowed. *)
  let* () =
    if in_frame_block then R.ok ()
    else
      let lhss = List.map fst lhss_poss in
      R.seq_ (List.map2 (fun lhs tree ->
        if has_leaf_none tree && not (is_discarded_lhs lhs) then
          let (var, pos) = get_lhs_var lhs in
          mk_error pos (MissingDefinitionInBranchError var)
        else R.ok ()
      ) lhss trees)
  in
  let trees, tie_gids =
    mk_clocked_call_ties ctx gids nis frame_nes in_frame_block lhss_poss trees
  in
  let lhs_poss = List.map (fun (A.StructDef (pos, _), _) -> pos) lhss_poss in
  let rhs_poss = List.map snd lhss_poss in
  let lhss = List.map fst lhss_poss in
  let ites = List.map2 tree_to_lazy_ite rhs_poss trees in
  let tys = (List.map (get_tree_type ctx) lhss) in
  let tys = (List.map (fun x -> match x with | Some y -> y | None -> assert false (* not possible *))
                       tys) in
  let res = List.map2 (fill_ite_with_oracles ctx) ites tys in
  let ites = List.map (fun (x, _, _) -> x) res in
  let gids = List.map (fun (_, y, _) -> y) res in
  let new_decls = List.map (fun (_, _, z) -> z) res |> List.flatten in
  let gids = List.fold_left GI.union tie_gids gids in
  let eqs = (List.map2 (fun (a, b) c -> (A.Body (A.Equation (a, b, c)))) (List.combine lhs_poss lhss) ites) in
  R.ok (new_decls, eqs, [gids])


(** Desugar an individual node item. Given a node item, it returns any generated
    local declarations (if we introduce new local variables), the converted
    node_item list in the form of ITEs, and any gids).
*)
let rec desugar_node_item node_id ctx node_gids all_nis frame_nes in_frame_block ni = match ni with
  | A.IfBlock _ as ib -> extract_equations_from_if node_id ctx ib in_frame_block
  | A.WhenBlock _ as wb ->
    extract_equations_from_when node_id ctx node_gids all_nis frame_nes wb in_frame_block
  | A.FrameBlock (pos, vars, nes, nis) ->
    let* res =
      R.seq (List.map (desugar_node_item node_id ctx node_gids all_nis nes true) nis)
    in
    let decls, nis, gids = split_and_flatten3 res in
    R.ok (decls, [A.FrameBlock(pos, vars, nes, nis)], gids)
  (* A no-op item is dropped. *)
  | A.Auto _ -> R.ok ([], [], [GI.empty ()])
  | _ -> R.ok ([], [ni], [GI.empty ()])


(** Desugars an individual node declaration (removing IfBlocks). *)
let desugar_node_decl ctx gids_map decl = match decl with
  | A.FuncDecl (s, (node_id, b, opac, nps, cctds, ctds, nlds, nis, co), is_rec) ->
    let ctx = Chk.add_full_node_ctx ctx node_id nps cctds ctds nlds in
    let node_gids =
      match NI.Map.find_opt node_id gids_map with
      | Some gids -> gids
      | None -> GI.empty ()
    in
    let* nis' = R.seq (List.map (desugar_node_item node_id ctx node_gids nis [] false) nis) in
    let new_decls, nis, gids = split_and_flatten3 nis' in
    let gids = List.fold_left GI.union (GI.empty ()) gids in
    R.ok (A.FuncDecl (s, (node_id, b, opac, nps, cctds, ctds, new_decls @ nlds, nis, co), is_rec),
    NI.Map.singleton node_id gids)
  | A.NodeDecl (s, (node_id, b, opac, nps, cctds, ctds, nlds, nis, co)) ->
    let ctx = Chk.add_full_node_ctx ctx node_id nps cctds ctds nlds in
    let node_gids =
      match NI.Map.find_opt node_id gids_map with
      | Some gids -> gids
      | None -> GI.empty ()
    in
    let* nis' = R.seq (List.map (desugar_node_item node_id ctx node_gids nis [] false) nis) in
    let new_decls, nis, gids = split_and_flatten3 nis' in
    let gids = List.fold_left GI.union (GI.empty ()) gids in
    R.ok (A.NodeDecl (s, (node_id, b, opac, nps, cctds, ctds, new_decls @ nlds, nis, co)), NI.Map.singleton node_id gids)
  | _ -> R.ok (decl, NI.Map.empty)


(** Desugars a declaration list to remove IfBlocks. Converts IfBlocks to
    declarative ITEs, filling in oracles if branches are undefined. *)
let desugar_if_blocks ctx sorted_node_contract_decls gids =
  NI.Hashtbl.clear pos_list_map ;
  let* res = R.seq (List.map (desugar_node_decl ctx gids) sorted_node_contract_decls) in
  let decls, gids2 = List.split res in
  let gids2 = List.fold_left (NI.Map.merge GI.union_keys2) NI.Map.empty gids2 in
  let gids = NI.Map.merge GI.union_keys2 gids gids2 in
  R.ok (decls, gids)
