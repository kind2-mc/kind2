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

 (** 
   Code for desugaring imperative-style if blocks to functional ITEs.

   The code has a few steps.
    1. Remove multiple assignment from if blocks using temp variables.
    2. Parse the if block and create a map of trees, one for each variable
    3. Fill in oracles in the trees for missing equations.
    4. Remove redundancy from the trees.
    5. Convert the trees to ITE expressions. 

   @author Rob Lorch
 *)

module R = Res
module A = LustreAst
module AH = LustreAstHelpers
module LAN = LustreAstNormalizer
module Chk = LustreTypeChecker
module Ctx = TypeCheckerContext


type error_kind = Unknown of string
  | MisplacedNodeItemError of A.node_item

let error_message error = match error with
  | Unknown s -> s
  | MisplacedNodeItemError ni -> "Node item " ^ Lib.string_of_t A.pp_print_node_item ni ^ " is not allowed in if block"

type error = [
  | `LustreDesugarIfBlocksError of Lib.position * error_kind
]

let mk_error pos kind = Error (`LustreDesugarIfBlocksError (pos, kind))

module LhsMap = struct
  include Map.Make (struct
    type t = A.eq_lhs
    let compare lhs1 lhs2 = 
      let (A.StructDef (_, ss1)) = lhs1 in
      let (A.StructDef (_, ss2)) = lhs2 in
      let vars1 = (List.map AH.vars_of_struct_item ss1) in
      let vars2 = (List.map AH.vars_of_struct_item ss2) in 
      compare vars1 vars2
  end)
end

type cond_tree =
	| Leaf of A.expr option
	| Node of cond_tree * A.expr * cond_tree

let (let*) = R.(>>=)


(** [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref (0)


(** Create a new oracle for use with if blocks. *)
let mk_fresh_ib_oracle expr_type =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_iboracle") in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let gids = { (LAN.empty ()) with
    ib_oracles = [name, expr_type]; }
  in nexpr, gids


(** Create a new fresh temporary variable name. *)
let mk_fresh_temp_name _ =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  HString.concat2 prefix (HString.mk_hstring "_temp") 


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
          if b then (Node (l, c, r))
          else (Node (l, c, add_eq_to_tree conds rhs r))
    )


(** Converts an if block to a map of trees (creates a tree for each equation LHS) *)
let if_block_to_trees ib =
  let rec helper ib trees conds = (
    match ib with 
      | A.IfBlock (pos, cond, ni::nis, nis') -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) -> 
          (* Update corresponding tree (or add new tree if it doesn't exist) *)
          let trees = LhsMap.update lhs 
            (fun tree -> match tree with
              | Some tree -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr tree)
              | None -> Some (add_eq_to_tree (conds @ [(true, cond)]) expr (Leaf None)))
            trees 
          in
          (helper (A.IfBlock (pos, cond, nis, nis')) trees conds)
          (* Recurse, keeping track of our location within the if blocks using the 
             'conds' list. *)
          | A.IfBlock _ -> 
            let* res = (helper ni trees (conds @ [(true, cond)])) in
            (helper (A.IfBlock (pos, cond, nis, nis'))
                   res
                   conds)
          (* Misplaced frame block, annot main, or annot property *)
          | A.Body (Assert (pos, _)) 
          | A.AnnotProperty (pos, _, _) -> mk_error pos (MisplacedNodeItemError ni)
          | A.AnnotMain _ -> mk_error Lib.dummy_pos (MisplacedNodeItemError ni)
          | _ -> failwith "stub"
        )
      | A.IfBlock (pos, cond, [], ni::nis) -> (
        match ni with
          | A.Body (Equation (_, lhs, expr)) -> 
            (* Update corresponding tree (or add new tree if it doesn't exist) *)
            let trees = LhsMap.update lhs 
              (fun tree -> match tree with
                | Some tree -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr tree)
                | None -> Some (add_eq_to_tree (conds @ [(false, cond)]) expr (Leaf None))) 
              trees 
            in
            (helper (A.IfBlock (pos, cond, [], nis)) trees conds)
          (* Recurse, keeping track of our location within the if blocks using the 
             'conds' list. *)
          | A.IfBlock _ -> 
            let* res = (helper ni trees (conds @ [(false, cond)])) in
            (helper (A.IfBlock (pos, cond, [], nis))
                   res
                   conds)
          (* Misplaced frame block, annot main, or annot property *)
          | A.Body (Assert (pos, _)) 
          | A.AnnotProperty (pos, _, _) -> mk_error pos (MisplacedNodeItemError ni)
          | A.AnnotMain _ -> mk_error Lib.dummy_pos (MisplacedNodeItemError ni)
          | _ -> failwith "stub"
        )
      (* We've processed everything in the if block. *)
      | A. IfBlock (_, _, [], []) -> R.ok (trees)
      (* shouldn't be possible *)
      | _ -> assert false
  ) in
  (helper ib LhsMap.empty [])
  
(** Converts a tree of conditions/expressions to an ITE expression. *)
let rec tree_to_ite pos node =
  match node with
    | Leaf Some expr -> expr
    | Leaf None -> A.Ident(pos, HString.mk_hstring "ib_oracle")
    | Node (left, cond, right) -> 
      TernaryOp (pos, Ite, cond, tree_to_ite pos left, tree_to_ite pos right)


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
(* add new decls *)
let rec fill_ite_with_oracles ite ty = 
  match ite with
    | A.TernaryOp (pos, Ite, cond, e1, e2) -> 
      let e1, gids1, decls1 = (
      match e1 with
        | TernaryOp _ as top -> fill_ite_with_oracles top ty
        | Ident(p, s) when s = HString.mk_hstring "ib_oracle" -> 
          let (expr, gids) = (mk_fresh_ib_oracle ty) in
          (match expr with
            | A.Ident (_, name) ->  expr, gids, [A.NodeVarDecl(p, (p, name, ty, ClockTrue))]
            | _ -> assert false (* not possible*))
        | _ -> e1, LAN.empty (), []
      ) in 
      let e2, gids2, decls2 = (
      match e2 with
        | TernaryOp _ as top -> fill_ite_with_oracles top ty
        | Ident(p, s) when s = HString.mk_hstring "ib_oracle" -> 
          let (expr, gids) = (mk_fresh_ib_oracle ty) in
          (match expr with
            | A.Ident (_, name) ->  expr, gids, [A.NodeVarDecl(p, (p, name, ty, ClockTrue))]
            | _ -> assert false (* not possible*))
        | _ -> e2, LAN.empty (), []
      ) in
      A.TernaryOp (pos, Ite, cond, e1, e2), LAN.union gids1 gids2, decls1 @ decls2
    (* shouldn't be possible *)
    | _ -> assert false

(** Removes redundancy from a binary tree. 
   Currently, redundancy check doesn't quite work because
   different positions mess with equality of leaves. *)
let rec simplify_tree node = 
  match node with
    | Leaf _ -> node
    | Node (Leaf i, _, Leaf j) -> if i = j then Leaf i else node
    | Node (((Node _) as i), str, Leaf j) -> 
      let i = simplify_tree i in
      if i = (Leaf j) then i else
      Node (i, str, Leaf j)
    |	Node (Leaf i, str, ((Node _) as j)) ->  
      let j = simplify_tree j in
      if (Leaf i) = j then j
    else Node (Leaf i, str, j)
    | Node (((Node _) as i), str, ((Node _) as j)) -> 
      let i = simplify_tree i in
      let j = simplify_tree j in
      if i = j then i else
      Node (i, str, j)


let split_and_flatten3 ls =
  let xs = List.map (fun (x, _, _) -> x) ls |> List.flatten in
  let ys = List.map (fun (_, y, _) -> y) ls |> List.flatten in
  let zs = List.map (fun (_, _, z) -> z) ls |> List.flatten in
  xs, ys, zs

let split_and_flatten4 ls =
  let xs = List.map (fun (x, _, _, _) -> x) ls |> List.flatten in
  let ys = List.map (fun (_, y, _, _) -> y) ls |> List.flatten in
  let zs = List.map (fun (_, _, z, _) -> z) ls |> List.flatten in
  let ws = List.map (fun (_, _, _, w) -> w) ls |> List.flatten in
  xs, ys, zs, ws


(* When pulling out temp variables for recursive array definitions,
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
      let update = List.find_map (fun pair -> match pair with 
        (* What if multiple js in ArrayDef? *)
        | (A.ArrayDef(_, i2, _), A.ArrayDef (_, i3, _)) when i1 = i2 -> 
          (* Some (A.ArrayIndex(pos, A.Ident (pos, i3), A.Ident(pos, j2))) *)
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
      let rec build_array_index js = (match js with
        | [j] -> A.ArrayIndex(p, A.Ident(p, temp), A.Ident(p, j))
        | j :: js -> ArrayIndex(p, build_array_index js, A.Ident(p, j))
        | [] -> assert false
      ) in
      let array_index = build_array_index (List.rev js) in
      (* Type error, shouldn't be possible *)
      let ty = (match Ctx.lookup_ty ctx i with 
        | Some ty -> ty 
        | None -> assert false) in
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
      A.pp_print_node_item Format.std_formatter (A.Body (Equation (pos, A.StructDef(pos, sis), expr))); 
      (
        (* modify expr if we have an ArrayDef in temp_lhs *)
        [A.Body (Equation (pos, A.StructDef(pos, sis), expr))],
        eqs,
        decls,
        ctx
      )
      


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
let rec remove_mult_assign_from_ni ctx ni = 
  match ni with 
    | A.Body (Equation (_, lhs, expr)) -> 
      let lhs_vars = AH.vars_lhs_of_eqn_with_pos ni in
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
      let* res1 = R.seq (List.map (remove_mult_assign_from_ni ctx) l1) in
      let nis1, nis2, decls1, ctx1 = split_and_flatten4 res1 in
      let* res2 = R.seq (List.map (remove_mult_assign_from_ni ctx) l2) in
      let nis3, nis4, decls2, ctx2 = split_and_flatten4 res2 in
      (* nis1 and nis3 are the temp variables need to get pulled outside the if block *)
      R.ok (nis1 @ nis3, [A.IfBlock (pos, e, nis2, nis4)], decls1 @ decls2, ctx1 @ ctx2)

    | FrameBlock (pos, nes, nis) -> 
      let nes = List.map (fun x -> A.Body x) nes in 
      let* res1 = R.seq (List.map (remove_mult_assign_from_ni ctx) nes) in
      let nis1, nis2, decls1, ctx1 = split_and_flatten4 res1 in
      let* res2 = R.seq (List.map (remove_mult_assign_from_ni ctx) nis) in
      let nis3, nis4, decls2, ctx2 = split_and_flatten4 res2 in     
      let nis2 = List.map 
        (fun x -> match x with | A.Body (Equation _ as e) -> e | _ -> assert false) 
        nis2 in
      R.ok (nis1 @ nis3, [A.FrameBlock (pos, nis2, nis4)], decls1 @ decls2, ctx1 @ ctx2)
      
    (* Misplaced assert, annotmain, annotproperty in if block*)
    | A.Body (Assert (pos, _)) 
    | A.AnnotProperty (pos, _, _) -> mk_error pos (MisplacedNodeItemError ni)
    | A.AnnotMain _ -> mk_error Lib.dummy_pos (MisplacedNodeItemError ni)


(** Helper function for 'desugar_node_item' that converts IfBlocks to a list
    of ITEs. There are a number of steps in this process.
    1. Removing multiple assignment in if blocks
    2. Converting the if block to a list of trees modeling the ITEs to generate
    3. Doing any possible simplication on the above trees.
    4. Converting the trees to ITE expressions.
    5. Filling in the ITE expressions with oracles where variables are undefined.
    6. Returning lists of new local declarations, generated equations, and gids
    *)
let extract_equations_from_if ctx ib =
  let* (nis, ibs, new_decls, ctx) = remove_mult_assign_from_ni ctx ib in 
  let ctx = List.fold_left Ctx.union Ctx.empty_tc_context ctx in
  let ib = List.hd(ibs) in
  let* tree_map = if_block_to_trees ib in
  let (lhss, trees) = LhsMap.bindings (tree_map) |> List.split in
  let trees = List.map simplify_tree trees in 
  let poss = List.map (fun (A.StructDef (a, _)) -> a) lhss in
  let ites = List.map2 tree_to_ite poss trees in
  let tys = (List.map (get_tree_type ctx) lhss) in 
  (* Type error, shouldn't be possible *)
  let tys = (List.map (fun x -> match x with | Some y -> y | None -> assert false) 
                       tys) in
  let res = List.map2 fill_ite_with_oracles ites tys |>
                               List.map (fun (a, b, c) -> a, b, c) in
                               (*ites, gids, new_decls2*)
  let ites = List.map (fun (x, _, _) -> x) res in
  let gids = List.map (fun (_, y, _) -> y) res in
  let new_decls2 = List.map (fun (_, _, z) -> z) res |> List.flatten in

  let gids = List.fold_left LAN.union (LAN.empty ()) gids in
  (* Combine poss, lhss, and ites into a list of equations *)
  let eqs = (List.map2 (fun (a, b) c -> (A.Body (A.Equation (a, b, c)))) (List.combine poss lhss) ites) in
  R.ok (new_decls @ new_decls2, nis @ eqs, [gids])


(** Desugar an individual node item. Given a node item, it returns any generated
    local declarations (if we introduce new local variables), the converted
    node_item list in the form of ITEs, and any gids).
*)
let rec desugar_node_item ctx ni = match ni with
  | A.IfBlock _ as ib -> extract_equations_from_if ctx ib
  | A.FrameBlock _ -> 
    let* (nis2, fb, decls1, _) = remove_mult_assign_from_ni ctx ni in 
      let (pos, nes, nis) = (match fb with 
      | [A.FrameBlock (pos, nes, nis)] -> (pos, nes, nis)
      | _ -> assert false
    ) in
    let* res = R.seq (List.map (desugar_node_item ctx) nis) in
    let decls2, nis, gids = split_and_flatten3 res in
    R.ok (decls1 @ decls2, nis2 @ [A.FrameBlock(pos, nes, nis)], gids)
  | _ -> R.ok ([], [ni], [LAN.empty ()])

  
(** Helper function for get_node_ctx. *)
let unwrap result = match result with
  | Ok r -> r
  | Error _ ->
    Log.log L_debug "(Lustre Desugar If Blocks Internal Error)";
    assert false


(** Collects a node's context. *)
let get_node_ctx ctx (_, _, _, inputs, outputs, locals, _, _) =
  let constants_ctx = inputs
    |> List.map Ctx.extract_consts
    |> (List.fold_left Ctx.union ctx)
  in
  let input_ctx = inputs
    |> List.map Ctx.extract_arg_ctx
    |> (List.fold_left Ctx.union ctx)
  in
  let output_ctx = outputs
    |> List.map Ctx.extract_ret_ctx
    |> (List.fold_left Ctx.union ctx)
  in
  let ctx = Ctx.union
    (Ctx.union constants_ctx ctx)
    (Ctx.union input_ctx output_ctx) in
  List.fold_left
    (fun ctx local -> Chk.local_var_binding ctx local |> unwrap)
    ctx
    locals


(** Desugars an individual node declaration (removing IfBlocks). *)
let desugar_node_decl ctx decl = match decl with
  | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) -> 
    let ctx = get_node_ctx ctx d in
    let* nis = R.seq (List.map (desugar_node_item ctx) nis) in
    let new_decls, nis, gids = split_and_flatten3 nis in
    let gids = List.fold_left LAN.union (LAN.empty ()) gids in
    R.ok (A.NodeDecl (s, (node_id, b, nps, cctds, ctds, new_decls @ nlds, nis, co)), LAN.StringMap.singleton node_id gids) 
  | _ -> R.ok (decl, LAN.StringMap.empty)


(** Desugars a declaration list to remove IfBlocks. Converts IfBlocks to
    declarative ITEs, filling in oracles if branches are undefined. *)
let desugar_if_blocks ctx normalized_nodes_and_contracts = 
  let* res = R.seq (List.map (desugar_node_decl ctx) normalized_nodes_and_contracts) in
  let decls, gids = List.split res in
  let gids = List.fold_left (LAN.StringMap.union (fun _ b _ -> Some b)) (LAN.StringMap.empty) gids in
  R.ok (decls, gids)