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

module LhsMap = struct
  include Map.Make(struct
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

(* [i] is module state used to guarantee newly created identifiers are unique *)
let i = ref (0)

(* Create a new oracle for use with if blocks. *)
let mk_fresh_ib_oracle expr_type =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  let name = HString.concat2 prefix (HString.mk_hstring "_iboracle") in
  let nexpr = A.Ident (Lib.dummy_pos, name) in
  let gids = { (LAN.empty ()) with
    ib_oracles = [name, expr_type]; }
  in nexpr, gids

let mk_fresh_temp_name _ =
  i := !i + 1;
  let prefix = HString.mk_hstring (string_of_int !i) in
  HString.concat2 prefix (HString.mk_hstring "_temp") 

(* Updates a tree (modeling a conditional expression) with a new equation *)
let rec add_eq_to_tree conds rhs node = 
  (* let ppf = Format.std_formatter in *)
  match conds with
    | [] -> node
    | [(b, cond)] -> (
      match node with
        | Leaf (Some _) -> 
          failwith "error-- double assignment in if block 1" 
        | Leaf None -> 
          if b then Node (Leaf (Some rhs), cond, Leaf None)
          else      Node (Leaf None, cond, Leaf (Some rhs))
        | Node (l, c, r) -> 
          if b then Node (Leaf (Some rhs), c, r)
          else      Node (l, c, Leaf (Some rhs))
    )
    | (b, cond)::conds -> (
      match node with
        | Leaf (Some _) -> 
          failwith "error-- double assignment in if block 2" 
        | Leaf None -> 
          if b then Node (add_eq_to_tree conds rhs (Leaf None), cond, Leaf None)
          else      Node (Leaf None, cond, add_eq_to_tree conds rhs (Leaf None))
        | Node (l, c, r) -> 
          if b then Node (add_eq_to_tree conds rhs l, c, r)
          else      Node (l, c, add_eq_to_tree conds rhs r)
    )

(* Converts an if block to a map of trees (create a tree for each equation LHS) *)
let if_block_to_trees ib =
  let rec helper ib trees conds =
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
          helper (A.IfBlock (pos, cond, nis, nis')) trees conds
          | A.IfBlock _ -> 
            helper (A.IfBlock (pos, cond, nis, nis'))
                   (helper ni trees (conds @ [(true, cond)]))
                   conds
          | _ -> failwith "error4"
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
            helper (A.IfBlock (pos, cond, [], nis)) trees conds
          | A.IfBlock _ -> 
            helper (A.IfBlock (pos, cond, [], nis))
                   (helper ni trees (conds @ [(false, cond)]))
                   conds
          | _ -> failwith "error5"
        )
      | A. IfBlock (_, _, [], []) -> trees
      | _ -> failwith "error6"
    in
  helper ib LhsMap.empty []
  
(* Converts a tree of conditions/expressions to an ITE expression. *)
let rec tree_to_ite pos node =
  match node with
    | Leaf Some expr -> expr
    | Leaf None -> A.Ident(pos, HString.mk_hstring "STUB")
    | Node (left, cond, right) -> 
      TernaryOp (pos, Ite, cond, tree_to_ite pos left, tree_to_ite pos right)

(* Returns the type associated with a tree. *)
let rec get_tree_type ctx tree = match tree with
  | Leaf None -> R.ok None
  | Leaf (Some expr) -> 
    A.pp_print_expr Format.std_formatter expr;
    let* ty = (Chk.infer_type_expr ctx expr) in
    R.ok (Some ty)
  | Node (l, _, r) -> (
    match (get_tree_type ctx l) with
      | Ok (None) -> (get_tree_type ctx r)
      | Ok (Some ty) -> R.ok (Some ty)
      | Error (_) -> failwith "error1"
  )

(* Fills empty spots in an ITE with oracles. *)
let rec fill_ite_with_oracles ite ty = 
  match ite with
    | A.TernaryOp (pos, Ite, cond, e1, e2) -> 
      let e1, gids1 = (
      match e1 with
        | TernaryOp _ as top -> fill_ite_with_oracles top ty
        | Ident(_, s) when s = HString.mk_hstring "STUB" -> 
          let (expr, gids) = (mk_fresh_ib_oracle ty) in
          expr, gids
        | _ -> e1, LAN.empty ()
      ) in 
      let e2, gids2 = (
      match e2 with
        | TernaryOp _ as top -> fill_ite_with_oracles top ty
        | Ident(_, s) when s = HString.mk_hstring "STUB" -> 
          let (expr, gids) = (mk_fresh_ib_oracle ty) in
          expr, gids
        | _ -> e2, LAN.empty ()
      ) in
      A.TernaryOp (pos, Ite, cond, e1, e2), LAN.union gids1 gids2
    | _ -> failwith "error2"

(* Removes redundancy from a binary tree. *)
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
  let xs = (List.map (fun (x, _, _) -> x) ls) |> List.flatten in
  let ys = List.map (fun (_, y, _) -> y) ls |> List.flatten in
  let zs = List.map (fun (_, _, z) -> z) ls |> List.flatten in
  xs, ys, zs

let split_and_flatten4 ls =
  let xs = (List.map (fun (x, _, _, _) -> x) ls) |> List.flatten in
  let ys = List.map (fun (_, y, _, _) -> y) ls |> List.flatten in
  let zs = List.map (fun (_, _, z, _) -> z) ls |> List.flatten in
  let ws = List.map (fun (_, _, _, w) -> w) ls |> List.flatten in
  xs, ys, zs, ws

(* Might need to refine ArrayDef *)
(* Takes in an equation LHS and returns 
    * updated LHS with temp variables,
    * equations setting original variable equal to temp variables, and
    * new declarations
   *)
let create_temp_lhs ctx lhs = 
  let rec convert_struct_item = (function
    | A.SingleIdent (p, i) as si -> 
      print_endline("creating temp variable");
      let temp = mk_fresh_temp_name i in
      print_endline (HString.string_of_hstring temp);
      print_endline (HString.string_of_hstring i);
      Ctx.pp_print_tc_context Format.std_formatter ctx;
      
      (* print the context here-- either identifiers aren't equal, or it doesn't
         contain the correct information. *)
      let ty = match Ctx.lookup_ty ctx i with | Some ty -> ty | None -> failwith "error_a" in
      let ctx = Ctx.add_ty ctx temp ty in
      R.ok (
        [A.SingleIdent(p, temp)],
        [A.Body (A.Equation(p, StructDef(p, [si]), Ident(p, temp)))],
        [A.NodeVarDecl(p, (p, temp, ty, ClockTrue))],
        [ctx]
      )
    | TupleStructItem (_, ts) -> 
      let* res = R.seq (List.map convert_struct_item ts) in
      let sis, eqs, decls, ctx = split_and_flatten4 res in
      R.ok (sis, eqs, decls, ctx) 
    | TupleSelection (p, i, _)
    | FieldSelection (p, i, _)
    | ArraySliceStructItem (p, i, _)
    | ArrayDef (p, i, _) as si-> 
      let temp = mk_fresh_temp_name i in
      let ty = match Ctx.lookup_ty ctx i with | Some ty -> ty | None -> failwith "error_b" in
      let ctx = Ctx.add_ty ctx temp ty in
      R.ok (
        [A.SingleIdent(p, temp)],
        [A.Body (A.Equation(p, StructDef(p, [si]), Ident(p, temp)))],
        [A.NodeVarDecl(p, (p, temp, ty, ClockTrue))],
        [ctx]
      )
  ) in
  match lhs with
    | A.StructDef (pos, ss) -> 
      let* res = R.seq (List.map convert_struct_item ss) in
      let sis, eqs, decls, ctx = split_and_flatten4 res in
      R.ok (
        A.StructDef(pos, sis),
        eqs,
        decls,
        ctx
      )



(* Removes multiple assignment from an if block by pulling out equations
   with multiple assignment and using temp variables. *)
(* No gids. Example: 
   if cond
   then 
      y1, y2 = node(expr1);
   else
      y1 = expr2;
      y2 = expr3;
  -->
   t1, t2 = node(expr1);
   if cond
   then 
      y1 = t1;
      y2 = t2;
   else
      y1 = expr2;
      y2 = expr3;

  For each temp variable, add a new declaration.
*)
let rec remove_mult_assign_from_ib ctx ni = 
  match ni with 
    | A.Body (Equation (pos, lhs, expr)) -> 
      let lhs_vars = AH.vars_lhs_of_eqn_with_pos ni in
      if (List.length lhs_vars = 1) 
      then R.ok([], [ni], [], [ctx])
      else (
        let* temp_lhs, split_eqs, new_decls, ctx = create_temp_lhs ctx lhs in
        let ni = A.Body (Equation (pos, temp_lhs, expr)) in
        R.ok ([ni], split_eqs, new_decls, ctx)
      )
    
    | IfBlock (pos, e, l1, l2) -> 
      (* nis is a list of lists, where the first element in each list of lists 
         is pulled out of the if block*)
      let* res1 = R.seq (List.map (remove_mult_assign_from_ib ctx) l1) in
      let nis1, nis2, decls1, ctx1 = split_and_flatten4 res1 in
      let* res2 = R.seq (List.map (remove_mult_assign_from_ib ctx) l2) in
      let nis3, nis4, decls2, ctx2 = split_and_flatten4 res2 in

      (* nis that define the temp variables need to get pulled outside the if block *)
      R.ok (nis1 @ nis3, [A.IfBlock (pos, e, nis2, nis4)], decls1 @ decls2, ctx1 @ ctx2)
    | _ -> failwith "stub"



let extract_equations_from_if ctx ib =
  let* (nis, ibs, new_decls, ctx) = remove_mult_assign_from_ib ctx ib in 
  let ctx = List.fold_left Ctx.union Ctx.empty_tc_context ctx in
  Ctx.pp_print_tc_context Format.std_formatter ctx;
  let ib = List.hd(ibs) in
  let (lhss, trees) = LhsMap.bindings (if_block_to_trees ib) |> List.split in
  let trees = List.map simplify_tree trees in 
  let poss = List.map (fun (A.StructDef (a, _)) -> a) lhss in
  let ites = List.map2 tree_to_ite poss trees in

  (* Convert holes in ITEs to oracles. *)
  let* tys = R.seq (List.map (get_tree_type ctx) trees) in 
  let tys = List.map (fun x -> match x with | Some y -> y | None -> failwith "error3") tys in
  let ites, gids = List.map2 fill_ite_with_oracles ites tys |> List.split in
  let gids = List.fold_left LAN.union (LAN.empty ()) gids in
  (* Combine poss, lhss, and ites into a list of equations *)
  let eqs = (List.map2 (fun (a, b) c -> (A.Body (A.Equation (a, b, c)))) (List.combine poss lhss) ites) in
  R.ok (new_decls, nis @ eqs, [gids])

let desugar_node_item ctx ni = match ni with
  | A.IfBlock _ as ib -> extract_equations_from_if ctx ib
  | _ -> R.ok ([], [ni], [LAN.empty ()])

(* Ugly... *)
let unwrap result = match result with
  | Ok r -> r
  | Error e ->
    let msg = LustreErrors.error_message e in
    Log.log L_debug "(Lustre AST Normalizer Internal Error: %s)" msg;
    assert false

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

let desugar_node_decl ctx decl = match decl with
  | A.NodeDecl (s, ((node_id, b, nps, cctds, ctds, nlds, nis, co) as d)) -> 
    let ctx = get_node_ctx ctx d in
    let* nis = R.seq (List.map (desugar_node_item ctx) nis) in
    let new_decls, nis, gids = split_and_flatten3 nis in
    let gids = List.fold_left LAN.union (LAN.empty ()) gids in
    R.ok (A.NodeDecl (s, (node_id, b, nps, cctds, ctds, new_decls @ nlds, nis, co)), LAN.StringMap.singleton node_id gids) 
  | _ -> R.ok (decl, LAN.StringMap.empty)

(* declaration_list -> gids -> (declaration_list * gids) *)
let desugar_if_blocks ctx normalized_nodes_and_contracts = 
  let* res = R.seq (List.map (desugar_node_decl ctx) normalized_nodes_and_contracts) in
  let decls, gids = List.split res in
  let gids = List.fold_left (LAN.StringMap.union (fun _ b _ -> Some b)) (LAN.StringMap.empty) gids in
  R.ok (decls, gids)

(*
  Also need to update type context with new declaration stuff.  (?) 
  What about contracts? Getting context for contracts?
*)