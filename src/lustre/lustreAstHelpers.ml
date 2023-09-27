(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015  by the Board of Trustees of the University of Iowa

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

open LustreAst
open LustreReporting

type iset = LustreAst.SI.t

let (let*) = Res.(>>=)

(***********)
(* Helpers *)
(***********)

let expr_is_id = function
  | Ident (_, _) -> true
  | _ -> false

let expr_is_const = function
  | Const (_, _) -> true
  | _ -> false

let expr_is_true = function
  | Const (_, True) -> true
  | _ -> false
  
let expr_is_false = function
  | Const (_, False) -> true
  | _ -> false

let pos_of_expr = function
  | Ident (pos , _) | ModeRef (pos , _ ) | RecordProject (pos , _ , _)
  | TupleProject (pos , _ , _) | StructUpdate (pos , _ , _ , _) | Const (pos, _)
  | ConvOp (pos , _, _) | GroupExpr (pos , _, _ ) | ArrayConstr (pos , _ , _ )
  | ArrayIndex (pos , _, _)
  | RecordExpr (pos , _ , _) | UnaryOp (pos , _, _) | BinaryOp (pos , _, _ , _)
  | TernaryOp (pos , _, _ , _ , _) | CompOp (pos , _, _ , _)
  | Quantifier (pos, _, _, _)
  | When (pos , _ , _) | Condact (pos , _ , _ , _ , _, _)
  | Activate (pos , _ , _ , _ , _) | Merge (pos , _ , _ ) | Pre (pos , _)
  | RestartEvery (pos, _, _, _)
  | Arrow (pos , _ , _) | Call (pos , _ , _ )
  | ChooseOp (pos, _, _, _)
  -> pos

let type_arity ty =
  let inner_types = function
    | GroupType (_, es) -> List.length es
    | _ -> 1
  in
  match ty with
  | TArr (_, a, b) -> (inner_types a, inner_types b)
  | _ -> (0, 0)

let rec expr_contains_call = function
  | Ident (_, _) | ModeRef (_, _) | Const (_, _) -> false
  | RecordProject (_, e, _) | TupleProject (_, e, _) | UnaryOp (_, _, e)
  | ConvOp (_, _, e) | Quantifier (_, _, _, e) | When (_, e, _)
  | Pre (_, e) 
    -> expr_contains_call e
  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) | StructUpdate (_, e1, _, e2)
  | ArrayConstr (_, e1, e2) | ArrayIndex (_, e1, e2)
  | Arrow (_, e1, e2)
    -> expr_contains_call e1 || expr_contains_call e2
  | TernaryOp (_, _, e1, e2, e3)
    -> expr_contains_call e1 || expr_contains_call e2 || expr_contains_call e3
  | GroupExpr (_, _, expr_list)
    -> List.fold_left (fun acc x -> acc || expr_contains_call x) false expr_list
  | RecordExpr (_, _, expr_list) | Merge (_, _, expr_list)
    -> List.fold_left (fun acc (_, e) -> acc || expr_contains_call e) false expr_list
  | Activate (_, _, e1, e2, expr_list) -> 
    expr_contains_call e1 || expr_contains_call e2
    || List.fold_left (fun acc x -> acc || expr_contains_call x) false expr_list
  | Call (_, _, _) | Condact (_, _, _, _, _, _) | RestartEvery (_, _, _, _) | ChooseOp (_, _, _, _)
    -> true

let rec type_contains_subrange = function
  | IntRange _ -> true
  | TupleType (_, tys) | GroupType (_, tys) ->
    List.fold_left (fun acc ty -> acc || type_contains_subrange ty) false tys
  | RecordType (_, _, tys) ->
    List.fold_left (fun acc (_, _, ty) -> acc || type_contains_subrange ty)
      false tys
  | ArrayType (_, (ty, _)) -> type_contains_subrange ty
  | _ -> false

(* Substitute t for var. ChooseOp and Quantifier are not supported due to introduction of bound variables. *)
let rec substitute_naive (var:HString.t) t = function
  | Ident (_, i) as e -> if i = var then t else e
  | ModeRef (_, _) as e -> e
  | RecordProject (pos, e, idx) -> RecordProject (pos, substitute_naive var t e, idx)
  | TupleProject (pos, e, idx) -> TupleProject (pos, substitute_naive var t e, idx)
  | Const (_, _) as e -> e
  | UnaryOp (pos, op, e) -> UnaryOp (pos, op, substitute_naive var t e)
  | BinaryOp (pos, op, e1, e2) ->
    BinaryOp (pos, op, substitute_naive var t e1, substitute_naive var t e2)
  | TernaryOp (pos, op, e1, e2, e3) ->
    TernaryOp (pos, op, substitute_naive var t e1, substitute_naive var t e2, substitute_naive var t e3)
  | ConvOp (pos, op, e) -> ConvOp (pos, op, substitute_naive var t e)
  | CompOp (pos, op, e1, e2) ->
    CompOp (pos, op, substitute_naive var t e1, substitute_naive var t e2)
  | ChooseOp _ -> assert false (* Not supported due to introduction of bound variables *)
  | Quantifier _ -> assert false (* Not supported due to introduction of bound variables *)
  | RecordExpr (pos, ident, expr_list) ->
    RecordExpr (pos, ident, List.map (fun (i, e) -> (i, substitute_naive var t e)) expr_list)
  | GroupExpr (pos, kind, expr_list) ->
    GroupExpr (pos, kind, List.map (fun e -> substitute_naive var t e) expr_list)
  | StructUpdate (pos, e1, idx, e2) ->
    StructUpdate (pos, substitute_naive var t e1, idx, substitute_naive var t e2)
  | ArrayConstr (pos, e1, e2) ->
    ArrayConstr (pos, substitute_naive var t e1, substitute_naive var t e2)
  | ArrayIndex (pos, e1, e2) ->
    ArrayIndex (pos, substitute_naive var t e1, substitute_naive var t e2)
  | When (pos, e, clock) -> When (pos, substitute_naive var t e, clock)
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let e1, e2 = substitute_naive var t e1, substitute_naive var t e2 in
    let expr_list1 = List.map (fun e -> substitute_naive var t e) expr_list1 in
    let expr_list2 = List.map (fun e -> substitute_naive var t e) expr_list2 in
    Condact (pos, e1, e2, id, expr_list1, expr_list2)
  | Activate (pos, ident, e1, e2, expr_list) ->
    let e1, e2 = substitute_naive var t e1, substitute_naive var t e2 in
    let expr_list = List.map (fun e -> substitute_naive var t e) expr_list in
    Activate (pos, ident, e1, e2, expr_list)
  | Merge (pos, ident, expr_list) ->
    Merge (pos, ident, List.map (fun (i, e) -> (i, substitute_naive var t e)) expr_list)
  | RestartEvery (pos, ident, expr_list, e) ->
    let expr_list = List.map (fun e -> substitute_naive var t e) expr_list in
    let e = substitute_naive var t e in
    RestartEvery (pos, ident, expr_list, e)
  | Pre (pos, e) -> Pre (pos, substitute_naive var t e)
  | Arrow (pos, e1, e2) -> Arrow (pos, substitute_naive var t e1, substitute_naive var t e2)
  | Call (pos, id, expr_list) ->
    Call (pos, id, List.map (fun e -> substitute_naive var t e) expr_list)

let rec has_unguarded_pre ung = function
  | Const _ | Ident _ | ModeRef _ -> false
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | When (_, e, _)
  | TupleProject (_, e, _) | Quantifier (_, _, _, e) -> has_unguarded_pre ung e
  | ChooseOp (pos, _, _, _) -> fail_at_position pos "Choose operations are not supported in the old front end"
  | BinaryOp (_, _, e1, e2) | ArrayConstr (_, e1, e2) 
  | CompOp (_, _, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2

  | TernaryOp (_, _, e1, e2, e3) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    let u3 = has_unguarded_pre ung e3 in
    u1 || u2 || u3

  | ArrayIndex (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2
 
  | GroupExpr (_, _, l) | Call (_, _, l) ->
    let us = List.map (has_unguarded_pre ung) l in
    List.exists Lib.identity us

  | Merge (_, _, l) ->
    let us = List.map (has_unguarded_pre ung) (List.map snd l) in
    List.exists Lib.identity us

  | RestartEvery (_, _, l, e) ->
    let us = List.map (has_unguarded_pre ung) (e :: l) in
    List.exists Lib.identity us

  | Activate (_, _, e, r, l)  ->
    let us = List.map (has_unguarded_pre ung) (e :: r :: l) in
    List.exists Lib.identity us

  | Condact (_, e, r, _, l1, l2) ->
    let us = List.map (has_unguarded_pre ung) (e :: r :: l1 @ l2) in
    List.exists Lib.identity us

  | RecordExpr (_, _, ie) ->
    let us = List.map (fun (_, e) -> has_unguarded_pre ung e) ie in
    List.exists Lib.identity us

  | StructUpdate (_, e1, li, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let us = List.map (function
        | Label _ -> false
        | Index (_, e) -> has_unguarded_pre ung e
      ) li in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2 || List.exists Lib.identity us

  | Pre (pos, e) as p ->
    if ung then begin
      (* Fail only if in strict mode *)
      let err_or_warn =
        if Flags.lus_strict () then fail_at_position else warn_at_position in

      err_or_warn pos
        (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]"
           pp_print_expr p)
    end;

    let u = has_unguarded_pre true e in
    ung || u

  | Arrow (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre false e2 in
    u1 || u2


let has_unguarded_pre e =
  let u = has_unguarded_pre true e in
  if u && Flags.lus_strict ()
  then raise Parser_error; u

let rec has_unguarded_pre_no_warn ung = function
  | Const _ | Ident _ | ModeRef _ -> false
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | When (_, e, _)
  | TupleProject (_, e, _) | Quantifier (_, _, _, e) -> has_unguarded_pre_no_warn ung e
  | ChooseOp _ -> assert false (* desugared in lustreDesugarChooseOps *)
  | BinaryOp (_, _, e1, e2) | ArrayConstr (_, e1, e2) 
  | CompOp (_, _, e1, e2) ->
    let u1 = has_unguarded_pre_no_warn ung e1 in
    let u2 = has_unguarded_pre_no_warn ung e2 in
    u1 || u2

  | TernaryOp (_, _, e1, e2, e3) ->
    let u1 = has_unguarded_pre_no_warn ung e1 in
    let u2 = has_unguarded_pre_no_warn ung e2 in
    let u3 = has_unguarded_pre_no_warn ung e3 in
    u1 || u2 || u3

  | ArrayIndex (_, e1, e2) ->
    let u1 = has_unguarded_pre_no_warn ung e1 in
    let u2 = has_unguarded_pre_no_warn ung e2 in
    u1 || u2
 
  | GroupExpr (_, _, l) | Call (_, _, l) ->
    let us = List.map (has_unguarded_pre_no_warn ung) l in
    List.exists Lib.identity us

  | Merge (_, _, l) ->
    let us = List.map (has_unguarded_pre_no_warn ung) (List.map snd l) in
    List.exists Lib.identity us

  | RestartEvery (_, _, l, e) ->
    let us = List.map (has_unguarded_pre_no_warn ung) (e :: l) in
    List.exists Lib.identity us

  | Activate (_, _, e, r, l)  ->
    let us = List.map (has_unguarded_pre_no_warn ung) (e :: r :: l) in
    List.exists Lib.identity us

  | Condact (_, e, r, _, l1, l2) ->
    let us = List.map (has_unguarded_pre_no_warn ung) (e :: r :: l1 @ l2) in
    List.exists Lib.identity us

  | RecordExpr (_, _, ie) ->
    let us = List.map (fun (_, e) -> has_unguarded_pre_no_warn ung e) ie in
    List.exists Lib.identity us

  | StructUpdate (_, e1, li, e2) ->
    let u1 = has_unguarded_pre_no_warn ung e1 in
    let us = List.map (function
        | Label _ -> false
        | Index (_, e) -> has_unguarded_pre_no_warn ung e
      ) li in
    let u2 = has_unguarded_pre_no_warn ung e2 in
    u1 || u2 || List.exists Lib.identity us

  | Pre (_, e)->
    let u = has_unguarded_pre_no_warn true e in
    ung || u

  | Arrow (_, e1, e2) ->
    let u1 = has_unguarded_pre_no_warn ung e1 in
    let u2 = has_unguarded_pre_no_warn false e2 in
    u1 || u2

let has_unguarded_pre_no_warn e =
  has_unguarded_pre_no_warn true e 

(** If second argument is `Some _`, returns that. Otherwise runs `f`. *)
let unwrap_or f = function
| None -> f ()
| res -> res

(** If input list contains `Some _`, returns that. Otherwise returns `None`. *)
let some_of_list = List.fold_left (
  function
  | None -> Lib.identity
  | res -> (fun _ -> res)
) None

(** Checks whether an expression has a `pre` or a `->`. *)
let rec has_pre_or_arrow = function
  | Const _ | Ident _ | ModeRef _ -> None
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | When (_, e, _)
  | TupleProject (_, e, _) | Quantifier (_, _, _, e) 
  | ChooseOp (_, _, e, None) -> 
    has_pre_or_arrow e

  | ChooseOp (_, _, e1, Some e2) -> 
    has_pre_or_arrow e1 |> unwrap_or (fun _ -> has_pre_or_arrow e2)

  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) 
  | ArrayIndex (_, e1, e2) | ArrayConstr (_, e1, e2)  -> (
    match has_pre_or_arrow e1 with
    | None -> has_pre_or_arrow e2
    | res -> res
  )

  | TernaryOp (_, _, e1, e2, e3) ->
    has_pre_or_arrow e1
    |> unwrap_or (
      fun _ ->
        has_pre_or_arrow e2
        |> unwrap_or (
          fun _ -> has_pre_or_arrow e3
        )
    )

  
  
  | GroupExpr (_, _, l) | Call (_, _, l) ->
    List.map has_pre_or_arrow l
    |> some_of_list

  | Merge (_, _, l) ->
    List.map has_pre_or_arrow (List.map snd l)
    |> some_of_list

  | RestartEvery (_, _, l, e) ->
    List.map has_pre_or_arrow (e :: l)
    |> some_of_list

  | Activate (_, _, e, r, l) ->
    List.map has_pre_or_arrow (e :: r :: l)
    |> some_of_list

  | Condact (_, e, r, _, l1, l2) ->
    List.map has_pre_or_arrow (e :: r :: l1 @ l2)
    |> some_of_list

  | RecordExpr (_, _, ie) ->
    List.map (fun (_, e) -> has_pre_or_arrow e) ie
    |> some_of_list

  | StructUpdate (_, e1, li, e2) ->
    has_pre_or_arrow e1
    |> unwrap_or (
      fun _ ->
        has_pre_or_arrow e2
        |> unwrap_or (
          fun _ ->
            List.map (function
              | Label _ -> None
              | Index (_, e) -> has_pre_or_arrow e
            ) li
            |> some_of_list
        )
    )

  | Pre (pos, _) -> Some pos

  | Arrow (pos, _, _) -> Some pos

(*
(** Returns identifiers under a last operator *)
let rec lasts_of_expr acc = function
  | Const _ | Ident _ | ModeRef _ -> acc
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | TupleProject (_, e, _) | Quantifier (_, _, _, e) ->
    lasts_of_expr acc e

  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) 
    | ArrayConcat (_, e1, e2) | ArrayIndex (_, e1, e2) | ArrayConstr (_, e1, e2)  ->
     lasts_of_expr (lasts_of_expr acc e1) e2

  | TernaryOp (_, _, e1, e2, e3) | ArraySlice (_, e1, (e2, e3)) ->
    lasts_of_expr (lasts_of_expr (lasts_of_expr acc e1) e2) e3
  
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
    List.fold_left lasts_of_expr acc l

  | Merge (_, _, l) ->
    List.fold_left (fun acc (_, e) -> lasts_of_expr acc e) acc l

  | RestartEvery (_, _, l, e) ->
    List.fold_left lasts_of_expr acc (e :: l)

  | Activate (_, _, e, r, l) ->
    List.fold_left lasts_of_expr acc (e :: r :: l)

  | Condact (_, e, r, _, l1, l2) ->
    List.fold_left lasts_of_expr acc (e :: r :: l1 @ l2)

  | RecordExpr (_, _, ie) ->
    List.fold_left (fun acc (_, e) -> lasts_of_expr acc e) acc ie

  | StructUpdate (_, e1, li, e2) ->
    let acc = lasts_of_expr (lasts_of_expr acc e1) e2 in
    List.fold_left (fun acc -> function
        | Label _ -> acc
        | Index (_, e) -> lasts_of_expr acc e
      ) acc li
    
  | Fby (_, e1, _, e2) ->
    lasts_of_expr (lasts_of_expr acc e1) e2

  | Pre (pos, e) -> lasts_of_expr acc e
                      
  | Last (pos, i) -> SI.add i acc

  | Arrow (pos, e1, e2) ->
    lasts_of_expr (lasts_of_expr acc e1) e2
*)

(** Checks whether a struct item has a `pre` or a `->`. *)
let rec struct_item_has_pre_or_arrow = function
| SingleIdent _ | FieldSelection _ | ArrayDef _ -> None
| TupleStructItem (_, l) ->
  List.map struct_item_has_pre_or_arrow l
  |> some_of_list
| ArraySliceStructItem (_, _, l) ->
  List.map (
    fun (e1, e2) ->
      has_pre_or_arrow e1
      |> unwrap_or (fun _ -> has_pre_or_arrow e2)
  ) l
  |> some_of_list
| TupleSelection (_, _, e) -> has_pre_or_arrow e


(** Checks whether a constant declaration has a `pre` or a `->`. *)
let const_decl_has_pre_or_arrow = function
| FreeConst _ -> None
| UntypedConst (_, _, e) -> has_pre_or_arrow e
| TypedConst (_, _, e, _) -> has_pre_or_arrow e



(** Checks whether a node local declaration has a `pre` or a `->`. *)
let node_local_decl_has_pre_or_arrow = function
| NodeConstDecl (_, decl) -> const_decl_has_pre_or_arrow decl
| NodeVarDecl _ -> None


(** Checks whether an equation lhs has a `pre` or a `->`. *)
let eq_lhs_has_pre_or_arrow = function
| StructDef (_, l) ->
  List.map struct_item_has_pre_or_arrow l
  |> some_of_list


(** Checks whether a node equation has a `pre` or a `->`. *)
let rec node_item_has_pre_or_arrow = function
| Body (Assert (_, e)) -> has_pre_or_arrow e
| Body (Equation (_, lhs, e)) ->
  eq_lhs_has_pre_or_arrow lhs
  |> unwrap_or (fun _ -> has_pre_or_arrow e)
| IfBlock (_, e, l1, l2) -> (match has_pre_or_arrow e with
  | Some pos -> Some pos
  | None -> (match node_item_list_has_pre_or_arrow l1 with 
    | Some pos -> Some pos
    | None -> node_item_list_has_pre_or_arrow l2
    )
  )
| FrameBlock (_, _, nes, nis) -> 
  let nes = List.map (fun x -> Body x) nes in 
  (match node_item_list_has_pre_or_arrow nes with
    | Some pos -> Some pos
    | None ->  node_item_list_has_pre_or_arrow nis)
| AnnotMain _ -> None
| AnnotProperty (_, _, e, _) -> has_pre_or_arrow e
and

node_item_list_has_pre_or_arrow = function 
  | ni :: nis -> (match node_item_has_pre_or_arrow ni with 
    | Some pos -> Some pos 
    | None -> node_item_list_has_pre_or_arrow nis)
  | [] -> None



(** Checks whether a contract node equation has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_node_equation_has_pre_or_arrow = function
| GhostConst decl -> const_decl_has_pre_or_arrow decl
| GhostVars (_, _, e)
| Assume (_, _, _, e)
| Guarantee (_, _, _, e) -> has_pre_or_arrow e
| Mode (_, _, reqs, enss) ->
  List.map (fun (_, _, e) -> has_pre_or_arrow e) reqs
  |> some_of_list
  |> unwrap_or (
    fun _ ->
      List.map (fun (_, _, e) -> has_pre_or_arrow e) enss
      |> some_of_list
  )
| ContractCall (_, _, ins, _) ->
  some_of_list (List.map has_pre_or_arrow ins)
| AssumptionVars _ -> None


(** Checks whether a contract has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_has_pre_or_arrow l =
  List.map contract_node_equation_has_pre_or_arrow l
  |> some_of_list

let vars_of_ty_ids: typed_ident -> iset = fun (_, i, _) -> SI.singleton i 

let vars_of_clock_expr: clock_expr -> iset = function
  | ClockTrue -> SI.empty
  | ClockPos i -> SI.singleton i
  | ClockNeg i -> SI.singleton i
  | ClockConstr (i1, i2) -> SI.of_list [i1; i2]

let mk_mode_ref_id ids =
  Format.asprintf "%a" (Lib.pp_print_list pp_print_ident "::") ids
  |> HString.mk_hstring

let rec vars_of_node_calls_h obs =
  let vars obs = vars_of_node_calls_h obs in
  function
  | Ident (_, i) -> if obs then SI.singleton i else SI.empty
  | ModeRef (_, is) -> if obs then SI.singleton (mk_mode_ref_id is) else SI.empty
  | RecordProject (_, e, _) -> vars obs e 
  | TupleProject (_, e, _) -> vars obs e
  (* Values *)
  | Const _ -> SI.empty
  (* Operators *)
  | UnaryOp (_,_,e) -> vars obs e
  | BinaryOp (_,_,e1, e2) -> vars obs e1 |> SI.union (vars obs e2)
  | TernaryOp (_,_, e1, e2, e3) -> vars obs e1 |> SI.union (vars obs e2) |> SI.union (vars obs e3) 
  | ConvOp  (_,_,e) -> vars obs e
  | CompOp (_,_,e1, e2) -> (vars obs e1) |> SI.union (vars obs e2)
  | ChooseOp (_, (_, i, _), e, None) -> SI.diff (vars true e) (SI.singleton i)
  | ChooseOp (_, (_, i, _), e1, Some e2) -> SI.diff (SI.union (vars true e1) (vars true e2)) (SI.singleton i)
  (* Structured expressions *)
  | RecordExpr (_, _, flds) -> SI.flatten (List.map (vars obs) (snd (List.split flds)))
  | GroupExpr (_, _, es) -> SI.flatten (List.map (vars obs) es)
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) -> SI.union (vars obs e1) (vars obs e2)
  | ArrayConstr (_, e1, e2) -> SI.union (vars obs e1) (vars obs e2)
  | ArrayIndex (_, e1, e2) -> SI.union (vars obs e1) (vars obs e2)
  (* Quantified expressions *)
  | Quantifier (_, _, qs, e) -> SI.diff (vars obs e) (SI.flatten (List.map vars_of_ty_ids qs)) 
  (* Clock operators *)
  | When (_, e, clkE) -> SI.union (vars obs e) (vars_of_clock_expr clkE)
  | Condact (_, e1, e2, _, es1, es2) ->
    SI.flatten (vars obs e1 :: vars obs e2:: (List.map (vars obs) es1) @ (List.map (vars obs) es2))
  | Activate (_, _, e1, e2, es) -> SI.flatten (vars obs e1 :: vars obs e2 :: List.map (vars obs) es)
  | Merge (_, _, es) -> List.split es |> snd |> List.map (vars obs) |> SI.flatten
  | RestartEvery (_, _, es, e) -> SI.flatten (vars obs e :: List.map (vars obs) es)
  (* Temporal operators *)
  | Pre (_, e) -> vars obs e
  | Arrow (_, e1, e2) ->  SI.union (vars obs e1) (vars obs e2)
  (* Node calls *)
  | Call (_, _, es) -> SI.flatten (List.map (vars true) es)

(** returns all identifiers from the [expr] ast that are inside node calls *)
let vars_of_node_calls = vars_of_node_calls_h false

let rec vars_without_node_call_ids: expr -> iset =
  let vars = vars_without_node_call_ids in
  function
  | Ident (_, i) -> SI.singleton i
  | ModeRef (_, is) -> SI.singleton (mk_mode_ref_id is)
  | RecordProject (_, e, _) -> vars e 
  | TupleProject (_, e, _) -> vars e
  (* Values *)
  | Const _ -> SI.empty
  (* Operators *)
  | UnaryOp (_,_,e) -> vars e
  | BinaryOp (_,_,e1, e2) -> vars e1 |> SI.union (vars e2)
  | TernaryOp (_,_, e1, e2, e3) -> vars e1 |> SI.union (vars e2) |> SI.union (vars e3) 
  | ConvOp  (_,_,e) -> vars e
  | CompOp (_,_,e1, e2) -> (vars e1) |> SI.union (vars e2)
  (* Structured expressions *)
  | RecordExpr (_, _, flds) -> SI.flatten (List.map vars (snd (List.split flds)))
  | GroupExpr (_, _, es) -> SI.flatten (List.map vars es)
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) -> SI.union (vars e1) (vars e2)
  | ArrayConstr (_, e1, e2) -> SI.union (vars e1) (vars e2)
  | ArrayIndex (_, e1, e2) -> SI.union (vars e1) (vars e2)
  (* Quantified expressions *)
  | Quantifier (_, _, qs, e) -> SI.diff (vars e) (SI.flatten (List.map vars_of_ty_ids qs)) 
  (* Clock operators *)
  | When (_, e, clkE) -> SI.union (vars e) (vars_of_clock_expr clkE)
  | Condact (_, e1, e2, _, es1, es2) ->
    SI.flatten (vars e1 :: vars e2:: (List.map vars es1) @ (List.map vars es2))
  | Activate (_, _, e1, e2, es) -> SI.flatten (vars e1 :: vars e2 :: List.map vars es)
  | Merge (_, _, es) -> List.split es |> snd |> List.map vars |> SI.flatten
  | RestartEvery (_, _, es, e) -> SI.flatten (vars e :: List.map vars es)
  | ChooseOp (_, (_, i, _), e, None) -> SI.diff (vars e) (SI.singleton i)
  | ChooseOp (_, (_, i, _), e1, Some e2) -> SI.diff (SI.union (vars e1) (vars e2)) (SI.singleton i)
  (* Temporal operators *)
  | Pre (_, e) -> vars e
  | Arrow (_, e1, e2) ->  SI.union (vars e1) (vars e2)
  (* Node calls *)
  | Call (_, _, es) -> SI.flatten (List.map vars es)

let rec vars_of_struct_item_with_pos = function
  | SingleIdent (p, i) -> [(p, i)]
  | TupleStructItem (_, ts) -> List.flatten (List.map vars_of_struct_item_with_pos ts)  
  | TupleSelection (p, i, _)
  | FieldSelection (p, i, _)
  | ArraySliceStructItem (p, i, _)
  | ArrayDef (p, i, _) -> [(p, i)]

let rec vars_of_struct_item = function
  | SingleIdent (_, i) -> SI.singleton i
  | TupleStructItem (_, ts) -> SI.flatten (List.map vars_of_struct_item ts)  
  | TupleSelection (_, i, _)
  | FieldSelection (_, i, _)
  | ArraySliceStructItem (_, i, _)
  | ArrayDef (_, i, _) -> SI.singleton i


let rec defined_vars_with_pos = function
  | Body (Equation (_, StructDef (_, ss), _)) -> List.flatten (List.map vars_of_struct_item_with_pos ss)
  | IfBlock (_, _, l1, l2) -> 
    List.flatten (List.map defined_vars_with_pos l1) @
    List.flatten (List.map defined_vars_with_pos l2)
  | FrameBlock (_, vars, _, _) ->
    vars
  | _ -> [] 


let add_exp: Lib.position -> expr -> expr -> expr = fun pos e1 e2 ->
  BinaryOp (pos, Plus, e1, e2)
(** Return an ast that adds two expressions*)

let abs_diff: Lib.position -> expr -> expr -> expr = fun pos e1 e2 ->
  TernaryOp (pos, Ite,
             CompOp (pos, Gte, e1, e2)
             , BinaryOp (pos, Minus, e1, e2)
             , BinaryOp (pos, Minus, e2, e1))
(** returns an ast which is the absolute difference of two expr ast*)

let extract_ip_ty: const_clocked_typed_decl -> ident * lustre_type
  = fun  (_, i, ty, _, _) -> (i, ty)

let extract_op_ty: clocked_typed_decl -> ident * lustre_type
  = fun (_, i, ty, _) -> (i, ty)

let is_const_arg: const_clocked_typed_decl -> bool
  = fun (_, _, _, _, is_const) -> is_const
                                                                        
let is_type_num: lustre_type -> bool
  = function
  | Int _
    | UInt8 _       
    | UInt16 _   
    | UInt32 _   
    | UInt64 _  
    | Int8 _   
    | Int16 _    
    | Int32 _    
    | Int64 _    
    | IntRange _
    | Real _ -> true
  | _ -> false

let is_type_int: lustre_type -> bool
  = function
  | Int _
  | IntRange _ -> true
  | _ -> false

let is_type_real_or_int: lustre_type -> bool
  = function
  | Real _
  | Int _
  | IntRange _ -> true
  | _ -> false

let is_type_int_or_machine_int: lustre_type -> bool
  = function
  |  Int _
     | UInt8 _       
     | UInt16 _   
     | UInt32 _   
     | UInt64 _  
     | Int8 _   
     | Int16 _    
     | Int32 _    
     | Int64 _    
     | IntRange _ -> true
  | _ -> false

let is_type_unsigned_machine_int: lustre_type -> bool
  = function
  | UInt8 _       
    | UInt16 _   
    | UInt32 _   
    | UInt64 _ -> true    
  | _ -> false  

let is_type_signed_machine_int: lustre_type -> bool
  = function
  | Int8 _       
    | Int16 _   
    | Int32 _   
    | Int64 _ -> true    
  | _ -> false  
       
let is_type_machine_int: lustre_type -> bool = fun ty ->
  is_type_signed_machine_int ty || is_type_unsigned_machine_int ty 

let is_type_array : lustre_type -> bool =
  function
  | ArrayType _ -> true
  | _ -> false

let is_machine_type_of_associated_width: (lustre_type * lustre_type) -> bool
  = function
  | Int8 _, UInt8 _       
    | Int16 _,UInt16 _   
    | Int32 _, UInt32 _   
    | Int64 _, UInt64 _
    | UInt8 _, UInt8 _       
    | UInt16 _,UInt16 _   
    | UInt32 _, UInt32 _   
    | UInt64 _, UInt64 _ -> true
  | _ -> false

let is_type_or_const_decl: declaration -> bool = 
  function
  | TypeDecl _
    | ConstDecl _ -> true
  | _ -> false

let rec flatten_group_type: lustre_type -> lustre_type list = function
  | GroupType (_, tys) -> List.concat (List.map flatten_group_type tys)
  | ty -> [ty] 

let flatten_group_types: lustre_type list -> lustre_type list
  = fun tys -> List.concat (List.map flatten_group_type tys)
       
let split_program: declaration list -> (declaration list * declaration list)
  = List.fold_left
      (fun (ds, ds') d ->
        if is_type_or_const_decl d then (d::ds, ds')
        else (ds, d::ds')) ([], [])  
(** Splits program into type and constant decls and rest of the program *)


let rec replace_with_constants: expr -> expr =
  let c p = Const(p, Num (HString.mk_hstring "42")) in
  function
  | Ident(p, _) -> c p 
    | ModeRef _ as e -> e 
  | RecordProject (p, e, i) -> RecordProject (p, replace_with_constants e, i)  
  | TupleProject (p, e, i) -> TupleProject (p, replace_with_constants e, i)
  (* Values *)
  | Const _ as e -> e

  (* Operators *)
  | UnaryOp (p, op, e) -> UnaryOp (p, op, replace_with_constants e)
  | BinaryOp (p, op,e1, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     BinaryOp (p, op, e1', e2') 
  | TernaryOp (p, op, e1, e2, e3) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     let e3' = replace_with_constants e3 in
     TernaryOp (p, op, e1', e2', e3')
  | ConvOp  (p, op, e) -> ConvOp (p, op, replace_with_constants e)
  | CompOp (p, op, e1, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     CompOp (p, op, e1', e2')
  | ChooseOp _ -> assert false (* desugared in lustreDesugarChooseOps *)

  (* Structured expressions *)
  | RecordExpr (p, i, flds) -> RecordExpr (p, i, (List.map (fun (f, e) -> (f, replace_with_constants e)) flds))
  | GroupExpr (p, g, es) -> GroupExpr (p, g, List.map replace_with_constants es)

  (* Update of structured expressions *)
  | StructUpdate (p, e1, i, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     StructUpdate (p, e1', i, e2') 

  | ArrayConstr (p, e1, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     ArrayConstr (p, e1', e2') 

  | ArrayIndex (p, e1, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     ArrayIndex (p, e1', e2') 

  (* Quantified expressions *)
  | Quantifier (p, q, qs, e) ->
     Quantifier (p, q, qs, replace_with_constants e)

   (* Clock operators *)
   | When (p, e, c) -> When (p, replace_with_constants e, c) 
   | Condact (p, e1, e2, i, es1, es2) ->
      Condact (p, replace_with_constants e1
               , replace_with_constants e2
               , i
               , List.map replace_with_constants es1
               , List.map replace_with_constants es2)
   | Activate (p, i, e1, e2, es) ->
      Activate(p, i
               , replace_with_constants e1
               , replace_with_constants e2
               , List.map replace_with_constants es)
   | Merge (p, i, es) ->
      Merge (p, i, List.map (fun (i, e) -> i, replace_with_constants e) es)
   | RestartEvery (p, i, es, e) ->
      RestartEvery (p, i, List.map replace_with_constants es, replace_with_constants e)

  (* Temporal operators *)
  | Pre (_, e) -> replace_with_constants e
  | Arrow (p, e1, e2) ->  Arrow (p, replace_with_constants e1, replace_with_constants e2)

  (* Node calls *)
  | Call (p, i, es) -> Call (p, i, List.map replace_with_constants es) 

(** replaces all the identifiers with constants. This is structure preserving
and is used inside abstract_pre_subexpressions *)

  
let rec abstract_pre_subexpressions: expr -> expr = function
  | Ident _ 
    | ModeRef _ as e -> e 
  | RecordProject (p, e, i) -> RecordProject (p, abstract_pre_subexpressions e, i)  
  | TupleProject (p, e, i) -> TupleProject (p, abstract_pre_subexpressions e, i)
  (* Values *)
  | Const _ as e -> e

  (* Operators *)
  | UnaryOp (p, op, e) -> UnaryOp (p, op, abstract_pre_subexpressions e)
  | BinaryOp (p, op,e1, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     BinaryOp (p, op, e1', e2') 
  | TernaryOp (p, op, e1, e2, e3) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     let e3' = abstract_pre_subexpressions e3 in
     TernaryOp (p, op, e1', e2', e3')
  | ConvOp  (p, op, e) -> ConvOp (p, op, abstract_pre_subexpressions e)
  | CompOp (p, op, e1, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     CompOp (p, op, e1', e2')
  | ChooseOp _ -> assert false (* desugared in lustreDesugarChooseOps *)

  (* Structured expressions *)
  | RecordExpr (p, i, flds) -> RecordExpr (p, i, (List.map (fun (f, e) -> (f, abstract_pre_subexpressions e)) flds))
  | GroupExpr (p, g, es) -> GroupExpr (p, g, List.map abstract_pre_subexpressions es)

  (* Update of structured expressions *)
  | StructUpdate (p, e1, i, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     StructUpdate (p, e1', i, e2') 

  | ArrayConstr (p, e1, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     ArrayConstr (p, e1', e2') 

  | ArrayIndex (p, e1, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     ArrayIndex (p, e1', e2')

  (* Quantified expressions *)
  | Quantifier (p, q, qs, e) ->
     Quantifier (p, q, qs, abstract_pre_subexpressions e)

   (* Clock operators *)
   | When (p, e, c) -> When (p, abstract_pre_subexpressions e, c) 
   | Condact (p, e1, e2, i, es1, es2) ->
      Condact (p, abstract_pre_subexpressions e1
               , abstract_pre_subexpressions e2
               , i
               , List.map abstract_pre_subexpressions es1
               , List.map abstract_pre_subexpressions es2)
   | Activate (p, i, e1, e2, es) ->
      Activate(p, i
               , abstract_pre_subexpressions e1
               , abstract_pre_subexpressions e2
               , List.map abstract_pre_subexpressions es)
   | Merge (p, i, es) ->
      Merge (p, i, List.map (fun (i, e) -> i, abstract_pre_subexpressions e) es)
   | RestartEvery (p, i, es, e) ->
      RestartEvery (p, i, List.map abstract_pre_subexpressions es, abstract_pre_subexpressions e)

  (* Temporal operators *)
  | Pre (p, e) -> Pre(p, replace_with_constants e)
  | Arrow (p, e1, e2) ->  Arrow (p, abstract_pre_subexpressions e1, abstract_pre_subexpressions e2)

  (* Node calls *)
  | Call (p, i, es) -> Call (p, i, List.map abstract_pre_subexpressions es) 
                 
let rec replace_idents locals1 locals2 expr = 
  match expr with
  | Ident (pos, i) -> (
    match List.assoc_opt i (List.combine locals1 locals2) with
      | Some i2 -> Ident (pos, i2)
      | None -> Ident (pos, i)
  )
  (* Everything else is just recursing to find Idents *)
  | Pre (a, e) -> Pre (a, replace_idents locals1 locals2 e)
  | Arrow (a, e1, e2) -> Arrow (a, replace_idents locals1 locals2 e1, replace_idents locals1 locals2 e2)
  | Const _ as e -> e
  | ModeRef _ as e -> e
    
  | RecordProject (a, e, b) -> RecordProject (a, replace_idents locals1 locals2 e, b)
  | ConvOp (a, b, e) -> ConvOp (a, b, replace_idents locals1 locals2 e)
  | UnaryOp (a, b, e) -> UnaryOp (a, b, replace_idents locals1 locals2 e)
  
  | When (a, e, b) -> When (a, replace_idents locals1 locals2 e, b)
  | TupleProject (a, e, b) -> TupleProject (a, replace_idents locals1 locals2 e, b)
  | BinaryOp (a, b, e1, e2) -> BinaryOp (a, b, replace_idents locals1 locals2 e1, replace_idents locals1 locals2 e2)
  | CompOp (a, b, e1, e2) -> CompOp (a, b, replace_idents locals1 locals2 e1, replace_idents locals1 locals2 e2)
  | ArrayIndex (a, e1, e2) -> ArrayIndex (a, replace_idents locals1 locals2 e1, replace_idents locals1 locals2 e2)
  | ArrayConstr (a, e1, e2)  -> ArrayConstr (a, replace_idents locals1 locals2 e1, replace_idents locals1 locals2 e2)
  | TernaryOp (a, b, e1, e2, e3) -> TernaryOp (a, b, replace_idents locals1 locals2 e1, replace_idents locals1 locals2 e2, replace_idents locals1 locals2 e3)
  
  | GroupExpr (a, b, l) -> GroupExpr (a, b, List.map (replace_idents locals1 locals2) l)
  | Call (a, b, l) -> Call (a, b, List.map (replace_idents locals1 locals2) l)

  | ChooseOp _ -> assert false (* desugared in lustreDesugarChooseOps *)
  | Quantifier (a, b, tis, e) -> 
    (* Remove 'tis' from locals because they're bound in 'e' *)
    let locals = List.combine locals1 locals2 in 
    let is = List.map (fun (_, i, _) -> i) tis in
    let locals1, locals2 = List.filter (fun (i, _) -> not (List.mem i is)) locals |> List.split in
    Quantifier (a, b, tis, replace_idents locals1 locals2 e)

  | Merge (a, b, l) -> Merge (a, b, 
    List.combine
    (List.map fst l)
    (List.map (replace_idents locals1 locals2) (List.map snd l)))
  
  | RecordExpr (a, b, l) -> RecordExpr (a, b,     
    List.combine
    (List.map fst l)
    (List.map (replace_idents locals1 locals2) (List.map snd l)))
  
  | RestartEvery (a, b, l, e) -> 
    RestartEvery (a, b, List.map (replace_idents locals1 locals2) l, replace_idents locals1 locals2 e)
  | Activate (a, b, e, r, l) ->
    Activate (a, b, (replace_idents locals1 locals2) e, (replace_idents locals1 locals2) r, List.map (replace_idents locals1 locals2) l)
  | Condact (a, e, r, b, l1, l2) ->
    Condact (a, (replace_idents locals1 locals2) e, (replace_idents locals1 locals2) r, b, 
             List.map (replace_idents locals1 locals2) l1, List.map (replace_idents locals1 locals2) l2)

  | StructUpdate (a, e1, li, e2) -> 
    StructUpdate (a, replace_idents locals1 locals2 e1, 
    List.map (function
              | Label (a, b) -> Label (a, b)
              | Index (a, e) -> Index (a, replace_idents locals1 locals2 e)
             ) li, 
    replace_idents locals1 locals2 e2)
(** For every identifier, if that identifier is position n in locals1,
   replace it with position n in locals2 *)

let extract_node_equation: node_item -> (eq_lhs * expr) list =
  function
  | Body (Equation (_, lhs, expr)) -> [(lhs, expr)]
  | _ -> []

let get_last_node_name: declaration list -> ident option
  = fun ds -> 
  let rec get_first_node_name: declaration list -> ident option =
    function
    | [] -> None
    | NodeDecl (_, (n, _, _, _, _, _, _, _)) :: _ -> Some n
    | _ :: rest -> get_first_node_name rest
  in get_first_node_name (List.rev ds)   

let rec remove_node_in_declarations:
          ident ->
          declaration list ->
          declaration list ->
          (declaration * declaration list) option =
  fun n pres ->
  function
  | [] -> None
  | (NodeDecl (_, (n', _, _, _, _, _, _, _)) as mn) :: rest ->
     if HString.compare n' n = 0
     then Some (mn, pres @ rest)
     else remove_node_in_declarations n (pres @ [mn]) rest 
  | d :: rest -> remove_node_in_declarations n (pres @ [d]) rest 
  
               
let move_node_to_last: ident -> declaration list -> declaration list = 
  fun n ds ->
  match (remove_node_in_declarations n [] ds) with
  | Some (mn, ds') -> ds' @ [mn]
  | None -> failwith ("Could not find main node " ^ HString.string_of_hstring n)


let sort_typed_ident: typed_ident list -> typed_ident list = fun ty_idents ->
  List.sort (fun (_,i1,_) (_,i2,_) -> HString.compare i1 i2) ty_idents
(** Sort identifiers  *)

let sort_idents: ident list -> ident list = fun ids ->
  List.sort (fun i1 i2 -> HString.compare i1 i2) ids
(** sort typed identifiers *)

let rec syn_expr_equal depth_limit x y : (bool, unit) result =
  let (>>=) = Res.(>>=) in
  let rec r depth x y =
    let rlist xl yl = if List.length xl = List.length yl then
        List.map2 (fun x y -> r (depth + 1) x y) xl yl
      else [Ok (false)]
    in
    let join l = List.fold_left
      (fun a x -> a >>= fun a -> x >>= fun x -> Ok (a && x))
      (Ok (true))
      l
    in
    if Lib.is_some depth_limit && depth > Lib.get depth_limit then Error ()
    else match x, y with
    | Ident (_, x), Ident (_, y) -> Ok (HString.equal x y)
    | ModeRef (_, x), ModeRef (_, y) ->
      let t = if List.length x = List.length y then
          List.fold_left2 (fun a x y -> a && HString.equal x y) false x y
        else false
      in
      Ok t
    | RecordProject (_, xe, xi), RecordProject (_, ye, yi) ->
      r (depth + 1) xe ye >>= fun e -> Ok (e && HString.equal xi yi)
    | TupleProject (_, xe, xi), TupleProject(_, ye, yi) ->
      r (depth + 1) xe ye >>= fun e -> Ok (e && xi = yi)
    | Const (_, True), Const(_, True) -> Ok (true)
    | Const (_, False), Const (_, False) -> Ok (true)
    | Const (_, Num x), Const (_, Num y) -> Ok (HString.equal x y)
    | Const (_, Dec x), Const (_, Dec y) -> Ok (HString.equal x y)
    | UnaryOp (_, xop, xe), UnaryOp (_, yop, ye) ->
      r (depth + 1) xe ye >>= fun e -> Ok (e && xop = yop)
    | BinaryOp (_, xop, xe1, xe2), BinaryOp (_, yop, ye1, ye2) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      Ok (e1 && e2 && xop = yop)
    | TernaryOp (_, xop, xe1, xe2, xe3), TernaryOp (_, yop, ye1, ye2, ye3) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      r (depth + 1) xe3 ye3 >>= fun e3 ->
      Ok (e1 && e2 && e3 && xop = yop)
    | ConvOp (_, xop, x), ConvOp (_, yop, y) ->
      r (depth + 1) x y >>= fun e -> Ok (e && xop = yop)
    | CompOp (_, xop, xe1, xe2), CompOp (_, yop, ye1, ye2) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      Ok (e1 && e2 && xop = yop)
    | RecordExpr (_, xi, x), RecordExpr (_, yi, y) ->
      let (x1, x2), (y1, y2) = List.split x, List.split y in
      rlist x2 y2 |> join >>= fun e ->
      let t = List.length x1 = List.length y1
        && List.fold_left2 (fun a x y -> a && HString.equal x y) true x1 y1
      in
      Ok (e && t && HString.equal xi yi)
    | GroupExpr (_, xop, x), GroupExpr(_, yop, y) ->
      rlist x y |> join >>= fun e -> Ok (e && xop = yop)
    | StructUpdate (_, xe1, xl, xe2), StructUpdate (_, ye1, yl, ye2) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      let l = if List.length xl = List.length yl then
          List.map2 (fun x y -> match x, y with
            | Label (_, xi), Label (_, yi) -> Ok (HString.equal xi yi)
            | Index (_, xe), Index (_, ye) -> r (depth + 1) xe ye
            | _ -> Ok (false))
          xl yl
        else [Ok (false)]
      in
      l |> join >>= fun e3 ->
      Ok (e1 && e2 && e3)
    | ArrayConstr (_, xe1, xe2), ArrayConstr (_, ye1, ye2)
    | ArrayIndex (_, xe1, xe2), ArrayIndex (_, ye1, ye2) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      Ok (e1 && e2)
    | Quantifier (_, xq, xl, xe), Quantifier (_, yq, yl, ye) ->
      r (depth + 1) xe ye >>= fun e ->
      let l = if List.length xl = List.length yl then
          List.map2 (fun (_, xi, xt) (_, yi, yt) ->
            syn_type_equal depth_limit xt yt >>= fun t ->
              Ok (t && HString.equal xi yi))
          xl yl
        else [Ok (false)]
      in
      l |> join >>= fun l ->
      Ok (e && l && xq = yq)
    | When (_, x, ClockTrue), When (_, y, ClockTrue) -> r (depth + 1) x y
    | When (_, x, ClockPos xi), When (_, y, ClockPos yi)
    | When (_, x, ClockNeg xi), When (_, y, ClockNeg yi) ->
      r (depth + 1) x y >>= fun e ->
      Ok (e && HString.equal xi yi)
    | When (_, x, ClockConstr (i1, i2)), When (_, y, ClockConstr (j1, j2)) ->
      r (depth + 1) x y >>= fun e ->
      Ok (e && HString.equal i1 j1 && HString.equal i2 j2)
    | Condact (_, xe1, xe2, xi, xl1, xl2), Condact (_, ye1, ye2, yi, yl1, yl2) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      rlist xl1 yl1 |> join >>= fun l1 ->
      rlist xl2 yl2 |> join >>= fun l2 ->
      Ok (e1 && e2 && l1 && l2 && HString.equal xi yi)
    | Activate (_, xi, xe1, xe2, xl), Activate (_, yi, ye1, ye2, yl) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      rlist xl yl |> join >>= fun l ->
      Ok (e1 && e2 && l && HString.equal xi yi)
    | Merge (_, xi, xl), Merge (_, yi, yl) ->
      let (x1, x2), (y1, y2) = List.split xl, List.split yl in
      rlist x2 y2 |> join >>= fun e ->
      let t = List.length x1 = List.length y1
        && List.fold_left2 (fun a x y -> a && HString.equal x y) true x1 y1
      in
      Ok (e && t && HString.equal xi yi)
    | RestartEvery (_, xi, xl, xe), RestartEvery (_, yi, yl, ye) ->
      r (depth + 1) xe ye >>= fun e ->
      rlist xl yl |> join >>= fun l ->
      Ok (e && l && HString.equal xi yi)
    | Pre (_, x), Pre (_, y) -> r (depth + 1) x y
    | Arrow (_, xe1, xe2), Arrow (_, ye1, ye2) ->
      r (depth + 1) xe1 ye1 >>= fun e1 ->
      r (depth + 1) xe2 ye2 >>= fun e2 ->
      Ok (e1 && e2)
    | Call (_, xi, xl), Call (_, yi, yl) ->
      rlist xl yl |> join >>= fun l -> Ok (l && xi = yi)
    | _ -> Ok (false)
  in
  r 0 x y

and syn_type_equal depth_limit x y : (bool, unit) result =
  let (>>=) = Res.(>>=) in
  let rec r depth x y =
    let rlist xl yl = if List.length xl = List.length yl then
        List.map2 (fun x y -> r (depth + 1) x y) xl yl
      else [Ok (false)]
    in
    let join l = List.fold_left
      (fun a x -> a >>= fun a -> x >>= fun x -> Ok (a && x))
      (Ok (true))
      l
    in
    if Lib.is_some depth_limit && depth > Lib.get depth_limit then Error ()
    else match x, y with
    | TVar (_, x), TVar (_, y) -> Ok (HString.equal x y)
    | Bool _, Bool _
    | Int _, Int _
    | UInt8 _, UInt8 _
    | UInt16 _, UInt16 _
    | UInt32 _, UInt32 _
    | UInt64 _, UInt64 _
    | Int8 _, Int8 _
    | Int16 _, Int16 _
    | Int32 _, Int32 _
    | Int64 _, Int64 _
    | Real _, Real _ ->
      Ok (true)
    | IntRange (_, xe1, xe2), IntRange (_, ye1, ye2) ->
      let* e1 = match xe1, ye1 with
        | None, None -> Ok true
        | Some xe1, Some ye1 -> syn_expr_equal depth_limit xe1 ye1
        | _ -> Ok false
      in
      let* e2 =  match xe2, ye2 with
        | None, None -> Ok true
        | Some xe2, Some ye2 -> syn_expr_equal depth_limit xe2 ye2
        | _ -> Ok false
      in
      Ok (e1 && e2)
    | UserType (_, x), UserType (_, y)
    | AbstractType (_, x), AbstractType (_, y) ->
      Ok (HString.equal x y)
    | TupleType (_, xl), TupleType (_, yl)
    | GroupType (_, xl), GroupType (_, yl) ->
      rlist xl yl |> join
    | RecordType (_, xn, xl), RecordType (_, yn, yl) ->
      let t = if List.length xl = List.length yl then
          List.map2 (fun (_, xi, xt) (_, yi, yt) ->
            let* t = r (depth + 1) xt yt in
            Ok (t && HString.equal xi yi))
          xl yl
        else [Ok (false)]
      in
      join (Ok (xn = yn) :: t)
    | ArrayType (_, (xt, xe)), ArrayType (_, (yt, ye)) ->
      r (depth + 1) xt yt >>= fun t ->
      syn_expr_equal depth_limit xe ye >>= fun e ->
      Ok (t && e)
    | EnumType (_, xi, xl), EnumType (_, yi, yl) ->
      let t = if List.length xl = List.length yl then
          List.map2 HString.equal xl yl
          |> List.fold_left (&&) true
        else false
      in
      Ok (t && HString.equal xi yi)
    | TArr (_, xt1, xt2), TArr (_, yt1, yt2) ->
      r (depth + 1) xt1 yt1 >>= fun t1 ->
      r (depth + 1) xt2 yt2 >>= fun t2 ->
      Ok (t1 && t2)
    | _ -> Ok (false)
  in
  r 0 x y

let hash depth_limit expr =
  let rec r depth expr =
    if Lib.is_some depth_limit && depth > Lib.get depth_limit then 
      Hashtbl.hash (0, Lib.get depth_limit)
    else match expr with
      | Ident (_, x) -> Hashtbl.hash (1, HString.hash x)
      | ModeRef (_, path) ->
        let path_hash = List.map HString.hash path in
        Hashtbl.hash (2, path_hash)
      | RecordProject (_, e, i) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (3, e_hash, HString.hash i)
      | TupleProject (_, e, i) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (4, e_hash, i)
      | Const (_, True) -> Hashtbl.hash (5, 0)
      | Const (_, False) -> Hashtbl.hash (5, 1)
      | Const (_, Num x) -> Hashtbl.hash (5, 2, HString.hash x)
      | Const (_, Dec x) -> Hashtbl.hash (5, 3, HString.hash x)
      | UnaryOp (_, op, e) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (6, op, e_hash)
      | BinaryOp (_, op, e1, e2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        Hashtbl.hash (7, op, e1_hash, e2_hash)
      | TernaryOp (_, op, e1, e2, e3) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        let e3_hash = r (depth + 1) e3 in
        Hashtbl.hash (8, op, e1_hash, e2_hash, e3_hash)
      | ConvOp (_, op, e) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (9, op, e_hash)
      | CompOp (_, op, e1, e2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        Hashtbl.hash (10, op, e1_hash, e2_hash)
      | RecordExpr (_, i, es) ->
        let es_hash = List.map
          (fun (i, e) ->
            let e_hash = r (depth + 1) e in
            (HString.hash i, e_hash))
          es
        in
        Hashtbl.hash (11, HString.hash i, es_hash)
      | GroupExpr (_, op, es) ->
        let es_hash = List.map (r (depth + 1)) es in
        Hashtbl.hash (12, op, es_hash)
      | StructUpdate (_, e1, l, e2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        let l_hash = List.map (function
          | Label (_, i) -> HString.hash i
          | Index (_, e) -> r (depth + 1) e)
          l
        in
        Hashtbl.hash (13, e1_hash, l_hash, e2_hash)
      | ArrayConstr (_, e1, e2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        Hashtbl.hash (14, e1_hash, e2_hash)
      | ArrayIndex (_, e1, e2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        Hashtbl.hash (15, e1_hash, e2_hash)
      | Quantifier (_, e1, l, e2) ->
        let e2_hash = r (depth + 1) e2 in
        let l_hash = List.map (fun (_, i, _) -> HString.hash i) l in
        Hashtbl.hash (16, e1, l_hash, e2_hash)
      | When (_, e, ClockTrue) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (17, e_hash, ClockTrue)
      | When (_, e, ClockPos i) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (17, e_hash, 0, HString.hash i)
      | When (_, e, ClockNeg i) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (17, e_hash, 1, HString.hash i)
      | When (_, e, ClockConstr (i1, i2)) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (17, e_hash, 0, HString.hash i1, HString.hash i2)
      | Condact (_, e1, e2, i, l1, l2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        let l1_hash = List.map (r (depth + 1)) l1 in
        let l2_hash = List.map (r (depth + 1)) l2 in
        Hashtbl.hash (18, e1_hash, e2_hash, HString.hash i, l1_hash, l2_hash)
      | Activate (_, i, e1, e2, l) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        let l_hash = List.map (r (depth + 1)) l in
        Hashtbl.hash (19, HString.hash i, e1_hash, e2_hash, l_hash)
      | Merge (_, i, l) ->
        let l_hash = List.map
          (fun (i, e) -> let e_hash = r (depth + 1) e in
            (HString.hash i, e_hash))
          l
        in
        Hashtbl.hash (20, HString.hash i, l_hash)
      | RestartEvery (_, i, l, e) ->
        let l_hash = List.map (r (depth + 1)) l in
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (21, HString.hash i, l_hash, e_hash)
      | Pre (_, e) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (22, e_hash)
      | Arrow (_, e1, e2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        Hashtbl.hash (23, e1_hash, e2_hash)
      | Call (_, i, l) ->
        let l_hash = List.map (r (depth + 1)) l in
        Hashtbl.hash (24, HString.hash i, l_hash)
      | ChooseOp (_, (_, i, _), e, None) ->
        let e_hash = r (depth + 1) e in
        Hashtbl.hash (25, HString.hash i, e_hash)
      | ChooseOp (_, (_, i, _), e1, Some e2) ->
        let e1_hash = r (depth + 1) e1 in
        let e2_hash = r (depth + 1) e2 in
        Hashtbl.hash (25, HString.hash i, e1_hash, e2_hash)
  in
  r 0 expr

let rec rename_contract_vars = function
  | Ident (p, i) as e ->
    let components = String.split_on_char '_' (HString.string_of_hstring i) in
    (try
      (* Test that this name is an internal name *)
      let _ = int_of_string (List.nth components 0) in
      let _ = String.equal (List.nth components 1) "contract" in
      (* This is a renamed contract variable, with #_contract_name format *)
      let id = components |> List.tl |> List.tl |> String.concat "_" in
      let id = HString.mk_hstring id in
      Ident (p, id)
    with _ -> e)
  | ModeRef (_, _) as e -> e
  | RecordProject (pos, e, idx) -> RecordProject (pos, rename_contract_vars e, idx)
  | TupleProject (pos, e, idx) -> TupleProject (pos, rename_contract_vars e, idx)
  | Const (_, _) as e -> e
  | UnaryOp (pos, op, e) -> UnaryOp (pos, op, rename_contract_vars e)
  | BinaryOp (pos, op, e1, e2) ->
    BinaryOp (pos, op, rename_contract_vars e1, rename_contract_vars e2)
  | TernaryOp (pos, op, e1, e2, e3) ->
    TernaryOp (pos, op, rename_contract_vars e1, rename_contract_vars e2, rename_contract_vars e3)
  | ConvOp (pos, op, e) -> ConvOp (pos, op, rename_contract_vars e)
  | CompOp (pos, op, e1, e2) ->
    CompOp (pos, op, rename_contract_vars e1, rename_contract_vars e2)
  | ChooseOp _ -> assert false (* desugared in lustreDesugarChooseOps *)
  | RecordExpr (pos, ident, expr_list) ->
    RecordExpr (pos, ident, List.map (fun (i, e) -> (i, rename_contract_vars e)) expr_list)
  | GroupExpr (pos, kind, expr_list) ->
    GroupExpr (pos, kind, List.map (fun e -> rename_contract_vars e) expr_list)
  | StructUpdate (pos, e1, idx, e2) ->
    StructUpdate (pos, rename_contract_vars e1, idx, rename_contract_vars e2)
  | ArrayConstr (pos, e1, e2) ->
    ArrayConstr (pos, rename_contract_vars e1, rename_contract_vars e2)
  | ArrayIndex (pos, e1, e2) ->
    ArrayIndex (pos, rename_contract_vars e1, rename_contract_vars e2)
  | Quantifier (pos, kind, idents, e) ->
    Quantifier (pos, kind, idents, rename_contract_vars e)
  | When (pos, e, clock) -> When (pos, rename_contract_vars e, clock)
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let e1, e2 = rename_contract_vars e1, rename_contract_vars e2 in
    let expr_list1 = List.map (fun e -> rename_contract_vars e) expr_list1 in
    let expr_list2 = List.map (fun e -> rename_contract_vars e) expr_list2 in
    Condact (pos, e1, e2, id, expr_list1, expr_list2)
  | Activate (pos, ident, e1, e2, expr_list) ->
    let e1, e2 = rename_contract_vars e1, rename_contract_vars e2 in
    let expr_list = List.map (fun e -> rename_contract_vars e) expr_list in
    Activate (pos, ident, e1, e2, expr_list)
  | Merge (pos, ident, expr_list) ->
    Merge (pos, ident, List.map (fun (i, e) -> (i, rename_contract_vars e)) expr_list)
  | RestartEvery (pos, ident, expr_list, e) ->
    let expr_list = List.map (fun e -> rename_contract_vars e) expr_list in
    let e = rename_contract_vars e in
    RestartEvery (pos, ident, expr_list, e)
  | Pre (pos, e) -> Pre (pos, rename_contract_vars e)
  | Arrow (pos, e1, e2) -> Arrow (pos, rename_contract_vars e1, rename_contract_vars e2)
  | Call (pos, id, expr_list) ->
    Call (pos, id, List.map (fun e -> rename_contract_vars e) expr_list)

let name_of_prop pos name k =
  match name with 
  | Some name -> name
  | None -> 
    let kind_str = match k with
      | Invariant -> "Inv"
      | Reachable _ -> "Reach"
      | Provided _ -> "Prov"
    in
    Format.asprintf "%sProp%a" kind_str Lib.pp_print_line_and_column pos
    |> HString.mk_hstring
