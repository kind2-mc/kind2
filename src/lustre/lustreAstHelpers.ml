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
    | ArraySlice (pos , _ , _) | ArrayIndex (pos , _, _) | ArrayConcat (pos , _ , _)
    | RecordExpr (pos , _ , _) | UnaryOp (pos , _, _) | BinaryOp (pos , _, _ , _)
    | NArityOp (pos , _, _ ) | TernaryOp (pos , _, _ , _ , _) | CompOp (pos , _, _ , _)
    | Quantifier (pos, _, _, _)
    | When (pos , _ , _) | Current (pos , _) | Condact (pos , _ , _ , _ , _, _)
    | Activate (pos , _ , _ , _ , _) | Merge (pos , _ , _ ) | Pre (pos , _)
    | Last (pos , _) | RestartEvery (pos, _, _, _)
    | Fby (pos , _ , _ , _) | Arrow (pos , _ , _) | Call (pos , _ , _ )
    | CallParam (pos , _ , _ , _ )
    -> pos

let rec substitute var t = function
  | Ident (_, i) as e -> if i = var then t else e
  | ModeRef (_, _) as e -> e
  | RecordProject (pos, e, idx) -> RecordProject (pos, substitute var t e, idx)
  | TupleProject (pos, e, idx) -> TupleProject (pos, substitute var t e, idx)
  | Const (_, _) as e -> e
  | UnaryOp (pos, op, e) -> UnaryOp (pos, op, substitute var t e)
  | BinaryOp (pos, op, e1, e2) ->
    BinaryOp (pos, op, substitute var t e1, substitute var t e2)
  | TernaryOp (pos, op, e1, e2, e3) ->
    TernaryOp (pos, op, substitute var t e1, substitute var t e2, substitute var t e3)
  | NArityOp (pos, op, expr_list) ->
    NArityOp (pos, op, List.map (fun e -> substitute var t e) expr_list)
  | ConvOp (pos, op, e) -> ConvOp (pos, op, substitute var t e)
  | CompOp (pos, op, e1, e2) ->
    CompOp (pos, op, substitute var t e1, substitute var t e2)
  | RecordExpr (pos, ident, expr_list) ->
    RecordExpr (pos, ident, List.map (fun (i, e) -> (i, substitute var t e)) expr_list)
  | GroupExpr (pos, kind, expr_list) ->
    GroupExpr (pos, kind, List.map (fun e -> substitute var t e) expr_list)
  | StructUpdate (pos, e1, idx, e2) ->
    StructUpdate (pos, substitute var t e1, idx, substitute var t e2)
  | ArrayConstr (pos, e1, e2) ->
    ArrayConstr (pos, substitute var t e1, substitute var t e2)
  | ArraySlice (pos, e1, (e2, e3)) ->
    ArraySlice (pos, substitute var t e1, (substitute var t e2, substitute var t e3))
  | ArrayIndex (pos, e1, e2) ->
    ArrayIndex (pos, substitute var t e1, substitute var t e2)
  | ArrayConcat (pos, e1, e2) ->
    ArrayConcat (pos, substitute var t e1, substitute var t e2)
  | Quantifier (pos, kind, idents, e) ->
    Quantifier (pos, kind, idents, substitute var t e)
  | When (pos, e, clock) -> When (pos, substitute var t e, clock)
  | Current (pos, e) -> Current (pos, substitute var t e)
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let e1, e2 = substitute var t e1, substitute var t e2 in
    let expr_list1 = List.map (fun e -> substitute var t e) expr_list1 in
    let expr_list2 = List.map (fun e -> substitute var t e) expr_list2 in
    Condact (pos, e1, e2, id, expr_list1, expr_list2)
  | Activate (pos, ident, e1, e2, expr_list) ->
    let e1, e2 = substitute var t e1, substitute var t e2 in
    let expr_list = List.map (fun e -> substitute var t e) expr_list in
    Activate (pos, ident, e1, e2, expr_list)
  | Merge (pos, ident, expr_list) ->
    Merge (pos, ident, List.map (fun (i, e) -> (i, substitute var t e)) expr_list)
  | RestartEvery (pos, ident, expr_list, e) ->
    let expr_list = List.map (fun e -> substitute var t e) expr_list in
    let e = substitute var t e in
    RestartEvery (pos, ident, expr_list, e)
  | Pre (pos, e) -> Pre (pos, substitute var t e)
  | Last (_, _) as e -> e
  | Fby (pos, e1, i, e2) -> Fby (pos, substitute var t e1, i, substitute var t e2)
  | Arrow (pos, e1, e2) -> Arrow (pos, substitute var t e1, substitute var t e2)
  | Call (pos, id, expr_list) ->
    Call (pos, id, List.map (fun e -> substitute var t e) expr_list)
  | CallParam (pos, id, types, expr_list) ->
    CallParam (pos, id, types, List.map (fun e -> substitute var t e) expr_list)

let rec has_unguarded_pre ung = function
  | Const _ | Ident _ | ModeRef _ -> false
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | TupleProject (_, e, _) | Quantifier (_, _, _, e) -> has_unguarded_pre ung e
  | BinaryOp (_, _, e1, e2) | ArrayConstr (_, e1, e2) 
  | CompOp (_, _, e1, e2) | ArrayConcat (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2

  | TernaryOp (_, _, e1, e2, e3)
  | ArraySlice (_, e1, (e2, e3)) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    let u3 = has_unguarded_pre ung e3 in
    u1 || u2 || u3

  | ArrayIndex (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2
 
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
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

  | Fby (_, e1, _, e2) ->
    let u1, u2 = has_unguarded_pre ung e1, has_unguarded_pre ung e2 in
    u1 || u2

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

  | Last _ -> false

  (* TODO: Only report unguarded lasts contained in automaton states
     that are activable at the initial state *)
(*
  | Last (pos, _) as p ->
    if ung then begin
      (* Fail only if in strict mode *)
      let err_or_warn =
        if Flags.lus_strict () then error_at_position else warn_at_position in

      err_or_warn pos
        (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]"
           pp_print_expr p)
    end;
    ung
*)
  | Arrow (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre false e2 in
    u1 || u2

let has_unguarded_pre e =
  let u = has_unguarded_pre true e in
  if u && Flags.lus_strict ()
  then raise Parser_error; u

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
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | TupleProject (_, e, _) | Quantifier (_, _, _, e) ->
    has_pre_or_arrow e

  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) 
  | ArrayConcat (_, e1, e2) | ArrayIndex (_, e1, e2) | ArrayConstr (_, e1, e2)  -> (
    match has_pre_or_arrow e1 with
    | None -> has_pre_or_arrow e2
    | res -> res
  )

  | TernaryOp (_, _, e1, e2, e3) | ArraySlice (_, e1, (e2, e3)) ->
    has_pre_or_arrow e1
    |> unwrap_or (
      fun _ ->
        has_pre_or_arrow e2
        |> unwrap_or (
          fun _ -> has_pre_or_arrow e3
        )
    )
  
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
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

  | Fby (_, e1, _, e2) ->
    has_pre_or_arrow e1
    |> unwrap_or (fun _ -> has_pre_or_arrow e2)

  | Pre (pos, _) | Last (pos, _) -> Some pos

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

let rec replace_lasts allowed prefix acc ee = match ee with
  | Const _ | Ident _ | ModeRef _ ->
    ee, acc
    
  | RecordProject (pos, e, i) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else RecordProject (pos, e', i), acc'
         
  | ConvOp (pos, op, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else ConvOp (pos, op, e'), acc'

  | UnaryOp (pos, op, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else UnaryOp (pos, op, e'), acc'

  | Current (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Current (pos, e'), acc'

  | When (pos, e, c) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else When (pos, e', c), acc'

  | Quantifier (pos, q, vs, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Quantifier (pos, q, vs, e'), acc'

  | TupleProject (pos, e1, i) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    if e1 == e1' then ee, acc
    else TupleProject (pos, e1', i), acc'

  | ArrayConstr (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else ArrayConstr (pos, e1', e2'), acc'

  | BinaryOp (pos, op, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else BinaryOp (pos, op, e1', e2'), acc'

  | CompOp (pos, op, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else CompOp (pos, op, e1', e2'), acc'

  | ArrayConcat (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else ArrayConcat (pos, e1', e2'), acc'

  | TernaryOp (pos, op, e1, e2, e3) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    let e3', acc' = replace_lasts allowed prefix acc' e3 in
    if e1 == e1' && e2 == e2' && e3 == e3' then ee, acc
    else TernaryOp (pos, op, e1', e2', e3'), acc'

  | ArraySlice (pos, e1, (e2, e3)) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    let e3', acc' = replace_lasts allowed prefix acc' e3 in
    if e1 == e1' && e2 == e2' && e3 == e3' then ee, acc
    else ArraySlice (pos, e1', (e2', e3')), acc'

  | ArrayIndex (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else ArrayIndex (pos, e1', e2'), acc'
   
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    if try List.for_all2 (==) l l' with _ -> false then ee, acc
    else (match ee with
        | GroupExpr (pos, g, _) -> GroupExpr (pos, g, l')
        | NArityOp (pos, op, _) -> NArityOp (pos, op, l')
        | Call (pos, n, _) -> Call (pos, n, l')
        | CallParam (pos, n, t, _) -> CallParam (pos, n, t, l')
        | _ -> assert false
      ), acc'

  | Merge (pos, c, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) (c, e) ->
          let e, acc = replace_lasts allowed prefix acc e in
          (c, e) :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    if try List.for_all2 (fun (_, x) (_, x') -> x == x') l l' with _ -> false
    then ee, acc
    else Merge (pos, c, l'), acc'

  | RestartEvery (pos, n, l, e) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    let e', acc' = replace_lasts allowed prefix acc' e in
    if try e == e' && List.for_all2 (==) l l'  with _ -> false then ee, acc'
    else RestartEvery (pos, n, l', e'), acc'

  | Activate (pos, n, e, r, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    let e', acc' = replace_lasts allowed prefix acc' e in
    let r', acc' = replace_lasts allowed prefix acc' r in
    if try e == e' && r == r' &&
           List.for_all2 (==) l l'  with _ -> false then ee, acc
    else Activate (pos, n, e', r', l'), acc'

  | Condact (pos, e, r, n, l1, l2) ->
    let l1', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l1 in
    let l1' = List.rev l1' in
    let l2', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc') l2 in
    let l2' = List.rev l2' in
    let e', acc' = replace_lasts allowed prefix acc' e in
    let r', acc' = replace_lasts allowed prefix acc' r in
    if try e == e' && r == r' &&
           List.for_all2 (==) l1 l1' &&
           List.for_all2 (==) l2 l2'
      with _ -> false then ee, acc
    else Condact (pos, e', r', n, l1', l2'), acc'

  | RecordExpr (pos, n, ie) ->
    let ie', acc' =
      List.fold_left (fun (ie, acc) (i, e) ->
          let e, acc = replace_lasts allowed prefix acc e in
          (i, e) :: ie, acc
        ) ([], acc) ie in
    let ie' = List.rev ie' in
    if try List.for_all2 (fun (_, e) (_, e') -> e == e') ie ie' with _ -> false
    then ee, acc
    else RecordExpr (pos, n, ie'), acc'

  | StructUpdate (pos, e1, li, e2) ->
    let li', acc' =
      List.fold_left (fun (li, acc) -> function
          | Label _ as s -> s :: li, acc
          | Index (i, e) as s ->
            let e', acc' = replace_lasts allowed prefix acc e in
            if e == e' then s :: li, acc'
            else Index (i, e') :: li, acc'
        ) ([], acc) li in
    let li' = List.rev li' in
    let e1', acc' = replace_lasts allowed prefix acc' e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if try e1 == e1' && e2 == e2' &&
           List.for_all2 (fun ei ei' -> match ei, ei' with
               | Label _, Label _ -> true
               | Index (_, e), Index (_, e') -> e == e'
               | _ -> false
             ) li li'
      with _ -> false then ee, acc
    else StructUpdate (pos, e1', li', e2'), acc'
        
  | Fby (pos, e1, i, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else Fby (pos, e1', i, e2'), acc'
    
  | Pre (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc else Pre (pos, e'), acc'
                      
  | Last (pos, i) ->
    if not (List.mem i allowed) then
      fail_at_position pos
        "Only visible variables in the node are allowed under last";
    let acc = SI.add i acc in
    Ident (pos, prefix ^ ".last." ^ i), acc

  | Arrow (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else Arrow (pos, e1', e2'), acc'



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
let node_item_has_pre_or_arrow = function
| Body (Assert (_, e)) -> has_pre_or_arrow e
| Body (Equation (_, lhs, e)) ->
  eq_lhs_has_pre_or_arrow lhs
  |> unwrap_or (fun _ -> has_pre_or_arrow e)
| AnnotMain _ -> None
| AnnotProperty (_, _, e) -> has_pre_or_arrow e
| Body (Automaton _) -> assert false

(** Checks whether a contract node equation has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_node_equation_has_pre_or_arrow = function
| GhostConst decl
| GhostVar decl -> const_decl_has_pre_or_arrow decl
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


(** Checks whether a contract has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_has_pre_or_arrow l =
  List.map contract_node_equation_has_pre_or_arrow l
  |> some_of_list

(** returns all identifiers from the [expr] ast*)
let rec vars: expr -> iset = function
  | Ident (_, i) -> SI.singleton i
  | ModeRef (_, is) -> SI.of_list is
  | RecordProject (_, e, _) -> vars e 
  | TupleProject (_, e, _) -> vars e
  (* Values *)
  | Const _ -> SI.empty
  (* Operators *)
  | UnaryOp (_,_,e) -> vars e
  | BinaryOp (_,_,e1, e2) -> vars e1 |> SI.union (vars e2)
  | TernaryOp (_,_, e1, e2, e3) -> vars e1 |> SI.union (vars e2) |> SI.union (vars e3) 
  | NArityOp (_, _,es) -> SI.flatten (List.map vars es)
  | ConvOp  (_,_,e) -> vars e
  | CompOp (_,_,e1, e2) -> (vars e1) |> SI.union (vars e2)
  (* Structured expressions *)
  | RecordExpr (_, _, flds) -> SI.flatten (List.map vars (snd (List.split flds)))
  | GroupExpr (_, _, es) -> SI.flatten (List.map vars es)
  (* Update of structured expressions *)
   | StructUpdate (_, e1, _, e2) -> SI.union (vars e1) (vars e2)
   | ArrayConstr (_, e1, e2) -> SI.union (vars e1) (vars e2)
   | ArrayIndex (_, e1, e2) -> SI.union (vars e1) (vars e2)
   | ArraySlice (_, e1, (e2, e3)) -> SI.union (vars e3) (SI.union (vars e1) (vars e2))
   | ArrayConcat (_, e1, e2) -> SI.union (vars e1) (vars e2)
  (* Quantified expressions *)
   | Quantifier (_, _, qs, e) -> SI.diff (vars e) (SI.flatten (List.map vars_of_ty_ids qs)) 
  (* Clock operators *)
  | When (_, e, clkE) -> SI.union (vars e) (vars_of_clocl_expr clkE)
  | Current  (_, e) -> vars e
  | Condact (_, e1, e2, i, es1, es2) ->
     SI.add i (SI.flatten (vars e1 :: vars e2:: (List.map vars es1) @ (List.map vars es2)))
  | Activate (_, _, e1, e2, es) -> SI.flatten (vars e1 :: vars e2 :: List.map vars es)
  | Merge (_, _, es) -> List.split es |> snd |> List.map vars |> SI.flatten
  | RestartEvery (_, i, es, e) -> SI.add i (SI.flatten (vars e :: List.map vars es)) 
  (* Temporal operators *)
  | Pre (_, e) -> vars e
  | Last (_, i) -> SI.singleton i
  | Fby (_, e1, _, e2) -> SI.union (vars e1) (vars e2)
  | Arrow (_, e1, e2) ->  SI.union (vars e1) (vars e2)
  (* Node calls *)
  | Call (_, i, es) -> SI.add i (SI.flatten (List.map vars es)) 
  | CallParam (_, i, _, es) -> SI.add i (SI.flatten (List.map vars es))
and vars_of_ty_ids: typed_ident -> iset = fun (_, i, _) -> SI.singleton i 

and vars_of_clocl_expr: clock_expr -> iset = function
  | ClockTrue -> SI.empty
  | ClockPos i -> SI.singleton i
  | ClockNeg i -> SI.singleton i
  | ClockConstr (i1, i2) -> SI.of_list [i1; i2]

let rec vars_of_struct_item: struct_item -> iset = function
  | SingleIdent (_, i) -> SI.singleton i
  | TupleStructItem (_, ts) -> SI.flatten (List.map vars_of_struct_item ts)  
  | TupleSelection (_, i, _)
    | FieldSelection (_, i, _)
    | ArraySliceStructItem (_, i, _)
    | ArrayDef (_, i, _) -> SI.singleton i 

let vars_lhs_of_eqn: node_item -> iset = function
  | Body (Equation (_, StructDef (_, ss), _)) -> SI.flatten (List.map vars_of_struct_item ss)
  | _ -> SI.empty


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
  let c p = Const(p, Num "42") in
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
  | NArityOp (p, op,es) -> NArityOp (p, op, List.map replace_with_constants es) 
  | ConvOp  (p, op, e) -> ConvOp (p, op, replace_with_constants e)
  | CompOp (p, op, e1, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     CompOp (p, op, e1', e2')

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

  | ArrayConcat (p, e1, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     ArrayConcat (p, e1', e2') 

  | ArrayIndex (p, e1, e2) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     ArrayIndex (p, e1', e2') 

  | ArraySlice (p, e1, (e2, e3)) ->
     let e1' = replace_with_constants e1 in
     let e2' = replace_with_constants e2 in
     let e3' = replace_with_constants e3 in
     ArraySlice (p, e1', (e2', e3'))

  (* Quantified expressions *)
  | Quantifier (p, q, qs, e) ->
     Quantifier (p, q, qs, replace_with_constants e)

   (* Clock operators *)
   | When (p, e, c) -> When (p, replace_with_constants e, c) 
   | Current  (p, e) -> Current  (p, replace_with_constants e) 
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
  | Last _ as e -> e
  | Fby (p, e1, i, e2) ->
     Fby (p, replace_with_constants e1, i, replace_with_constants e2)
  | Arrow (p, e1, e2) ->  Arrow (p, replace_with_constants e1, replace_with_constants e2)

  (* Node calls *)
  | Call (p, i, es) -> Call (p, i, List.map replace_with_constants es) 
  | CallParam (p, i, tys, es) -> CallParam (p, i, tys, List.map replace_with_constants es) 

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
  | NArityOp (p, op,es) -> NArityOp (p, op, List.map abstract_pre_subexpressions es) 
  | ConvOp  (p, op, e) -> ConvOp (p, op, abstract_pre_subexpressions e)
  | CompOp (p, op, e1, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     CompOp (p, op, e1', e2')

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

  | ArrayConcat (p, e1, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     ArrayConcat (p, e1', e2') 

  | ArrayIndex (p, e1, e2) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     ArrayIndex (p, e1', e2') 

  | ArraySlice (p, e1, (e2, e3)) ->
     let e1' = abstract_pre_subexpressions e1 in
     let e2' = abstract_pre_subexpressions e2 in
     let e3' = abstract_pre_subexpressions e3 in
     ArraySlice (p, e1', (e2', e3'))

  (* Quantified expressions *)
  | Quantifier (p, q, qs, e) ->
     Quantifier (p, q, qs, abstract_pre_subexpressions e)

   (* Clock operators *)
   | When (p, e, c) -> When (p, abstract_pre_subexpressions e, c) 
   | Current  (p, e) -> Current  (p, abstract_pre_subexpressions e) 
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
  | Last _ as e -> e
  | Fby (p, e1, i, e2) ->
     Fby (p, abstract_pre_subexpressions e1, i, abstract_pre_subexpressions e2)
  | Arrow (p, e1, e2) ->  Arrow (p, abstract_pre_subexpressions e1, abstract_pre_subexpressions e2)

  (* Node calls *)
  | Call (p, i, es) -> Call (p, i, List.map abstract_pre_subexpressions es) 
  | CallParam (p, i, tys, es) -> CallParam (p, i, tys, List.map abstract_pre_subexpressions es) 
                                   


let extract_equation: node_item list -> node_equation list
  = let extract_equation_helper: node_item -> node_equation list
      = function
      | Body n -> [n]
      | _ -> []
    in fun items ->
       List.concat (List.map extract_equation_helper items)
                               
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
     if Stdlib.compare n' n = 0
     then Some (mn, pres @ rest)
     else remove_node_in_declarations n (pres @ [mn]) rest 
  | d :: rest -> remove_node_in_declarations n (pres @ [d]) rest 
  
               
let move_node_to_last: ident -> declaration list -> declaration list = 
  fun n ds ->
  match (remove_node_in_declarations n [] ds) with
  | Some (mn, ds') -> ds' @ [mn]
  | None -> failwith ("Could not find main node " ^ n)


let sort_typed_ident: typed_ident list -> typed_ident list = fun ty_idents ->
  List.sort (fun (_,i1,_) (_,i2,_) -> Stdlib.compare i1 i2) ty_idents
(** Sort identifiers  *)

let sort_idents: ident list -> ident list = fun ids ->
  List.sort (fun i1 i2 -> Stdlib.compare i1 i2) ids
(** sort typed identifiers *)
      
