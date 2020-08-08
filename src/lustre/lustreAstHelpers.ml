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

open Lib

open LustreAst

type iset = LustreAst.SI.t
   
let error_at_position pos msg =
  match Log.get_log_format () with
  | Log.F_pt ->
    Log.log L_error "Parser error at %a: %s" Lib.pp_print_position pos msg
  | Log.F_xml -> Log.parse_log_xml L_error pos msg
  | Log.F_json -> Log.parse_log_json L_error pos msg
  | Log.F_relay -> ()


let warn_at_position pos msg = 
  match Log.get_log_format () with
  | Log.F_pt ->
    Log.log L_warn "Parser warning at %a: %s" Lib.pp_print_position pos msg
  | Log.F_xml -> Log.parse_log_xml L_warn pos msg
  | Log.F_json -> Log.parse_log_json L_warn pos msg
  | Log.F_relay -> ()

                 
(***********)
(* Helpers *)
(***********)

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


let rec has_unguarded_pre ung = function
  | Const _ | Ident _ | ModeRef _ -> false
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | Quantifier (_, _, _, e) -> has_unguarded_pre ung e

  | TupleProject (_, e1, e2) | BinaryOp (_, _, e1, e2) | ArrayConstr (_, e1, e2) 
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
        if Flags.lus_strict () then error_at_position else warn_at_position in

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
    let u2 = has_unguarded_pre false e1 in
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
  | Quantifier (_, _, _, e) ->
    has_pre_or_arrow e

  | TupleProject (_, e1, e2) | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) 
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

  | Arrow (pos, e1, e2) -> Some pos


(** Returns identifiers under a last operator *)
let rec lasts_of_expr acc = function
  | Const _ | Ident _ | ModeRef _ -> acc
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | Quantifier (_, _, _, e) ->
    lasts_of_expr acc e

  | TupleProject (_, e1, e2) | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) 
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

  | TupleProject (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else TupleProject (pos, e1', e2'), acc'

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
        | GroupExpr (pos, g, l) -> GroupExpr (pos, g, l')
        | NArityOp (pos, op, l) -> NArityOp (pos, op, l')
        | Call (pos, n, l) -> Call (pos, n, l')
        | CallParam (pos, n, t, l) -> CallParam (pos, n, t, l')
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
    if try e == e' && List.for_all2 (==) l l'  with _ -> false then ee, acc
    else RestartEvery (pos, n, l', e'), acc

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
    let l1' = List.rev l1 in
    let l2', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc') l2 in
    let l2' = List.rev l2 in
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
            if e == e' then s :: li, acc
            else Index (i, e') :: li, acc
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
      error_at_position pos
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
| ContractCall (_, _, ins, outs) ->
  List.map has_pre_or_arrow ins
  |> some_of_list
  |> unwrap_or (
    fun _ ->
      List.map has_pre_or_arrow outs
      |> some_of_list
  )

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
and vars_of_ty_ids: typed_ident -> iset = fun (_, i, ty) -> SI.singleton i 
and vars_of_clocl_expr: clock_expr -> iset = function
  | ClockTrue -> SI.empty
  | ClockPos i -> SI.singleton i
  | ClockNeg i -> SI.singleton i
  | ClockConstr (i1, i2) -> SI.of_list [i1; i2]


(** Return an ast that adds two expressions*)
let add_exp: Lib.position -> expr -> expr -> expr = fun pos e1 e2 ->
  Lib.todo __LOC__

(** returns an ast which is the absolute difference of two expr ast*)
let abs_diff: Lib.position -> expr -> expr -> expr = fun pos e1 e2 -> Lib.todo __LOC__
