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


(** Type checking the surface syntax of Lustre programs
  
  @author Apoorv Ingle *)

(* TODO: Introduce GroupType which is like tuple type but has flattened cannonical structure*)

module R = Res

module LA = LustreAst
module LH = LustreAstHelpers
module IC = LustreAstInlineConstants
module LSC = LustreSyntaxChecks
open TypeCheckerContext

type tc_type  = LA.lustre_type
(** Type alias for lustre type from LustreAst  *)

let string_of_tc_type: tc_type -> string = fun t -> Lib.string_of_t LA.pp_print_lustre_type t
(** String of the type to display in type errors *)

type error_kind = Unknown of string
  | Impossible of string
  | MergeCaseExtraneous of HString.t * tc_type
  | MergeCaseMissing of HString.t
  | MergeCaseNotUnique of HString.t
  | UnboundIdentifier of HString.t
  | UnboundModeReference of HString.t
  | UnboundNodeName of HString.t
  | NotAFieldOfRecord of HString.t
  | NoValueForRecordField of HString.t
  | IlltypedRecordProjection of tc_type
  | TupleIndexOutOfBounds of int * tc_type
  | IlltypedTupleProjection of tc_type
  | UnequalIteBranchTypes of tc_type * tc_type
  | ExpectedBooleanExpression of tc_type
  | ExpectedIntegerExpression of tc_type
  | Unsupported of string
  | UnequalArrayExpressionType
  | TypeMismatchOfRecordLabel of HString.t * tc_type * tc_type
  | IlltypedRecordUpdate of tc_type
  | ExpectedLabel of LA.expr
  | IlltypedArraySlice of tc_type
  | ExpectedIntegerTypeForSlice
  | IlltypedArrayIndex of tc_type
  | ExpectedIntegerTypeForArrayIndex of tc_type
  | IlltypedArrayConcat of bool * tc_type * tc_type option
  | IlltypedDefaults
  | IlltypedMerge of tc_type
  | IlltypedFby of tc_type * tc_type
  | IlltypedArrow of tc_type * tc_type
  | IlltypedCall of tc_type * tc_type
  | ExpectedFunctionType of tc_type
  | IlltypedIdentifier of HString.t * tc_type * tc_type
  | UnificationFailed of tc_type * tc_type
  | ExpectedType of tc_type * tc_type
  | EmptyArrayExpression
  | ExpectedArrayType of tc_type
  | MismatchedNodeType of HString.t * tc_type * tc_type
  | IlltypedBitNot of tc_type
  | IlltypedUnaryMinus of tc_type
  | ExpectedIntegerTypes of tc_type * tc_type
  | ExpectedNumberTypes of tc_type * tc_type
  | ExpectedMachineIntegerTypes of tc_type * tc_type
  | ExpectedBitShiftConstantOfSameWidth of tc_type
  | ExpectedBitShiftMachineIntegerType of tc_type
  | InvalidConversion of tc_type * tc_type
  | NodeArgumentOnLHS of HString.t
  | NodeInputOutputShareIdentifier of ty_set
  | MismatchOfEquationType of LA.struct_item list option * tc_type
  | DisallowedReassignment of ty_set
  | DisallowedSubrangeInContractReturn of bool * HString.t * tc_type
  | AssumptionMustBeInputOrOutput of HString.t
  | Redeclaration of HString.t
  | ExpectedConstant of string * string
  | UndeclaredType of HString.t
  | EmptySubrange of int * int
  | SubrangeArgumentMustBeConstantInteger of LA.expr
  | IntervalMustHaveBound
  | ExpectedRecordType of tc_type
  | GlobalArrayConstraint of LA.expr

type error = [
  | `LustreTypeCheckerError of Lib.position * error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
]

let error_message kind = match kind with
  | Unknown s -> s
  | Impossible s -> "This should be impossible! " ^ s
  | MergeCaseExtraneous (case, ty) -> "Merge case " ^ HString.string_of_hstring case ^ " does not exist in type " ^ string_of_tc_type ty
  | MergeCaseMissing case -> "Merge case " ^ HString.string_of_hstring case ^ " is missing from merge expression"
  | MergeCaseNotUnique case -> "Merge case " ^ HString.string_of_hstring case ^ " must be unique"
  | UnboundIdentifier id -> "Unbound identifier '" ^ HString.string_of_hstring id ^ "'"
  | UnboundModeReference id -> "Unbound mode reference '" ^ HString.string_of_hstring id ^ "'"
  | UnboundNodeName id -> "Unbound node identifier '" ^ HString.string_of_hstring id ^ "'"
  | NotAFieldOfRecord id -> "No field name '" ^ HString.string_of_hstring id ^ "' in record type"
  | NoValueForRecordField id -> "No value given for field '" ^ HString.string_of_hstring id ^ "'"
  | IlltypedRecordProjection ty -> "Cannot project field out of non record expression type " ^ string_of_tc_type ty
  | TupleIndexOutOfBounds (id, ty) -> "Index " ^ string_of_int id ^ " is out of bounds for tuple type " ^ string_of_tc_type ty
  | IlltypedTupleProjection ty -> "Cannot project field out of non tuple type " ^ string_of_tc_type ty
  | UnequalIteBranchTypes (ty1, ty2) -> "Expected equal types of each if-then-else branch but found: "
    ^ string_of_tc_type ty1 ^ " on the then-branch and " ^ string_of_tc_type ty2 ^ " on the the else-branch"
  | ExpectedBooleanExpression ty -> "Expected a boolean expression but found expression of type " ^ string_of_tc_type ty
  | ExpectedIntegerExpression ty -> "Expected an integer expression but found expression of type "  ^ string_of_tc_type ty
  | Unsupported s -> "Unsupported: " ^ s
  | UnequalArrayExpressionType -> "All expressions must be of the same type in an Array"
  | TypeMismatchOfRecordLabel (label, ty1, ty2) -> "Type mismatch. Type of record label '" ^ (HString.string_of_hstring label)
    ^ "' is of type " ^ string_of_tc_type ty1 ^ " but the type of the expression is " ^ string_of_tc_type ty2
  | IlltypedRecordUpdate ty -> "Cannot do an update on non-record type " ^ string_of_tc_type ty
  | ExpectedLabel e -> "Only labels can be used for record expressions but found " ^ LA.string_of_expr e
  | IlltypedArraySlice ty -> "Slicing can only be done on an array type but found " ^ string_of_tc_type ty
  | ExpectedIntegerTypeForSlice -> "Slicing should have integer types"
  | IlltypedArrayIndex ty -> "Indexing can only be done on an array type but found " ^ string_of_tc_type ty
  | ExpectedIntegerTypeForArrayIndex ty -> "Array index should have an integer type but found " ^ string_of_tc_type ty
  | IlltypedArrayConcat (both_array_types, ty1, ty2) -> "Cannot concat "
    ^ (match both_array_types with
      | true -> "array of two different types" ^ string_of_tc_type ty1
        ^ (match ty2 with | Some ty2 -> " and " ^ string_of_tc_type ty2 | None -> "")
      | false -> "non-array type " ^ string_of_tc_type ty1)
  | IlltypedDefaults -> "Defaults do not have the same type as node call"
  | IlltypedMerge ty -> "All expressions in merge expected to be the same type " ^ string_of_tc_type ty
  | IlltypedFby (ty1, ty2) -> "Both the expressions in Fby should be of the same type."
    ^ "Found types " ^ string_of_tc_type ty1 ^ " and " ^ string_of_tc_type ty2
  | IlltypedArrow (ty1, ty2) -> "Arrow types do not match " ^ string_of_tc_type ty1 ^ " and " ^ string_of_tc_type ty2
  | IlltypedCall (ty1, ty2) -> "Node arguments at call expect to have type "
    ^ string_of_tc_type ty1 ^ " but found type " ^ string_of_tc_type ty2
  | ExpectedFunctionType ty -> "Expected node type to be a function type, but found type " ^ string_of_tc_type ty
  | IlltypedIdentifier (id, ty1, ty2) -> "Identifier '" ^ HString.string_of_hstring id
    ^ "' does not match expected type " ^ string_of_tc_type ty1 ^ " with inferred type " ^ string_of_tc_type ty2
  | UnificationFailed (ty1, ty2) -> "Cannot unify type " ^ string_of_tc_type ty1
    ^ " with inferred type " ^ string_of_tc_type ty2
  | ExpectedType (ty1, ty2) -> "Expected type " ^ string_of_tc_type ty1 ^ " but found type " ^ string_of_tc_type ty2
  | EmptyArrayExpression -> "Array expression cannot be empty"
  | ExpectedArrayType ty -> "Expected an array type but found type " ^ string_of_tc_type ty
  | MismatchedNodeType (id, ty1, ty2) -> "Node '" ^ HString.string_of_hstring id ^ "' of type " ^ string_of_tc_type ty1
    ^ " does not match expected type " ^ string_of_tc_type ty2
  | IlltypedBitNot ty -> "Cannot apply the bit-value not operator to a non machine integer value of type "
    ^ string_of_tc_type ty
  | IlltypedUnaryMinus ty -> "Unary minus cannot be applied to non number expression of type " ^ string_of_tc_type ty
  | ExpectedIntegerTypes (ty1, ty2) -> "Expected both arguments of operator to be of same integer type but found "
    ^ string_of_tc_type ty1 ^ " and " ^ string_of_tc_type ty2
  | ExpectedNumberTypes (ty1, ty2) -> "Expected both arguments of operator to be of same integer type (or type real) but found "
    ^ string_of_tc_type ty1 ^ " and " ^ string_of_tc_type ty2
  | ExpectedMachineIntegerTypes (ty1, ty2) -> "Expected both arguments of operator to be of machine integer type but found "
    ^ string_of_tc_type ty1 ^ " and " ^ string_of_tc_type ty2
  | ExpectedBitShiftConstantOfSameWidth ty -> "Expected second argument of shit opperator to be a constant of type "
    ^ "unsigned machine integer of the same width as first argument but found type " ^ string_of_tc_type ty
  | ExpectedBitShiftMachineIntegerType ty -> "Expected first argument of shit operator to be of type signed "
    ^ "or unsigned machine integer but found type " ^ string_of_tc_type ty
  | InvalidConversion (ty1, ty2) -> "Cannot convert type " ^ string_of_tc_type ty1 ^ " to type " ^ string_of_tc_type ty2
  | NodeArgumentOnLHS v -> "Input '" ^ HString.string_of_hstring v ^ "' can not be defined"
  | NodeInputOutputShareIdentifier set -> "Input and output parameters cannot have common identifiers, "
    ^ "but found common parameters: " ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") (LA.SI.elements set)
  | MismatchOfEquationType (items, ty) -> "Term structure on left hand side of the equation "
    ^ (match items with
      | Some items -> Lib.string_of_t (Lib.pp_print_list LA.pp_print_struct_item ", ") items
      | None -> "")
    ^ " does not match expected type " ^ string_of_tc_type ty ^ " on right hand side of the node equation"
  | DisallowedReassignment vars -> "Cannot reassign value to a constant or enum but found reassignment to identifier(s): "
    ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") (LA.SI.elements vars)
  | DisallowedSubrangeInContractReturn (kind, id, ty) -> (match kind with | true -> "Argument '" | false -> "Return '")
    ^ HString.string_of_hstring id ^ "' can not have type "
    ^ string_of_tc_type ty ^ ". Contract " ^ (match kind with | true -> "assumptions" | false -> "guarantees")
    ^ " should be used instead"
  | AssumptionMustBeInputOrOutput id -> "Assumption variable must be either an input or an output variable, "
    ^ "but found '" ^ HString.string_of_hstring id ^ "'"
  | Redeclaration id -> HString.string_of_hstring id ^ " is already declared"
  | ExpectedConstant (where, what) -> "Illegal " ^ what ^ " in " ^ where
  | UndeclaredType id -> "Type '" ^ HString.string_of_hstring id ^ "' is undeclared"
  | EmptySubrange (v1, v2) -> "Range can not be empty, but found range: ["
    ^ string_of_int v1 ^ ", " ^ string_of_int v2 ^ "]"
  | SubrangeArgumentMustBeConstantInteger e -> "Range arguments should be of constant integers, but found: "
    ^ Lib.string_of_t LA.pp_print_expr e
  | IntervalMustHaveBound -> "Range should have at least one bound"
  | ExpectedRecordType ty -> "Expected record type but found " ^ string_of_tc_type ty
  | GlobalArrayConstraint expr -> "Unresolved global array constraint " ^ LA.string_of_expr expr

let (>>=) = R.(>>=)
let (let*) = R.(>>=)
let (>>) = R.(>>)

let type_error pos kind = Error (`LustreTypeCheckerError (pos, kind))
(** [type_error] returns an [Error] of [tc_result] *)


let union_keys key id1 id2 = match key, id1, id2 with
  | _, None, None -> None
  | _, (Some v), None -> Some v
  | _, None, (Some v) -> Some v
  | _, (Some v1), (Some v2) -> Some (v1 @ v2)

let mk_array_prop_desc is_call_arg pos = 
  let pos = (Lib.string_of_t Lib.pp_print_position pos) in
  if is_call_arg
  then "Node call argument at position " ^ pos ^ " has correct corresponding length argument"
  else "Definition of variable at position " ^ pos ^ " respects array length constraint" 

(**********************************************
 * Type inferring and type checking functions *
 **********************************************)
 let infer_type_const: Lib.position -> LA.constant -> tc_type
  = fun pos -> function
  | Num _ -> Int pos
  | Dec _ -> Real pos
  | _ -> Bool pos
(** Infers type of constants *)

let check_merge_clock: LA.expr -> LA.lustre_type -> (unit, [> error]) result = fun e ty ->
  match ty with
  | EnumType _ -> LSC.no_mismatched_clock false e
  | Bool _ -> LSC.no_mismatched_clock true e
  | _ -> Ok ()

let check_merge_exhaustive: tc_context -> Lib.position -> LA.lustre_type -> HString.t list -> (unit, [> error]) result
  = fun ctx pos ty cases ->
    match ty with
    | EnumType (_, enum_id, _) -> (match lookup_variants ctx enum_id with
        | Some variants ->
          let check_cases_containment = R.seq_
            (List.map (fun i ->
                if not (List.mem i variants) then
                  type_error pos (MergeCaseExtraneous (i, ty))
                else Ok ())
              cases)
          in
          let check_cases_cover = R.seq_
            (List.map (fun i ->
                if not (List.mem i cases) then
                  type_error pos (MergeCaseMissing i)
                else Ok ())
              variants)
          in
          let check_cases_unique = R.seq_
            (List.map (fun i -> 
              if List.length (List.filter (fun x -> HString.equal x i) cases) > 1 then
                type_error pos (MergeCaseNotUnique i)
              else Ok ())
              variants)
          in
          check_cases_containment >> check_cases_cover >> check_cases_unique
        | None -> type_error pos (Impossible ("Identifier "
          ^ (HString.string_of_hstring enum_id)
          ^ " is not an enumeration identifier")))
    | Bool _ -> Ok () (* TODO: What checks should we do for a boolean merge? *)
    | _ -> type_error pos (Impossible ("Type " ^ string_of_tc_type ty ^
      " must be a bool or an enum type"))

let rec infer_const_attr ctx exp =
  let r = infer_const_attr ctx in
  let combine l1 l2 = List.map2 (fun r1 r2 -> r1 >> r2) l1 l2 in
  let error exp what =
    let pos = LH.pos_of_expr exp in
    Error (pos, fun w -> ExpectedConstant (w, what))
  in
  match exp with
  | LA.Ident (_, i) ->
    let res =
      if member_val ctx i then R.ok ()
      else error exp ("variable '" ^ HString.string_of_hstring i ^ "'") 
    in
    [res]
  | ModeRef _ -> [error exp "mode reference"]
  | RecordProject (_, e, _) -> r e
  | TupleProject (_, e, _) -> r e
  (* Values *)
  | Const _ -> [R.ok ()]
  (* Operators *)
  | UnaryOp (_,_,e) -> r e
  | BinaryOp (_,_, e1, e2) -> combine (r e1) (r e2)
  | TernaryOp (_, Ite, e1, e2, e3) -> (
    let r_e2 = r e2 in
    match r e1 with
    | [Ok _] -> combine r_e2 (r e3)
    | [err] -> List.map (fun _ -> err) r_e2
    | _ -> assert false
  )
  | ConvOp  (_,_,e) -> r e
  | CompOp (_,_, e1, e2) -> combine (r e1) (r e2)
  (* Structured expressions *)
  | RecordExpr (_, _, flds) ->
    List.fold_left
      (fun l1 l2 -> combine l1 l2)
      [R.ok ()]
      (List.map r (snd (List.split flds)))
  | GroupExpr (_, ArrayExpr, es) | GroupExpr (_, TupleExpr, es) ->
    List.fold_left
      (fun l1 l2 -> combine l1 l2)
      [R.ok ()]
      (List.map r es)
  | GroupExpr (_, ExprList, es) -> List.flatten (List.map r es)
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) -> combine (r e1) (r e2)
  | ArrayConstr (_, e1, e2) -> combine (r e1) (r e2)
  | ArrayIndex (_, e1, e2) -> combine (r e1) (r e2)
  (* Quantified expressions *)
  | Quantifier (_, _, _, _) ->
    [error exp "quantified expression"]
  (* Clock operators *)
  | When (_, e, _) ->
    List.map (fun _ -> error exp "when operator") (r e)
  | Merge (_, _, es) ->
    List.map (fun _ -> error exp "merge operator")
      (r (List.hd (snd (List.split es))))
  (* Temporal operators *)
  | Pre (_, e) ->
    List.map (fun _ -> error exp "pre operator") (r e)
  | Arrow (_, e1, _) ->
    List.map (fun _ -> error exp "arrow operator") (r e1)
  (* Node calls *)
  | AnyOp _ -> assert false
  | Condact (_, _, _, i, _, _)
  | Activate (_, i, _, _, _)
  | RestartEvery (_, i, _, _)
  | Call (_, i, _) -> (
    let err = error exp "node call or any operator" in
    match lookup_node_ty ctx i with
    | Some (TArr (_, _, exp_ret_tys)) -> (
      match exp_ret_tys with
      | GroupType (_, tys) -> List.map (fun _ -> err) tys
      | _ -> [err]
    )
    | _ -> [err]
  )

let check_expr_is_constant ctx kind e =
  match R.seq_ (infer_const_attr ctx e) with
  | Ok _ -> R.ok ()
  | Error (pos, exn_fn) -> type_error pos (exn_fn kind)

let check_and_add_constant_definition ctx i e ty =
  match R.seq_ (infer_const_attr ctx e) with
  | Ok _ -> R.ok (add_ty (add_const ctx i e ty) i ty)
  | Error (pos, exn_fn) ->
    let where =
      "definition of constant '" ^ HString.string_of_hstring i ^ "'"
    in
    type_error pos (exn_fn where)

let check_constant_args ctx i arg_exprs =
  let check param_attr =
    let arg_attr =
      List.map (infer_const_attr ctx) arg_exprs
      |> List.flatten
    in
    R.seq_chain
      (fun _ ((id, is_const_param), res) ->
        match is_const_param, res with
        | true, Error (pos, exn_fn) -> (
          let where =
            "argument for constant parameter '" ^ HString.string_of_hstring id ^ "'"
          in
          type_error pos (exn_fn where)
        )
        | _ -> R.ok ()
      )
      ()
      (List.combine param_attr arg_attr)
  in
  match lookup_node_param_attr ctx i with
  | None -> assert false
  | Some param_attr -> (
    if List.exists (fun (_, is_const) -> is_const) param_attr then (
      check param_attr
    )
    else R.ok ()
  )

let rec type_extract_array_lens ctx ty = match ty with 
  | LA.ArrayType (_, (ty, expr)) -> expr :: type_extract_array_lens ctx ty
  | TupleType (_, tys) -> List.map (type_extract_array_lens ctx) tys |> List.flatten
  | GroupType (_, tys) -> List.map (type_extract_array_lens ctx) tys |> List.flatten
  | TArr (_, ty1, ty2) -> 
    type_extract_array_lens ctx ty1 @ type_extract_array_lens ctx ty2
  | RecordType (_, _, tis) ->
    let tys = List.map (fun (_, _, ty) -> ty) tis in 
    List.map (type_extract_array_lens ctx) tys |> List.flatten
  | UserType (_, id) -> 
    (match (lookup_ty_syn ctx id) with 
      | Some ty -> type_extract_array_lens ctx ty;
      | None -> [])
  | _ -> []

let update_ty_with_ctx node_ty call_params ctx arg_exprs =
  let call_param_len_idents =
    type_extract_array_lens ctx node_ty
    |> List.map (LH.vars_without_node_call_ids)
    (* Remove duplicates *)
    |> List.fold_left (fun acc vars -> LA.SI.union vars acc) LA.SI.empty
    |> LA.SI.elements
    (* Filter out constants. If "id" is a constant, it must be a local constant  *)
    |> List.filter (fun id -> not (member_val ctx id) || (List.mem id call_params) )
  in
  match call_param_len_idents with
  | [] -> node_ty
  | _ -> (
    let find_matching_len_params array_param_lens = 
      List.map (fun len -> (Lib.list_index (fun id2 -> len = id2) call_params)) array_param_lens
    in
    (* Find indices of array length parameters. E.g. in Call(m :: const int, A :: int^m), the index 
      of array length param "m" is 0. *)
    let array_len_indices = find_matching_len_params call_param_len_idents in
    (* Retrieve concrete arguments passed as array lengths *)
    let array_len_exprs = List.map (List.nth arg_exprs) array_len_indices in
    (* Do substitution to express exp_arg_tys and exp_ret_tys in terms of the current context *)
    LH.apply_subst_in_type (List.combine call_param_len_idents array_len_exprs) node_ty
  )

let rec infer_type_expr: tc_context -> LA.expr -> (tc_type * (LA.expr * string) list, [> error]) result
  = fun ctx -> function
  (* Identifiers *)
  | LA.Ident (pos, i) ->
    (match (lookup_ty ctx i) with
    | None -> type_error pos (UnboundIdentifier i) 
    | Some ty -> R.ok (ty, []))
  | LA.ModeRef (pos, ids) ->      
    let lookup_mode_ty ctx (ids:HString.t list) =
      match ids with
      | [] -> failwith ("empty mode name")
      | rest -> let i = HString.concat (HString.mk_hstring "::") rest in 
                match (lookup_ty ctx i) with
                | None -> type_error pos (UnboundModeReference i)
                | Some ty -> R.ok (ty, []) in
    lookup_mode_ty ctx ids
  | LA.RecordProject (pos, e, fld) ->
    let* rec_ty, constraints = infer_type_expr ctx e in
    let rec_ty = expand_type_syn ctx rec_ty in
    (match rec_ty with
    | LA.RecordType (_, _, flds) ->
        let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
        (match (List.assoc_opt fld typed_fields) with
        | Some ty -> R.ok (expand_type_syn ctx ty, constraints)
        | None -> type_error pos (NotAFieldOfRecord fld))
    | _ -> type_error (LH.pos_of_expr e) (IlltypedRecordProjection rec_ty))

  | LA.TupleProject (pos, e1, i) ->
    let* tup_ty, constraints = infer_type_expr ctx e1 in
    let tup_ty = expand_type_syn ctx tup_ty in
    (match tup_ty with
    | LA.TupleType (pos, tys) as ty ->
        if List.length tys <= i
        then type_error pos (TupleIndexOutOfBounds (i, ty))
        else R.ok (expand_type_syn ctx (List.nth tys i), constraints)
    | ty -> type_error pos (IlltypedTupleProjection ty))

  (* Values *)
  | LA.Const (pos, c) -> R.ok (infer_type_const pos c, [])

  (* Operator applications *)
  | LA.UnaryOp (pos, op, e) ->
    infer_type_unary_op ctx pos e op
  | LA.BinaryOp (pos, bop, e1, e2) ->
    infer_type_binary_op ctx pos bop e1 e2
  | LA.TernaryOp (pos, top, con, e1, e2) ->
    (match top with
    | Ite -> 
        infer_type_expr ctx con
        >>= (function
            | Bool _, cons1 ->
                let* e1_ty, cons2 = infer_type_expr ctx e1 in
                let* e2_ty, cons3 = infer_type_expr ctx e2 in
                let* eq_test, cons4 = eq_lustre_type ctx e1_ty e2_ty in
                    if eq_test then R.ok (e1_ty, cons1 @ cons2 @ cons3 @ cons4)
                    else type_error pos (UnequalIteBranchTypes (e1_ty, e2_ty))
            | c_ty, _  ->  type_error pos  (ExpectedBooleanExpression c_ty))
    )
  | LA.ConvOp (pos, cop, e) ->
    infer_type_conv_op ctx pos e cop
  | LA.CompOp (pos, cop, e1, e2) ->
    infer_type_comp_op ctx pos e1 e2 cop

  (* Structured expressions *)
  | LA.RecordExpr (pos, name, flds) -> (
    match lookup_ty_syn ctx name with
    | None -> type_error pos (UndeclaredType name)
    | Some ty ->
      match ty with
      | LA.RecordType (_, _, fld_tys) -> (
        let* matches =
          R.seq_chain
            (fun acc (p, f, ty) ->
              match List.assoc_opt f flds with
               | None -> type_error pos (NoValueForRecordField f)
               | Some e -> R.ok ( (p, f, e, ty) :: acc)
             )
             []
             fld_tys
        in
        if List.length flds > List.length matches then (
          let open HString in
          let fnames1 =
            HStringSet.of_list (List.map fst flds)
          in
          let fnames2 =
            HStringSet.of_list (List.map (fun (_, n, _) -> n) fld_tys)
          in
          let diff = HStringSet.diff fnames1 fnames2 in
          match HStringSet.choose_opt diff with
          | None -> assert false
          | Some name -> type_error pos (NotAFieldOfRecord name)
        )
        else (
          let infer_field ctx (p, i, exp, ty) =
            let* exp_ty, cons1 = infer_type_expr ctx exp in
            let* eq, cons2 = eq_lustre_type ctx ty exp_ty in
            if eq then R.ok (p, i, ty, cons1 @ cons2)
            else type_error (LH.pos_of_expr exp) (ExpectedType (ty, exp_ty))
          in
          let* fld_tys_cons = R.seq (List.map (infer_field ctx) matches) in
          let fld_tys = List.map (fun (a, b, c, _) -> (a, b, c)) fld_tys_cons in 
          let cons = List.map (fun (_, _, _, d) -> d) fld_tys_cons in
          R.ok (LA.RecordType (pos, name, fld_tys), List.flatten cons)
        )
      )
      | _ -> type_error pos (ExpectedRecordType ty)
  )
  | LA.GroupExpr (pos, struct_type, exprs) ->
    (match struct_type with
    | LA.ExprList ->
        let* tys, cons = R.seq (List.map (infer_type_expr ctx) exprs) |> R.splitM in
        R.ok (LA.GroupType (pos, tys), List.flatten cons)
    | LA.TupleExpr ->
        let* tys, cons = R.seq (List.map (infer_type_expr ctx) exprs) |> R.splitM in
        R.ok (LA.TupleType (pos, tys), List.flatten cons)
    | LA.ArrayExpr ->
        R.seq (List.map (infer_type_expr ctx) exprs) |> R.splitM
        >>= (fun (tys, cons1) ->
        let elty = List.hd tys in
        let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in 
        let* b, cons2 = (R.seqM f (true, []) (List.map (eq_lustre_type ctx elty) tys)) in
        if b
        then (let arr_ty = List.hd tys in
              let arr_size = LA.Const (pos, Num (List.length tys |> string_of_int |> HString.mk_hstring)) in
              R.ok (LA.ArrayType (pos, (arr_ty, arr_size)), List.flatten cons1 @ cons2))
        else (type_error pos UnequalArrayExpressionType)))
    
  (* Update structured expressions *)
  | LA.ArrayConstr (pos, b_expr, sup_expr) -> (
    let* b_ty, cons = infer_type_expr ctx b_expr in
    check_array_size_expr ctx sup_expr
    >> R.ok (LA.ArrayType (pos, (b_ty, sup_expr)), cons)
  )
  | LA.StructUpdate (pos, r, i_or_ls, e) ->
    if List.length i_or_ls != 1
    then type_error pos (Unsupported ("List of labels or indices for structure update is not supported"))
    else
      (match List.hd i_or_ls with
      | LA.Label (pos, l) ->  
          infer_type_expr ctx r
          >>= (function 
              | RecordType (_, _, flds) as r_ty, cons1 ->
                  (let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
                  (match (List.assoc_opt l typed_fields) with
                    | Some f_ty ->
                      infer_type_expr ctx e
                      >>= (fun (e_ty, cons2) -> 
                        let* b, cons3 = (eq_lustre_type ctx f_ty e_ty) in
                        if b                     then R.ok (r_ty, cons1 @ cons2 @ cons3)
                        else (type_error pos (TypeMismatchOfRecordLabel (l, f_ty, e_ty))))
                    | None -> type_error pos (NotAFieldOfRecord l)))
              | r_ty, _ -> type_error pos (IlltypedRecordUpdate r_ty))
      | LA.Index (_, e) -> type_error pos (ExpectedLabel e))
  | LA.ArrayIndex (pos, e, i) ->
    let* index_type, cons1 =  infer_type_expr ctx i in
    let index_type = expand_type_syn ctx index_type in
    if is_expr_int_type ctx i
    then infer_type_expr ctx e
        >>= (function
              | ArrayType (_, (b_ty, _)), cons2 -> R.ok (b_ty, cons1 @ cons2)
              | ty, _ -> type_error pos (IlltypedArrayIndex ty))
    else type_error pos (ExpectedIntegerTypeForArrayIndex index_type)

  (* Quantified expressions *)
  | LA.Quantifier (_, _, qs, e) ->
    let extn_ctx = List.fold_left union ctx
                    (List.map (fun (_, i, ty) -> singleton_ty i ty) qs) in
    infer_type_expr extn_ctx e 

  | AnyOp _ -> assert false
  (* Already desugared in lustreDesugarAnyOps *)
  (*check_type_expr ctx e ty >>
    R.ok ty*)
  (* Clock operators *)
  | LA.When (_, e, _) -> infer_type_expr ctx e
  | LA.Condact (pos, c, _, node, args, defaults) ->
    check_type_expr ctx c (Bool pos)
    >> let* r_ty, cons1 = infer_type_expr ctx (Call (pos, node, args)) in
    let* d_tys, cons2 = R.seq (List.map (infer_type_expr ctx) defaults) |> R.splitM in
    let* b, cons3 = (eq_lustre_type ctx r_ty (GroupType (pos, d_tys))) in
    if b
    then R.ok (r_ty, cons1 @ List.flatten cons2 @ cons3)
    else (type_error pos IlltypedDefaults)
  | LA.Activate (pos, node, cond, _, args) ->
    check_type_expr ctx cond (Bool pos)
    >> infer_type_expr ctx (Call (pos, node, args))
  | LA.Merge (pos, i, mcases) as e ->
    let* ty, cons1 = infer_type_expr ctx (LA.Ident (pos, i)) in
    let mcases_ids, mcases_exprs = List.split mcases in
    let case_tys = mcases_exprs |> List.map (infer_type_expr ctx) in
    check_merge_exhaustive ctx pos ty mcases_ids >>
    check_merge_clock e ty >>
    let* tys, cons2 = R.seq case_tys |> R.splitM in
    let main_ty = List.hd tys in
    let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in 
    let* b, cons3 = (R.seqM f (true, []) (List.map (eq_lustre_type ctx main_ty) tys)) in
    if b
    then R.ok (main_ty, cons1 @ List.flatten cons2 @ cons3)
    else (type_error pos (IlltypedMerge main_ty))
  | LA.RestartEvery (pos, node, args, cond) ->
    check_type_expr ctx cond (LA.Bool pos)
    >> infer_type_expr ctx (LA.Call (pos, node, args))
                                
  (* Temporal operators *)
  | LA.Pre (_, e) -> infer_type_expr ctx e
  | LA.Arrow (pos, e1, e2) ->
    let* ty1, cons1 = infer_type_expr ctx e1 in
    let* ty2, cons2 = infer_type_expr ctx e2 in
    let* b, cons3 = eq_lustre_type ctx ty1 ty2 in 
    if b
    then (R.ok (ty1, cons1 @ cons2 @ cons3))
    else (type_error pos (IlltypedArrow (ty1, ty2)))
     
  (* Node calls *)
  | LA.Call (pos, i, arg_exprs) -> (
    Debug.parse "Inferring type for node call %a" LA.pp_print_ident i ;
    let infer_type_node_args: tc_context -> LA.expr list -> (tc_type * (LA.expr * string) list, [> error]) result =
    fun ctx args ->
      let* arg_tys, cons = R.seq (List.map (infer_type_expr ctx) args) |> R.splitM in
      if List.length arg_tys = 1 then R.ok (List.hd arg_tys, List.hd cons)
      else R.ok (LA.GroupType (pos, arg_tys), List.flatten cons)
    in
    match (lookup_node_param_ids ctx i), (lookup_node_ty ctx i) with
    | Some call_params, Some node_ty -> (
      (* Express exp_arg_tys and exp_ret_tys in terms of the current context *)
      let node_ty = update_ty_with_ctx node_ty call_params ctx arg_exprs in

      let exp_arg_tys, exp_ret_tys = match node_ty with 
        | LA.TArr (_, exp_arg_tys, exp_ret_tys) -> exp_arg_tys, exp_ret_tys 
        | _ -> assert false 
      in
      let* given_arg_tys, cons1 = infer_type_node_args ctx arg_exprs in
      let* are_equal, cons2 = eq_lustre_type ~is_call_arg:true ctx given_arg_tys exp_arg_tys in
      if are_equal then
        let* ctx = (check_constant_args ctx i arg_exprs >> (R.ok exp_ret_tys)) in 
        R.ok (ctx, cons1 @ cons2)
      else
        (type_error pos (IlltypedCall (exp_arg_tys, given_arg_tys)))
    )
    | _, Some ty -> type_error pos (ExpectedFunctionType ty)
    | _, None -> type_error pos (UnboundNodeName i)
  )
(** Infer the type of a [LA.expr] with the types of free variables given in [tc_context] *)

and check_type_expr: tc_context -> LA.expr -> tc_type -> ((LA.expr * string) list, [> error]) result
  = fun ctx expr exp_ty ->
  match expr with
  (* Identifiers *)
  | Ident (pos, i) as ident ->
    let* ty, cons1 = infer_type_expr ctx ident in
    let* b, cons2 = (eq_lustre_type ctx ty exp_ty) in
    if b then R.ok (cons1 @ cons2)
    else (type_error pos (IlltypedIdentifier (i, exp_ty, ty)))
  | ModeRef (pos, ids) ->
    let id = (match ids with
              | [] -> failwith ("empty mode name")
              | rest -> HString.concat (HString.mk_hstring "::") rest) in
    check_type_expr ctx (LA.Ident (pos, id)) exp_ty
  | RecordProject (pos, expr, fld) -> check_type_record_proj pos ctx expr fld exp_ty
  | TupleProject (pos, expr, idx) -> check_type_tuple_proj pos ctx expr idx exp_ty

  (* Operators *)
  | UnaryOp (pos, op, e) ->
    let* inf_ty, cons1 = infer_type_unary_op ctx pos e op in
    let* b, cons2 = (eq_lustre_type ctx inf_ty exp_ty) in
    if b
    then R.ok (cons1 @ cons2) 
    else (type_error pos (UnificationFailed (exp_ty, inf_ty)))
  | BinaryOp (pos, op, e1, e2) -> 
    let* inf_ty, cons1 = infer_type_binary_op ctx pos op e1 e2 in
    let* b, cons2 = eq_lustre_type ctx inf_ty exp_ty in
    if b then R.ok (cons1 @ cons2) 
    else (type_error pos (UnificationFailed (exp_ty, inf_ty)))
  | LA.TernaryOp (pos, _, con, e1, e2) ->
    infer_type_expr ctx con
    >>= (function 
        | Bool _, cons1 ->
          let* ty1, cons2 = infer_type_expr ctx e1 in 
          let* ty2, cons3 = infer_type_expr ctx e2 in
          let* b, cons4 = eq_lustre_type ctx ty1 ty2 in 
          if b then R.ok (cons1 @ cons2 @ cons3 @ cons4)
          else (type_error pos (UnificationFailed (ty1, ty2)))
        | ty, _ -> type_error pos (ExpectedType ((Bool pos), ty)))
  | ConvOp (pos, cvop, e) ->
    let* inf_ty, cons1 = infer_type_conv_op ctx pos e cvop in
    let* b, cons2 = eq_lustre_type ctx inf_ty exp_ty in 
    if b then R.ok (cons1 @ cons2)
    else (type_error pos (UnificationFailed (exp_ty, inf_ty)))
  | CompOp (pos, cop, e1, e2) ->
    let* inf_ty, cons1 = infer_type_comp_op ctx pos e1 e2 cop in
    let* b, cons2 = (eq_lustre_type ctx inf_ty exp_ty) in
    if b then 
    R.ok (cons1 @ cons2)
    else (type_error pos (UnificationFailed (exp_ty, inf_ty)))

  (* Values/Constants *)
  | Const (pos, c) ->
    let cty = infer_type_const pos c in
    let* b, cons = (eq_lustre_type ctx cty exp_ty) in 
    if b then R.ok cons 
    else (type_error pos (UnificationFailed (exp_ty, cty)))

  (* Structured expressions *)
  | RecordExpr (pos, name, flds) ->
    let (ids, es) = List.split flds in
    let mk_ty_ident p i t = (p, i, t) in
    let* inf_tys, cons1 = R.seq (List.map (infer_type_expr ctx) es) |> R.splitM in
    let inf_r_ty = LA.RecordType (pos, name, (List.map2 (mk_ty_ident pos) ids inf_tys)) in
    let* b, cons2 = (eq_lustre_type ctx inf_r_ty exp_ty) in
    if b then R.ok (List.flatten cons1 @ cons2)
    else (type_error pos (UnificationFailed (exp_ty, inf_r_ty)))
  | GroupExpr (pos, group_ty, es) ->
    (match group_ty with
    (* These should be tuple type  *)
    | ExprList ->
        let* inf_tys, cons1 = R.seq (List.map (infer_type_expr ctx) es) |> R.splitM in 
        let inf_ty = LA.GroupType (pos, inf_tys) in
        let* b, cons2 = (eq_lustre_type ctx inf_ty exp_ty) in
        if b then 
        R.ok (List.flatten cons1 @ cons2)
        else (type_error pos (ExpectedType (exp_ty, inf_ty)))
      | TupleExpr ->
        let* inf_tys, cons1 = R.seq (List.map (infer_type_expr ctx) es) |> R.splitM in
        let inf_ty = LA.TupleType (pos, inf_tys) in
        let* b, cons2 = (eq_lustre_type ctx inf_ty exp_ty) in
        if b     then R.ok (List.flatten cons1 @ cons2) 
        else (type_error pos (ExpectedType (exp_ty, inf_ty)))
    (* This should be array type *)
    | ArrayExpr ->
        let* inf_tys, cons1 = R.seq (List.map (infer_type_expr ctx) es) |> R.splitM in
        if List.length inf_tys < 1
        then type_error pos EmptyArrayExpression
        else
          let elty = List.hd inf_tys in
          let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in
          let* b, cons2 = (R.seqM f (true, []) (List.map (eq_lustre_type ctx elty) inf_tys)) in
          if b
          then (
            let arr_size = LA.Const (pos, Num (List.length inf_tys |> string_of_int |> HString.mk_hstring)) in
            let arr_ty = LA.ArrayType (pos, (elty, arr_size)) in
            let* b, cons3 = (eq_lustre_type ctx (LA.ArrayType (pos, (arr_ty, arr_size))) exp_ty) in (
            if b then R.ok (List.flatten cons1 @ cons2 @ cons3)
            else (type_error pos (ExpectedType (exp_ty, arr_ty))))
          )
          else (type_error pos UnequalArrayExpressionType)
      )

  (* Update of structured expressions *)
  | StructUpdate (pos, r, i_or_ls, e) ->
    if List.length i_or_ls != 1
    then type_error pos (Unsupported ("List of labels or indices for structure update is not supported"))
    else (match List.hd  i_or_ls with
          | LA.Label (pos, l) ->  (
            let* r_ty, cons1 = infer_type_expr ctx r in 
              match r_ty with
              | RecordType (_, _, flds) ->
                (let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
                  (match (List.assoc_opt l typed_fields) with
                  | Some ty -> 
                    let* cons2  = check_type_expr ctx e ty in 
                    R.ok (cons1 @ cons2)
                  | None -> type_error pos (NotAFieldOfRecord l)))
              | _ -> type_error pos (IlltypedRecordUpdate r_ty)
            )
          | LA.Index (_, e) -> type_error pos (ExpectedLabel e))

  (* Array constructor*)
  | ArrayConstr (pos, b_exp, sup_exp) ->
    let* b_ty, cons1 = infer_type_expr ctx b_exp in
    let* _ = infer_type_expr ctx sup_exp in
    let arr_ty = (LA.ArrayType (pos, (b_ty, sup_exp))) in
    let* b, cons2 = (eq_lustre_type ctx arr_ty exp_ty) in
    if b then R.ok (cons1 @ cons2)
    else (type_error pos (ExpectedType (exp_ty, arr_ty)))

  | ArrayIndex (pos, e, idx) ->
    let* index_type, cons1 = infer_type_expr ctx idx in
    if is_expr_int_type ctx idx
    then let* inf_arr_ty, cons2 = infer_type_expr ctx e in
        (match inf_arr_ty with
          | ArrayType (_, (arr_b_ty, _)) ->
            let* b, cons3  = (eq_lustre_type ctx exp_ty arr_b_ty) in
            if b         then R.ok (cons1 @ cons2 @ cons3)
            else (type_error pos (ExpectedType (exp_ty, arr_b_ty)))
          | _ -> type_error pos (ExpectedArrayType inf_arr_ty))
    else type_error pos (ExpectedIntegerTypeForArrayIndex index_type)

  (* Quantified expressions *)
  | Quantifier (_, _, qs, e) ->
    let extn_ctx = List.fold_left union ctx
                    (List.map (fun (_, i, ty) -> singleton_ty i ty) qs) in
    check_type_expr extn_ctx e exp_ty

  | AnyOp _ -> assert false 
    (* Already desugared in lustreDesugarAnyOps *)
    (*let extn_ctx = union ctx (singleton_ty i ty) in
    check_type_expr extn_ctx e (Bool pos)
    >> R.guard_with (eq_lustre_type ctx exp_ty ty) (type_error pos (UnificationFailed (exp_ty, ty)))
  | AnyOp (pos, (_, i ,ty), e1, Some e2) ->
    let extn_ctx = union ctx (singleton_ty i ty) in
    check_type_expr extn_ctx e1 (Bool pos)
    >> check_type_expr extn_ctx e2 (Bool pos)
    >> R.guard_with (eq_lustre_type ctx exp_ty ty) (type_error pos (UnificationFailed (exp_ty, ty)))*)
  (* Clock operators *)
  | When (_, e, _) -> check_type_expr ctx e exp_ty
  | Condact (pos, c, _, node, args, defaults) ->
    let* cons1 = check_type_expr ctx c (Bool pos) in 
    let* cons2 = check_type_expr ctx (Call (pos, node, args)) exp_ty in
    let* d_tys, cons3 =  R.seq (List.map (infer_type_expr ctx) defaults) |> R.splitM in 
    let* b, cons4 = eq_lustre_type ctx (GroupType (pos, d_tys)) exp_ty in
    if b then R.ok (cons1 @ cons2 @ List.flatten cons3 @ cons4)
    else (type_error pos IlltypedDefaults)
  | Activate (pos, node, cond, _, args) -> 
    check_type_expr ctx cond (Bool pos)
    >> check_type_expr ctx (Call (pos, node, args)) exp_ty 
  | Merge (pos, i, mcases) as e ->
    let* ty, cons1 = infer_type_expr ctx (LA.Ident (pos, i)) in
    let mcases_ids, mcases_exprs = List.split mcases in
    let* cons2 = R.seq
      (List.map (fun e -> check_type_expr ctx e exp_ty) mcases_exprs)
    in
      check_merge_exhaustive ctx pos ty mcases_ids
      >> check_merge_clock e ty
      >> R.ok (cons1 @ List.flatten cons2)
  | RestartEvery (pos, node, args, cond) ->
    check_type_expr ctx cond (LA.Bool pos)
    >> check_type_expr ctx (LA.Call (pos, node, args)) exp_ty

  (* Temporal operators *)
  | Pre (_, e) -> check_type_expr ctx e exp_ty
  | Arrow (_, e1, e2) ->
    check_type_expr ctx e1 exp_ty
    >> check_type_expr ctx e2 exp_ty

  (* Node calls *)
  | Call (pos, i, args) ->
    let* arg_tys, cons1 = R.seq (List.map (infer_type_expr ctx) args) |> R.splitM in
    let arg_ty = if List.length arg_tys = 1 then List.hd arg_tys
                else GroupType (pos, arg_tys) in
    (match (lookup_node_ty ctx i), (lookup_node_param_ids ctx i) with
    | None, _ 
    | _, None -> type_error pos (UnboundNodeName i)
    | Some ty, Some call_params -> 
      (* Express ty in terms of the current context *)
      let ty = update_ty_with_ctx ty call_params ctx args in
      let* b, cons2 = (eq_lustre_type ctx (LA.TArr (pos, arg_ty, exp_ty)) ty) in
      if b then R.ok (List.flatten cons1 @ cons2) 
      else (type_error pos (MismatchedNodeType (i, (TArr (pos, arg_ty, exp_ty)), ty))))
(** Type checks an expression and returns [ok] 
 * if the expected type is the given type [tc_type]  
 * returns an [Error of string] otherwise *)

and infer_type_unary_op: tc_context -> Lib.position -> LA.expr -> LA.unary_operator -> (tc_type * (LA.expr * string) list, [> error]) result
  = fun ctx pos e op ->
  let* ty, cons1 = infer_type_expr ctx e in
  match op with
  | LA.Not ->
    let* b, cons2 = (eq_lustre_type ctx ty (Bool pos)) in
    if b
    then (R.ok (LA.Bool pos, cons1 @ cons2))
    else (type_error pos (ExpectedType (LA.Bool pos, ty)))
  | LA.BVNot ->
    if LH.is_type_machine_int ty
    then R.ok (ty, cons1)
    else type_error pos (IlltypedBitNot ty)
  | LA.Uminus ->
    if (LH.is_type_num ty)
    then R.ok (ty, cons1)
    else type_error pos (IlltypedUnaryMinus ty)
(** Infers type of unary operator application *)

and are_args_num: tc_context -> Lib.position -> tc_type -> tc_type -> (bool * (LA.expr * string) list, [> error]) result
  = fun ctx pos ty1 ty2 ->
  let num1 = HString.mk_hstring "1" in
  let num_tys = [
      LA.Int pos
    ; LA.UInt8 pos
    ; LA.UInt16 pos
    ; LA.UInt32 pos
    ; LA.UInt64 pos
    ; LA.Int8 pos
    ; LA.Int16 pos
    ; LA.Int32 pos
    ; LA.Int64 pos
    ; LA.IntRange (pos, Some (Const (pos, Num num1)), Some (Const (pos, Num num1))) 
    ; LA.Real pos] in
  let are_equal_types: tc_context -> tc_type -> tc_type -> tc_type -> (bool * (LA.expr * string) list, [> error]) result
    = fun ctx ty1 ty2 ty ->
    let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in  
    R.seqM f (true, []) [ eq_lustre_type ctx ty1 ty
                        ; eq_lustre_type ctx ty2 ty ] 
    in
  let f = (fun (b1, exprs1) (b2, exprs2) -> b1 || b2, exprs1 @ exprs2) in
  R.seqM f (false, []) (List.map (are_equal_types ctx ty1 ty2) num_tys) 
(** This is an ugly fix till we have polymorphic unification, may be qualified types? *)
  
and infer_type_binary_op: tc_context -> Lib.position
                          -> LA.binary_operator -> LA.expr -> LA.expr
                          -> (tc_type * (LA.expr * string) list, [> error]) result
  = fun ctx pos op e1 e2 ->
  let* ty1, cons1 = infer_type_expr ctx e1 in
  let* ty2, cons2 = infer_type_expr ctx e2 in
  match op with
  | LA.And | LA.Or | LA.Xor | LA.Impl ->
    let* b1, cons3 = (eq_lustre_type ctx ty1 (Bool pos)) in
    if b1
    then (
      let* b2, cons4 = (eq_lustre_type ctx ty2 (Bool pos)) in
      if b2 
      then (R.ok (LA.Bool pos, cons1 @ cons2 @ cons3 @ cons4))
      else (type_error pos (ExpectedType ((LA.Bool pos), ty2)))
    )
    else (type_error pos (ExpectedType ((LA.Bool pos), ty1)))
  | LA.Mod ->
    if LH.is_type_int_or_machine_int ty1 && LH.is_type_int_or_machine_int ty2
    then (
      let* b, cons3 = (eq_lustre_type ctx ty1 ty2) in
      if b
      then R.ok (ty1, cons1 @ cons2 @ cons3)
      else (type_error pos (UnificationFailed (ty1, ty2)))
    )
    else (type_error pos (ExpectedIntegerTypes (ty1, ty2)))
  | LA.Plus | LA.Minus | LA.Times | LA.Div ->
    let* is_num, cons3 = are_args_num ctx pos ty1 ty2 in
    if is_num
    then R.ok (ty2, cons1 @ cons2 @ cons3)
    else type_error pos (ExpectedNumberTypes (ty1, ty2))
  | LA.IntDiv ->
    if LH.is_type_int_or_machine_int ty1 && LH.is_type_int_or_machine_int ty2
    then (
      let* b, cons3 = (eq_lustre_type ctx ty1 ty2) in 
      if b   then R.ok (ty1, cons1 @ cons2 @ cons3)
      else (type_error pos (UnificationFailed (ty1, ty2)))
    )
    else type_error pos (ExpectedIntegerTypes (ty1, ty2))
  | LA.BVAnd | LA.BVOr ->
    let* b, cons3 = (eq_lustre_type ctx ty1 ty2) in 
    if b then  
      (if LH.is_type_machine_int ty1 && LH.is_type_machine_int ty2
      then R.ok (ty2, cons1 @ cons2 @ cons3)
      else type_error pos (ExpectedMachineIntegerTypes (ty1, ty2)))
    else (type_error pos (UnificationFailed (ty1, ty2)))
  | LA.BVShiftL | LA.BVShiftR ->
    if (LH.is_type_signed_machine_int ty1 || LH.is_type_unsigned_machine_int ty1)
    then (if (LH.is_type_unsigned_machine_int ty2
              && LH.is_machine_type_of_associated_width (ty1, ty2))
          then R.ok (ty1, cons1 @ cons2)
          else type_error pos (ExpectedBitShiftConstantOfSameWidth ty1))
    else type_error pos (ExpectedBitShiftMachineIntegerType ty1)
(** infers the type of binary operators  *)

and infer_type_conv_op: tc_context -> Lib.position
                        ->  LA.expr -> LA.conversion_operator
                        -> (tc_type * (LA.expr * string) list, [> error]) result
  = fun ctx pos e op ->
  let* ty, cons = infer_type_expr ctx e in
  match op with
  | ToInt ->
    if LH.is_type_num ty
    then R.ok (LA.Int pos, cons)
    else type_error pos (InvalidConversion (ty, (Int pos)))
  | ToReal ->
    if LH.is_type_real_or_int ty
    then R.ok (LA.Real pos, cons)
    else type_error pos (InvalidConversion (ty, (Real pos)))
  | ToInt8 ->
    if LH.is_type_signed_machine_int ty || LH.is_type_int ty
    then R.ok (LA.Int8 pos, cons)
    else type_error pos (InvalidConversion (ty, (Int8 pos)))
  | ToInt16 ->
    if LH.is_type_signed_machine_int ty || LH.is_type_int ty
    then R.ok (LA.Int16 pos, cons)
    else type_error pos (InvalidConversion (ty, (Int16 pos)))
  | ToInt32 ->
    if LH.is_type_signed_machine_int ty || LH.is_type_int ty
    then R.ok (LA.Int32 pos, cons)
    else type_error pos (InvalidConversion (ty, (Int32 pos)))
  | ToInt64 ->
    if LH.is_type_signed_machine_int ty || LH.is_type_int ty
    then R.ok (LA.Int64 pos, cons)
    else type_error pos (InvalidConversion (ty, (Int64 pos)))
  | ToUInt8 ->
    if LH.is_type_unsigned_machine_int ty || LH.is_type_int ty
    then R.ok (LA.UInt8 pos, cons)
    else type_error pos (InvalidConversion (ty, (UInt8 pos)))
  | ToUInt16 ->
    if LH.is_type_unsigned_machine_int ty || LH.is_type_int ty
    then R.ok (LA.UInt16 pos, cons)
    else type_error pos (InvalidConversion (ty, (UInt16 pos)))
  | ToUInt32 ->
    if LH.is_type_unsigned_machine_int ty || LH.is_type_int ty
    then R.ok (LA.UInt32 pos, cons)
    else type_error pos (InvalidConversion (ty, (UInt32 pos)))
  | ToUInt64 ->
    if LH.is_type_unsigned_machine_int ty || LH.is_type_int ty
    then R.ok (LA.UInt64 pos, cons)
    else type_error pos (InvalidConversion (ty, (UInt64 pos)))
(** Converts from given type to the intended type aka casting *)
    
and infer_type_comp_op: tc_context -> Lib.position -> LA.expr -> LA.expr
                        -> LA.comparison_operator -> (tc_type * (LA.expr * string) list, [> error]) result
  = fun ctx pos e1 e2 op ->
  let* ty1, cons1 = infer_type_expr ctx e1 in
  let* ty2, cons2 = infer_type_expr ctx e2 in
  match op with
  | Neq  | Eq ->
    let* b, cons3 = (eq_lustre_type ctx ty1 ty2) in
    if b then (
      if LH.type_contains_array ty1 
      then type_error pos (Unsupported "Extensional array equality is not supported")
      else R.ok (LA.Bool pos, cons1 @ cons2 @ cons3)
    )
    else (type_error pos (UnificationFailed (ty1, ty2)))
  | Lte | Lt  | Gte | Gt ->
    let* is_num, cons3 = are_args_num ctx pos ty1 ty2 in
    if is_num
    then R.ok (LA.Bool pos, cons1 @ cons2 @ cons3)
    else type_error pos (ExpectedIntegerTypes (ty1, ty2))
(** infer the type of comparison operator application *)
                  
and check_type_record_proj: Lib.position -> tc_context -> LA.expr -> LA.index -> tc_type -> ((LA.expr * string) list, [> error]) result =
  fun pos ctx expr idx exp_ty -> 
  infer_type_expr ctx expr
  >>= function
  | RecordType (_, _, flds), cons1 ->
    (match (List.find_opt (fun (_, i, _) -> i = idx) flds) with 
    | None -> type_error pos (NotAFieldOfRecord idx)
    | Some f -> R.ok (f, cons1))
    >>= fun ((_, _, fty), cons1) ->
    let* b, cons2 = (eq_lustre_type ctx fty exp_ty) in 
    if b then R.ok (cons1 @ cons2)
    else (type_error pos (UnificationFailed (exp_ty, fty)))
  | rec_ty, _ -> type_error (LH.pos_of_expr expr) (IlltypedRecordProjection rec_ty)

and check_type_tuple_proj : Lib.position -> tc_context -> LA.expr -> int -> tc_type -> ((LA.expr * string) list, [> error]) result =
  fun pos ctx expr idx exp_ty ->
  infer_type_expr ctx expr
  >>= function
  | TupleType (_, tys) as ty, cons ->
    if List.length tys <= idx
    then type_error pos (TupleIndexOutOfBounds (idx, ty))
    else R.ok (List.nth tys idx, cons)
    >>= fun (ity, cons1) ->
    let* b, cons2 = (eq_lustre_type ctx ity exp_ty) in
    if b then R.ok (cons1 @ cons2)
    else (type_error pos (UnificationFailed (exp_ty, ity)))
  | ty, _ -> type_error (LH.pos_of_expr expr) (IlltypedTupleProjection ty)

and check_type_const_decl: tc_context -> LA.const_decl -> tc_type -> ((LA.expr * string) list, [> error]) result =
  fun ctx const_decl exp_ty ->
  match const_decl with
  | FreeConst (pos, i, _) ->
    (match (lookup_ty ctx i) with
    | None -> failwith "Free constant should have an associated type"
    | Some inf_ty -> 
      let* b, cons = (eq_lustre_type ctx inf_ty exp_ty) in
      if b
      then R.ok cons
      else (type_error pos (IlltypedIdentifier (i, inf_ty, exp_ty))))
  | UntypedConst (pos, i, e) ->
    let* inf_ty, cons1 = infer_type_expr ctx e in
    let* b, cons2 = (eq_lustre_type ctx inf_ty exp_ty) in
    if b then R.ok (cons1 @ cons2)
    else (type_error pos (IlltypedIdentifier (i, exp_ty, inf_ty)))
  | TypedConst (pos, i, exp, _) ->
    let* inf_ty, cons1 = infer_type_expr ctx exp in
    let* b, cons2 = (eq_lustre_type ctx inf_ty exp_ty) in 
    if b then R.ok (cons1 @ cons2)
    else (type_error pos (IlltypedIdentifier (i, exp_ty, inf_ty)))

and local_var_binding: tc_context -> LA.node_local_decl -> (tc_context * (LA.expr * string) list, [> error]) result = fun ctx ->
    function
    | LA.NodeConstDecl (_, const_decls) ->
      Debug.parse "Extracting typing context from const declaration: %a"
        LA.pp_print_const_decl const_decls
      ; tc_ctx_const_decl ctx const_decls 
    | LA.NodeVarDecl (pos, (_, v, ty, _)) ->
      if (member_ty ctx v) then type_error pos (Redeclaration v)
      else check_type_well_formed ctx ty
          >> R.ok (add_ty ctx v ty, [])

and check_type_node_decl: Lib.position -> tc_context -> LA.node_decl -> ((LA.expr * string) list, [> error]) result
  = fun pos ctx
        (node_name, is_extern, params, input_vars, output_vars, ldecls, items, contract)
        ->
  Debug.parse "TC declaration node: %a {" LA.pp_print_ident node_name;
  let arg_ids = LA.SI.of_list (List.map (fun a -> LH.extract_ip_ty a |> fst) input_vars) in
  let ret_ids = LA.SI.of_list (List.map (fun a -> LH.extract_op_ty a |> fst) output_vars) in

  (* check if any of the arg ids or return ids already exist in the typing context.
      Fail if they do. 
      This is a strict no-shadowing policy put inplace to be in agreement with 
      the old type checking flow. 
      This behavior can be relaxed once the backend supports it.    
    *)

  R.seq_chain (fun _ i ->
      (if (member_ty ctx i) then
          type_error pos (Redeclaration i)
        else R.ok()))
    () (LA.SI.elements arg_ids @ LA.SI.elements ret_ids)
  
  >>
    (Debug.parse "Params: %a (skipping)" LA.pp_print_node_param_list params;
    (* store the input constants passed in the input *)
    let ip_constants_ctx = List.fold_left union ctx
      (List.map extract_consts input_vars)
    in
    (* These are inputs to the node *)
    let ctx_plus_ips = List.fold_left union ip_constants_ctx
      (List.map extract_arg_ctx input_vars)
    in
    (* These are outputs of the node *)
    let ctx_plus_ops_and_ips = List.fold_left union ctx_plus_ips
      (List.map extract_ret_ctx output_vars)
    in
    Debug.parse "Local Typing Context after extracting ips/ops/consts {%a}"
      pp_print_tc_context ctx_plus_ops_and_ips;
    (* Type check the contract *)
    let* cons1 = (match contract with
      | None -> R.ok ([])
      | Some c ->
        let* con_ctx, cons1 = tc_ctx_of_contract ctx_plus_ops_and_ips c in
        Debug.parse "Checking node contract with context %a"
          pp_print_tc_context con_ctx;
        let* cons2 = check_type_contract (arg_ids, ret_ids) con_ctx c in 
        R.ok (cons1 @ cons2)) in
      (* if the node is extern, we will not have any body to typecheck *)
      if is_extern
      then R.ok ( Debug.parse "External Node, no body to type check."
                ; Debug.parse "TC declaration node %a done }" LA.pp_print_ident node_name; [])
      else (
        (* add local variable binding in the context *)
        let* local_var_ctxts, cons2 = R.seq (List.map (local_var_binding ctx_plus_ips) ldecls) |> R.splitM in
        (* Local TC context is input vars + output vars + local const + var decls *)
        let local_ctx = List.fold_left union ctx_plus_ops_and_ips local_var_ctxts in
        Debug.parse "Local Typing Context with local state: {%a}" pp_print_tc_context local_ctx;
        (* Type check the node items now that we have all the local typing context *)
        let* cons3 = R.seq (List.map (do_item local_ctx) items) in
        (* check that the LHS of the equations are not args to node *)
        let check_lhs_eqns = List.map (fun (pos, v) ->
            if SI.mem v arg_ids then
              type_error pos (NodeArgumentOnLHS v)
            else R.ok ())
          (List.flatten (List.map LH.defined_vars_with_pos items))
          |> R.seq_
        in
        Debug.parse "TC declaration node %a done }"
          LA.pp_print_ident node_name;
        check_lhs_eqns >> R.ok (cons1 @ List.flatten cons2 @ List.flatten cons3)))

and do_node_eqn: tc_context -> LA.node_equation -> ((LA.expr * string) list, [> error]) result = fun ctx ->
  function
  | LA.Assert (pos, e) ->
    Debug.parse "Checking assertion: %a" LA.pp_print_expr e;
    check_type_expr ctx e (Bool pos)
  | LA.Equation (_, lhs, e)  as eqn ->
    Debug.parse "Checking equation: %a" LA.pp_print_node_body eqn;
    (* This is a special case where we have undeclared identifiers 
       as short hands for assigning values to arrays aka recursive technique *)
    let get_array_def_context: LA.struct_item -> tc_context = 
      function
      | ArrayDef (pos, _, is) ->
        List.fold_left (fun c i -> add_ty c i (LA.Int pos)) empty_tc_context is 
      | _ -> empty_tc_context
    in
    let ctx_from_lhs ctx (LA.StructDef (_, items)) =
      List.fold_left union ctx (List.map get_array_def_context items)
    in
    let new_ctx = ctx_from_lhs ctx lhs in
    Debug.parse "Checking node equation lhs=%a; rhs=%a"
      LA.pp_print_eq_lhs lhs
      LA.pp_print_expr e;
    let* ty, cons1 = infer_type_expr new_ctx e in
    Debug.parse "RHS has type %a for lhs %a" LA.pp_print_lustre_type ty LA.pp_print_eq_lhs lhs;
    let* cons2  = check_type_struct_def new_ctx lhs ty in 
    R.ok (cons1 @ cons2)

and do_item: tc_context -> LA.node_item -> ((LA.expr * string) list, [> error]) result = fun ctx ->
  function
  | LA.Body eqn -> do_node_eqn ctx eqn
  | LA.IfBlock (pos, e, l1, l2) ->
    let* guard_type, cons1 = infer_type_expr ctx e in
    (match guard_type with
      | Bool _ -> 
        let* cons2 = (R.seq ((List.map (do_item ctx) l1) @ (List.map (do_item ctx) l2))) in
        R.ok (cons1 @ List.flatten cons2)
      | e_ty -> type_error pos  (ExpectedBooleanExpression e_ty)
    )
  | LA.FrameBlock (pos, vars, nes, nis) -> 
    let vars = List.map snd vars in
    let reassigned_consts = (SI.filter (fun e -> (member_val ctx e)) (SI.of_list vars)) in
    let* cons = R.seq (
      (
        if ((SI.cardinal reassigned_consts) = 0) 
        then R.ok ([])
        else type_error pos (DisallowedReassignment reassigned_consts)
      ) :: (List.map (do_node_eqn ctx) nes) @ (List.map (do_item ctx) nis) 
    ) in 
    R.ok (List.flatten cons)
  | LA.AnnotMain _ as ann ->
    Debug.parse "Node Item Skipped (Main Annotation): %a" LA.pp_print_node_item ann
    ; R.ok []
  | LA.AnnotProperty (_, _, e1, Provided e2) as ann ->
    Debug.parse "Checking Node Item (Annotation Property): %a (%a)"
      LA.pp_print_node_item ann LA.pp_print_expr e1
    ; check_type_expr ctx e1 (Bool (LH.pos_of_expr e1)) >> check_type_expr ctx e2 (Bool (LH.pos_of_expr e2)) 
  | LA.AnnotProperty (_, _, e, _) as ann ->
    Debug.parse "Checking Node Item (Annotation Property): %a (%a)"
      LA.pp_print_node_item ann LA.pp_print_expr e
    ; check_type_expr ctx e (Bool (LH.pos_of_expr e))
  
and check_type_struct_item: tc_context -> LA.struct_item -> tc_type -> ((LA.expr * string) list, [> error]) result
  = fun ctx st exp_ty ->
  match st with
  | SingleIdent (pos, i) ->
    let* inf_ty = (match (lookup_ty ctx i) with
      | None -> type_error pos
        (Impossible ("Could not find Identifier " ^ (HString.string_of_hstring i)))
      | Some ty -> R.ok ty)
    in
    let* inferred_is_expected1, cons1 = eq_lustre_type ~pos:pos ctx inf_ty exp_ty in
    let* inferred_is_expected2, cons2 = eq_lustre_type ~pos:pos ctx (GroupType (pos, [inf_ty])) exp_ty in
    let cons = if inferred_is_expected1 then cons1 else cons2 in
    if inferred_is_expected1 || inferred_is_expected2 then
      if member_val ctx i then 
        type_error pos (Impossible ("Constant "
          ^ (HString.string_of_hstring i)
          ^ " cannot be re-defined"))
        else R.ok (cons)
    else
      type_error pos (ExpectedType (exp_ty, inf_ty))

    (* R.ifM (R.seqM (||) false [ eq_lustre_type ctx exp_ty inf_ty
                            ; eq_lustre_type ctx exp_ty (GroupType (pos,[inf_ty])) ])
      (if member_val ctx i
      then type_error pos (Impossible ("Constant "
        ^ (HString.string_of_hstring i)
        ^ " cannot be re-defined"))
      else R.ok ())
      (type_error pos (ExpectedType (exp_ty, inf_ty))) *)
  | ArrayDef (pos, base_e, idxs) ->
    let array_idx_expr =
      List.fold_left (fun e i -> LA.ArrayIndex (pos, e, i))
        (LA.Ident (pos, base_e))
        (List.map (fun i -> LA.Ident (pos, i)) idxs)
    in
    check_type_expr ctx array_idx_expr exp_ty
  | TupleStructItem _ -> Lib.todo __LOC__
  | TupleSelection _ -> Lib.todo __LOC__
  | FieldSelection _ -> Lib.todo __LOC__
  | ArraySliceStructItem _ -> Lib.todo __LOC__

and check_type_struct_def: tc_context -> LA.eq_lhs -> tc_type -> ((LA.expr * string) list, [> error]) result
  = fun ctx (StructDef (pos, lhss)) exp_ty ->
  (* This is a structured type, and we would want the expected type exp_ty to be a tuple type *)
  (Debug.parse "Checking if structure definition: %a has type %a \nwith local context %a"
    (Lib.pp_print_list LA.pp_print_struct_item ",") lhss
    LA.pp_print_lustre_type exp_ty
    pp_print_tc_context ctx;
  
  (* check if the members of LHS are constants or enums before assignment *)
  let lhs_vars = SI.flatten (List.map LH.vars_of_struct_item lhss) in
  if (SI.for_all (fun i -> not (member_val ctx i)) lhs_vars)
  then (match exp_ty with
    | GroupType (_, exp_ty_lst') ->
      let exp_ty_lst = LH.flatten_group_types exp_ty_lst' in
      if List.length lhss = 1
        (* Case 1. the LHS is just one identifier 
          * so we have to check if the exp_type is the same as LHS *)
        then check_type_struct_item ctx (List.hd lhss) exp_ty 
        else (* Case 2. LHS is a compound statment *)
          if List.length lhss = List.length exp_ty_lst
          then 
            let* cons = R.seq (List.map2 (check_type_struct_item ctx) lhss exp_ty_lst) in 
            R.ok (List.flatten cons)
          else type_error pos (MismatchOfEquationType (Some lhss, exp_ty))
    (* We are dealing with simple types, so lhs has to be a singleton list *)
    | _ -> if (List.length lhss != 1)
          then type_error pos (MismatchOfEquationType (None, exp_ty))
          else let lhs = List.hd lhss in
              check_type_struct_item ctx lhs exp_ty)
  else type_error pos (DisallowedReassignment (SI.filter (fun e -> (member_val ctx e)) lhs_vars)))
(** The structure of the left hand side of the equation 
 * should match the type of the right hand side expression *)

(* Difference between this and tc_ctx_contract_node_eqn? *)
and tc_ctx_contract_eqn: tc_context -> LA.contract_node_equation -> (tc_context * (LA.expr * string) list, [> error]) result
  = fun ctx -> function
  | GhostConst c -> tc_ctx_const_decl ctx c
  | GhostVars vs -> 
    let* ctx = tc_ctx_contract_vars ctx vs in 
    R.ok (ctx, [])
  | Assume _ -> R.ok (ctx, [])
  | Guarantee _ -> R.ok (ctx, [])
  | AssumptionVars _ -> R.ok (ctx, [])
  | Mode (pos, name, _, _) -> R.ok (add_ty ctx name (Bool pos), []) 
  | ContractCall (_, cc, _, _) ->
    match (lookup_contract_exports ctx cc) with
    | None -> failwith ("Cannot find exports for contract "
      ^ (HString.string_of_hstring cc))
    | Some m -> R.ok (List.fold_left
      (fun c (i, ty) -> add_ty c (HString.concat (HString.mk_hstring "::") [cc;i]) ty)
      ctx
      (IMap.bindings m), []) 

and check_type_contract_decl: tc_context -> LA.contract_node_decl -> ((LA.expr * string) list, [> error]) result
  = fun ctx (cname, _, args, rets, contract) ->
  let arg_ids = LA.SI.of_list (List.map (fun arg -> LH.extract_ip_ty arg |> fst) args) in
  let ret_ids = LA.SI.of_list (List.map (fun ret -> LH.extract_op_ty ret |> fst) rets) in
  Debug.parse "TC Contract Decl: %a {" LA.pp_print_ident cname;
  (* build the appropriate local context *)
  let arg_ctx = List.fold_left union ctx (List.map extract_arg_ctx args) in
  let ret_ctx = List.fold_left union arg_ctx (List.map extract_ret_ctx rets) in
  let local_const_ctx = List.fold_left union ret_ctx (List.map extract_consts args) in
  (* forbid subranges in the arguments or return types *)
  let* cons1 = R.seq (List.map (fun (pos, i, ty, _, _) -> 
    let ty = expand_nested_type_syn arg_ctx ty in
    if LH.type_contains_subrange ty then type_error pos (DisallowedSubrangeInContractReturn (true, i, ty))
    else Ok ([]))
    args) in 
  let* cons2 = R.seq (List.map (fun (pos, i, ty, _) -> 
    let ty = expand_nested_type_syn ret_ctx ty in
    if LH.type_contains_subrange ty then type_error pos (DisallowedSubrangeInContractReturn (false, i, ty))
    else Ok ([]))
    rets) in
  (* get the local const var declarations into the context *)
  let* ctxs, cons3 = R.seq (List.map (tc_ctx_contract_eqn local_const_ctx) contract) |> R.splitM in
  let local_ctx = List.fold_left union local_const_ctx ctxs in
  Debug.parse "Local Typing Context {%a}" pp_print_tc_context local_ctx;
  check_type_contract (arg_ids, ret_ids) local_ctx contract
    >> R.ok (Debug.parse "TC Contract Decl %a done }" LA.pp_print_ident cname; 
             List.flatten cons1 @ List.flatten cons2 @ List.flatten cons3)

and check_type_contract: (LA.SI.t * LA.SI.t) -> tc_context -> LA.contract -> ((LA.expr * string) list, [> error]) result
  = fun node_params ctx eqns ->
  (let* cons = R.seq (List.map (check_contract_node_eqn node_params ctx) eqns) in
  R.ok (List.flatten cons))

and check_contract_node_eqn: (LA.SI.t * LA.SI.t) -> tc_context -> LA.contract_node_equation -> ((LA.expr * string) list, [> error]) result
  = fun node_params ctx eqn ->
  Debug.parse "Checking node's contract equation: %a" LA.pp_print_contract_item eqn
  ; match eqn with
    | AssumptionVars (_, ids) -> (
      let (node_in_params, node_out_params) = node_params in
      let io_params = LA.SI.union node_in_params node_out_params in
      match List.find_opt (fun (_, id) -> LA.SI.mem id io_params |> not) ids with
      | Some (pos, id) ->
        type_error pos (AssumptionMustBeInputOrOutput id)
      | None -> R.ok []
    )
    | GhostConst (FreeConst (_, _, exp_ty) as c) -> check_type_const_decl ctx c exp_ty
    | GhostConst (TypedConst (_, _, _, exp_ty) as c) -> check_type_const_decl ctx c exp_ty
    | GhostConst (UntypedConst _) -> R.ok []
    | GhostVars v -> let node_eqn = contract_eqn_to_node_eqn v in do_node_eqn ctx node_eqn
    | Assume (pos, _, _, e) ->
      check_type_expr ctx e (Bool pos)
         
    | Guarantee (pos, _, _, e) -> check_type_expr ctx e (Bool pos)
    | Mode (pos, _, reqs, ensures) ->
      let* cons = R.seq (Lib.list_apply (List.map (check_type_expr ctx)
                                (List.map (fun (_,_, e) -> e) (reqs @ ensures)))
                (Bool pos)) in 
      R.ok (List.flatten cons)
      
    | ContractCall (pos, cname, args, rets) ->
      let arg_ids =
        List.fold_left
          (fun a s -> LA.SI.union a s)
          LA.SI.empty
          (List.map LH.vars_without_node_call_ids args)
      in
      let ret_ids = LA.SI.of_list rets in
      let common_ids = LA.SI.inter arg_ids ret_ids in
      if (LA.SI.equal common_ids LA.SI.empty)
      then 
        let* ret_tys, cons1 = R.seq (List.map (infer_type_expr ctx)
          (List.map (fun i -> LA.Ident (pos, i)) rets))
          |> R.splitM
        in
        let ret_ty = if List.length ret_tys = 1
          then List.hd ret_tys
          else LA.GroupType (pos, ret_tys)
        in
        let* arg_tys, cons2 = R.seq(List.map (infer_type_expr ctx) args) |> R.splitM in
        let arg_ty = if List.length arg_tys = 1
          then List.hd arg_tys
          else LA.GroupType (pos, arg_tys)
        in
        let exp_ty = LA.TArr (pos, arg_ty, ret_ty) in
        (match (lookup_contract_ty ctx cname) with
        | Some inf_ty -> 
            let* b, cons3 = eq_lustre_type ctx inf_ty exp_ty in 
            if b then R.ok (List.flatten cons1 @ List.flatten cons2 @ cons3)
            else (type_error pos (MismatchedNodeType (cname, exp_ty, inf_ty)))
        | None -> type_error pos (Impossible ("Undefined or not in scope contract name "
          ^ (HString.string_of_hstring cname))))
      else type_error pos (NodeInputOutputShareIdentifier common_ids)

and contract_eqn_to_node_eqn: LA.contract_ghost_vars -> LA.node_equation
  = fun (pos1, GhostVarDec(pos2, tis), expr) ->
    let lhs = LA.StructDef(pos2, 
    List.map (fun (pos, i, _) -> LA.SingleIdent(pos, i)) tis
    ) in
    Equation(pos1, lhs, expr)

and tc_ctx_const_decl: tc_context -> LA.const_decl -> (tc_context * (LA.expr * string) list, [> error]) result
  = fun ctx ->
  function
  | LA.FreeConst (pos, i, ty) ->
    check_type_well_formed ctx ty
    >> if member_ty ctx i
       then type_error pos (Redeclaration i)
       else R.ok (add_ty (add_const ctx i (LA.Ident (pos, i)) ty) i ty, [])
  | LA.UntypedConst (pos, i, e) ->
    if member_ty ctx i then
      type_error pos (Redeclaration i)
    else (
      let* ty, cons = infer_type_expr ctx e in
      let* ctx = check_and_add_constant_definition ctx i e ty in 
      R.ok (ctx, cons)
    )
  | LA.TypedConst (pos, i, e, exp_ty) ->
    check_type_well_formed ctx exp_ty >>
    if member_ty ctx i then
      type_error pos (Redeclaration i)
    else
      let* cons = check_type_expr (add_ty ctx i exp_ty) e exp_ty in
      let* ctx = check_and_add_constant_definition ctx i e exp_ty in 
      R.ok (ctx, cons)
(** Fail if a duplicate constant is detected  *)
  
and tc_ctx_contract_vars: tc_context -> LA.contract_ghost_vars -> (tc_context, [> error]) result 
  = fun ctx (_, GhostVarDec (_, tis), _) ->
    R.seq_chain
      (fun ctx (pos, i, ty) ->
        check_type_well_formed ctx ty
        >> if member_ty ctx i
          then type_error pos (Redeclaration i)
          else R.ok (add_ty ctx i ty)
      )
      ctx
      tis
(** Adds the type of contract variables in the typing context  *)


     
and tc_ctx_of_ty_decl: tc_context -> LA.type_decl -> (tc_context, [> error]) result
  = fun ctx ->
  function
  | LA.AliasType (_, i, ty) ->
    check_type_well_formed ctx ty >> (match ty with
      | LA.EnumType (pos, ename, econsts) ->
        if (List.for_all (fun e -> not (member_ty ctx e)) econsts)
          && (List.for_all (fun e -> not (member_val ctx e)) econsts)
        then
          let mk_ident = fun i -> LA.Ident (pos, i) in
          let enum_type_bindings = List.map
            ((Lib.flip singleton_ty) (LA.UserType (pos, ename)))
            econsts
          in
          let enum_const_bindings = Lib.list_apply
            ((List.map2 (Lib.flip singleton_const) (List.map mk_ident econsts) econsts))
            (LA.UserType (pos, ename))
          in
          (* Adding enums into the typing context consists of 4 parts *)
          (* 1. add the enum type and variants to the enum context *)
          let ctx' = add_enum_variants ctx ename econsts in
          (* 2. add the enum type as a valid type in context*)
          let ctx'' = add_ty_syn ctx' i ty in
          R.ok (List.fold_left union (add_ty_decl ctx'' ename)
          (* 3. Lift all enum constants (terms) with associated user type of enum name *)
            (enum_type_bindings
          (* 4. Lift all the enum constants (terms) into the value store as constants *)
            @ enum_const_bindings))
        else
          type_error pos (Redeclaration (HString.mk_hstring "Enum value or constant"))
      | _ -> R.ok (add_ty_syn ctx i ty))
  | LA.FreeType (pos, i) ->
    let ctx' = add_ty_syn ctx i (LA.AbstractType (pos, i)) in
    R.ok (add_ty_decl ctx' i)

and tc_ctx_of_node_decl: Lib.position -> tc_context -> LA.node_decl -> (tc_context, [> error]) result
  = fun pos ctx (nname, _, _ , ip, op, _ ,_ ,_)->
  Debug.parse
    "Extracting type of node declaration: %a"
    LA.pp_print_ident nname
  ;
  if (member_node ctx nname)
  then type_error pos (Redeclaration nname)
  else build_node_fun_ty pos ctx ip op >>= fun fun_ty ->
    R.ok (let ctx = add_ty_node ctx nname fun_ty in add_node_param_attr ctx nname ip)
(** computes the type signature of node or a function and its node summary*)

and tc_ctx_contract_node_eqn ?(ignore_modes = false) (ctx, cons) =
  function
  | LA.GhostConst c -> 
    let* ctx, cons2 = tc_ctx_const_decl ctx c
    in R.ok (ctx, cons @ cons2) 
  | LA.GhostVars vs -> 
    let* ctx = tc_ctx_contract_vars ctx vs in 
    R.ok (ctx, cons)
  | LA.Mode (pos, mname, _, _) ->
    if ignore_modes then R.ok (ctx, [])
    else if (member_ty ctx mname) then
      type_error pos (Redeclaration mname)
    else R.ok (add_ty ctx mname (Bool pos), cons)
  | LA.ContractCall (p, cc, _, _) ->
    (match (lookup_contract_exports ctx cc) with
    | None -> type_error p (Impossible ("Cannot find contract " ^ (HString.string_of_hstring cc)))
    | Some m -> R.ok (List.fold_left
      (fun c (i, ty) -> add_ty c (HString.concat (HString.mk_hstring "::") [cc;i]) ty)
      ctx
      (IMap.bindings m), cons)) 
  | _ -> R.ok (ctx, cons)
                         
and tc_ctx_of_contract: ?ignore_modes:bool -> tc_context -> LA.contract -> (tc_context * (LA.expr * string) list, [> error ]) result  
  = fun ?(ignore_modes = false) ctx con ->
  R.seq_chain (tc_ctx_contract_node_eqn ~ignore_modes) (ctx, []) con

and extract_exports: LA.ident -> tc_context -> LA.contract -> (tc_context * (LA.expr * string) list, [> error]) result
  = let exports_from_eqn: tc_context -> LA.contract_node_equation -> ((LA.ident * tc_type * (LA.expr * string) list) list, [> error]) result
      = fun ctx -> 
      function
      | LA.GhostConst (FreeConst (_, i, ty)) -> R.ok [(i, ty, [])]
      | LA.GhostConst (UntypedConst (_, i, e)) ->
        let* ty, cons = infer_type_expr ctx e in
        R.ok [(i, ty, cons)]
      | LA.GhostConst (TypedConst (_, i, _, ty)) ->
        R.ok [(i, ty, [])]
      | LA.GhostVars (_, (GhostVarDec (_, tis)), _) ->
        R.ok (List.map (fun (_, i, ty) -> (i, ty, [])) tis)
      | LA.Mode (pos, mname, _, _) ->
        if (member_ty ctx mname)
        then type_error pos (Redeclaration mname)
        else R.ok [(mname, (LA.Bool pos), [])] 
      | LA.ContractCall (p, cc, _, _) ->
        (match (lookup_contract_exports ctx cc) with
        | None -> type_error p (Impossible ("Cannot find contract " ^ (HString.string_of_hstring cc)))
        | Some m -> R.ok (List.map
          (fun (k, v) -> (HString.concat (HString.mk_hstring "::") [cc;k], v, []))
          (IMap.bindings m)))
      | _ -> R.ok [] in
    fun cname ctx contract ->
    (R.seq_chain
      (fun (exp_acc, lctx, cons) e ->
        let* id_tys = exports_from_eqn lctx e in
        R.ok (List.fold_left
          (fun (a, c, cons1) (i, ty, cons2) -> (IMap.add i ty a, add_ty c i ty, cons1 @ cons2))
          (exp_acc, lctx, cons) id_tys))
      (IMap.empty, ctx, []) contract) >>=
    fun (exports, _, cons) -> R.ok (add_contract_exports ctx cname exports, cons)  
                 
and tc_ctx_of_contract_node_decl: Lib.position -> tc_context
                                  -> LA.contract_node_decl
                                  -> (tc_context * (LA.expr * string) list, [> error]) result
  = fun pos ctx (cname, _, inputs, outputs, contract) ->
  Debug.parse
    "Extracting type of contract declaration: %a"
    LA.pp_print_ident cname
  ; if (member_contract ctx cname)
    then type_error pos (Redeclaration cname)
    else build_node_fun_ty pos ctx inputs outputs >>= fun fun_ty ->
        let* export_ctx, cons = extract_exports cname ctx contract in
        R.ok ((add_ty_contract (union ctx export_ctx) cname fun_ty), cons)

and tc_ctx_of_declaration: (tc_context * ((LA.expr * string) list IMap.t)) -> LA.declaration -> (tc_context * ((LA.expr * string) list IMap.t), [> error]) result
    = fun (ctx', m1) ->
    function
    | LA.ConstDecl ({start_pos;}, const_decl) -> 
      let* ctx, cons = tc_ctx_const_decl ctx' const_decl in 
      (match cons with 
        | (expr, _) :: _ -> type_error start_pos (GlobalArrayConstraint expr)
        | _ -> R.ok (ctx, m1))
    | LA.NodeDecl ({LA.start_pos=pos}, node_decl) ->
      let* ctx = tc_ctx_of_node_decl pos ctx' node_decl in 
      R.ok (ctx, m1)
    | LA.FuncDecl ({LA.start_pos=pos}, func_decl) ->
      let* ctx = tc_ctx_of_node_decl pos ctx' func_decl in 
      R.ok (ctx, m1)
    | LA.ContractNodeDecl ({LA.start_pos=pos}, ((id, _, _, _, _) as contract_decl)) ->
      let* ctx, cons = tc_ctx_of_contract_node_decl pos ctx' contract_decl in 
      let m2 = IMap.singleton id cons in 
      R.ok (ctx, IMap.merge union_keys m1 m2)
    | _ -> R.ok (ctx', m1)

and tc_context_of: tc_context -> LA.t -> (tc_context * (LA.expr * string) list IMap.t, [> error]) result
  = fun ctx decls ->
  R.seq_chain (tc_ctx_of_declaration) (ctx, IMap.empty) decls 
(** Obtain a global typing context, get constants and function decls*)
  
and build_type_and_const_context : tc_context -> LA.t -> (tc_context * (LA.expr * string) list IMap.t, [> error]) result 
  = fun ctx ->
  function
  | [] -> R.ok (ctx, IMap.empty)
  | LA.TypeDecl (_, ty_decl) :: rest ->
    let* ctx' = tc_ctx_of_ty_decl ctx ty_decl in
    build_type_and_const_context ctx' rest
  | ConstDecl ({ start_pos; }, const_decl) :: rest ->
    let* ctx', cons = tc_ctx_const_decl ctx const_decl in
    (match cons with 
        | (expr, _) :: _ -> type_error start_pos (GlobalArrayConstraint expr)
        | _ -> 
          let* ctx, m = build_type_and_const_context ctx' rest in 
          R.ok (ctx, m))
  | _ :: rest -> build_type_and_const_context ctx rest  
(** Process top level type declarations and make a type context with 
 * user types, enums populated *)

and check_const_integer_expr ctx kind e =
  match infer_type_expr ctx e with
  | Error (`LustreTypeCheckerError (pos, UnboundNodeName _)) ->
    type_error pos
      (ExpectedConstant (kind, "node call or any operator"))
  | Ok (ty, _) ->
    let* eq, _ = eq_lustre_type ctx ty (LA.Int (LH.pos_of_expr e)) in
    if eq then
      check_expr_is_constant ctx kind e
    else
      type_error (LH.pos_of_expr e) (ExpectedIntegerExpression ty)
  | Error err -> Error err

and check_array_size_expr ctx e =
  check_const_integer_expr ctx "array size expression" e

and check_range_bound ctx e =
  check_const_integer_expr ctx "subrange bound" e

and check_type_well_formed: tc_context -> tc_type -> (unit, [> error]) result
  = fun ctx ->
  function
  | LA.TArr (_, arg_ty, res_ty) ->
    check_type_well_formed ctx arg_ty
    >> check_type_well_formed ctx res_ty
  | LA.RecordType (_, _, idTys) ->
      (R.seq_ (List.map (fun (_, _, ty)
                -> check_type_well_formed ctx ty) idTys))
  | LA.ArrayType (_, (b_ty, s)) -> (
    check_array_size_expr ctx s
    >> check_type_well_formed ctx b_ty
  )
  | LA.TupleType (_, tys) ->
    R.seq_ (List.map (check_type_well_formed ctx) tys)
  | LA.GroupType (_, tys) ->
    R.seq_ (List.map (check_type_well_formed ctx) tys)
  | LA.UserType (pos, i) ->
    if (member_ty_syn ctx i || member_u_types ctx i)
    then R.ok () else type_error pos (UndeclaredType i)
  | LA.IntRange (pos, e1, e2) -> (
    match e1, e2 with
    | None, None -> type_error pos IntervalMustHaveBound
    | Some e, None | None, Some e -> 
      check_range_bound ctx e >> IC.eval_int_expr ctx e >> Ok ()
    | Some e1, Some e2 ->
      check_range_bound ctx e1 >> check_range_bound ctx e2 >>
      let* v1 = IC.eval_int_expr ctx e1 in
      let* v2 = IC.eval_int_expr ctx e2 in
      if v1 > v2 then type_error pos (EmptySubrange (v1, v2)) else Ok ()
    )
  | _ -> R.ok ()
(** Does it make sense to have this type i.e. is it inhabited? 
 * We do not want types such as int^true to creep in the typing context *)
       
and build_node_fun_ty: Lib.position -> tc_context
                       -> LA.const_clocked_typed_decl list
                       -> LA.clocked_typed_decl list -> (tc_type, [> error]) result
  = fun pos ctx args rets ->
  let fun_const_ctx = List.fold_left (fun ctx (i,ty) -> add_const ctx i (LA.Ident (pos,i)) ty)
                        ctx (List.filter LH.is_const_arg args |> List.map LH.extract_ip_ty) in
  let fun_ctx = List.fold_left (fun ctx (i, ty)-> add_ty ctx i ty) fun_const_ctx (List.map LH.extract_ip_ty args) in   
  let ops = List.map snd (List.map LH.extract_op_ty rets) in
  let ips = List.map snd (List.map LH.extract_ip_ty args) in
  let ret_ty = if List.length ops = 1 then List.hd ops else LA.GroupType (pos, ops) in
  let arg_ty = if List.length ips = 1 then List.hd ips else LA.GroupType (pos, ips) in
  check_type_well_formed fun_ctx ret_ty
  >> check_type_well_formed fun_ctx arg_ty
  >>  R.ok (LA.TArr (pos, arg_ty, ret_ty))
(** Function type for nodes will be [TupleType ips] -> [TupleTy outputs]  *)

and eq_lustre_type : ?is_call_arg: bool -> ?pos: Lib.position -> tc_context -> LA.lustre_type -> LA.lustre_type -> (bool * (LA.expr * string) list, [> error]) result
  = fun ?(is_call_arg = false) ?(pos = Lib.dummy_pos) ctx t1 t2 ->
  match (t1, t2) with
  (* Type Variable *)
  | TVar (_, i1), TVar (_, i2) -> R.ok (i1 = i2, [])

  (* Simple types *)
  | Bool _, Bool _ -> R.ok (true, [])
  | Int _, Int _ -> R.ok (true, [])
  | UInt8 _, UInt8 _ -> R.ok (true, [])
  | UInt16 _, UInt16 _ -> R.ok (true, [])              
  | UInt32 _, UInt32 _ -> R.ok (true, [])
  | UInt64 _,UInt64 _ -> R.ok (true, []) 
  | Int8 _, Int8 _ -> R.ok (true, []) 
  | Int16 _, Int16 _ -> R.ok (true, [])
  | Int32 _, Int32 _ -> R.ok (true, [])
  | Int64 _, Int64 _ -> R.ok (true, [])
  | Real _, Real _ -> R.ok (true, [])

  (* Integer Range *)
  | IntRange _, IntRange _ -> R.ok (true, [])
  | IntRange _, Int _ -> R.ok (true, [])
  | Int _, IntRange _ -> R.ok (true, [])

  (* Lustre V6 features *)
  | UserType (_, i1), UserType (_, i2) -> R.ok (i1 = i2, [])
  | AbstractType (_, i1), AbstractType (_, i2) -> R.ok (i1 = i2, [])
  | TupleType (_, tys1), TupleType (_, tys2) ->
    if List.length tys1 = List.length tys2
    then 
      let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in   
      (R.seqM f (true, []) (List.map2 (eq_lustre_type ~is_call_arg ~pos ctx) tys1 tys2))
    else R.ok (false, [])
  (* For Equality for group types, flatten out the structures  *)
  | GroupType (_, tys1), GroupType (_, tys2) ->
    let (ftys1, ftys2) = LH.flatten_group_types tys1, LH.flatten_group_types tys2 in 
    if List.length ftys1 = List.length ftys2
    then 
      let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in
      (R.seqM f (true, []) (List.map2 (eq_lustre_type ~is_call_arg ~pos ctx) ftys1 ftys2))
    else R.ok (false, [])
  | RecordType (_, n1, tys1), RecordType (_, n2, tys2) ->
    if List.length tys1 = List.length tys2
    then (
      let* isEqs = R.seq (List.map2 (eq_typed_ident ctx)
        (LH.sort_typed_ident tys1)
        (LH.sort_typed_ident tys2))
      in
      let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in
      let b, cons = List.fold_left f (true, []) isEqs in
      R.ok (b && n1 == n2, cons)
    )
    else R.ok (false, [])
  | ArrayType (_, arr1), ArrayType (_, arr2) -> eq_type_array ~is_call_arg ~pos ctx arr1 arr2 
  | EnumType (_, n1, is1), EnumType (_, n2, is2) ->
    if List.length is1 = List.length is2
    then
      R.ok (n1 = n2 &&
        (List.fold_left (&&) true (List.map2 (=) (LH.sort_idents is1) (LH.sort_idents is2))), [])
    else
      R.ok (false, [])
  (* node/function type *)
  | TArr (_, arg_ty1, ret_ty1), TArr (_, arg_ty2, ret_ty2) ->
    let f = (fun (b1, exprs1) (b2, exprs2) -> b1 && b2, exprs1 @ exprs2) in
    R.seqM f (true, []) [ eq_lustre_type ~is_call_arg ~pos ctx arg_ty1 arg_ty2
                        ; eq_lustre_type ~is_call_arg ~pos ctx ret_ty1 ret_ty2 ]

  (* special case for type synonyms *)
  | UserType (pos, u), ty
  | ty, UserType (pos, u) ->
    if member_ty_syn ctx u then
      let* ty_alias = (match (lookup_ty_syn ctx u) with
        | None -> type_error pos
          (Impossible ("Cannot find definition of Identifier "
            ^ (HString.string_of_hstring u)))
        | Some ty -> R.ok ty)
      in
      eq_lustre_type ~is_call_arg ~pos ctx ty ty_alias
    else R.ok (false, [])
  (* Another special case for GroupType equality *)
  | GroupType (_, tys), t
  | t, GroupType (_, tys) ->
    if List.length tys = 1
    then (eq_lustre_type ~is_call_arg ~pos ctx (List.hd tys) t)
    else R.ok (false, [])
  | _, _ -> R.ok (false, [])
(** Compute Equality for lustre types  *)

and is_expr_int_type: tc_context -> LA.expr -> bool = fun ctx e ->
  R.safe_unwrap false
    (let* ty, _ = infer_type_expr ctx e in 
     let* res, _ = eq_lustre_type ctx ty (LA.Int (LH.pos_of_expr e)) in 
     R.ok res)
(** Checks if the expr is of type Int. This will be useful 
 *  in evaluating array sizes that we need to have as constant integers
 *  while declaring the array type *)
  
and eq_typed_ident: tc_context -> LA.typed_ident -> LA.typed_ident -> (bool * (LA.expr * string) list, [> error]) result =
  fun ctx (_, _, ty1) (_, _, ty2) -> eq_lustre_type ctx ty1 ty2
(** Compute type equality for [LA.typed_ident] *)

and eq_type_array: ?is_call_arg: bool -> ?pos: Lib.position -> tc_context -> (LA.lustre_type * LA.expr) -> (LA.lustre_type * LA.expr) -> (bool * (LA.expr * string) list, [> error]) result
  = fun ?(is_call_arg = false) ?(pos = Lib.dummy_pos) ctx (ty1, e1) (ty2, e2)   ->
  (* eq_lustre_type ctx ty1 ty2 *)
  let* b, constraints = eq_lustre_type ctx ty1 ty2 in
  if b
  then 
    (* Are the array sizes equal numerals? *)
    ( match IC.eval_int_expr ctx e1, IC.eval_int_expr ctx e2 with
      | Ok l1,  Ok l2  -> R.ok (l1 = l2, constraints)
      | Error _ , _ | _, Error _ ->
        (* Are the array sizes syntactically identical? *)
        match LH.syn_expr_equal None e1 e2 with
        | Ok b -> 
          if b then R.ok (true, constraints) 
          else 
            let pos = if pos = Lib.dummy_pos then (LustreAstHelpers.pos_of_expr e2) else pos in
            let desc = mk_array_prop_desc is_call_arg pos in
            R.ok (
              true, (LA.CompOp(Lib.dummy_pos, Eq, e1, e2), desc) 
              :: constraints
            )
        | Error _ -> R.ok (false, constraints)) 
  else (R.ok (true, constraints))
(** Compute equality for [LA.ArrayType].
   If there are free constants in the size, the eval function will fail,
   but we want to pass such cases, as there might be some
   value assigment to the free constant that satisfies the type checker. 
   Hence, silently return true and defer later checks to the model checking phase. *)         

                                 
let rec type_check_group: tc_context -> LA.t ->  ((LA.expr * string) list IMap.t, [> error]) result
  = fun global_ctx
  -> function
  | [] -> R.ok (IMap.empty)
  (* skip over type declarations and const_decls*)
  | (LA.TypeDecl _ :: rest) 
  | LA.ConstDecl _ :: rest -> type_check_group global_ctx rest  
  | LA.NodeDecl (span, ((id, _, _, _, _, _, _, _) as node_decl)) :: rest ->
    let { LA.start_pos = pos } = span in
    let* cons = check_type_node_decl pos global_ctx node_decl in 
    let m1 = IMap.singleton id cons  in
    let* m2 = (type_check_group global_ctx rest) in
    R.ok (IMap.merge union_keys m1 m2)
  | LA.FuncDecl (span, ((id, _, _, _, _, _, _, _) as node_decl)):: rest ->
    let { LA.start_pos = pos } = span in
    let* cons = (check_type_node_decl pos global_ctx node_decl) in
    let m1 = IMap.singleton id cons in
    let* m2 = type_check_group global_ctx rest in 
    R.ok (IMap.merge union_keys m1 m2)
  | LA.ContractNodeDecl (_, ((id, _, _, _, _) as contract_decl)) :: rest ->
    let* cons = (check_type_contract_decl global_ctx contract_decl) in 
    let m1 = IMap.singleton id cons in 
    let* m2 = type_check_group global_ctx rest in 
    R.ok (IMap.merge union_keys m1 m2)
  | LA.NodeParamInst  _ :: rest ->
    type_check_group global_ctx rest
(** By this point, all the circularity should be resolved,
 * the top most declaration should be able to access 
 * the types of all the forward referenced indentifiers from the context*) 
 
(** Collects a node's context. *)
let get_node_ctx ctx (_, _, _, inputs, outputs, locals, _, _) =
  let constants_ctx = inputs
    |> List.map extract_consts
    |> (List.fold_left union ctx)
  in
  let input_ctx = inputs
    |> List.map extract_arg_ctx
    |> (List.fold_left union ctx)
  in
  let output_ctx = outputs
    |> List.map extract_ret_ctx
    |> (List.fold_left union ctx)
  in
  let ctx = union
    (union constants_ctx ctx)
    (union input_ctx output_ctx) in
  let rec helper ctx locals = match locals with
    | local :: locals -> 
      let* ctx, _ = local_var_binding ctx local in 
      helper ctx locals
    | [] -> R.ok ctx in
  helper ctx locals


let type_check_decl_grps: tc_context -> LA.t list -> ((LA.expr * string) list IMap.t, [> error]) result
  = fun ctx decls ->
    Debug.parse ("@.===============================================@."
      ^^ "Phase: Type checking declaration Groups@."
      ^^"===============================================@.");
    let* maps = R.seq (List.map (fun decl -> type_check_group ctx decl) decls) in 
    R.ok (List.fold_left (fun acc map -> IMap.merge union_keys acc map) IMap.empty maps)
(** Typecheck a list of independent groups using a global context*)

(**************************************************************************************
 * The main functions of the file that kicks off type checking or type inference flow  *
 ***************************************************************************************)

let type_check_infer_globals: tc_context -> LA.t -> (tc_context * (LA.expr * string) list IMap.t, [> error]) result
  = fun ctx prg ->
    Debug.parse ("@.===============================================@."
      ^^ "Building TC Global Context@."
      ^^"===============================================@.");
    (* Build base constant and type context *)
    let* global_ctx, cons = build_type_and_const_context ctx prg in
    R.ok (global_ctx, cons)

let type_check_infer_nodes_and_contracts: tc_context -> LA.t -> (tc_context * ((LA.expr * string) list IMap.t), [> error]) result
  = fun ctx prg -> 
  (* type check the nodes and contract decls using this base typing context  *)
  Debug.parse ("@.===============================================@."
    ^^ "Building node and contract Context@."
    ^^"===============================================@.");
  (* Build base constant and type context *)
  let* global_ctx, m1 = tc_context_of ctx prg in
  Debug.parse ("@.===============================================@."
    ^^ "Type checking declaration Groups@." 
    ^^ "with TC Context@.%a@."
    ^^"===============================================@.")
    pp_print_tc_context global_ctx;
  let* m2 = type_check_decl_grps global_ctx [prg] in
  Debug.parse ("@.===============================================@."
    ^^ "Type checking declaration Groups Done@."
    ^^"===============================================@.");
  R.ok (global_ctx, IMap.merge union_keys m1 m2)

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
