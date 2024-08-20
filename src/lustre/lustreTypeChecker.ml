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
  | AssumptionOnCurrentOutput of HString.t
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
  | IlltypedUpdateWithLabel of tc_type
  | IlltypedUpdateWithIndex of tc_type
  | ExpectedLabel of LA.expr
  | ExpectedIntegerLiteral of LA.expr
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
  | MismatchOfEquationType of LA.struct_item list option * tc_type
  | DisallowedReassignment of ty_set
  | AssumptionMustBeInputOrOutput of HString.t
  | Redeclaration of HString.t
  | ExpectedConstant of string * string
  | UndeclaredType of HString.t
  | EmptySubrange of int * int
  | SubrangeArgumentMustBeConstantInteger of LA.expr
  | IntervalMustHaveBound
  | ExpectedRecordType of tc_type
  | GlobalConstRefType of HString.t
  | QuantifiedAbstractType of HString.t
  | InvalidPolymorphicCall of HString.t

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
  | AssumptionOnCurrentOutput id -> "Refinement type references an illegal variable '"  ^ HString.string_of_hstring id ^ "' (either an assumption on the current value of an output, or an out-of-scope type argument)"
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
  | IlltypedUpdateWithLabel ty -> "Expected a record type but found " ^ string_of_tc_type ty
  | IlltypedUpdateWithIndex ty -> "Expected a tuple type or an array type but found " ^ string_of_tc_type ty
  | ExpectedLabel e -> "Only labels can be used for record expressions but found " ^ LA.string_of_expr e
  | ExpectedIntegerLiteral e -> "Expected an integer literal but found " ^ LA.string_of_expr e
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
  | MismatchOfEquationType (items, ty) -> "Term structure on left hand side of the equation "
    ^ (match items with
      | Some items -> Lib.string_of_t (Lib.pp_print_list LA.pp_print_struct_item ", ") items
      | None -> "")
    ^ " does not match expected type " ^ string_of_tc_type ty ^ " on right hand side of the node equation"
  | DisallowedReassignment vars -> "Cannot reassign value to a constant or enum but found reassignment to identifier(s): "
    ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") (LA.SI.elements vars)
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
  | GlobalConstRefType id -> "Global constant '" ^ HString.string_of_hstring id ^ "' has refinement type (not yet supported)"
  | QuantifiedAbstractType id -> "Variable '" ^ HString.string_of_hstring id ^ "' with type that contains an abstract type (or type variable) cannot be quantified"
  | InvalidPolymorphicCall id -> "Call to node, contract, or user type '" ^ HString.string_of_hstring id ^ "' passes an incorrect number of type parameters"

type warning_kind = 
  | UnusedBoundVariableWarning of HString.t

let warning_message warning = match warning with
  | UnusedBoundVariableWarning id -> "Unused refinement type bound variable " ^ HString.string_of_hstring id

type warning = [
  | `LustreTypeCheckerWarning of Lib.position * warning_kind
]

let mk_warning pos kind = `LustreTypeCheckerWarning (pos, kind)

let (>>=) = R.(>>=)
let (let*) = R.(>>=)
let (>>) = R.(>>)

let type_error pos kind = Error (`LustreTypeCheckerError (pos, kind))
(** [type_error] returns an [Error] of [tc_result] *)


(********************************
 * Functions to update context  *
 ********************************)
let add_ty_params_node_ctx ctx nname params =
  let ctx = add_ty_vars_node ctx nname params in
  List.fold_left
    (fun acc p ->
      add_ty_syn acc p (LA.AbstractType (Lib.dummy_pos, p))
    )
    ctx params

let add_io_node_ctx ctx nname params inputs outputs =
  let ctx = add_ty_params_node_ctx ctx nname params in
  let ctx = inputs
    |> List.map extract_consts
    |> (List.fold_left union ctx)
  in
  let ctx = inputs
    |> List.map extract_arg_ctx
    |> (List.fold_left union ctx)
  in
  let ctx = outputs
    |> List.map extract_ret_ctx
    |> (List.fold_left union ctx)
  in
  ctx

let add_local_node_ctx ctx locals =
  locals 
    |> List.map extract_loc_ctx
    |> (List.fold_left union ctx)

let add_full_node_ctx ctx nname params inputs outputs locals =
  let ctx = add_io_node_ctx ctx nname params inputs outputs in
  add_local_node_ctx ctx locals

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
  | EnumType _ -> LSC.no_mismatched_clock false e >> Ok ()
  | Bool _ -> LSC.no_mismatched_clock true e >> Ok ()
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
  | RecordExpr (_, _, _, flds) ->
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
  | Call (_, _, i, _) -> (
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

let check_and_add_constant_definition ctx i e ty sc =
  match R.seq_ (infer_const_attr ctx e) with
  | Ok _ -> R.ok (add_ty (add_const ctx i e ty sc) i ty)
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
  | UserType (_, ty_args, id) -> 
    (match (lookup_ty_syn ctx id ty_args) with 
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

let instantiate_type_variables: tc_context -> Lib.position -> HString.t -> tc_type -> tc_type list -> (tc_type, [> error ]) result
= fun ctx pos nname ty ty_args -> 
  (* In "ty", substitute each type variable for corresponding type from "tys" *)
  match lookup_node_ty_vars ctx nname, 
        lookup_contract_ty_vars ctx nname, 
        lookup_ty_ty_vars ctx nname with 
  | None, None, None ->
    let* substitution = 
      try 
        R.ok (List.combine [] ty_args) 
      with Invalid_argument _ -> type_error pos (InvalidPolymorphicCall nname)
    in 
    R.ok (LustreAstHelpers.apply_type_subst_in_type substitution ty)
  | Some ty_vars, _, _ 
  | _, Some ty_vars, _
  | _, _, Some ty_vars ->
    let* substitution = 
      try 
        R.ok (List.combine ty_vars ty_args) 
      with Invalid_argument _ -> type_error pos (InvalidPolymorphicCall nname)
    in 
    R.ok (LustreAstHelpers.apply_type_subst_in_type substitution ty)

let rec instantiate_type_variables_expr: tc_context -> HString.t -> tc_type list -> LA.expr -> (LA.expr, [> error ]) result
= fun ctx nname ty_args expr -> 
  let call = instantiate_type_variables_expr ctx nname ty_args in
  match expr with
  | Call (pos, old_ty_args, id, es) ->
    let* ty_args = R.seq (List.map (fun ty_arg -> 
      instantiate_type_variables ctx pos nname ty_arg ty_args
    ) old_ty_args) in
    let* es = R.seq (List.map call es) in
    Ok (LA.Call (pos, ty_args, id, es))
  | Quantifier (pos, q, tis, e) -> 
    let* tis = R.seq (List.map (fun (p, id, ty) -> 
      let* ty = instantiate_type_variables ctx pos nname ty ty_args in 
      R.ok (p, id, ty)
    ) tis) in 
    let* e = call e in 
    R.ok (LA.Quantifier (pos, q, tis, e))
  | Ident _ 
  | ModeRef _ -> R.ok expr
  | RecordProject (pos, e, idx) -> 
    let* e = call e in 
    R.ok (LA.RecordProject (pos, e, idx))
  | TupleProject (pos, e, idx) -> 
    let* e = call e in
    R.ok (LA.TupleProject (pos, e, idx))
  | Const (_, _) as e -> R.ok e
  | UnaryOp (pos, op, e) -> 
    let* e = call e in
    R.ok (LA.UnaryOp (pos, op, e))
  | BinaryOp (pos, op, e1, e2) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in 
    R.ok (LA.BinaryOp (pos, op, e1, e2))
  | TernaryOp (pos, op, e1, e2, e3) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in 
    let* e3 = call e3 in
    R.ok (LA.TernaryOp (pos, op, e1, e2, e3))
  | ConvOp (pos, op, e) -> 
    let* e = call e in
    R.ok (LA.ConvOp (pos, op, e))
  | CompOp (pos, op, e1, e2) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in
    R.ok (LA.CompOp (pos, op, e1, e2))
  | RecordExpr (pos, ident, ty_args, expr_list) ->
    let* ty_args = R.seq (List.map (fun ty_arg ->
      instantiate_type_variables ctx pos nname ty_arg ty_args
    ) ty_args) in
    let* expr_list = R.seq (List.map (fun (id, expr) -> 
      let* expr = call expr in 
      R.ok (id, expr)
      ) expr_list) in
    R.ok (LA.RecordExpr (pos, ident, ty_args, expr_list))
  | GroupExpr (pos, kind, expr_list) ->
    let* expr_list = R.seq (List.map call expr_list) in
    R.ok (LA.GroupExpr (pos, kind, expr_list))
  | StructUpdate (pos, e1, idx, e2) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in
    R.ok (LA.StructUpdate (pos, e1, idx, e2))
  | ArrayConstr (pos, e1, e2) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in
    R.ok (LA.ArrayConstr (pos, e1, e2))
  | ArrayIndex (pos, e1, e2) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in
    R.ok (LA.ArrayIndex (pos, e1, e2))
  | When (pos, e, clock) -> 
    let* e = call e in
    R.ok (LA.When (pos, e, clock))
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in 
    let* expr_list1 = R.seq (List.map call expr_list1) in 
    let* expr_list2 = R.seq (List.map call expr_list2) in 
    R.ok (LA.Condact (pos, e1, e2, id, expr_list1, expr_list2))
  | Activate (pos, ident, e1, e2, expr_list) ->
    let* e1 = call e1 in 
    let* e2 = call e2 in 
    let* expr_list = R.seq (List.map call expr_list) in 
    R.ok (LA.Activate (pos, ident, e1, e2, expr_list))
  | Merge (pos, ident, expr_list) ->
    let* expr_list = R.seq (List.map (fun (id, expr) -> 
      let* expr = call expr in 
      R.ok (id, expr)
    ) expr_list) in 
    R.ok (LA.Merge (pos, ident, expr_list))
  | RestartEvery (pos, ident, expr_list, e) ->
    let* e = call e in 
    let* expr_list = R.seq (List.map call expr_list) in 
    R.ok (LA.RestartEvery (pos, ident, expr_list, e))
  | Pre (pos, e) -> 
    let* e = call e in
    R.ok (LA.Pre (pos, e))
  | Arrow (pos, e1, e2) -> 
    let* e1 = call e1 in 
    let* e2 = call e2 in
    R.ok (LA.Arrow (pos, e1, e2))
  | AnyOp _ -> assert false (* Polymorphism is handled after any ops are desugared *)


let rec expand_type_syn_reftype_history ?(expand_subrange = false) ctx ty =
  let rec_call = expand_type_syn_reftype_history ~expand_subrange ctx in
  match ty with
  | LA.IntRange (pos, _, _) ->
    if expand_subrange then R.ok (LA.Int pos) else R.ok ty
  | LA.History (pos, i) -> (
    match lookup_ty ctx i with
    | None -> type_error pos (UnboundIdentifier i)
    | Some ty -> rec_call ty
  )
  | LA.RefinementType (_, (_, _, ty), _) -> rec_call ty
  | UserType (_, ty_args, i) as ty -> 
    (match lookup_ty_syn ctx i ty_args with
    | None -> R.ok ty
    | Some ty' -> R.ok ty')
  | TupleType (p, tys) ->
    let* tys = R.seq (List.map rec_call tys) in
    R.ok (LA.TupleType (p, tys))
  | GroupType (p, tys) ->
    let* tys = R.seq (List.map rec_call tys) in
    R.ok (LA.GroupType (p, tys))
  | RecordType (p, name, tys) ->
    let* tys = R.seq (List.map (fun (p, i, t) -> 
      let* t = rec_call t in
      R.ok (p, i, t)
    ) tys) in
    R.ok (LA.RecordType (p, name, tys))
  | ArrayType (p, (ty, e)) ->
    let* ty = rec_call ty in
    R.ok (LA.ArrayType (p, (ty, e)))
  | TArr (p, ty1, ty2) -> 
    let* ty1 = rec_call ty1 in
    let* ty2 = rec_call ty2 in
    R.ok (LA.TArr (p, ty1, ty2))
  | ty -> R.ok ty
(** Chases the type (and nested types) to its base form to resolve type synonyms. 
    Also simplifies refinement types and history types to their base types.
    In addition, chases int ranges to their base types (int)
    if [expand_subrange] is true.
*)

let expand_type_syn_reftype_history_subrange ctx =
  expand_type_syn_reftype_history ~expand_subrange:true ctx
(** Chases the type (and nested types) to its base form to resolve type synonyms. 
    Also simplifies refinement types, history types, __and subrange types__ to their base types. *)

let rec infer_type_expr: tc_context -> HString.t option -> LA.expr -> (tc_type * [> warning] list, [> error]) result
  = fun ctx nname -> function
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
                | Some ty -> R.ok ty in
    let* ty = lookup_mode_ty ctx ids in 
    R.ok (ty, [])
  | LA.RecordProject (pos, e, fld) ->
    let* rec_ty, warnings = infer_type_expr ctx nname e in
    let* rec_ty = expand_type_syn_reftype_history ctx rec_ty in
    (match rec_ty with
    | LA.RecordType (_, _, flds) ->
        let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
        (match (List.assoc_opt fld typed_fields) with
        | Some ty -> 
          let* ty = expand_type_syn_reftype_history ctx ty in 
          R.ok (ty, warnings)
        | None -> type_error pos (NotAFieldOfRecord fld))
    | _ -> type_error (LH.pos_of_expr e) (IlltypedRecordProjection rec_ty))

  | LA.TupleProject (pos, e1, i) ->
    let* tup_ty, warnings = infer_type_expr ctx nname e1 in
    let* tup_ty = expand_type_syn_reftype_history ctx tup_ty in
    (match tup_ty with
    | LA.TupleType (pos, tys) as ty ->
        if List.length tys <= i
        then type_error pos (TupleIndexOutOfBounds (i, ty))
        else 
          let* ty = expand_type_syn_reftype_history ctx (List.nth tys i) in 
          R.ok (ty, warnings)
    | ty -> type_error pos (IlltypedTupleProjection ty))

  (* Values *)
  | LA.Const (pos, c) -> 
    let ty = infer_type_const pos c in 
    R.ok (ty, [])

  (* Operator applications *)
  | LA.UnaryOp (pos, op, e) ->
    let* ty, warnings = infer_type_unary_op ctx nname pos e op in 
    R.ok (ty, warnings)
  | LA.BinaryOp (pos, bop, e1, e2) ->
    let* ty, warnings = infer_type_binary_op ctx nname pos bop e1 e2 in 
    R.ok (ty, warnings)
  | LA.TernaryOp (pos, top, con, e1, e2) ->
    (match top with
    | Ite -> 
        infer_type_expr ctx nname con
        >>= (function
            | Bool _, warnings1 ->
                let* e1_ty, warnings2 = infer_type_expr ctx nname e1 in
                let* e2_ty, warnings3 = infer_type_expr ctx nname e2 in
                eq_lustre_type ctx e1_ty e2_ty >>= fun eq_test ->
                    if eq_test then R.ok (e1_ty, warnings1 @ warnings2 @ warnings3)
                    else type_error pos (UnequalIteBranchTypes (e1_ty, e2_ty))
            | c_ty, _  ->  type_error pos  (ExpectedBooleanExpression c_ty))
    )
  | LA.ConvOp (pos, cop, e) ->
    let* ty, warnings = infer_type_conv_op ctx nname pos e cop in 
    R.ok (ty, warnings)
  | LA.CompOp (pos, cop, e1, e2) ->
    let* ty, warnings = infer_type_comp_op ctx nname pos e1 e2 cop in 
    R.ok (ty, warnings)

  (* Structured expressions *)
  | LA.RecordExpr (pos, name, ty_args, flds) -> (
    match lookup_ty_syn ctx name ty_args with
    | None -> type_error pos (UndeclaredType name)
    | Some ty ->
      match ty with
      | LA.RecordType (_, r_name, fld_tys) -> (
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
            let* exp_ty, warnings = infer_type_expr ctx nname exp in
            let* eq = eq_lustre_type ctx ty exp_ty in
            if eq then R.ok ((p, i, ty), warnings)
            else type_error (LH.pos_of_expr exp) (ExpectedType (ty, exp_ty))
          in
          let* fld_tys_warns = R.seq (List.map (infer_field ctx) matches) in
          let fld_tys, warnings = List.split fld_tys_warns in
          R.ok (LA.RecordType (pos, r_name, fld_tys), List.flatten warnings)
        )
      )
      | _ -> type_error pos (ExpectedRecordType ty)
  )
  | LA.GroupExpr (pos, struct_type, exprs) ->
    (match struct_type with
    | LA.ExprList ->
        let* tys_warns = R.seq (List.map (infer_type_expr ctx nname) exprs) in
        let tys, warnings = List.split tys_warns in
        R.ok (LA.GroupType (pos, tys), List.flatten warnings)
    | LA.TupleExpr ->
        let* tys_warns = R.seq (List.map (infer_type_expr ctx nname) exprs) in 
        let tys, warnings = List.split tys_warns in
        R.ok (LA.TupleType (pos, tys), List.flatten warnings)
    | LA.ArrayExpr ->
        R.seq (List.map (infer_type_expr ctx nname) exprs)
        >>= (fun tys_warns ->
        let tys, warnings = List.split tys_warns in
        let elty = List.hd tys in
        R.ifM (R.seqM (&&) true (List.map (eq_lustre_type ctx elty) tys))
          (let arr_ty = List.hd tys in
                let arr_size = LA.Const (pos, Num (List.length tys |> string_of_int |> HString.mk_hstring)) in
                R.ok (LA.ArrayType (pos, (arr_ty, arr_size)), List.flatten warnings))
          (type_error pos UnequalArrayExpressionType)))
    
  (* Update structured expressions *)
  | LA.ArrayConstr (pos, b_expr, sup_expr) -> (
    let* b_ty, warnings = infer_type_expr ctx nname b_expr in
    check_array_size_expr ctx nname sup_expr
    >> R.ok (LA.ArrayType (pos, (b_ty, sup_expr)), warnings)
  )
  | LA.StructUpdate (pos, ue, i_or_ls, e) ->
    if List.length i_or_ls != 1
    then type_error pos (Unsupported ("List of labels or indices for structure update is not supported"))
    else
      (match List.hd i_or_ls with
      | LA.Label (pos, l) ->  
          infer_type_expr ctx nname ue
          >>= (function 
              | RecordType (_, _, flds) as r_ty, warnings1 ->
                  (let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
                  (match (List.assoc_opt l typed_fields) with
                    | Some f_ty ->
                      let* e_ty, warnings2 = infer_type_expr ctx nname e in
                      R.ifM (eq_lustre_type ctx f_ty e_ty)
                        (R.ok (r_ty, warnings1 @ warnings2))
                        (type_error pos (TypeMismatchOfRecordLabel (l, f_ty, e_ty)))
                    | None -> type_error pos (NotAFieldOfRecord l)))
              | r_ty, _ -> type_error pos (IlltypedUpdateWithLabel r_ty))
      | LA.Index (pos, i) ->
        let* ue_ty, warnings1 = infer_type_expr ctx nname ue in
        (match ue_ty with
        | TupleType _ -> (
          let* idx =
            match LH.get_const_num_value i with
            | Some n -> Ok n
            | None -> type_error pos (ExpectedIntegerLiteral i)
          in
          let* e_ty, warnings2 = infer_type_expr ctx nname e in
          let* warnings3 = check_type_tuple_proj pos ctx nname ue idx e_ty in
          R.ok (ue_ty, warnings1 @ warnings2 @ warnings3)
        )
        | ArrayType (_, (b_ty, _)) -> (
          let* index_type, warnings1 = infer_type_expr ctx nname i in
          let* index_type = expand_type_syn_reftype_history ctx index_type in
          if is_expr_int_type ctx nname i then
            let* e_ty, warnings2 = infer_type_expr ctx nname e in
            R.ifM (eq_lustre_type ctx b_ty e_ty)
              (R.ok (ue_ty, warnings1 @ warnings2))
              (type_error pos (ExpectedType (e_ty, b_ty)))
          else
            type_error pos (ExpectedIntegerTypeForArrayIndex index_type)
        )
        | _ -> type_error pos (IlltypedUpdateWithIndex ue_ty)
        )
      )
  | LA.ArrayIndex (pos, e, i) ->
    let* index_type, warnings1 = infer_type_expr ctx nname i in
    let* index_type = expand_type_syn_reftype_history ctx index_type in
    if is_expr_int_type ctx nname i
    then 
      let* ty, warnings2 = infer_type_expr ctx nname e in 
      let* ty = expand_type_syn_reftype_history ctx ty in 
      match ty with 
      | LA.ArrayType (_, (b_ty, _)) -> R.ok (b_ty, warnings1 @ warnings2)
      | ty -> type_error pos (IlltypedArrayIndex ty)
    else type_error pos (ExpectedIntegerTypeForArrayIndex index_type)

  (* Quantified expressions *)
  | LA.Quantifier (_, _, qs, e) ->
    let* warnings1 =
      R.seq (List.map (fun (_, _, ty) ->
        check_type_well_formed ctx Local nname true ty) qs)
    in
    let extn_ctx = List.fold_left union ctx
                    (List.map (fun (_, i, ty) -> singleton_ty i ty) qs) in
    let* ty, warnings2 = infer_type_expr extn_ctx nname e in
    R.ok (ty, List.flatten warnings1 @ warnings2)

  | AnyOp _ -> assert false
  (* Already desugared in lustreDesugarAnyOps *)
  (*check_type_expr ctx nname e ty >>
    R.ok ty*)
  (* Clock operators *)
  | LA.When (_, e, _) -> infer_type_expr ctx nname e
  | LA.Condact (pos, c, _, node, args, defaults) ->
    check_type_expr ctx nname c (Bool pos) >> 
    let* r_ty, warnings1 = infer_type_expr ctx nname (Call (pos, [], node, args)) in
    let* d_tys_warns = R.seq (List.map (infer_type_expr ctx nname) defaults) in
    let d_tys, warnings2 = List.split d_tys_warns in
      R.ifM (eq_lustre_type ctx r_ty (GroupType (pos, d_tys)))
        (R.ok (r_ty, warnings1 @ List.flatten warnings2))
        (type_error pos IlltypedDefaults)
  | LA.Activate (pos, node, cond, _, args) ->
    check_type_expr ctx nname cond (Bool pos)
    >> infer_type_expr ctx nname (Call (pos, [], node, args))
  | LA.Merge (pos, i, mcases) as e ->
    let* ty, warnings1 = infer_type_expr ctx nname (LA.Ident (pos, i)) in
    let mcases_ids, mcases_exprs = List.split mcases in
    let* case_tys_warns = R.seq (List.map (infer_type_expr ctx nname) mcases_exprs) in
    let case_tys, warnings2 = List.split case_tys_warns in
    check_merge_exhaustive ctx pos ty mcases_ids >>
    check_merge_clock e ty >>
    let main_ty = List.hd case_tys in
    R.ifM (R.seqM (&&) true (List.map (eq_lustre_type ctx main_ty) case_tys))
    (R.ok (main_ty, warnings1 @ List.flatten warnings2))
    (type_error pos (IlltypedMerge main_ty))
  | LA.RestartEvery (pos, node, args, cond) ->
    check_type_expr ctx nname cond (LA.Bool pos)
    >> infer_type_expr ctx nname (LA.Call (pos, [], node, args))
                                
  (* Temporal operators *)
  | LA.Pre (_, e) -> infer_type_expr ctx nname e
  | LA.Arrow (pos, e1, e2) ->
    let* ty1, warnings1 = infer_type_expr ctx nname e1 in
    let* ty2, warnings2 = infer_type_expr ctx nname e2 in
    R.ifM (eq_lustre_type ctx ty1 ty2)
      (R.ok (ty1, warnings1 @ warnings2))
      (type_error pos (IlltypedArrow (ty1, ty2)))
     
  (* Node calls *)
  | LA.Call (pos, ty_args, i, arg_exprs) -> (
    Debug.parse "Inferring type for node call %a" LA.pp_print_ident i ;
    (* Values 'Input' and 'true' passed to check_type_well_formed are conservative 
       guesses in the case that ty_args contains refinement types. This rules out 
       instantiated polymorphic nodes having ill-formed refinement types (with e.g., assumptions on 
       current values of output variables).  *)
    let* warnings1 = R.seq (List.map (check_type_well_formed ctx Input nname true) ty_args) in
    let infer_type_node_args: tc_context -> LA.expr list -> (tc_type * [> warning] list, [> error]) result =
    fun ctx args ->
      let* arg_tys_warns = R.seq (List.map (infer_type_expr ctx nname) args) in
      let arg_tys, warnings = List.split arg_tys_warns in
      if List.length arg_tys = 1 then R.ok ((List.hd arg_tys), List.flatten warnings)
      else R.ok (LA.GroupType (pos, arg_tys), List.flatten warnings)
    in
    match (lookup_node_param_ids ctx i), (lookup_node_ty ctx i) with
    | Some call_params, Some node_ty -> (
      (* Express exp_arg_tys and exp_ret_tys in terms of the current context *)
      let node_ty = update_ty_with_ctx node_ty call_params ctx arg_exprs in
      let* node_ty = instantiate_type_variables ctx pos i node_ty ty_args in
      let exp_arg_tys, exp_ret_tys = match node_ty with 
        | LA.TArr (_, exp_arg_tys, exp_ret_tys) ->
          expand_type_syn ctx exp_arg_tys, expand_type_syn ctx exp_ret_tys
        | _ -> assert false 
      in
      let* given_arg_tys, warnings2 = infer_type_node_args ctx arg_exprs in
      let* are_equal = eq_lustre_type ctx exp_arg_tys given_arg_tys in
      if are_equal then
        (check_constant_args ctx i arg_exprs >> (R.ok (exp_ret_tys, List.flatten warnings1 @ warnings2)))
      else
        (type_error pos (IlltypedCall (exp_arg_tys, given_arg_tys)))
    )
    | _, Some ty -> type_error pos (ExpectedFunctionType ty)
    | _, None -> type_error pos (UnboundNodeName i)
  )
(** Infer the type of a [LA.expr] with the types of free variables given in [tc_context] *)

and check_type_expr: tc_context -> HString.t option -> LA.expr -> tc_type -> ([> warning] list, [> error]) result
  = fun ctx nname expr exp_ty ->
  match expr with
  (* Identifiers *)
  | Ident (pos, i) as ident ->
    let* ty, warnings = infer_type_expr ctx nname ident in
    R.ifM (eq_lustre_type ctx ty exp_ty)
      (R.ok warnings)
      (type_error pos (IlltypedIdentifier (i, exp_ty, ty)))
  | ModeRef (pos, ids) ->
    let id = (match ids with
              | [] -> failwith ("empty mode name")
              | rest -> HString.concat (HString.mk_hstring "::") rest) in
    check_type_expr ctx nname (LA.Ident (pos, id)) exp_ty
  | RecordProject (pos, expr, fld) -> 
    check_type_record_proj pos ctx nname expr fld exp_ty
  | TupleProject (pos, expr, idx) -> 
    check_type_tuple_proj pos ctx nname expr idx exp_ty

  (* Operators *)
  | UnaryOp (pos, op, e) ->
    let* inf_ty, warnings = infer_type_unary_op ctx nname pos e op in
    R.ifM 
      (eq_lustre_type ctx inf_ty exp_ty) 
      (R.ok warnings)
      (type_error pos (UnificationFailed (exp_ty, inf_ty)))
  | BinaryOp (pos, op, e1, e2) -> 
    let* inf_ty, warnings = infer_type_binary_op ctx nname pos op e1 e2 in
    R.ifM (eq_lustre_type ctx inf_ty exp_ty) 
      (R.ok warnings)
      (type_error pos (UnificationFailed (exp_ty, inf_ty)))
  | LA.TernaryOp (pos, _, con, e1, e2) ->
    infer_type_expr ctx nname con
    >>= (function 
        | Bool _, warnings1 ->
            let* ty1, warnings2 = infer_type_expr ctx nname e1 in
            let* ty2, warnings3 = infer_type_expr ctx nname e2 in
            R.ifM (eq_lustre_type ctx ty1 ty2)
              (R.ok (warnings1 @ warnings2 @ warnings3)) 
              (type_error pos (UnificationFailed (ty1, ty2)))
        | ty, _ -> type_error pos (ExpectedType ((Bool pos), ty)))
  | ConvOp (pos, cvop, e) ->
    let* inf_ty, warnings = infer_type_conv_op ctx nname pos e cvop in
    R.ifM (eq_lustre_type ctx inf_ty exp_ty)
      (R.ok warnings)
      (type_error pos (UnificationFailed (exp_ty, inf_ty)))
  | CompOp (pos, cop, e1, e2) ->
    let* inf_ty, warnings = infer_type_comp_op ctx nname pos e1 e2 cop in
    R.ifM (eq_lustre_type ctx inf_ty exp_ty)
      (R.ok warnings)
      (type_error pos (UnificationFailed (exp_ty, inf_ty)))

  (* Values/Constants *)
  | Const (pos, c) ->
    let cty = infer_type_const pos c in
    R.ifM (eq_lustre_type ctx cty exp_ty)
      (R.ok [])
      (type_error pos (UnificationFailed (exp_ty, cty)))

  (* Structured expressions *)
  | RecordExpr (pos, name, ty_args, flds) ->
    let (ids, es) = List.split flds in
    let mk_ty_ident p i t = (p, i, t) in
    let* inf_tys_warns = R.seq (List.map (infer_type_expr ctx nname) es) in
    let inf_tys, warnings = List.split inf_tys_warns in
    let inf_r_ty = LA.RecordType (pos, name, (List.map2 (mk_ty_ident pos) ids inf_tys)) in
    let* exp_ty = instantiate_type_variables ctx pos name exp_ty ty_args in
    R.ifM (eq_lustre_type ctx exp_ty inf_r_ty)
      (R.ok (List.flatten warnings))
      (type_error pos (UnificationFailed (exp_ty, inf_r_ty)))
  | GroupExpr (pos, group_ty, es) ->
    (match group_ty with
    (* These should be tuple type  *)
    | ExprList ->
        let* inf_tys_warns = R.seq (List.map (infer_type_expr ctx nname) es) in 
        let inf_tys, warnings = List.split inf_tys_warns in
        let inf_ty = LA.GroupType (pos, inf_tys) in
        (R.ifM (eq_lustre_type ctx exp_ty inf_ty)
          (R.ok (List.flatten warnings))
          (type_error pos (ExpectedType (exp_ty, inf_ty))))
      | TupleExpr ->
        let* inf_tys_warns = R.seq (List.map (infer_type_expr ctx nname) es) in
        let inf_tys, warnings = List.split inf_tys_warns in
        let inf_ty = LA.TupleType (pos, inf_tys) in
        (R.ifM (eq_lustre_type ctx exp_ty inf_ty)
          (R.ok (List.flatten warnings))
          (type_error pos (ExpectedType (exp_ty, inf_ty))))
    (* This should be array type *)
    | ArrayExpr ->
        let* inf_tys_warns = R.seq (List.map (infer_type_expr ctx nname) es) in 
        let inf_tys, warnings = List.split inf_tys_warns in
        if List.length inf_tys < 1
        then type_error pos EmptyArrayExpression
        else
          let elty = List.hd inf_tys in
          R.ifM (R.seqM (&&) true (List.map (eq_lustre_type ctx elty) inf_tys))
            (let arr_size = LA.Const (pos, Num (List.length inf_tys |> string_of_int |> HString.mk_hstring)) in
             let arr_ty = LA.ArrayType (pos, (elty, arr_size)) in
             (R.ifM (eq_lustre_type ctx exp_ty arr_ty)
                (R.ok (List.flatten warnings))
                (type_error pos (ExpectedType (exp_ty, arr_ty)))))
            (type_error pos UnequalArrayExpressionType))

  (* Update of structured expressions *)
  | StructUpdate (pos, ue, i_or_ls, e) ->
    if List.length i_or_ls != 1
    then type_error pos (Unsupported ("List of labels or indices for structure update is not supported"))
    else
      (match List.hd i_or_ls with
      | LA.Label (pos, l) ->
        let* r_ty, warnings1 = infer_type_expr ctx nname ue in (
          match r_ty with
          | RecordType (_, _, flds) ->
            (let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
              (match (List.assoc_opt l typed_fields) with
              | Some ty ->
                let* warnings2 = check_type_expr ctx nname e ty in
                R.ok (warnings1 @ warnings2)
              | None -> type_error pos (NotAFieldOfRecord l)))
          | _ -> type_error pos (IlltypedUpdateWithLabel r_ty))
      | LA.Index (_, i) ->
        let* ue_ty, warnings1 = infer_type_expr ctx nname ue in
        (match ue_ty with
        | TupleType _ -> (
          let* idx =
            match LH.get_const_num_value i with
            | Some n -> Ok n
            | None -> type_error pos (ExpectedIntegerLiteral i)
          in
          let* e_ty, warnings2 = infer_type_expr ctx nname e in
          let* warnings3 = check_type_tuple_proj pos ctx nname ue idx e_ty in
          R.ok (warnings1 @ warnings2 @ warnings3)
        )
        | ArrayType (_, (b_ty, _)) -> (
          let* index_type, warnings1 = infer_type_expr ctx nname i in
          let* index_type = expand_type_syn_reftype_history ctx index_type in
          if is_expr_int_type ctx nname i then
            let* warnings2 = check_type_expr ctx nname e b_ty in
            R.ok (warnings1 @ warnings2)
          else
            type_error pos (ExpectedIntegerTypeForArrayIndex index_type)
        )
        | _ -> type_error pos (IlltypedUpdateWithIndex ue_ty)
        ))

  (* Array constructor*)
  | ArrayConstr (pos, b_exp, sup_exp) ->
    let* b_ty, warnings1 = infer_type_expr ctx nname b_exp in
    let* _, warnings2 = infer_type_expr ctx nname sup_exp in
    let arr_ty = (LA.ArrayType (pos, (b_ty, sup_exp))) in
    R.ifM (eq_lustre_type ctx exp_ty arr_ty)
      (R.ok (warnings1 @ warnings2))
      (type_error pos (ExpectedType (exp_ty, arr_ty)))
  | ArrayIndex (pos, e, idx) ->
    let* index_type, warnings1 = infer_type_expr ctx nname idx in
    if is_expr_int_type ctx nname idx
    then 
      let* inf_arr_ty, warnings2 = infer_type_expr ctx nname e in
      (match inf_arr_ty with
        | ArrayType (_, (arr_b_ty, _)) ->
          R.ifM (eq_lustre_type ctx arr_b_ty exp_ty)
            (R.ok (warnings1 @ warnings2))
            (type_error pos (ExpectedType (exp_ty, arr_b_ty)))
        | _ -> type_error pos (ExpectedArrayType inf_arr_ty))
    else type_error pos (ExpectedIntegerTypeForArrayIndex index_type)

  (* Quantified expressions *)
  | Quantifier (_, _, qs, e) -> (
    let* warnings1 =
      R.seq (List.map (fun (_, _, ty) ->
        check_type_well_formed ctx Local nname true ty) qs)
    in
    (* Disallow quantification over abstract types *)
    let* _ = R.seq_ (List.map (fun (pos, id, ty) -> 
      if type_contains_abstract ctx ty 
      then 
        type_error pos (QuantifiedAbstractType id) 
      else 
        R.ok ()
    ) qs) in
    let extn_ctx = List.fold_left union ctx
                    (List.map (fun (_, i, ty) -> singleton_ty i ty) qs) in
    let* warnings2 = check_type_expr extn_ctx nname e exp_ty in
    R.ok (List.flatten warnings1 @ warnings2)
  )
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
  | When (_, e, _) -> check_type_expr ctx nname e exp_ty
  | Condact (pos, c, _, node, args, defaults) ->
    let* warnings1 = check_type_expr ctx nname c (Bool pos) in
    let* warnings2 = check_type_expr ctx nname (Call (pos, [], node, args)) exp_ty in
    let* dy_tys_warns =  R.seq (List.map (infer_type_expr ctx nname) defaults) in
    let d_tys, warnings3 = List.split dy_tys_warns in
    R.ifM (eq_lustre_type ctx exp_ty (GroupType (pos, d_tys)))
          (R.ok (warnings1 @ warnings2 @ List.flatten warnings3))
          (type_error pos IlltypedDefaults)
  | Activate (pos, node, cond, _, args) -> 
    let* warnings1 = check_type_expr ctx nname cond (Bool pos) in
    let* warnings2  = check_type_expr ctx nname (Call (pos, [], node, args)) exp_ty in 
    R.ok (warnings1 @ warnings2)
  | Merge (pos, i, mcases) as e ->
    let* ty, warnings1 = infer_type_expr ctx nname (LA.Ident (pos, i)) in
    let mcases_ids, mcases_exprs = List.split mcases in
    let* warnings2 = R.seq
      (List.map (fun e -> check_type_expr ctx nname e exp_ty) mcases_exprs)
    in
    check_merge_exhaustive ctx pos ty mcases_ids 
    >> check_merge_clock e ty >>
    R.ok (warnings1 @ List.flatten warnings2)
  | RestartEvery (pos, node, args, cond) ->
    let* warnings1 = check_type_expr ctx nname cond (LA.Bool pos) in 
    let* warnings2 = check_type_expr ctx nname (LA.Call (pos, [], node, args)) exp_ty in 
    R.ok (warnings1 @ warnings2)

  (* Temporal operators *)
  | Pre (_, e) -> check_type_expr ctx nname e exp_ty
  | Arrow (_, e1, e2) ->
    let* warnings1 = check_type_expr ctx nname e1 exp_ty in
    let* warnings2 = check_type_expr ctx nname e2 exp_ty in 
    R.ok (warnings1 @ warnings2)

  (* Node calls *)
  | Call (pos, ty_args, i, args) ->
    let* arg_tys_warns = R.seq (List.map (infer_type_expr ctx nname) args) in
    let arg_tys, warnings = List.split arg_tys_warns in
    let arg_ty = if List.length arg_tys = 1 then List.hd arg_tys
                else GroupType (pos, arg_tys) in
    (match (lookup_node_ty ctx i), (lookup_node_param_ids ctx i) with
    | None, _ 
    | _, None -> type_error pos (UnboundNodeName i)
    | Some ty, Some call_params -> 
      (* Express ty in terms of the current context *)
      let ty = update_ty_with_ctx ty call_params ctx args in
      let* ty = instantiate_type_variables ctx pos i ty ty_args in
      let* b = (eq_lustre_type ctx ty (LA.TArr (pos, arg_ty, exp_ty))) in
      if b then R.ok (List.flatten warnings)
      else (type_error pos (MismatchedNodeType (i, (TArr (pos, arg_ty, exp_ty)), ty))))
(** Type checks an expression and returns [ok] 
 * if the expected type is the given type [tc_type]  
 * returns an [Error of string] otherwise *)

and infer_type_unary_op: tc_context -> HString.t option -> Lib.position -> LA.expr -> LA.unary_operator -> (tc_type * [> warning] list, [> error]) result
  = fun ctx nname pos e op ->
  let* ty, warnings = infer_type_expr ctx nname e in
  match op with
  | LA.Not ->
    R.ifM (eq_lustre_type ctx ty (Bool pos))
      (R.ok (LA.Bool pos, warnings))
      (type_error pos (ExpectedType (LA.Bool pos, ty)))
  | LA.BVNot ->
    (match (is_type_machine_int ctx ty) with
      | Ok(b) -> if b then R.ok(ty, warnings) else (type_error pos (IlltypedBitNot ty))
      | Error id -> (type_error pos (UnboundIdentifier id)))
  | LA.Uminus ->
    (match (is_type_num ctx ty) with
      | Ok(b) -> if b then R.ok(ty, warnings) else (type_error pos (IlltypedUnaryMinus ty))
      | Error id -> (type_error pos (UnboundIdentifier id)))
(** Infers type of unary operator application *)

and are_args_num: tc_context -> Lib.position -> tc_type -> tc_type -> (bool, [> error]) result
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
  let are_equal_types: tc_context -> tc_type -> tc_type -> tc_type -> (bool, [> error]) result
    = fun ctx ty1 ty2 ty ->
    R.seqM (&&) true [ eq_lustre_type ctx ty1 ty
                    ; eq_lustre_type ctx ty2 ty ] in
  R.seqM (||) false (List.map (are_equal_types ctx ty1 ty2) num_tys) 
(** This is an ugly fix till we have polymorphic unification, may be qualified types? *)
  
and infer_type_binary_op: tc_context -> HString.t option -> Lib.position
                          -> LA.binary_operator -> LA.expr -> LA.expr
                          -> (tc_type * [> warning] list, [> error]) result
  = fun ctx nname pos op e1 e2 ->
  let* ty1, warnings1 = infer_type_expr ctx nname e1 in
  let* ty2, warnings2 = infer_type_expr ctx nname e2 in
  match op with
  | LA.And | LA.Or | LA.Xor | LA.Impl ->
    R.ifM (eq_lustre_type ctx ty1 (Bool pos))
      (R.ifM (eq_lustre_type ctx ty2 (Bool pos))
        (R.ok (LA.Bool pos, warnings1 @ warnings2))
        (type_error pos (ExpectedType ((LA.Bool pos), ty2))))
      (type_error pos (ExpectedType ((LA.Bool pos), ty1)))
  | LA.Mod ->
    (match is_type_int_or_machine_int ctx ty1, is_type_int_or_machine_int ctx ty2 with
      | Ok(true), Ok(true) -> 
        (R.ifM (eq_lustre_type ctx ty1 ty2)
          (R.ok (ty1, warnings1 @ warnings2))
          (type_error pos (UnificationFailed (ty1, ty2))))
      | Ok _, Ok _ -> (type_error pos (ExpectedIntegerTypes (ty1, ty2)))
      | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | LA.Plus | LA.Minus | LA.Times | LA.Div ->
    are_args_num ctx pos ty1 ty2 >>= fun is_num ->
    if is_num
    then R.ok (ty2, warnings1 @ warnings2)
    else type_error pos (ExpectedNumberTypes (ty1, ty2))
  | LA.IntDiv ->
    (match is_type_int_or_machine_int ctx ty1, is_type_int_or_machine_int ctx ty2 with
      | Ok(true), Ok(true) -> 
        (R.ifM (eq_lustre_type ctx ty1 ty2)
          (R.ok (ty1, warnings1 @ warnings2))
          (type_error pos (UnificationFailed (ty1, ty2))))
      | Ok _, Ok _ -> (type_error pos (ExpectedIntegerTypes (ty1, ty2)))
      | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | LA.BVAnd | LA.BVOr ->
    (R.ifM (eq_lustre_type ctx ty1 ty2)
      (match is_type_machine_int ctx ty1, is_type_machine_int ctx ty2 with
        | Ok(true), Ok(true) -> R.ok (ty2, warnings1 @ warnings2)
        | Ok _, Ok _ -> (type_error pos (ExpectedMachineIntegerTypes (ty1, ty2)))
        | Error id, _ -> (type_error pos (UnboundIdentifier id))
        | _, Error id -> (type_error pos (UnboundIdentifier id)))
      (type_error pos (UnificationFailed (ty1, ty2))))
  | LA.BVShiftL | LA.BVShiftR ->
    (match is_type_signed_machine_int ctx ty1, is_type_unsigned_machine_int ctx ty1 with
      | Ok(b1), Ok(b2) when b1 || b2 -> 
        (match is_type_unsigned_machine_int ctx ty2, is_machine_type_of_associated_width ctx (ty1, ty2) with
          | Ok (true), Ok (true) -> (R.ok (ty1, warnings1 @ warnings2))
          | Ok _, Ok _ -> type_error pos (ExpectedBitShiftConstantOfSameWidth ty1)
          | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
      | Ok _, Ok _ -> (type_error pos (ExpectedBitShiftMachineIntegerType ty1))
      | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
(** infers the type of binary operators  *)

and infer_type_conv_op: tc_context -> HString.t option -> Lib.position
                        ->  LA.expr -> LA.conversion_operator
                        -> (tc_type * [> warning] list, [> error]) result
  = fun ctx nname pos e op ->
  let* ty, warnings = infer_type_expr ctx nname e in
  match op with
  | ToInt ->
    (match (is_type_num ctx ty) with
      | Ok(b) -> if b then R.ok(LA.Int pos, warnings) else (type_error pos (InvalidConversion (ty, Int pos)))
      | Error id -> (type_error pos (UnboundIdentifier id)))
  | ToReal ->
    (match (is_type_real_or_int ctx ty) with
      | Ok(b) -> if b then R.ok(LA.Real pos, warnings) else (type_error pos (InvalidConversion (ty, Real pos)))
      | Error id -> (type_error pos (UnboundIdentifier id)))
  | ToInt8 ->
    (match (is_type_signed_machine_int ctx ty, is_type_int ctx ty) with
      | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.Int8 pos, warnings)  
      | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, Int8 pos)))
      | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | ToInt16 ->
    (match (is_type_signed_machine_int ctx ty, is_type_int ctx ty) with
    | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.Int16 pos, warnings)  
    | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, Int16 pos)))
    | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | ToInt32 ->
    (match (is_type_signed_machine_int ctx ty, is_type_int ctx ty) with
    | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.Int32 pos, warnings)  
    | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, Int32 pos)))
    | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | ToInt64 ->
    (match (is_type_signed_machine_int ctx ty, is_type_int ctx ty) with
    | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.Int64 pos, warnings)  
    | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, Int64 pos)))
    | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | ToUInt8 ->
    (match (is_type_unsigned_machine_int ctx ty, is_type_int ctx ty) with
    | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.UInt8 pos, warnings)  
    | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, UInt8 pos)))
    | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | ToUInt16 ->
    (match (is_type_unsigned_machine_int ctx ty, is_type_int ctx ty) with
    | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.UInt16 pos, warnings)  
    | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, UInt16 pos)))
    | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | ToUInt32 ->
    (match (is_type_unsigned_machine_int ctx ty, is_type_int ctx ty) with
    | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.UInt32 pos, warnings)  
    | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, UInt32 pos)))
    | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
  | ToUInt64 ->
    (match (is_type_unsigned_machine_int ctx ty, is_type_int ctx ty) with
    | Ok(b1), Ok(b2) when b1 || b2 -> R.ok(LA.UInt64 pos, warnings)  
    | Ok _, Ok _ -> (type_error pos (InvalidConversion (ty, UInt64 pos)))
    | Error id, _ | _, Error id -> (type_error pos (UnboundIdentifier id)))
(** Converts from given type to the intended type aka casting *)
    
and infer_type_comp_op: tc_context -> HString.t option -> Lib.position -> LA.expr -> LA.expr
                        -> LA.comparison_operator -> (tc_type * [> warning] list, [> error]) result
  = fun ctx nname pos e1 e2 op ->
  let* ty1, warnings1 = infer_type_expr ctx nname e1 in
  let* ty2, warnings2 = infer_type_expr ctx nname e2 in
  match op with
  | Neq  | Eq ->
    R.ifM (eq_lustre_type ctx ty1 ty2)
      (if LH.type_contains_array ty1 then
         type_error pos (Unsupported "Extensional array equality is not supported")
       else
         R.ok (LA.Bool pos, warnings1 @ warnings2)
      )
      (type_error pos (UnificationFailed (ty1, ty2)))
  | Lte  | Lt  | Gte | Gt ->
    are_args_num ctx pos ty1 ty2
    >>= fun is_num ->
    if is_num
    then R.ok (LA.Bool pos, warnings1 @ warnings2)
    else type_error pos (ExpectedIntegerTypes (ty1, ty2))
(** infer the type of comparison operator application *)
                  
and check_type_record_proj: Lib.position -> tc_context -> HString.t option -> LA.expr -> LA.index -> tc_type -> ([> warning] list, [> error]) result =
  fun pos ctx nname expr idx exp_ty -> 
  infer_type_expr ctx nname expr
  >>= function
  | RecordType (_, _, flds), warnings ->
    (match (List.find_opt (fun (_, i, _) -> i = idx) flds) with 
    | None -> type_error pos (NotAFieldOfRecord idx)
    | Some f -> R.ok f)
    >>= fun (_, _, fty) ->
    R.ifM (eq_lustre_type ctx fty exp_ty)
      (R.ok warnings)
      (type_error pos (UnificationFailed (exp_ty, fty)))
  | rec_ty, _ -> type_error (LH.pos_of_expr expr) (IlltypedRecordProjection rec_ty)

and check_type_tuple_proj : Lib.position -> tc_context -> HString.t option -> LA.expr -> int -> tc_type -> ([> warning] list, [> error]) result =
  fun pos ctx nname expr idx exp_ty ->
  infer_type_expr ctx nname expr
  >>= function
  | TupleType (_, tys) as ty, warnings ->
    if List.length tys <= idx
    then type_error pos (TupleIndexOutOfBounds (idx, ty))
    else R.ok (List.nth tys idx)
    >>= fun ity ->
    R.ifM (eq_lustre_type ctx ity exp_ty)
      (R.ok warnings)
      (type_error pos (UnificationFailed (exp_ty, ity)))
  | ty, _ -> type_error (LH.pos_of_expr expr) (IlltypedTupleProjection ty)

and check_type_const_decl: tc_context -> HString.t option -> LA.const_decl -> tc_type -> ([> warning] list, [> error]) result =
  fun ctx nname const_decl exp_ty ->
  match const_decl with
  | FreeConst (pos, i, _) ->
    (match (lookup_ty ctx i) with
    | None -> failwith "Free constant should have an associated type"
    | Some inf_ty -> R.ifM (eq_lustre_type ctx inf_ty exp_ty)
      (R.ok [])
      (type_error pos (IlltypedIdentifier (i, inf_ty, exp_ty))))
  | UntypedConst (pos, i, e) ->
    let* inf_ty, warnings = infer_type_expr ctx nname e in
    R.ifM (eq_lustre_type ctx inf_ty exp_ty)
      (R.ok warnings)
      (type_error pos (IlltypedIdentifier (i, exp_ty, inf_ty)))
  | TypedConst (pos, i, exp, _) ->
    let* inf_ty, warnings = infer_type_expr ctx nname exp in 
    R.ifM (eq_lustre_type ctx inf_ty exp_ty)
      (R.ok warnings)
      (type_error pos (IlltypedIdentifier (i, exp_ty, inf_ty)))

and check_type_node_decl: Lib.position -> tc_context -> LA.node_decl -> ([> warning] list, [> error]) result
  = fun pos ctx
        (node_name, is_extern, params, input_vars, output_vars, ldecls, items, contract)
        ->
  Debug.parse "TC declaration node: %a {" LA.pp_print_ident node_name;
  let arg_ids = LA.SI.of_list (List.map (fun a -> LH.extract_ip_ty a |> fst) input_vars) in
  let ret_ids = LA.SI.of_list (List.map (fun a -> LH.extract_op_ty a |> fst) output_vars) in
  let loc_ids = LA.SI.of_list (List.map (fun a -> LH.extract_loc_ty a |> fun (id, _, _) -> id) ldecls) in

  (* check if any of the arg ids or return ids already exist in the typing context.
      Fail if they do. 
      This is a strict no-shadowing policy put inplace to be in agreement with 
      the old type checking flow. 
      This behavior can be relaxed once the backend supports it.    
    *)
  R.seq_chain (fun _ i ->
    if (member_ty ctx i) then
      type_error pos (Redeclaration i)
    else R.ok ()
  ) () (LA.SI.elements arg_ids @ LA.SI.elements ret_ids @ LA.SI.elements loc_ids)
  >>
  (* Analogous check for shadowing at the type level *)
  R.seq_chain (fun _ i ->
    if (member_ty_syn ctx i) then
      type_error pos (Redeclaration i)
    else R.ok ()
  ) () (params)
  >>
    let ctx =
      List.fold_left (fun acc p ->
        add_ty_syn acc p (LA.AbstractType (pos, p))
      ) ctx params
    in
    (* (Debug.parse "Params: %a (skipping)" LA.pp_print_node_param_list params; *)
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
    (match contract with
      | None -> R.ok ([])
      | Some c ->
        let* con_ctx, warnings = tc_ctx_of_contract ctx_plus_ops_and_ips Ghost node_name c in
        Debug.parse "Checking node contract with context %a"
          pp_print_tc_context con_ctx;
        check_type_contract (arg_ids, ret_ids) con_ctx node_name c
        >> R.ok warnings)
      (* if the node is extern, we will not have any body to typecheck *)
      >> if is_extern
      then R.ok ( Debug.parse "External Node, no body to type check."
                ; Debug.parse "TC declaration node %a done }" LA.pp_print_ident node_name ;
                [])
      else (
        (* Add local variable bindings to the context *)
        let local_ctx = add_local_node_ctx ctx_plus_ops_and_ips ldecls in
        (* Check locals' types and their well-formedness *)
        let* warnings1 = R.seq (List.map (fun local_decl -> match local_decl with 
          | LA.NodeConstDecl (_, (TypedConst (_, i, e, ty))) -> 
            let* _ = check_expr_is_constant local_ctx "constant definition" e in
            let* warnings2 = check_type_expr (add_ty local_ctx i ty) (Some node_name) e ty in 
            let* warnings3 = check_type_well_formed local_ctx Local (Some node_name) true ty in 
            R.ok (warnings2 @ warnings3)
          | LA.NodeVarDecl (_, (_, _, ty, _)) -> 
            check_type_well_formed local_ctx Local (Some node_name) false ty 
          | LA.NodeConstDecl (_, FreeConst (_, _, ty)) ->
            check_type_well_formed local_ctx Local (Some node_name) true ty 
          | LA.NodeConstDecl (_, UntypedConst (_, _, _)) -> assert false  
        ) ldecls) in 
        Debug.parse "Local Typing Context with local state: {%a}" pp_print_tc_context local_ctx;
        (* Type check the node items now that we have all the local typing context *)
        let* warnings2 = R.seq (List.map (do_item local_ctx node_name) items) in
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
        check_lhs_eqns >> R.ok (List.flatten warnings1 @ List.flatten warnings2))

and do_node_eqn: tc_context -> HString.t -> LA.node_equation -> ([> warning] list, [> error]) result = fun ctx nname ->
  function
  | LA.Assert (pos, e) ->
    Debug.parse "Checking assertion: %a" LA.pp_print_expr e;
    check_type_expr ctx (Some nname) e (Bool pos)
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
    let* ty, warnings1 = infer_type_expr new_ctx (Some nname) e in
    Debug.parse "RHS has type %a for lhs %a" LA.pp_print_lustre_type ty LA.pp_print_eq_lhs lhs;
    let* warnings2 = check_type_struct_def new_ctx nname lhs ty in 
    R.ok (warnings1 @ warnings2)

and do_item: tc_context -> HString.t -> LA.node_item -> ([> warning] list, [> error]) result = fun ctx nname ->
  function
  | LA.Body eqn -> do_node_eqn ctx nname eqn >> R.ok []
  | LA.IfBlock (pos, e, l1, l2) ->
    let* guard_type, warnings1 = infer_type_expr ctx (Some nname) e in
    (match guard_type with
      | Bool _ -> 
        let* warnings2 = (R.seq ((List.map (do_item ctx nname) l1) @ (List.map (do_item ctx nname) l2))) in 
        R.ok (warnings1 @ List.flatten warnings2)
      | e_ty -> type_error pos  (ExpectedBooleanExpression e_ty)
    )
  | LA.FrameBlock (pos, vars, nes, nis) -> 
    let vars = List.map snd vars in
    let reassigned_consts = (SI.filter (fun e -> (member_val ctx e)) (SI.of_list vars)) in
    let* warnings = R.seq (
      (
        if ((SI.cardinal reassigned_consts) = 0) 
        then R.ok ([])
        else type_error pos (DisallowedReassignment reassigned_consts)
      ) :: (List.map (do_node_eqn ctx nname) nes) @ (List.map (do_item ctx nname) nis) 
    ) in 
    R.ok (List.flatten warnings)
  | LA.AnnotMain _ as ann ->
    Debug.parse "Node Item Skipped (Main Annotation): %a" LA.pp_print_node_item ann
    ; R.ok []
  | LA.AnnotProperty (_, _, e1, Provided e2) as ann ->
    Debug.parse "Checking Node Item (Annotation Property): %a (%a)"
      LA.pp_print_node_item ann LA.pp_print_expr e1
    ; 
    let* warnings1 = check_type_expr ctx (Some nname) e1 (Bool (LH.pos_of_expr e1)) in 
    let* warnings2 = check_type_expr ctx (Some nname) e2 (Bool (LH.pos_of_expr e2)) in 
    R.ok (warnings1 @ warnings2)
  | LA.AnnotProperty (_, _, e, _) as ann ->
    Debug.parse "Checking Node Item (Annotation Property): %a (%a)"
      LA.pp_print_node_item ann LA.pp_print_expr e
    ; check_type_expr ctx (Some nname) e (Bool (LH.pos_of_expr e))
  
and check_type_struct_item: tc_context -> HString.t -> LA.struct_item -> tc_type -> ([> warning] list, [> error]) result
  = fun ctx nname st exp_ty ->
  match st with
  | SingleIdent (pos, i) ->
    let* inf_ty = (match (lookup_ty ctx i) with
      | None -> type_error pos
        (Impossible ("Could not find Identifier " ^ (HString.string_of_hstring i)))
      | Some ty -> R.ok ty)
    in
    let* inferred_is_expected1 = eq_lustre_type ctx exp_ty inf_ty in
    let* inferred_is_expected2 = eq_lustre_type ctx exp_ty (GroupType (pos, [inf_ty])) in
    if inferred_is_expected1 || inferred_is_expected2 then
      if member_val ctx i then 
        type_error pos (Impossible ("Constant "
          ^ (HString.string_of_hstring i)
          ^ " cannot be re-defined"))
        else R.ok ([])
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
    check_type_expr ctx (Some nname) array_idx_expr exp_ty
  | TupleStructItem _ -> Lib.todo __LOC__
  | TupleSelection _ -> Lib.todo __LOC__
  | FieldSelection _ -> Lib.todo __LOC__
  | ArraySliceStructItem _ -> Lib.todo __LOC__

and check_type_struct_def: tc_context -> HString.t -> LA.eq_lhs -> tc_type -> ([> warning] list, [> error]) result
  = fun ctx nname (StructDef (pos, lhss)) exp_ty ->
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
        then check_type_struct_item ctx nname (List.hd lhss) exp_ty 
        else (* Case 2. LHS is a compound statment *)
          if List.length lhss = List.length exp_ty_lst
          then 
            let* warnings = R.seq (List.map2 (check_type_struct_item ctx nname) lhss exp_ty_lst) in 
            R.ok (List.flatten warnings)
          else type_error pos (MismatchOfEquationType (Some lhss, exp_ty))
    (* We are dealing with simple types, so lhs has to be a singleton list *)
    | _ -> if (List.length lhss != 1)
          then type_error pos (MismatchOfEquationType (None, exp_ty))
          else let lhs = List.hd lhss in
              check_type_struct_item ctx nname lhs exp_ty)
  else type_error pos (DisallowedReassignment (SI.filter (fun e -> (member_val ctx e)) lhs_vars)))
(** The structure of the left hand side of the equation 
 * should match the type of the right hand side expression *)

and tc_ctx_contract_eqn: tc_context -> HString.t -> LA.contract_node_equation -> (tc_context * [> warning] list, [> error]) result
  = fun ctx cname -> function
  | GhostConst c -> tc_ctx_const_decl ctx Ghost (Some cname) c
  | GhostVars vs -> 
    let* ctx = tc_ctx_contract_vars ctx cname vs in 
    R.ok (ctx, [])
  | Assume _ -> R.ok (ctx, [])
  | Guarantee _ -> R.ok (ctx, [])
  | AssumptionVars _ -> R.ok (ctx, [])
  | Mode (pos, name, _, _) -> R.ok (add_ty ctx name (Bool pos), []) 
  | ContractCall (_, cc, _, _, _) ->
    match (lookup_contract_exports ctx cc) with
    | None -> failwith ("Cannot find exports for contract "
      ^ (HString.string_of_hstring cc))
    | Some m -> R.ok (List.fold_left
      (fun c (i, ty) -> add_ty c (HString.concat (HString.mk_hstring "::") [cc;i]) ty)
      ctx
      (IMap.bindings m), []) 

and check_type_contract_decl: tc_context -> LA.contract_node_decl -> ([> warning] list, [> error]) result
  = fun ctx (cname, _, args, rets, (p, contract)) ->
  let arg_ids = LA.SI.of_list (List.map (fun arg -> LH.extract_ip_ty arg |> fst) args) in
  let ret_ids = LA.SI.of_list (List.map (fun ret -> LH.extract_op_ty ret |> fst) rets) in
  Debug.parse "TC Contract Decl: %a {" LA.pp_print_ident cname;
  (* build the appropriate local context *)
  let arg_ctx = List.fold_left union ctx (List.map extract_arg_ctx args) in
  let ret_ctx = List.fold_left union arg_ctx (List.map extract_ret_ctx rets) in
  let local_const_ctx = List.fold_left union ret_ctx (List.map extract_consts args) in
  (* get the local const var declarations into the context *)
  R.seq (List.map (tc_ctx_contract_eqn local_const_ctx cname) contract)
  >>= fun ctxs_warnings ->
  let ctxs, warnings1 = List.split ctxs_warnings in
  let local_ctx = List.fold_left union local_const_ctx ctxs in
  Debug.parse "Local Typing Context {%a}" pp_print_tc_context local_ctx;
  let* warnings2 = check_type_contract (arg_ids, ret_ids) local_ctx cname (p, contract) in
  R.ok (Debug.parse "TC Contract Decl %a done }" LA.pp_print_ident cname; List.flatten warnings1 @ warnings2)

and check_type_contract: (LA.SI.t * LA.SI.t) -> tc_context -> HString.t -> LA.contract -> ([> warning] list, [> error]) result
  = fun node_params ctx nname (_, eqns) ->
  let* warnings = R.seq (List.map (check_contract_node_eqn node_params ctx nname) eqns) in 
  R.ok (List.flatten warnings)

and check_contract_node_eqn: (LA.SI.t * LA.SI.t) -> tc_context -> HString.t -> LA.contract_node_equation -> ([> warning] list, [> error]) result
  = fun node_params ctx nname eqn ->
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
    | GhostConst (FreeConst (_, _, exp_ty) as c) -> 
      check_type_const_decl ctx (Some nname) c exp_ty
    | GhostConst (TypedConst (_, _, _, exp_ty) as c) -> check_type_const_decl ctx (Some nname) c exp_ty
    | GhostConst (UntypedConst _) -> R.ok []
    | GhostVars v -> let node_eqn = contract_eqn_to_node_eqn v in do_node_eqn ctx nname node_eqn
    | Assume (pos, _, _, e) ->
      check_type_expr ctx (Some nname) e (Bool pos)
         
    | Guarantee (pos, _, _, e) -> check_type_expr ctx (Some nname) e (Bool pos)
    | Mode (pos, _, reqs, ensures) ->
      let* warnings = R.seq (Lib.list_apply (List.map (check_type_expr ctx (Some nname))
                                (List.map (fun (_,_, e) -> e) (reqs @ ensures)))
                (Bool pos)) in 
      R.ok (List.flatten warnings)
      
    | ContractCall (pos, cname, ty_args, args, rets) ->
      let* ret_tys_warns = R.seq (List.map (infer_type_expr ctx (Some nname))
        (List.map (fun i -> LA.Ident (pos, i)) rets))
      in
      let ret_tys, warnings1 = List.split ret_tys_warns in
      let ret_ty = if List.length ret_tys = 1
        then List.hd ret_tys
        else LA.GroupType (pos, ret_tys)
      in
      let* arg_tys_warns = R.seq (List.map (infer_type_expr ctx (Some nname)) args) in
      let arg_tys, warnings2 = List.split arg_tys_warns in
      let arg_ty = if List.length arg_tys = 1
        then List.hd arg_tys
        else LA.GroupType (pos, arg_tys)
      in
      let exp_ty = LA.TArr (pos, arg_ty, ret_ty) in
      (match (lookup_contract_ty ctx cname) with
      | Some inf_ty -> 
          let* inf_ty = instantiate_type_variables ctx pos cname inf_ty ty_args in
          R.ifM (eq_lustre_type ctx inf_ty exp_ty)
            (R.ok (List.flatten warnings1 @ List.flatten warnings2))
            (type_error pos (MismatchedNodeType (cname, exp_ty, inf_ty)))
      | None -> type_error pos (Impossible ("Undefined or not in scope contract name "
        ^ (HString.string_of_hstring cname))))

and contract_eqn_to_node_eqn: LA.contract_ghost_vars -> LA.node_equation
  = fun (pos1, GhostVarDec(pos2, tis), expr) ->
    let lhs = LA.StructDef(pos2, 
    List.map (fun (pos, i, _) -> LA.SingleIdent(pos, i)) tis
    ) in
    Equation(pos1, lhs, expr)

and tc_ctx_const_decl: tc_context -> source -> HString.t option  -> LA.const_decl -> (tc_context * [> warning] list, [> error]) result
  = fun ctx src nname ->
  function
  | LA.FreeConst (pos, i, ty) ->
    let* warnings = check_type_well_formed ctx src nname true ty in
    if member_ty ctx i
    then type_error pos (Redeclaration i)
    else R.ok (add_ty (add_const ctx i (LA.Ident (pos, i)) ty src) i ty, warnings)
  | LA.UntypedConst (pos, i, e) ->
    if member_ty ctx i then
      type_error pos (Redeclaration i)
    else (
      let* ty, warnings = infer_type_expr ctx nname e in
      let* ctx = check_and_add_constant_definition ctx i e ty src in 
      R.ok (ctx, warnings)
    )
  | LA.TypedConst (pos, i, e, exp_ty) ->
    let* warnings1 = check_type_well_formed ctx src nname true exp_ty in
    if member_ty ctx i then
      type_error pos (Redeclaration i)
    else
      let* warnings2 = check_type_expr (add_ty ctx i exp_ty) nname e exp_ty in 
      let* ctx = check_and_add_constant_definition ctx i e exp_ty src in 
      R.ok (ctx, warnings1 @ warnings2)
(** Fail if a duplicate constant is detected  *)
  
and tc_ctx_contract_vars: tc_context -> HString.t -> LA.contract_ghost_vars -> (tc_context, [> error]) result 
  = fun ctx cname (_, GhostVarDec (_, tis), _) ->
    R.seq_chain
      (fun ctx (pos, i, ty) ->
        check_type_well_formed ctx Ghost (Some cname) false ty
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
  | LA.AliasType (pos, i, ps, ty) ->
    (* Disallow shadowing of type variables *)
    let* _ = R.seq_chain (fun _ i ->
      if (member_ty_syn ctx i) then
        type_error pos (Redeclaration i)
      else R.ok ()
    ) () ps in

    let ctx' = List.fold_left (fun acc p -> 
      add_ty_syn acc p (LA.AbstractType (pos, p))
    ) ctx ps in
    let ctx = add_ty_vars_ty ctx i ps in
    check_type_well_formed ctx' Global None false ty >> (match ty with
      | LA.EnumType (pos, ename, econsts) ->
        if (List.for_all (fun e -> not (member_ty ctx e)) econsts)
          && (List.for_all (fun e -> not (member_val ctx e)) econsts)
        then
          let mk_ident = fun i -> LA.Ident (pos, i) in
          let enum_type_bindings = List.map
            ((Lib.flip singleton_ty) (LA.UserType (pos, [], ename)))
            econsts
          in
          let enum_const_bindings = Lib.list_apply
            ((List.map2 (Lib.flip singleton_const) (List.map mk_ident econsts) econsts))
            (LA.UserType (pos, [], ename))
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
            @ (Lib.list_apply enum_const_bindings Global)))
        else
          type_error pos (Redeclaration (HString.mk_hstring "Enum value or constant"))
      | _ -> R.ok (add_ty_syn ctx i ty))
  | LA.FreeType (pos, i) ->
    let ctx' = add_ty_syn ctx i (LA.AbstractType (pos, i)) in
    R.ok (add_ty_decl ctx' i)

and tc_ctx_of_node_decl: Lib.position -> tc_context -> LA.node_decl -> (tc_context * [> warning] list, [> error]) result
  = fun pos ctx (nname, _, ps, ip, op, _, _, _)->
  Debug.parse
    "Extracting type of node declaration: %a"
    LA.pp_print_ident nname
  ;
  if (member_node ctx nname)
  then type_error pos (Redeclaration nname)
  else 
    let ctx = add_node_param_attr ctx nname ip in
    let ctx = add_ty_vars_node ctx nname ps in
    let* fun_ty, warnings = build_node_fun_ty pos ctx nname ps ip op in
    let ctx = add_ty_node ctx nname fun_ty in 
    R.ok (ctx, warnings)
(** computes the type signature of node or a function and its node summary*)

and tc_ctx_contract_node_eqn ?(ignore_modes = false) src cname (ctx, warnings) =
  function
  | LA.GhostConst c -> 
    tc_ctx_const_decl ctx src (Some cname) c
  | LA.GhostVars vs -> 
    let* ctx = tc_ctx_contract_vars ctx cname vs in 
    R.ok (ctx, warnings)
  | LA.Mode (pos, mname, _, _) ->
    if ignore_modes then R.ok (ctx, warnings)
    else if (member_ty ctx mname) then
      type_error pos (Redeclaration mname)
    else R.ok (add_ty ctx mname (Bool pos), warnings)
  | LA.ContractCall (p, cc, _, _, _) ->
    (match (lookup_contract_exports ctx cc) with
    | None -> type_error p (Impossible ("Cannot find contract " ^ (HString.string_of_hstring cc)))
    | Some m -> R.ok (List.fold_left
      (fun c (i, ty) -> add_ty c (HString.concat (HString.mk_hstring "::") [cc;i]) ty)
      ctx
      (IMap.bindings m), warnings)) 
  | _ -> R.ok (ctx, warnings)
                         
and tc_ctx_of_contract: ?ignore_modes:bool -> tc_context -> source -> HString.t -> LA.contract -> (tc_context * [> warning] list, [> error ]) result 
= fun ?(ignore_modes = false) ctx src cname (_, con) ->
  R.seq_chain (tc_ctx_contract_node_eqn ~ignore_modes src cname) (ctx, []) con

and extract_exports: LA.ident -> tc_context -> LA.contract -> (tc_context * [> warning] list, [> error]) result
  = let exports_from_eqn: tc_context -> HString.t -> LA.contract_node_equation -> ((LA.ident * tc_type) list * [> warning] list, [> error]) result
      = fun ctx nname -> 
      function
      | LA.GhostConst (FreeConst (_, i, ty)) -> R.ok ([(i, ty)], [])
      | LA.GhostConst (UntypedConst (_, i, e)) ->
        let* ty, warnings = infer_type_expr ctx (Some nname) e in
        R.ok ([(i, ty)], warnings)
      | LA.GhostConst (TypedConst (_, i, _, ty)) ->
        R.ok ([(i, ty)], [])
      | LA.GhostVars (_, (GhostVarDec (_, tis)), _) ->
        R.ok (List.map (fun (_, i, ty) -> (i, ty)) tis, [])
      | LA.Mode (pos, mname, _, _) ->
        if (member_ty ctx mname)
        then type_error pos (Redeclaration mname)
        else R.ok ([(mname, (LA.Bool pos))], []) 
      | LA.ContractCall (p, cc, _, _, _) ->
        (match (lookup_contract_exports ctx cc) with
        | None -> type_error p (Impossible ("Cannot find contract " ^ (HString.string_of_hstring cc)))
        | Some m -> R.ok (List.map
          (fun (k, v) -> (HString.concat (HString.mk_hstring "::") [cc;k], v))
          (IMap.bindings m), []))
      | _ -> R.ok ([], []) in
    fun cname ctx (_, contract) ->
    let* (exports, _), warnings = (R.seq_chain
      (fun ((exp_acc, lctx), warn_acc) e ->
        let* id_tys, warnings = exports_from_eqn lctx cname e in
        R.ok (List.fold_left
          (fun (a, c) (i, ty) -> (IMap.add i ty a, add_ty c i ty))
          (exp_acc, lctx) id_tys, warnings @ warn_acc))
      ((IMap.empty, ctx), []) contract) in
      R.ok (add_contract_exports ctx cname exports, warnings)  
                 
and tc_ctx_of_contract_node_decl: Lib.position -> tc_context
                                  -> LA.contract_node_decl
                                  -> (tc_context * [> warning] list, [> error]) result
  = fun pos ctx (cname, params, inputs, outputs, contract) ->
  Debug.parse
    "Extracting type of contract declaration: %a"
    LA.pp_print_ident cname
  ; if (member_contract ctx cname)
    then type_error pos (Redeclaration cname)
    else  
      let ctx = add_ty_vars_contract ctx cname params in
      let* fun_ty, warnings1 = build_node_fun_ty pos ctx cname params inputs outputs in
      let* export_ctx, warnings2 = extract_exports cname ctx contract in  
      let ctx = add_ty_contract (union ctx export_ctx) cname fun_ty in
      R.ok (ctx, warnings1 @ warnings2)

and tc_ctx_of_declaration: (tc_context * [> warning] list) -> LA.declaration -> (tc_context * [> warning] list, [> error]) result
    = fun (ctx', warnings) ->
    function
    | LA.ConstDecl (_, const_decl) -> tc_ctx_const_decl ctx' Global None const_decl
    | LA.NodeDecl ({LA.start_pos=pos}, node_decl) ->
      tc_ctx_of_node_decl pos ctx' node_decl 
    | LA.FuncDecl ({LA.start_pos=pos}, node_decl) ->
      tc_ctx_of_node_decl pos ctx' node_decl 
    | LA.ContractNodeDecl ({LA.start_pos=pos}, contract_decl) ->
      tc_ctx_of_contract_node_decl pos ctx' contract_decl
    | _ -> R.ok (ctx', warnings)

and tc_context_of: (tc_context * [> warning] list) -> LA.t -> (tc_context * [> warning] list, [> error]) result
  = fun ctx decls ->
  R.seq_chain (tc_ctx_of_declaration) ctx decls 
(** Obtain a global typing context, get constants and function decls*)
  
and build_type_and_const_context: tc_context -> LA.t -> (tc_context * [> warning] list, [> error]) result 
  = fun ctx ->
  function
  | [] -> R.ok (ctx, [])
  | LA.TypeDecl (_, ty_decl) :: rest ->
    let* ctx' = tc_ctx_of_ty_decl ctx ty_decl in
    build_type_and_const_context ctx' rest
  | LA.ConstDecl (_, (TypedConst (p, i, _, ty) as const_decl)) :: rest 
  | LA.ConstDecl (_, ((FreeConst (p, i, ty)) as const_decl)) :: rest -> 
    let ty = expand_type_syn ctx ty in
    if type_contains_ref ctx ty then type_error p (GlobalConstRefType i)
    else (
      let* ctx', warnings1 = tc_ctx_const_decl ctx Global None const_decl in
      let* ctx', warnings2 = build_type_and_const_context ctx' rest in 
      R.ok (ctx', warnings1 @ warnings2)   
    )
  | LA.ConstDecl (_, UntypedConst _) :: _ -> assert false
  | _ :: rest -> build_type_and_const_context ctx rest  
(** Process top level type declarations and make a type context with 
 * user types, enums populated *)

and check_const_integer_expr: tc_context -> HString.t option -> string -> LA.expr -> ([> warning] list, [> error ]) result
= fun ctx nname kind e ->
  match infer_type_expr ctx nname e with
  | Error (`LustreTypeCheckerError (pos, UnboundNodeName _)) ->
    type_error pos
      (ExpectedConstant (kind, "node call or any operator"))
  | Ok (ty, warnings) ->
    let* eq = eq_lustre_type ctx ty (LA.Int (LH.pos_of_expr e)) in
    if eq then
      check_expr_is_constant ctx kind e >>
      R.ok (warnings)
    else
      type_error (LH.pos_of_expr e) (ExpectedIntegerExpression ty)
  | Error err -> Error err

and check_array_size_expr ctx nname e =
  check_const_integer_expr ctx nname "array size expression" e

and check_range_bound ctx nname e =
  check_const_integer_expr ctx nname "subrange bound" e

(* Disallow assumptions on current values of output variables.
   'nname' is optional because the refinement type may not be in the 
   context of a node (e.g., a global type declaration). *)
and check_ref_type_assumptions ctx src nname bound_var e =
  let vars = LH.vars_without_node_call_ids_current e |> SI.elements in
  let inputs = (match nname with 
  | Some nname -> lookup_node_param_attr ctx nname
  | None -> None
  )
  in
  match src with 
  | Input -> (
    (* Filter out variables that are inputs, bound variables,
       or global constants. *)
    let vars = List.filter (fun var -> 
      match inputs with 
      | None -> false 
      | Some inputs -> 
        not (List.mem var (List.map fst inputs)) && 
        var != bound_var
    ) vars |> List.filter (fun i -> 
      match lookup_const ctx i with 
      | Some (_, _, Global) -> false 
      | _ -> true
    )  
    in
    match vars with 
    | [] -> R.ok ()
    | h :: _ -> (type_error (LH.pos_of_expr e) (AssumptionOnCurrentOutput h)) 
  )
  | Output | Local | Ghost | Global -> R.ok ()

and check_type_well_formed: tc_context -> source -> HString.t option -> bool -> tc_type -> ([> warning] list, [> error]) result
  = fun ctx src nname is_const ->
  function
  | LA.TArr (_, arg_ty, res_ty) ->
    let* warnings1 = check_type_well_formed ctx src nname is_const arg_ty in
    let* warnings2 = check_type_well_formed ctx src nname is_const res_ty in 
    R.ok (warnings1 @ warnings2)
  | LA.RecordType (_, _, idTys) ->
      let* warnings = (R.seq (List.map (fun (_, _, ty)
        -> check_type_well_formed ctx src nname is_const ty) idTys)) in 
      R.ok (List.flatten warnings)
  | LA.ArrayType (_, (b_ty, s)) -> (
    check_array_size_expr ctx nname s
    >> check_type_well_formed ctx src nname is_const b_ty
  )
  | LA.RefinementType (pos, (_, i, ty), e) ->
    let ctx = add_ty ctx i ty in
    (if is_const then 
      let ctx = add_const ctx i (LA.Ident (pos, i)) ty Local in
      check_expr_is_constant ctx "type of constant or refinement type argument" e 
    else R.ok ()) >>
    let* warnings1 = check_type_expr ctx nname e (Bool pos) in
    check_ref_type_assumptions ctx src nname i e >>
    let warnings2 = 
      if not (LH.expr_contains_id i e) 
      then [mk_warning pos (UnusedBoundVariableWarning i)] 
      else []
    in
    let* warnings3 = check_type_well_formed ctx src nname is_const ty in
    R.ok (warnings1 @ warnings2 @ warnings3)
  | LA.TupleType (_, tys) ->
    let* warnings = R.seq (List.map (check_type_well_formed ctx src nname is_const) tys) in
    R.ok (List.flatten warnings)
  | LA.GroupType (_, tys) ->
    let* warnings = R.seq (List.map (check_type_well_formed ctx src nname is_const) tys) in 
    R.ok (List.flatten warnings)
  | LA.UserType (pos, ty_args, i) as ty ->
    if (member_ty_syn ctx i || member_u_types ctx i)
    then 
      (* Check that we are passing the correct number of type arguments *)
      let* _ = instantiate_type_variables ctx pos i ty ty_args in
      let ty = expand_type_syn ctx ty in
      check_type_well_formed ctx src nname is_const ty
    else (
      match nname with 
      | None -> type_error pos (UndeclaredType i)
      | Some nname -> 
        match lookup_node_ty_vars ctx nname, lookup_contract_ty_vars ctx nname with 
        | Some ty_vars, _ 
        | _, Some ty_vars -> 
          if (List.mem i ty_vars) 
          then R.ok []
          else type_error pos (UndeclaredType i)
        | None, None -> 
          type_error pos (UndeclaredType i)
    )
  | LA.IntRange (pos, e1, e2) -> (
    match e1, e2 with
    | None, None -> type_error pos IntervalMustHaveBound
    | Some e, None | None, Some e -> 
      check_range_bound ctx nname e >> IC.eval_int_expr ctx e >> Ok ([])
    | Some e1, Some e2 ->
      check_range_bound ctx nname e1 >> check_range_bound ctx nname e2 >>
      let* v1 = IC.eval_int_expr ctx e1 in
      let* v2 = IC.eval_int_expr ctx e2 in
      if v1 > v2 then type_error pos (EmptySubrange (v1, v2)) else Ok ([])
    )
  | Bool _ | Int _ | UInt8 _ | UInt16 _ | UInt32 _
  | UInt64 _ | Int8 _ | Int16 _ | Int32 _ | Int64 _ | Real _
  | AbstractType _ | EnumType _ | History _ -> R.ok ([])
(** Does it make sense to have this type i.e. is it inhabited? 
 * We do not want types such as int^true to creep in the typing context *)
       
and build_node_fun_ty: Lib.position -> tc_context -> HString.t -> HString.t list
                       -> LA.const_clocked_typed_decl list
                       -> LA.clocked_typed_decl list -> (tc_type * [> warning] list, [> error]) result
  = fun pos ctx nname params args rets ->
  let fun_ty_vars_ctx =
    List.fold_left (fun acc p ->
      add_ty_syn acc p (LA.AbstractType (pos, p))
    ) ctx params
  in
  let fun_const_ctx = List.fold_left (fun ctx (i,ty) -> add_const ctx i (LA.Ident (pos,i)) ty Local)
                        fun_ty_vars_ctx (List.filter LH.is_const_arg args |> List.map LH.extract_ip_ty) in
  let fun_ctx = List.fold_left (fun ctx (i, ty)-> add_ty ctx i ty) fun_const_ctx (List.map LH.extract_ip_ty args) in   
  let fun_ctx = List.fold_left (fun ctx (i, ty)-> add_ty ctx i ty) fun_ctx (List.map LH.extract_op_ty rets) in 
  let ops = List.map snd (List.map LH.extract_op_ty rets) in
  let ips = List.map snd (List.map LH.extract_ip_ty args) in
  let ret_ty = if List.length ops = 1 then List.hd ops else LA.GroupType (pos, ops) in
  let arg_ty = if List.length ips = 1 then List.hd ips else LA.GroupType (pos, ips) in
  let* warnings1 = check_type_well_formed fun_ctx Output (Some nname) false ret_ty in
  let* warnings2 = check_type_well_formed fun_ctx Input (Some nname) false arg_ty in
  R.ok (LA.TArr (pos, arg_ty, ret_ty), warnings1 @ warnings2)
(** Function type for nodes will be [TupleType ips] -> [TupleTy outputs]  *)

and eq_lustre_type : tc_context -> LA.lustre_type -> LA.lustre_type -> (bool, [> error]) result
  = fun ctx t1 t2 ->
  match (t1, t2) with
  (* Simple types *)
  | Bool _, Bool _ -> R.ok true
  | Int _, Int _ -> R.ok true
  | UInt8 _, UInt8 _ -> R.ok true
  | UInt16 _, UInt16 _ -> R.ok true              
  | UInt32 _, UInt32 _ -> R.ok true
  | UInt64 _,UInt64 _ -> R.ok true 
  | Int8 _, Int8 _ -> R.ok true 
  | Int16 _, Int16 _ -> R.ok true
  | Int32 _, Int32 _ -> R.ok true
  | Int64 _, Int64 _ -> R.ok true
  | Real _, Real _ -> R.ok true

  (* Integer Range *)
  | IntRange _, IntRange _ -> R.ok true
  | IntRange _, Int _ -> R.ok true
  | Int _, IntRange _ -> R.ok true

  (* Lustre V6 features *)
  | UserType (_, ty_args1, i1), UserType (_, ty_args2, i2) -> 
    if List.length ty_args1 = List.length ty_args2
    then (
      let* r1 = R.seqM (&&) true (List.map2 (eq_lustre_type ctx) ty_args1 ty_args2) in 
      let r2 = i1 = i2 in 
      R.ok (r1 && r2)
    )
    else R.ok false
   
  | AbstractType (_, i1), AbstractType (_, i2) -> R.ok (i1 = i2)
  | TupleType (_, tys1), TupleType (_, tys2) ->
    if List.length tys1 = List.length tys2
    then (R.seqM (&&) true (List.map2 (eq_lustre_type ctx) tys1 tys2))
    else R.ok false
  (* For Equality for group types, flatten out the structures  *)
  | GroupType (_, tys1), GroupType (_, tys2) ->
    let (ftys1, ftys2) = LH.flatten_group_types tys1, LH.flatten_group_types tys2 in 
    if List.length ftys1 = List.length ftys2
    then (R.seqM (&&) true (List.map2 (eq_lustre_type ctx) ftys1 ftys2))
    else R.ok false
  | RecordType (_, n1, tys1), RecordType (_, n2, tys2) ->
    if List.length tys1 = List.length tys2
    then (
      let* isEqs = R.seq (List.map2 (eq_typed_ident ctx)
        (LH.sort_typed_ident tys1)
        (LH.sort_typed_ident tys2))
      in
      R.ok (List.fold_left (&&) true isEqs && n1 == n2)
    )
    else R.ok false
  | ArrayType (_, arr1), ArrayType (_, arr2) -> eq_type_array ctx arr1 arr2 
  | RefinementType (_, (_, _, ty1), _), ty2 -> eq_lustre_type ctx ty1 ty2 
  | ty1, RefinementType (_, (_, _, ty2), _) -> eq_lustre_type ctx ty1 ty2
  | EnumType (_, n1, is1), EnumType (_, n2, is2) ->
    if List.length is1 = List.length is2
    then
      R.ok (n1 = n2 &&
        (List.fold_left (&&) true (List.map2 (=) (LH.sort_idents is1) (LH.sort_idents is2))))
    else
      R.ok false
  (* node/function type *)
  | TArr (_, arg_ty1, ret_ty1), TArr (_, arg_ty2, ret_ty2) ->
    R.seqM (&&) true [ eq_lustre_type ctx arg_ty1 arg_ty2
                    ; eq_lustre_type ctx ret_ty1 ret_ty2 ]

  (* special case for type synonyms *)
  | UserType (pos, ty_args, u), ty
  | ty, UserType (pos, ty_args, u) ->
    if member_ty_syn ctx u then
      let* ty_alias = (match (lookup_ty_syn ctx u ty_args) with
        | None -> type_error pos
          (Impossible ("Cannot find definition of Identifier "
            ^ (HString.string_of_hstring u)))
        | Some ty -> R.ok ty)
      in
      eq_lustre_type ctx ty ty_alias
    else R.ok false
  (* Another special case for GroupType equality *)
  | GroupType (_, tys), t
  | t, GroupType (_, tys) ->
    if List.length tys = 1
    then (eq_lustre_type ctx (List.hd tys) t)
    else R.ok false  
  | History (pos, v), ty
  | ty, History (pos, v) -> (
    match lookup_ty ctx v with
    | Some hist_ty -> eq_lustre_type ctx hist_ty ty
    | None -> type_error pos (UnboundIdentifier v)
  )
  | _, _ -> R.ok false
(** Compute Equality for lustre types  *)

and is_expr_int_type: tc_context -> HString.t option -> LA.expr -> bool  = fun ctx nname e ->
  R.safe_unwrap false
    (infer_type_expr ctx nname e
      >>= fun (ty, _) -> eq_lustre_type ctx ty (LA.Int (LH.pos_of_expr e)))
(** Checks if the expr is of type Int. This will be useful 
 * in evaluating array sizes that we need to have as constant integers
 * while declaring the array type *)
  
and eq_typed_ident: tc_context -> LA.typed_ident -> LA.typed_ident -> (bool, [> error]) result =
  fun ctx (_, _, ty1) (_, _, ty2) -> eq_lustre_type ctx ty1 ty2
(** Compute type equality for [LA.typed_ident] *)

and eq_type_array: tc_context -> (LA.lustre_type * LA.expr) -> (LA.lustre_type * LA.expr) -> (bool, [> error]) result
  = fun ctx (ty1, e1) (ty2, e2) ->
  (* eq_lustre_type ctx ty1 ty2 *)
  R.ifM (eq_lustre_type ctx ty1 ty2)
    (* Are the array sizes equal numerals? *)
    ( match IC.eval_int_expr ctx e1, IC.eval_int_expr ctx e2 with
      | Ok l1,  Ok l2  -> R.ok (l1 = l2)
      | Error _ , _ | _, Error _ ->
        (* Are the array sizes syntactically identical? *)
        match LH.syn_expr_equal None e1 e2 with
        | Ok b -> R.ok b
        | Error _ -> R.ok false) 
    (R.ok false)
(** Compute equality for [LA.ArrayType].
   If there are free constants in the size, the eval function will fail,
   but we want to pass such cases, as there might be some
   value assigment to the free constant that satisfies the type checker. 
   Hence, silently return true with a leap of faith. *)         

                                 
let rec type_check_group: tc_context -> LA.t ->  ([> warning] list, [> error]) result list
  = fun global_ctx
  -> function
  | [] -> [R.ok ([])]
  (* skip over type declarations and const_decls*)
  | (LA.TypeDecl _ :: rest) 
  | LA.ConstDecl _ :: rest -> type_check_group global_ctx rest  
  | LA.NodeDecl (span, node_decl) :: rest ->
    let { LA.start_pos = pos } = span in
    (check_type_node_decl pos global_ctx node_decl)
    :: type_check_group global_ctx rest
  | LA.FuncDecl (span, node_decl):: rest ->
    let { LA.start_pos = pos } = span in
    (check_type_node_decl pos global_ctx node_decl)
    :: type_check_group global_ctx rest
  | LA.ContractNodeDecl (_, contract_decl) :: rest ->
    (check_type_contract_decl global_ctx contract_decl)
    :: type_check_group global_ctx rest
  | LA.NodeParamInst  _ :: rest ->
    type_check_group global_ctx rest
(** By this point, all the circularity should be resolved,
 * the top most declaration should be able to access 
 * the types of all the forward referenced indentifiers from the context*) 

let type_check_decl_grps: tc_context -> LA.t list -> ([> warning] list, [> error]) result list
  = fun ctx decls ->
    Debug.parse ("@.===============================================@."
      ^^ "Phase: Type checking declaration Groups@."
      ^^"===============================================@.");
    List.concat (List.map (fun decl -> type_check_group ctx decl) decls)
(** Typecheck a list of independent groups using a global context*)

(**************************************************************************************
 * The main functions of the file that kicks off type checking or type inference flow  *
 ***************************************************************************************)

let type_check_infer_globals: tc_context -> LA.t -> (tc_context * [> warning] list, [> error]) result
  = fun ctx prg ->
    Debug.parse ("@.===============================================@."
      ^^ "Building TC Global Context@."
      ^^"===============================================@.");
    (* Build base constant and type context *)
    let* global_ctx, warnings = build_type_and_const_context ctx prg in
    R.ok (global_ctx, warnings)

let type_check_infer_nodes_and_contracts: tc_context -> LA.t -> (tc_context * [> warning] list, [> error]) result
  = fun ctx prg -> 
  (* type check the nodes and contract decls using this base typing context  *)
  Debug.parse ("@.===============================================@."
    ^^ "Building node and contract Context@."
    ^^"===============================================@.");
  (* Build base constant and type context *)
  let* global_ctx, warnings1 = tc_context_of (ctx, []) prg in
  Debug.parse ("@.===============================================@."
    ^^ "Type checking declaration Groups@." 
    ^^ "with TC Context@.%a@."
    ^^"===============================================@.")
    pp_print_tc_context global_ctx;
  let* warnings2 = R.seq (type_check_decl_grps global_ctx [prg]) in
  Debug.parse ("@.===============================================@."
    ^^ "Type checking declaration Groups Done@."
    ^^"===============================================@.");
  R.ok (global_ctx, warnings1 @ List.flatten warnings2)

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
