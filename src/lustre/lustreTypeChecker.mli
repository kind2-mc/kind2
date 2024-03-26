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
(** Functions for type checking surface syntax [LustreAst]
    
    @author Apoorv Ingle *)

module LA = LustreAst
open TypeCheckerContext

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

type error = [
  | `LustreTypeCheckerError of Lib.position * error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
]

type warning_kind =
  | UnusedBoundVariableWarning of HString.t

type warning = [
  | `LustreTypeCheckerWarning of Lib.position * warning_kind
]

val warning_message : warning_kind -> string

type source = 
  | Input | Output | Local | Global | Ghost

val error_message: error_kind -> string

val type_error: Lib.position -> error_kind -> ('a, [> error]) result 
(** [type_error] returns an [Error] of [tc_result] *)
     
val type_check_infer_globals: tc_context -> LA.t -> (tc_context * [> warning] list, [> error]) result  
(** Typechecks the toplevel globals i.e. constant decls and type decls. It returns 
    a [Ok (tc_context)] if it succeeds or and [Error of String] if the typechecker fails *)

val type_check_infer_nodes_and_contracts: tc_context -> LA.t -> (tc_context * [> warning] list, [> error]) result
(** Typechecks and infers type for the nodes and contracts. It returns
    a [Ok (tc_context)] if it succeeds or and [Error of String] if the typechecker fails *)

val tc_ctx_of_contract: ?ignore_modes:bool -> tc_context -> source -> HString.t -> LA.contract -> (tc_context * [> warning ] list, [> error ]) result 

val local_var_binding: tc_context ->  HString.t -> LA.node_local_decl -> (tc_context * [> warning ] list, [> error]) result 

val get_node_ctx : tc_context ->
  HString.t * 'b * 'c * LA.const_clocked_typed_decl list *
  LA.clocked_typed_decl list * LA.node_local_decl list * 'd * 'e ->
  (tc_context, [> error ]) result
  
val build_node_fun_ty : Lib.position ->
  tc_context ->
  HString.t ->
  LA.const_clocked_typed_decl list ->
  LA.clocked_typed_decl list -> (tc_type * [> warning ] list, [> error ]) result

val expand_type_syn_reftype_history : ?expand_subrange:bool ->
  tc_context ->
  tc_type ->
  ( tc_type,
    [> error] )
  result

val expand_type_syn_reftype_history_subrange : tc_context ->
  tc_type ->
  ( tc_type,
    [> error] )
  result
  
val infer_type_expr: tc_context -> LA.expr -> (tc_type, [> error]) result
(** Infer type of Lustre expression given a typing context *)

val eq_lustre_type : tc_context -> LA.lustre_type -> LA.lustre_type -> (bool, [> error]) result
(** Check if two lustre types are equal *)

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
                                
