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
  | UnboundedIdentifier of HString.t
  | UnboundedModeReference of HString.t
  | MissingRecordField of HString.t
  | IlltypedRecordProjection of tc_type
  | MissingTupleField of int * tc_type
  | IlltypedTupleProjection of tc_type
  | UnequalIteBranchTypes of tc_type * tc_type
  | ExpectedBooleanExpression of tc_type
  | Unsupported of string
  | UnequalArrayExpressionType
  | ExpectedNumeralArrayBound
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
  | ExpectedMachineIntegerTypes of tc_type * tc_type
  | ExpectedBitShiftConstant
  | ExpectedBitShiftConstantOfSameWidth of tc_type
  | ExpectedBitShiftMachineIntegerType of tc_type
  | InvalidConversion of tc_type * tc_type
  | NodeArgumentsAreOnLHS of ty_set
  | NodeInputOutputShareIdentifier of ty_set
  | MismatchOfEquationType of LA.struct_item list option * tc_type
  | DisallowedReassignment of ty_set
  | DisallowedSubrangeInContractReturn of bool * HString.t * tc_type
  | AssumptionMustBeInputOrOutput of HString.t
  | ContractOutputContainsContractArguments of ty_set
  | Redeclaration of HString.t
  | ExpectedConstant of LA.expr
  | ArrayBoundsInvalidExpression
  | Undefined of HString.t
  | EmptySubrange of int * int
  | SubrangeArgumentMustBeConstantInteger of LA.expr

type error = [
  | `LustreTypeCheckerError of Lib.position * error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
]

val error_message: error_kind -> string

val type_error: Lib.position -> error_kind -> ('a, [> error]) result 
(** [type_error] returns an [Error] of [tc_result] *)
     
val type_check_infer_globals: tc_context -> LA.t -> (tc_context, [> error]) result  
(** Typechecks the toplevel globals i.e. constant decls and type decls. It returns 
    a [Ok (tc_context)] if it succeeds or and [Error of String] if the typechecker fails *)

val type_check_infer_nodes_and_contracts: tc_context -> LA.t -> (tc_context, [> error]) result
(** Typechecks and infers type for the nodes and contracts. It returns
    a [Ok (tc_context)] if it succeeds or and [Error of String] if the typechecker fails *)

val tc_ctx_of_contract: tc_context -> LA.contract -> (tc_context, [> error]) result

val local_var_binding: tc_context -> LA.node_local_decl -> (tc_context, [> error]) result

val infer_type_expr: tc_context -> LA.expr -> (tc_type, [> error]) result
(** Infer type of Lustre expression given a typing context *)

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
                                
