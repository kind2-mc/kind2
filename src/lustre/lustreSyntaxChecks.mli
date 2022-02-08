(* This file is part of the Kind 2 model checker.

   Copyright (c) 2021 by the Board of Trustees of the University of Iowa

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
(** Check various syntactic properties that do not depend on type information
  
  @author Andrew Marmaduke *)

type error_kind = Unknown of string
  | UndefinedLocal of HString.t
  | UndefinedNode of HString.t
  | DanglingIdentifier of HString.t
  | QuantifiedVariableInNodeArgument of HString.t * HString.t
  | SymbolicArrayIndexInNodeArgument of HString.t * HString.t
  | NodeCallInFunction of HString.t
  | NodeCallInRefinableContract of string * HString.t
  | IllegalTemporalOperator of string * string
  | IllegalImportOfStatefulContract of HString.t
  | UnsupportedClockedInputOrOutput
  | UnsupportedClockedLocal of HString.t
  | UnsupportedExpression of LustreAst.expr
  | UnsupportedOutsideMerge of LustreAst.expr
  | UnsupportedParametricDeclaration
  | UnsupportedAssignment
  | AssumptionVariablesInContractNode
  | ClockMismatchInMerge

type error = [
  | `LustreSyntaxChecksError of Lib.position * error_kind
]

val error_message : error_kind -> string

val syntax_check : LustreAst.t -> (LustreAst.t, [> error]) result

val no_mismatched_clock : bool -> LustreAst.expr -> (unit, [> error]) result
(** Conservative syntactic check of clock arguments for merge expressions.
  To eventually be replaced with more general clock inference/checking.

  Note: type information is needed for this check, causing this check to
  be called in the lustreTypeChecker *)
