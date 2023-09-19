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

(** Inlining constants throughout the program
  
    @author Apoorv Ingle *)

module TC = TypeCheckerContext
module LA = LustreAst

type error_kind = Unknown of string
  | FreeIntIdentifier of HString.t
  | ConstantMustBeInt of LA.expr
  | UnaryMustBeInt of LA.expr
  | BinaryMustBeInt of LA.expr
  | FreeBoolIdentifier of HString.t
  | ConstantMustBeBool of LA.expr
  | ConstantOutOfSubrange of HString.t
  | ParamInConstantDef of HString.t
  | UnaryMustBeBool of LA.expr
  | BinaryMustBeBool of LA.expr
  | IdentifierMustBeConstant of HString.t
  | UnableToEvaluate of LA.expr
  | WidthOperatorUnsupported
  | OutOfBounds of string

type error = [
  | `LustreAstInlineConstantsError of Lib.position * error_kind
]

val error_message: error_kind -> string
(** Returns an message describing the error kind *)

val inline_constants: TC.tc_context -> LA.t -> ((TC.tc_context * LA.t), [> error]) result
(** Best effort at inlining constants *)

val inline_constants_of_lustre_type: TC.tc_context -> LA.lustre_type -> LA.lustre_type
(** Best effort at inlining constants in a lustre type *)

val eval_int_expr: TC.tc_context -> LA.expr -> (int, [> error]) result
(** try to evaluate an expression to an int *)

val simplify_expr: ?is_guarded:bool -> TC.tc_context -> LA.expr -> LA.expr
(** Best effort at inlining constants in a lustre expr *)
