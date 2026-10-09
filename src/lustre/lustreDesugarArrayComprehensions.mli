(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(** Replace array comprehensions with fresh local variables defined by
    array definitions.

    @author Kind 2 development team *)

type error_kind =
  | BoundVariableInComprehension of HString.t
  | UnsupportedComprehensionPosition of string
  | ComprehensionConstantInType of HString.t

val error_message : error_kind -> string

type error = [
  | `LustreDesugarArrayComprehensionsError of Lib.position * error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
]

(** [restore e] replaces in [e] the fresh locals introduced by
    [desugar_array_comprehensions] with the comprehensions they stand for, as
    written, to print [e] as the user wrote it *)
val restore : LustreAst.expr -> LustreAst.expr

(** Replace each array comprehension [(e foreach i, j)^m^n] in the body of a
    node or a function with a fresh local [x] defined by the equation
    [x[i][j] = e]. Returns an error for a comprehension in a contract or a
    constant declaration, and for one that mentions a variable bound around
    it. Must run after type checking. *)
val desugar_array_comprehensions :
  TypeCheckerContext.tc_context -> LustreAst.t ->
  (TypeCheckerContext.tc_context * LustreAst.t, [> error]) result

(** [inline_comprehension_constants consts decls] replaces in the nodes,
    functions and contracts of [decls] the constants whose definition
    contains an array comprehension, possibly through another such constant,
    with their definitions, and removes their declarations from the global
    constant declarations [consts] and from the local constants of the
    nodes. Returns an error if such a constant is used in a type. Must run
    before [desugar_array_comprehensions]. *)
val inline_comprehension_constants :
  LustreAst.t -> LustreAst.t -> (LustreAst.t * LustreAst.t, [> error]) result
