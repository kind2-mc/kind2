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

(**
    @author Andrew Marmaduke *)

type error_kind = Unknown of string
  | ComplicatedExpr of LustreAst.expr
  | ExprNotSmaller of LustreAst.expr
  | ExprMissingIndex of HString.t * LustreAst.expr

val error_message: error_kind -> string
(** Returns an message describing the error kind *)

type error = [
  | `LustreArrayDependencies of Lib.position * error_kind
]

val check_inductive_array_dependencies: TypeCheckerContext.tc_context
  -> LustreAst.t
  -> (unit, [> error]) result
