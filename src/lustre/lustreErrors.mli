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
(** Handle all error variants produced by the Lustre frontend
  
  @author Andrew Marmaduke *)

open Lib

type error = [
  | `LustreAstDependenciesError of (position * LustreAstDependencies.error_kind)
  | `AstInlineConstantsError of (position * string)
  | `AstNormalizerError of (position * string)
  | `SyntaxChecksError of (position * string)
  | `TypeCheckerError of (position * string)
]

val error_position : [< error] -> position
val error_message : [< error] -> string
