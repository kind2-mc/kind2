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

type error = [
  | `LustreArrayDependencies of Position.position * LustreArrayDependencies.error_kind
  | `LustreAstDependenciesError of Position.position * LustreAstDependencies.error_kind
  | `LustreAstInlineConstantsError of Position.position * LustreAstInlineConstants.error_kind
  | `LustreAstNormalizerError
  | `LustreSyntaxChecksError of Position.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Position.position * LustreTypeChecker.error_kind
  | `LustreUnguardedPreError of Position.position * LustreAst.expr
  | `LustreParserError of Position.position * string
  | `LustreDesugarIfBlocksError of Position.position * LustreDesugarIfBlocks.error_kind
  | `LustreDesugarFrameBlocksError of Position.position * LustreDesugarFrameBlocks.error_kind
]

val error_position : [< error] -> Position.position
val error_message : [< error] -> string
