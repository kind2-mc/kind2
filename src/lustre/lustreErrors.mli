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
  | `LustreArrayDependencies of Lib.position * LustreArrayDependencies.error_kind
  | `LustreAstDependenciesError of Lib.position * LustreAstDependencies.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreAbstractInterpretationError of Lib.position * LustreAbstractInterpretation.error_kind
  | `LustreAstNormalizerError of Lib.position * LustreAstNormalizer.error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreUnguardedPreError of Lib.position * LustreAst.expr
  | `LustreParserError of Lib.position * string
  | `LustreDesugarIfBlocksError of Lib.position * LustreDesugarIfBlocks.error_kind
  | `LustreDesugarFrameBlocksError of Lib.position * LustreDesugarFrameBlocks.error_kind
]

val error_position : [< error] -> Lib.position
val error_message : [< error] -> string
