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

module LA = LustreAst

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

let error_position error = match error with
  | `LustreArrayDependencies (pos, _) -> pos
  | `LustreAstDependenciesError (pos, _) -> pos
  | `LustreAstInlineConstantsError (pos, _) -> pos
  | `LustreAstNormalizerError -> assert false
  | `LustreSyntaxChecksError (pos, _) -> pos
  | `LustreTypeCheckerError (pos, _) -> pos
  | `LustreUnguardedPreError (pos, _) -> pos
  | `LustreParserError (pos, _) -> pos
  | `LustreDesugarIfBlocksError (pos, _) -> pos
  | `LustreDesugarFrameBlocksError (pos, _) -> pos

let error_message error = match error with
  | `LustreArrayDependencies (_, kind) -> LustreArrayDependencies.error_message kind
  | `LustreAstDependenciesError (_, kind) -> LustreAstDependencies.error_message kind
  | `LustreAstInlineConstantsError (_, kind) -> LustreAstInlineConstants.error_message kind
  | `LustreAstNormalizerError -> assert false
  | `LustreSyntaxChecksError (_, kind) -> LustreSyntaxChecks.error_message kind
  | `LustreTypeCheckerError (_, kind) -> LustreTypeChecker.error_message kind
  | `LustreUnguardedPreError (_, e) -> (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]" LA.pp_print_expr e)
  | `LustreParserError (_, e) -> e
  | `LustreDesugarIfBlocksError (_, kind) -> LustreDesugarIfBlocks.error_message kind
  | `LustreDesugarFrameBlocksError (_, kind) -> LustreDesugarFrameBlocks.error_message kind