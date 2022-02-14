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
  | `LustreAstDependenciesError of Lib.position * LustreAstDependencies.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreAstNormalizerError
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreInputOnlyParse
  | `LustreUnguardedPreError of Lib.position * LustreAst.expr
]


let error_position error = match error with
  | `LustreAstDependenciesError (pos, _) -> pos
  | `LustreAstInlineConstantsError (pos, _) -> pos
  | `LustreAstNormalizerError -> assert false
  | `LustreSyntaxChecksError (pos, _) -> pos
  | `LustreTypeCheckerError (pos, _) -> pos
  | `LustreInputOnlyParse -> Lib.dummy_pos
  | `LustreUnguardedPreError (pos, _) -> pos

let error_message error = match error with
| `LustreAstDependenciesError (_, kind) -> LustreAstDependencies.error_message kind
| `LustreAstInlineConstantsError (_, kind) -> LustreAstInlineConstants.error_message kind
| `LustreAstNormalizerError -> assert false
| `LustreSyntaxChecksError (_, kind) -> LustreSyntaxChecks.error_message kind
| `LustreTypeCheckerError (_, kind) -> LustreTypeChecker.error_message kind
| `LustreInputOnlyParse -> "TODO"
| `LustreUnguardedPreError (_, e) -> (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]" LA.pp_print_expr e)
