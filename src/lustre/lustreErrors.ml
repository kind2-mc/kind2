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

open Lib

type error = [
  | `AstDependencyError of (position * string)
  | `AstInlineConstantsError of (position * string)
  | `AstNormalizerError of (position * string)
  | `SyntaxChecksError of (position * string)
  | `TypeCheckerError of (position * string)
]

let error_position error = match error with
  | `AstDependencyError (pos, _) -> pos
  | `AstInlineConstantsError (pos, _) -> pos
  | `AstNormalizerError (pos, _) -> pos
  | `SyntaxChecksError (pos, _) -> pos
  | `TypeCheckerError (pos, _) -> pos

let error_message error = match error with
| `AstDependencyError (_, msg) -> msg
| `AstInlineConstantsError (_, msg) -> msg
| `AstNormalizerError (_, msg) -> msg
| `SyntaxChecksError (_, msg) -> msg
| `TypeCheckerError (_, msg) -> msg
