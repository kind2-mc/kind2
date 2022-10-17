(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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
   @author Rob Lorch
 *)

module A = LustreAst

type error_kind = Unknown of string | StubError

val error_message : error_kind -> string

type error = [
 (* | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreDesugarIfBlocksError of Lib.position * error_kind *)
  | `LustreDesugarFrameBlocksError of Lib.position * error_kind
]

val desugar_frame_blocks :
  A.declaration list ->
    (A.declaration list,
    [> error])
    result
