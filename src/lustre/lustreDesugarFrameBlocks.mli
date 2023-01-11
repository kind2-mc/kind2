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
   This file desugars frame blocks into a list of node items
   (equations), completing two major steps:
   1. Fill in any oracles within the frame block (for unguarded pres or 
      undefined variables in if blocks).
   2. Generate node equations for variables left completely undefined in frame 
      blocks.

   @author Rob Lorch
 *)

module A = LustreAst

type error_kind = 
  | MisplacedNodeItemError of A.node_item
  | MisplacedFrameBlockError of A.node_item

val error_message : error_kind -> string

type error = [
  | `LustreDesugarFrameBlocksError of Lib.position * error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
]


val desugar_frame_blocks :
  A.declaration list ->
    (A.declaration list,
    [> error])
    result
