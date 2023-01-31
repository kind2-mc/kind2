(* This file is part of the Kind 2 model checker.

   Copyright (c) 2023 by the Board of Trustees of the University of Iowa

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

type warning = [
  | `LustreDesugarFrameBlocksWarning of Lib.position * LustreDesugarFrameBlocks.warning_kind
  | `LustreAstNormalizerWarning of Lib.position * LustreAstNormalizer.warning_kind
]

let warning_position warning = match warning with
  | `LustreDesugarFrameBlocksWarning (pos, _) -> pos
  | `LustreAstNormalizerWarning (pos, _) -> pos

let warning_message warning = match warning with
  | `LustreDesugarFrameBlocksWarning (_, kind) -> LustreDesugarFrameBlocks.warning_message kind
  | `LustreAstNormalizerWarning (_, kind) -> LustreAstNormalizer.warning_message kind