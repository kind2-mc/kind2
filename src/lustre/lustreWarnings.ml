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

module LDF = LustreDesugarFrameBlocks
module LAN = LustreAstNormalizer
module LTC = LustreTypeChecker
module LSC = LustreSyntaxChecks

type warning = [
  | `LustreDesugarFrameBlocksWarning of Lib.position * LustreDesugarFrameBlocks.warning_kind
  | `LustreAstNormalizerWarning of Lib.position * LustreAstNormalizer.warning_kind
  | `LustreTypeCheckerWarning of Lib.position * LustreTypeChecker.warning_kind
  | `LustreSyntaxChecksWarning of Lib.position * LustreSyntaxChecks.warning_kind
]

let warning_position warning = match warning with
  | `LustreDesugarFrameBlocksWarning (pos, _) -> pos
  | `LustreAstNormalizerWarning (pos, _) -> pos
  | `LustreTypeCheckerWarning (pos, _) -> pos
  | `LustreSyntaxChecksWarning (pos, _) -> pos

let warning_message warning = match warning with
  | `LustreDesugarFrameBlocksWarning (_, kind) -> LustreDesugarFrameBlocks.warning_message kind
  | `LustreAstNormalizerWarning (_, kind) -> LustreAstNormalizer.warning_message kind
  | `LustreTypeCheckerWarning (_, kind) -> LustreTypeChecker.warning_message kind
  | `LustreSyntaxChecksWarning (_, kind) -> LustreSyntaxChecks.warning_message kind

let sort_warnings_by_pos l =
  List.sort (fun w1 w2 -> Lib.compare_pos (warning_position w1) (warning_position w2)) l

let error_if_lus_strict = function
  | `LustreDesugarFrameBlocksWarning (_, kind) -> LDF.error_if_lus_strict kind
  | `LustreAstNormalizerWarning (_, kind) -> LAN.error_if_lus_strict kind
  | `LustreTypeCheckerWarning (_, kind) -> LTC.error_if_lus_strict kind
  | `LustreSyntaxChecksWarning (_, kind) -> LSC.error_if_lus_strict kind
