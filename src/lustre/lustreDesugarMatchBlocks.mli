(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(** Desugars match blocks into chains of when blocks.

    A match block is to a match expression what an if block is to an
    if-then-else: the arms hold equations rather than a value. Each arm becomes
    a when block guarded by the constructor testers its pattern imposes, with
    the pattern's variables replaced by projections out of the scrutinee. The
    resulting when blocks give the arms the lazy semantics of a match
    expression, and the existing when-block desugaring supplies the rest: every
    variable defined in one arm must be defined in all of them, unless the
    block sits in a frame block, where an uncovered case stutters instead.

    Runs after {!LustreCheckADTDecreases} and before {!LustreDesugarADTs}, so
    the testers and projections it emits are still in surface form and
    {!LustreDesugarADTs} rewrites them for non-recursive datatypes.

    @author Rob Lorch *)

type error_kind =
  | MisplacedNodeItemInMatchArm of LustreAst.node_item
  | MisplacedMatchBlock of LustreAst.node_item
  | ShadowingPatternVariable of HString.t

val error_message : error_kind -> string

type error = [
  | `LustreDesugarMatchBlocksError of Lib.position * error_kind
]

(** Replaces every match block with the equivalent chain of when blocks. *)
val desugar_match_blocks :
  TypeCheckerContext.tc_context -> LustreAst.t -> (LustreAst.t, [> error]) result
