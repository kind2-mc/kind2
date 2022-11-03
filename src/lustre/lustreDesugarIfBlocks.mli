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
   Code for desugaring imperative-style if blocks to functional ITEs.

   The code has a few steps.
    1. Remove multiple assignment from if blocks using temp variables.
    2. Parse the if block and create a map of trees, one for each variable
    3. Fill in oracles in the trees for missing values.
    4. Remove redundancy from the trees.
    5. Convert the trees to ITE expressions. 

   @author Rob Lorch
 *)



type error_kind = Unknown of string
  | MisplacedNodeItemError of LustreAst.node_item

val error_message : error_kind -> string

type error = [
  | `LustreDesugarIfBlocksError of Lib.position * error_kind 
]


val get_node_ctx : TypeCheckerContext.tc_context ->
  'a * 'b * 'c * LustreAst.const_clocked_typed_decl list * LustreAst.clocked_typed_decl list *
  LustreAst.node_local_decl list * 'd * 'e -> TypeCheckerContext.tc_context

val desugar_if_blocks : 
TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  (LustreAst.declaration list * LustreAstNormalizer.generated_identifiers LustreAstNormalizer.StringMap.t,
   [> `LustreDesugarIfBlocksError of Lib.position * error_kind ])
  result
