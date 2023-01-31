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

   Precondition: Multiple assignment has been removed from if and frame blocks.

   The code has a few steps.
    1. Parse the if block and create a map of trees, one for each variable.
    2. Fill in oracles in the trees for missing values.
    3. Remove redundancy from the trees.
    4. Convert the trees to ITE expressions. 

   @author Rob Lorch
 *)



type error_kind = 
  | MisplacedNodeItemError of LustreAst.node_item

val error_message : error_kind -> string

type error = [
  | `LustreDesugarIfBlocksError of Lib.position * error_kind 
]

module IfHashtbl : Hashtbl.S with type key = HString.t

val pos_list_map : (Lib.position * HString.t) list IfHashtbl.t

val desugar_if_blocks : 
TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
    GeneratedIdentifiers.t GeneratedIdentifiers.StringMap.t ->
  (LustreAst.declaration list * GeneratedIdentifiers.t GeneratedIdentifiers.StringMap.t,
   [> error ])
  result
