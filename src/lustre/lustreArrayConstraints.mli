(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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
@author Rob Lorch *)


val add_array_constraints : TypeCheckerContext.tc_context -> LustreAst.declaration list -> LustreAst.declaration list

val add_array_constraints2: TypeCheckerContext.tc_context ->
  'a
  * 'b
  * 'c
  * LustreAst.const_clocked_typed_decl list
  * LustreAst.clocked_typed_decl list
  * LustreAst.node_local_decl list
  * LustreAst.node_item list
  * LustreAst.contract_node_equation list option ->
    LustreAst.contract_node_equation list option
