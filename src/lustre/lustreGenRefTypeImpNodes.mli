(* This file is part of the Kind 2 model checker.

   Copyright (c) 2024 by the Board of Trustees of the University of Iowa

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

 (** @author Rob Lorch *)


module A = LustreAst
module Ctx = TypeCheckerContext
module GI = GeneratedIdentifiers

val inputs_tag : string 
val contract_tag : string
val type_tag : string
val poly_gen_node_tag : string

type error_kind = 
  | EnvRealizabilityCheckModeRefAssumption

val error_message : error_kind -> string

type error = [
  | `LustreGenRefTypeImpNodesError of Lib.position * error_kind
]

type node_type = Environment | Contract | Type | User

(** Retrieve information about Kind 2-generated nodes *)
val get_node_type_and_name: string -> node_type * string

val gen_imp_nodes : Ctx.tc_context ->  A.declaration list -> (A.declaration list * Ctx.tc_context * GI.t HString.HStringMap.t, [> error]) result