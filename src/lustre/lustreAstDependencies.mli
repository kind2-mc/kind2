(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

(** Graph analysis on Lustre Ast Declarations  
    Builds a dependency graph of the lustre declarations,
    to detect circular dependencies and reject them and
    re-orders node and contract declarations to resolve
    forward references   

    @author: Apoorv Ingle *)

module LA = LustreAst
type 'a graph_result = ('a, Lib.position * string) result

module IMap: sig
  include (Map.S with type key = LA.ident)
  val keys: 'a t -> key list
end

val sort_declarations: LA.t -> LA.t graph_result
(** Returns a topological order of declarations *)

val analyze_circ_contract_equations: bool IMap.t -> LA.contract -> unit graph_result
(** Checks if there are circular dependencies in the contract equations *)

val analyze_circ_node_equations: bool IMap.t -> LA.ident list -> LA.node_item list -> unit graph_result
(** Checks if there are circular dependencies in node equations equations *)

val mk_node_call_summary: bool IMap.t -> LA.node_decl -> bool IMap.t
