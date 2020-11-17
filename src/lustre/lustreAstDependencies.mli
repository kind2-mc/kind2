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

module IMap: sig
  include (Map.S with type key = LA.ident)
  val keys: 'a t -> key list
end
          
type 'a graph_result = ('a, Lib.position * string) result
(** Result of the graph analysis procedures *)
                     
type node_summary = (int list) IMap.t
(** The node summary contains the positions of the input streams of a node 
    that are used in their current value. For example: if there 
    is an equation `y = x + 1` where `x` is the input stream to the 
    node `n(x:int, z:int)returns(y:int)`, the node summary will be
    `(n:-> 0)` as the node `n` uses the current value of `x`.
*)

val sort_declarations: LA.t -> LA.t graph_result
(** Returns a topological order of declarations *)

val analyze_circ_contract_equations: node_summary -> LA.contract -> unit graph_result
(** Checks if there are circular dependencies in the contract equations *)

val analyze_circ_node_equations: node_summary -> LA.ident list -> LA.node_item list -> unit graph_result
(** Checks if there are circular dependencies in node equations equations *)

val mk_node_summary: node_summary -> LA.node_decl -> node_summary
(** Generates a necessary node call summary that is required for inlining node calls for circularity check *)

val expression_current_streams: node_summary -> LA.expr -> LA.ident list
(** checks if the expression depends on the current value of the identifier *)
