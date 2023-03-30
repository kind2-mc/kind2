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

(** Graph analysis on Lustre Ast Declarations.
  
    We build a dependency graph of the lustre declarations
    to detect circular dependencies and reject them. We also
    reorder node and contract declarations to resolve
    forward references as backend cannot handle them.

    Note {!Types of dependency analysis}: There are two different kinds of 
    graph dependency analysis and sorting done here. 

    1. Top level constants and type declarations (starts at [sort_globals])
       We resolve all the forward references in this step.

    2a. Nodes, functions and contracts (starts at [sort_and_check_nodes_contracts])
        We resolve all the forward references in this step.
    
    2b. Sort contract equations and perform cirularity check of node equations. 

   TODO: This should module should supercede LustreDependencies when it hardens.     

   @author Apoorv Ingle *)

module LA = LustreAst

module IMap : sig
  include (Map.S with type key = HString.t)
end

module IntMap : sig
  include (Map.S with type key = int)
end

type error_kind = Unknown of string
  | IdentifierRedeclared of HString.t
  | WidthLengthsUnequal of LA.expr * LA.expr
  | EquationWidthsUnequal
  | ContractDependencyOnCurrentOutput of LA.SI.t
  | CyclicDependency of HString.t list

type error = [
  | `LustreAstDependenciesError of Lib.position * error_kind
]

val error_message: error_kind -> string
(** Returns an message describing the error kind *)

type node_summary = ((int list) IntMap.t) IMap.t

val pp_print_node_summary: Format.formatter -> int list IntMap.t IMap.t -> unit

val sort_globals: LA.t -> (LA.t, [> error]) result
(** Returns a topological order to resolve forward references of globals. 
    This step processes 1. type declarations, and 2. constant declarations *)  
                     
val sort_and_check_nodes_contracts: LA.t -> ((LA.t * LA.ident list * node_summary), [> error]) result
(** Returns a topological order of declarations to resolve all forward references,
    with a list of toplevel nodes.
    It also reorders contract equations and checks for circularity of node equations.
    This step processes 1. nodes, 2. contracts and 3. functions *)  
