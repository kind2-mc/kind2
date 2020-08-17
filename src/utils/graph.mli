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
(** Graph and graph traversals
   
   @author Apoorv Ingle *)

(* TODO: Make this polymorphic in vertex type.
 * Have a functor Graph.Make similar to Set.Make  *)
type vertex
(** the vertex name *)

val mk_vertex: string -> vertex
(** makes a vertex *)
  
type edge
(** edge is between two vertices *)

val mk_edge: vertex -> vertex -> edge   
(** make and edge from two vertices  *)

type vertices
(** Set of vertices *)

type edges
(** Set of edges *)

type t
(** the graph type  *)

val emp_g: t
(** The empty graph  *)

val add_vertex: t -> vertex -> t
(** Add a vertex to a graph  *)

val add_edge: t -> edge -> t
(** Add an edge to a graph  *)

val remove_vertex: t -> vertex -> t
(** Remove a vertex from a graph *)                             

val remove_edge: t -> edge -> t
(** Remove an edge from a graph *)                             
                                    
