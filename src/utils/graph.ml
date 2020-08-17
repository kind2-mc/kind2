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

type vertex = string
(** the vertex name *)

let mk_vertex: string -> vertex
  = fun v -> v
(** make a vertex given the vertex name  *)

module VSet = struct
  include (Set.Make (struct
               type t = vertex
               let compare = Stdlib.compare
             end))
  let flatten: t list -> t = fun sets ->
    List.fold_left union empty sets
end 
(** Set of vertices *)

type edge = vertex * vertex
(** edge is between two vertices *)

let mk_edge: vertex -> vertex -> edge
  = fun s t -> (s, t)
(** Make an edge given the source and the target vertices *)

module ESet = struct
  include (Set.Make (struct
               type t = edge
               let compare (v11, v12) (v21, v22)
                 = let c = Stdlib.compare v11 v21 in
                   if c <> 0 then c else Stdlib.compare v21 v22
             end))
  let flatten: t list -> t = fun sets ->
    List.fold_left union empty sets
end 
(** A set of vertices  *)

type vertices = VSet.t
(** type alias for set of vertices *)

type edges = ESet.t
(** type alias for set of edges *)
            
type t = vertices * edges
(** A graph is a set of vertices and set of edges  *)

let emp_g = (VSet.empty, ESet.empty)
(** An empty trivial graph contains no vertices and no edges *)

let mk_edge: vertex -> vertex -> edge
  = fun v1 v2 -> (v1, v2)

let add_vertex: t -> vertex -> t
  = fun (vs, es) v -> (VSet.add v vs,  es) 
(** add a vertex to a graph  *)

let add_edge: t -> edge -> t
  = fun (vs, es) e -> (vs,  ESet.add e es) 
(** add an edge to a graph  *)

let is_vertex_src: edge -> vertex -> bool
  = fun (sv, tv) v -> v = sv

let is_vertex_tgt: edge -> vertex -> bool
  = fun (sv, tv) v -> v = tv
                    
let find_edges_of_vertex: t -> vertex -> edges
  = fun (vs, es) v -> ESet.filter (fun e -> is_vertex_tgt e v || is_vertex_src e v) es 

let remove_vertex: t -> vertex -> t
  = fun (vs, es) v -> ( VSet.remove v vs
                      , ESet.filter
                          (fun e -> not (is_vertex_tgt e v
                                         || is_vertex_src e v)) es)
(** Remove a vertex from a graph and the associated edges *)                             

let remove_edge: t -> edge -> t
  = fun (vs, es) e -> (vs, ESet.remove e es) 
(** Remove an edge from a graph *)                             


