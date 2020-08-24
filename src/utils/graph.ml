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
(** A poor person's graph and graph traversal implementations
   
   @author Apoorv Ingle *)

module type OrderedType = sig
  type t
  val compare: t -> t -> int
end
                        
module type S = sig
  exception IllegalGraphOperation
  (** The exception raised when an illegal edge is added *)
  exception CyclicGraphException
  (** The exception raised when topological sort is tried on cyclic graph  *)
  
  type vertex
  (** thevertex name *)
    
  type edge
  (** edge is between two vertices *)

  val mk_edge: vertex -> vertex ->  edge   
  (** make and edge from two vertices  *)

  type vertices
  (** Set of vertices *)

  type edges
  (** Set of edges *)

  type t
  (** the graph type  *)

  val empty: t
  (** The empty graph  *)

  val is_empty: t -> bool
  (** Check if the graph is empty  *)
    
  val add_vertex: t ->vertex -> t
  (** Add avertex to a graph  *)

  val add_edge: t ->  edge -> t
  (** Add an edge to a graph  *)

  val remove_vertex: t ->vertex -> t
  (** Remove avertex from a graph *)                             

  val remove_edge: t -> edge -> t
  (** Remove an edge from a graph *)                             

  val topological_sort: t -> vertex list
  (** give a topological ordering of vertices *)
end

module Make(Ord: OrderedType) = struct
  exception IllegalGraphOperation
  (** The exception raised when an illegal edge is added *)
  exception CyclicGraphException
  (** The exception raised when topological sort is tried on cyclic graph  *)
  
  type vertex = Ord.t
  (** thevertex name *)

  type edge = vertex * vertex
  (** edge is between two vertices *)

  let mk_edge: vertex -> vertex ->  edge
    = fun s t -> (s, t)
  (** Make an edge given the source and the target vertices *)

  module VSet = struct
    include (Set.Make (struct
                 type t = Ord.t
                 let compare = Ord.compare
               end))
    let flatten: t list -> t = fun sets ->
      List.fold_left union empty sets
  end 
  (** Set of vertices *)

  module ESet = struct
    include (Set.Make (struct
                 type t = (Ord.t *  Ord.t)
                 let compare (v11, v12) (v21, v22)
                   = let c = Ord.compare v11 v21 in
                     if c <> 0 then c else Ord.compare v21 v22
               end))
    let flatten: t list -> t = fun sets ->
      List.fold_left union empty sets
  end 
  (** A set of vertices  *)

  type vertices = VSet.t
  (** type alias for set of vertices *)

  type  edges = ESet.t
  (** type alias for set of  edges *)
             
  type  t = vertices * edges
  (** A graph is a set of vertices and set of  edges  *)

  let empty = (VSet.empty, ESet.empty)
  (** An empty trivial graph contains no vertices and no  edges *)

  let is_empty:  t -> bool = fun  (vs, es) ->
    VSet.is_empty vs 

  let mk_edge:vertex ->vertex ->  edge
    = fun v1 v2 -> (v1, v2)

  let add_vertex:  t ->vertex ->  t
    = fun (vs, es) v -> (VSet.add v vs,  es) 
  (** add avertex to a graph  *)

  let add_edge:  t ->  edge ->  t
    = fun (vs, es) ((src, tgt) as e) ->
    if VSet.mem src vs && VSet.mem tgt vs
    then (vs,  ESet.add e es)
    else raise IllegalGraphOperation
  (** add an  edge to a graph  *)

  let is_vertex_src:  edge ->vertex -> bool
    = fun (sv, tv) v -> v = sv

  let is_vertex_tgt:  edge ->vertex -> bool
    = fun (sv, tv) v -> v = tv
                      
  let find_edges_of_vertex:  t ->vertex ->  edges
    = fun (vs, es) v -> ESet.filter (fun e -> is_vertex_tgt e v
                                              || is_vertex_src e v) es 

  let remove_vertex:  t ->vertex ->  t
    = fun (vs, es) v -> ( VSet.remove v vs
                        , ESet.filter
                            (fun e -> not (is_vertex_tgt e v
                                           || is_vertex_src e v)) es)
  (** Remove a vertex from a graph and the associated  edges *)                             

  let remove_edge:  t ->  edge ->  t
    = fun (vs, es) e -> (vs, ESet.remove e es) 
  (** Remove an  edge from a graph *)                             

  let non_tgt_vertices:  t ->vertex list
    = fun (vs, es) ->
    let vs' = VSet.elements vs in
    List.filter (fun v -> ESet.for_all (fun e -> not (is_vertex_tgt e v)) es) vs'
  (** Returns a list of all vertices that have no incoming edge  *)
    

  let topological_sort:  t ->vertex list = fun ((vs, es) as g) ->
    let rec topological_sort_helper:  t ->vertex list ->vertex list
      = fun ((vs, es) as g) sorted_vs ->
      let no_incoming_vs = non_tgt_vertices g in
      (** graph is empty case *)
      if List.length no_incoming_vs = 0
      then if not (is_empty g)
           then raise CyclicGraphException
           else sorted_vs
      else
        let new_g = List.fold_left remove_vertex g no_incoming_vs in
        topological_sort_helper new_g (sorted_vs @ no_incoming_vs) in
    topological_sort_helper g []
end
