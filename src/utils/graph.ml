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
  val pp_print_t: Format.formatter -> t -> unit
end
                        
exception IllegalGraphOperation
(** The exception raised when an illegal edge is added *)
exception CyclicGraphException of string list
(** The exception raised when topological sort is tried on cyclic graph  *)


module type S = sig 
  
  type vertex
  (** The vertex type *)
    
  type edge
  (** The edge type to represent line between two vertices *)

  val mk_edge: vertex -> vertex -> edge   
  (** Make an [edge] from two vertices  *)

  val get_source_vertex: edge -> vertex
  (** Get the source [vertex] from an [edge] *)

  val is_vertex_source: edge -> vertex -> bool
  (** Checks if the [vertex] is the source [vertex] *)

  val get_target_vertex: edge -> vertex
  (** Get the target [vertex] from an [edge] *)

  val is_vertex_target: edge -> vertex -> bool
  (** Checks if the [vertex] is the target [vertex] *)
    
  type vertices
  (** Set of vertices *)

  type edges
  (** Set of edges *)

  type t
  (** The graph type  *)

  val empty:  t
  (** The empty graph  *)

  val is_empty:  t -> bool
  (** Check if the graph is empty *)

  val singleton: vertex -> t
  (** returns a singleton graph *)

  val is_singleton: t -> bool
  (** returns true if the graph has only one vertex *)
    
  val add_vertex:  t ->  vertex ->  t
  (** Add a [vertex] to a graph  *)

  val mem_vertex: t -> vertex -> bool
  (** returns true if the vertex is in the graph *)

  val get_vertices: t -> vertices
  (** get all vertices in the graph *)
    
  val add_edge:  t ->  edge ->  t
  (** Add an [edge] to a graph  *)

  val remove_vertex: t ->  vertex ->  t
  (** Remove the [vertex] and its associated [edges] from the graph *)

  val remove_edge:  t ->  edge ->  t
  (** Remove an [edge] from a graph *)                             

  val connect: t -> vertex -> t
  (** Connect [vertex] to all the other vertices in the given graph *)

  val is_point_graph: t -> bool
  (** Returns true if the graph has no edges *)

  val union: t -> t -> t
  (** Unions two graphs *)

  val sub_graph: t -> vertices -> t    
  (** Gets a subgraph along with appropriate [edges] of given graph from a given set of [vertices] *)

  val map: (vertex -> vertex) -> t -> t
  (** Maps the [vertices] using the argument mapping, the structure should remain intact.
     Caution: The callee function (or the programmer) is supposed to make sure 
     it is not a surjective mapping to make sure that the graph structure is preserved. *)
    
  val topological_sort:  t ->  vertex list
  (** Computes a topological ordering of vertices 
   *  or throws an [CyclicGraphException] if the graph is cyclic.
   *  Implimentation is of this function is based on Kahn's algorithm *)


  val reachable: t -> vertex -> vertices

  val to_vertex_list: vertices -> vertex list
    
  val pp_print_vertex: Format.formatter -> vertex -> unit
  (** Pretty print a vertex *)

  val pp_print_vertices: Format.formatter -> vertices -> unit

  val pp_print_edge: Format.formatter -> edge -> unit

  val pp_print_edges: Format.formatter -> edges -> unit

  val pp_print_graph: Format.formatter -> t -> unit

end

module Make (Ord: OrderedType) = struct
  
  type vertex = Ord.t
  (** the vertex type *)

  let pp_print_vertex: Format.formatter -> vertex -> unit = fun ppf v -> 
    Ord.pp_print_t ppf v
    
  type edge = vertex * vertex
  (** directed edge type is between two vertices source and target *)

  let pp_print_edge: Format.formatter -> edge -> unit = fun ppf (s, t) ->
    Format.fprintf ppf "(%a) -> (%a)"
      pp_print_vertex s
      pp_print_vertex t 

  let mk_edge: vertex -> vertex ->  edge
    = fun s t -> (s, t)
  (** Make an edge given the source and the target vertices *)

  let get_source_vertex: edge -> vertex = fst
  (** Get the source vertex from an edge *)

  let get_target_vertex: edge -> vertex = snd
  (** Get the target vertex from an edge *)

  let is_vertex_source: edge -> vertex -> bool = fun e v ->
    Ord.compare v (get_source_vertex e) = 0
  (** Checks if the [vertex] is the source [vertex] *)

  let is_vertex_target: edge -> vertex -> bool = fun e v ->
    Ord.compare v (get_target_vertex e) = 0
  (** Checks if the [vertex] is the source [vertex] *)

  let is_vertex_in_edge: edge -> vertex -> bool = fun (s, t) v ->
    Ord.compare v s = 0 || Ord.compare v t = 0
    
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
                     if c <> 0 then c else Ord.compare v12 v22
               end))
    let flatten: t list -> t = fun sets ->
      List.fold_left union empty sets
  end 
  (** A set of edges *)

  type vertices = VSet.t
  (** type alias for set of vertices *)

  let pp_print_vertices: Format.formatter -> vertices -> unit = fun ppf vs ->
    Lib.pp_print_list pp_print_vertex ", " ppf (VSet.elements vs)

  type edges = ESet.t
  (** type alias for set of  edges *)

  let pp_print_edges: Format.formatter -> edges -> unit = fun ppf es ->
    Lib.pp_print_list pp_print_edge ", " ppf (ESet.elements es)
             
  type t = vertices * edges
  (** A graph is a set of vertices and set of  edges  *)

  let pp_print_graph: Format.formatter -> t -> unit = fun ppf (vs, es) ->
    Format.fprintf ppf "Vertices: %a\nEdges: %a"
      pp_print_vertices vs
      pp_print_edges es
         
  let get_vertices: t -> vertices = fst

  let get_edges: t -> edges = snd

  let empty = (VSet.empty, ESet.empty)
  (** An empty trivial graph contains no vertices and no  edges *)

  let is_empty: t -> bool = fun  (vs, es) ->
    VSet.is_empty vs 
  (** Check if the graph is empty *)

  let singleton: vertex -> t = fun v ->
    (VSet.singleton v, ESet.empty)
  (** returns a singleton graph *)

  let is_singleton: t -> bool = fun (vs, es) ->
    VSet.cardinal vs = 1 && ESet.cardinal es = 0
    
  let mk_edge: vertex -> vertex -> edge
    = fun v1 v2 -> (v1, v2)
  (** Make an edge from two vertices  *)

  let add_vertex: t -> vertex -> t
    = fun (vs, es) v -> (VSet.add v vs,  es) 
  (** add avertex to a graph  *)

  let mem_vertex: t -> vertex -> bool
    = fun (vs, es) v -> VSet.mem v vs
    
  let add_edge: t -> edge -> t
    = fun (vs, es) (src, tgt) ->
    if VSet.mem src vs && VSet.mem tgt vs
    then (vs,  ESet.add (src, tgt) es)
    else raise IllegalGraphOperation
  (** add an  edge to a graph  *)
                    
  let find_edges_of_vertex: t -> vertex -> edges
    = fun (vs, es) v -> ESet.filter (fun e -> is_vertex_in_edge e v) es 
                      
  let remove_vertex: t -> vertex -> t
    = fun (vs, es) v ->
    (VSet.remove v vs
    , ESet.filter (fun e -> not (is_vertex_in_edge e v)) es)           
  (** Remove the [vertex] and its associated [edges] from the graph *)

  let remove_edge:  t ->  edge ->  t
    = fun (vs, es) e -> (vs, ESet.remove e es) 
  (** Remove an [edge] from a graph *)                             

  let remove_edges: t -> edges -> t
    = fun (vs, es) es' -> (vs, ESet.diff es es') 
                      
  let non_target_vertices: t -> vertices
    = fun (vs, es) ->
    VSet.filter (fun v -> ESet.for_all (fun e -> not (is_vertex_target e v)) es) vs
  (** Returns a list of all vertices that have no incoming edge  *)

  let non_source_vertices: t -> vertices
    = fun (vs, es) ->
    VSet.filter (fun v -> ESet.for_all (fun e -> not (is_vertex_target e v)) es) vs
  (** Returns a list of all vertices that have no outgoing edges  *)
    
  let connect: t -> vertex -> t = fun g v ->
    let vs = get_vertices g in
    (VSet.add v vs
    , VSet.fold (fun v' es' -> ESet.add (mk_edge v v') es')
        (get_vertices g)
        (get_edges g))
  (** Connect [vertex] that is already in the graph to all the other vertices in the graph *)


  let sub_graph: t -> vertices -> t = fun g vs ->
    ( vs
    , ESet.filter (fun (src, tgt) -> VSet.mem src vs && VSet.mem tgt vs)
        (get_edges g))
  (** Gets a subgraph with appropriate edges of given graph from a given set of vertices *)
                                          
  let is_point_graph: t -> bool = fun (vs, es) ->
    ESet.is_empty es
  (** Returns true if the graph has no edges *)
    
  let union: t -> t -> t = fun (v1s, e1s) (v2s, e2s) ->
    (VSet.union v1s v2s, ESet.union e1s e2s) 
  (** Unions two graphs *)

  let map: (vertex -> vertex) -> t -> t = fun f (vs, es) ->
    let map_edge: (vertex -> vertex) -> edge -> edge = fun f (s, t) -> (f s, f t) in 
    let vs' = VSet.map f vs in
    let es' = ESet.map (map_edge f) es in
    (vs', es')
  (** Maps the [vertices] using the argument mapping, the structure should remain intact.
     Caution: The callee function (or the programmer) is supposed to make sure 
     it is not a surjective mapping to make sure that the graph structure is preserved. *)
    
  let topological_sort: t -> vertex list = fun ((vs, es) as g) ->
    let rec topological_sort_helper: t -> vertex list -> vertex list
      = fun ((vs, es) as g) sorted_vs ->
      let no_outgoing_vs = non_source_vertices g in

      Log.log L_trace
        "-----------\nGraph state:\n %a\nSorted vertices: %a\n new non source vertices: %a\n-------------"	
        pp_print_graph g	
        (Lib.pp_print_list pp_print_vertex ",") sorted_vs	
        pp_print_vertices no_outgoing_vs ;
      (** graph is empty case *)
      if VSet.is_empty no_outgoing_vs
      then if not (is_empty g)
           then raise (CyclicGraphException
                         (List.map (Lib.string_of_t pp_print_vertex) (VSet.elements vs)))
           else sorted_vs
      else
        let new_g = VSet.fold (fun v g' -> remove_vertex g' v) no_outgoing_vs g in
        topological_sort_helper new_g (sorted_vs @ VSet.elements no_outgoing_vs)
    in topological_sort_helper g []
  (** Computes a topological ordering of vertices 
   *  or throws an [CyclicGraphException] if the graph is cyclic.
   *  Implimentation is based on Kahn's algorithm 
   * https://en.wikipedia.org/wiki/Topological_sorting *)

  let reachable: t -> vertex -> vertices =
    fun ((vs, es) as g) origin_v ->
    let rec reachable_from_aux: vertices -> vertex -> t -> vertices
      = fun acc sv ((vs, es)  as g) ->
      Log.log L_trace
        "-----------\nGraph state:\n %a\naccumulated vertices: %a\n current vertex vertices: %a\n-------------"	
        pp_print_graph g	
        (Lib.pp_print_list pp_print_vertex ",") (VSet.elements acc)	
        pp_print_vertex sv ;
      if VSet.mem sv acc
      then acc (* we have already visited this vertex so skip *)
      else
        (* get all edges that have sv as source *)
        let new_edgs = (ESet.filter (Lib.flip is_vertex_source sv) es) in
        let vs' = List.map (get_target_vertex) (ESet.elements new_edgs) in
        (* Get the new vertices to be analysed  *)
        let new_vs = (VSet.diff (VSet.of_list vs') acc) in
        VSet.flatten (List.map (fun v ->
                          VSet.add v (reachable_from_aux
                                        (VSet.union acc (VSet.remove v new_vs))
                                        v
                                        (remove_edges g new_edgs))) (VSet.elements new_vs)) in  
    if (VSet.mem origin_v vs) then
      reachable_from_aux VSet.empty origin_v g 
    else VSet.empty
   (** Returns all the vertices rechable from the input vertex in the graph  *)

  let to_vertex_list: vertices -> vertex list = VSet.elements
    
    
end
