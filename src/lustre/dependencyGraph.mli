(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

(** Create a dependency graph from a transition system *)

module Vertex : Graph.OrderedType with type t = StateVar.t
module VarGraph : Graph.S with type vertex = Vertex.t

val dependency_graph_of_system : Term.TermSet.t -> TransSys.t -> VarGraph.t
(** [dependency_graph_of_system definition_set trans_sys] constructs a
    dependency graph representing the dependencies between state variables in
    the given transition system.

    @param definition_set A set of terms which are to be treated as dependencies
    @param trans_sys
      The transition system from which dependencies are extracted.
    @return
      A graph representing variable dependencies. The state variable `sv1`
      depends on `sv2` if there is the edge `sv1 -> sv2` *)

val cone_of_influence :
  VarGraph.t -> StateVar.StateVarSet.t -> StateVar.StateVarSet.t
(** [cone_of_influence properties dependency_graph] constructs the set of state
    variables which are depended upon by [properties]

    @param dependency_graph The dependency graph for the system
    @param roots Where the cone of influence starts
    @return The set of variables upon which [properties] depend *)

val pp_print_dot :
  ?cone_of_influence:StateVar.StateVarSet.t ->
  Format.formatter ->
  VarGraph.t ->
  unit
(** [pp_print_dot ?cone_of_influence ppf graph] prints a graphviz DOT
    representation of the given variable graph [graph] to the formatter [ppf].

    @param cone_of_influence
      (optional) A set of state variables that should be highlighted in the
      output. If omitted, no special highlighting is applied.
    @param ppf The formatter to which the DOT representation is printed.
    @param graph The dependency_graph graph to be printed. *)
