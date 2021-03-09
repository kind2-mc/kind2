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

(** Cone of influence reduction and dependency ordering of equations
    
    @author Christoph Sticksel *)


(** {1 Dependency order} *)

(** Return equations of node in topological order of their dependencies 

    [order_equations i d n] takes as input a Lustre node [n] and an
    association list [d] of node names to a map from output indexes to
    the list of input indexes the output variable depends on. Return
    the equations of [n] ordered such that each equation comes after
    the equations defining the variables occurring on its right-hand.

    Along with the list of equations, it returns a list and a map.
    The list contains pairs consisting of a variable and a set of
    variables the first variable depends on.
    The map is such that for each output identified by its position
    indicates which positions in the inputs it depends on.
    The input parameter [d] must contain such a map for
    each called node.

    If the flag [i] is true, consider the equations for the inital
    state only, otherwise consider the equations for post-initial
    states only. 

    Fail with a parse error if a variable definition is cyclic, that
    is, the variable on the left-hand side of the equation occurs in
    the definition of a variable on the right-hand side. 

    For the detection of cycles also consider definitions of called nodes
    by using the map of outputs to their dependent inputs. If in the node
    {[node N (i: t) returns (o: t)]}
    the output [o] depends on the input [i], then the node call [N(x)]
    must not occur in the definition of [x]. If the output [o] does not
    depend on the input [i], [N(x)] may occur in the definition of [x].

    In particular, if a node is viewed as its contract only, the
    implemention is omitted and node calls never cause cycles in
    defintions. One could argue that since the implementation is not
    known, the outputs should depend on all inputs, but this might
    trigger spurious cycles. We view this more as a realizability
    issue and we could implement separately a check if a node as
    specified by its contract can be implemented without introducing a
    depency on the inputs.

    Array typed variables are not considered in the cycle detection,
    and this may lead to actual cycles not rejected. This is
    difficult, because we would need to consider each occurrence of an
    array typed variable together with its indexes. Then we would need
    to compare indexes if a state variable occurs on a path with the
    same index. A syntactic comparison would again miss some cycles,
    and we would need to evaluate the indexes for a precise
    comparison. This is probably too much effort for what it is worth. *)
val order_equations : bool -> (
  LustreIdent.t * (
    LustreIndex.index list LustreIndex.t *
    LustreIndex.index list LustreIndex.t
  )
) list ->
LustreNode.t ->
LustreNode.equation list *
(StateVar.t * StateVar.StateVarSet.t) list *
LustreIndex.index list LustreIndex.t

(** Return the set of dependencies of each state variable

    See [order_equations] for further details. *)
val state_var_dependencies : bool -> (
  LustreIdent.t * (
    LustreIndex.index list LustreIndex.t *
    LustreIndex.index list LustreIndex.t
  )
) list ->
LustreNode.t ->
(StateVar.t * StateVar.StateVarSet.t) list *
LustreIndex.index list LustreIndex.t


(** {1 Cone of influence reduction} *)


(** Return [true] if the node is flagged as abstract in
    [abstraction_map]. Default to [false] if the node is not in the
    map. *)
val node_is_abstract : Analysis.param -> LustreNode.t -> bool

(** Return a node hierarchy reduced to the cone of influence of
    properties and contracts, given a list of which nodes should be
    abstracted. 

    [slice_to_abstraction r a s] takes the parameters of an analysis,
    which contains an association map [m] of scopes to a flag that is
    [true] if the node of that name is to be abstracted to its
    contract by omitting its implementation. Return a node hierarchy
    based on [s], reduced to the cone of influence of the properties
    and contracts if [r] is [true]. Otherwise, only abstraction is
    applied.

    For each node, start with a copy of the node without equations and
    node calls. Maintain a set of state variables, called the roots of
    the cone of influence, and move all equations and node calls that
    define a root to the copy of the node. Add all state variables as
    new roots that occur on the right-hand side of a moved equation,
    or are an inputs, oracles or the clock of a moved node call. Slice
    called nodes before the calling nodes. If an equation defines a
    record, tuple or array, the equations for each element are kept as
    soon as one of the elements is in the cone of influence.

    The roots of a node always contain its outputs and the state
    variables occurring in contracts, except for the top node. The top
    node is never called and we can safely change its signature. It
    would be possible to analyze each call of a node to see exactly
    which of its inputs and outputs of are in the cone of influence,
    then modify the signature appropriately, and adjust all calls to
    this modified signature. However, this non-local analyisis is
    probably more complicated and error-prone than it is worth.

    If a node is sliced to its implementation, add the property state
    variables and all state variables in assertions.

    State variables in assertions are considered to be roots, because
    they potentially constrain a state variable in the cone of
    influence together with a state variable not in the cone of
    influence. In this case, both state variables are in the cone of
    influence. We may add a better analysis later. *)
val slice_to_abstraction :
    ?preserve_sig:bool ->
    bool -> Analysis.param -> LustreNode.t SubSystem.t ->
    LustreNode.t SubSystem.t

val slice_to_abstraction_and_property :
    ?preserve_sig:bool ->
    Analysis.param -> StateVar.StateVarSet.t ->
    LustreNode.t SubSystem.t ->
    LustreNode.t SubSystem.t 

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
