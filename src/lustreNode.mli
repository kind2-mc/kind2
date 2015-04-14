(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

(** A Lustre node

    Nodes are normalized for easy translation into a transition system,
    mainly by introducing new variables. A LustreExpr.t does not
    contain node calls, temporal operators or expressions under a pre
    operator. Node equations become a map of identifiers to expressions
    in [node_eqs], all node calls are in [node_calls] as a list of tuples
    containing fresh variables the node output is assigned to and the
    expressions for the node input.

    The node signature as input and output variables as well as its
    local variables is in [node_inputs], [node_outputs] and
    [node_vars], respectively. Local constants are propagated and do
    not need to be stored. The inputs of a node can be extended by
    constant state variables in [node_oracles] for the initial value
    of unguarded pre operations.

    Assertions, properties to prove and contracts as assumptions and
    guarantees are lists of expressions in [node_asserts], [node_props],
    [node_requires], and [node_ensures].

    The flag [node_is_main] is set if the node has been annotated as
    main, it is not checked if more than one node or no node at all may
    have that annotation. 

    @author Christoph Sticksel
*)

open Lib

(** A call of a node *)
type node_call = 

  { 

    (** Position of node call in input file *)
    call_pos : position;

    (** Name of called node *)
    call_node_name : LustreIdent.t;
    
    (** Boolean activation condition *)
    call_clock : StateVar.t option;

    (** Variables for input parameters *)
    call_inputs : StateVar.t LustreIndex.t;

    (** Variables providing non-deterministic inputs *)
    call_oracles : StateVar.t list;

    (** Variables providing non-deterministic inputs *)
    call_outputs : StateVar.t LustreIndex.t;

    (** Variables capturing the observer streams *)
    call_observers : StateVar.t list;

    (** Expression for initial return values *)
    call_defaults : LustreExpr.t LustreIndex.t;

  }


(** A contract is a position, a list of observers for the
    requirements, a list of observers for the ensures, and an observer
    for the implication between its requirements and ensures. *)
type contract =
  { 

    (* Position of the contract in the input *)
    contract_pos: position;

    (* One observer for each requirement *)
    contract_reqs : StateVar.t list;

    (* One observer for each ensures *)
    contract_enss : StateVar.t list;

    (* One observer for the implication between requirements and ensures *)
    contract_impl : StateVar.t }

(** Bound for index variable, or fixed value for index variable *)
type 'a bound_or_fixed = 
  | Bound of 'a  (* Upper bound for index variable *)
  | Fixed of 'a  (* Fixed value for index variable *)


(** A Lustre node

    Every state variable occurs exactly once in [inputs], [outputs],
    [oracles], and [observers], and at most once on the left-hand side
    of [equations] and [calls]. *)
type t = 

  { 

    (** Name of the node *)
    name : LustreIdent.t;

    (** Input streams defined in the node

        Each input is indexed with an integer correpsonding to its
        position in the formal parameters. If the stream is indexed
        the indexes are appended to the position index. *)
    inputs : StateVar.t LustreIndex.t;

    (** Oracle inputs added to the node inputs

        Input streams added to the node to obtain non-deterministic
        values for the initial values of unguarded pre operators, and
        for undefined streams. In the first case, the state variable
        is constant.  *)
    oracles : StateVar.t list;

    (** Output streams defined in the node

        Each output is indexed with an integer correpsonding to its
        position in the formal parameters. If the stream is indexed
        the indexes are appended to the position index. If the node
        has only one output, the index of the output is empty. *)
    outputs : StateVar.t LustreIndex.t;

    (** Observer outputs added to the node outputs

        The order of the list is irrelevant, we are doing dependency
        analysis and cone of influence reduction later. *)
    observers : StateVar.t list;

    (** Local variables of node

        The order of the list is irrelevant, we are doing dependency
        analysis and cone of influence reduction later. *)
    locals : StateVar.t LustreIndex.t list;

    (** Equations for local and output variables *)
    equations : (StateVar.t * LustreExpr.expr bound_or_fixed list * LustreExpr.t) list;

    (** Node calls inside the node *)
    calls : node_call list;

    (** Assertions of node *)
    asserts : LustreExpr.t list;

    (** Proof obligations for the node *)
    props : (StateVar.t * TermLib.prop_source) list;

    (** The contracts of the node: an optional global contract and a
        list of named mode contracts *)
    contracts : contract option * (string * contract) list;

    (** Flag node as the top node *)
    is_main : bool;

  }

(** The empty node *)
val empty_node : LustreIdent.t -> t

(** Pretty-print a node *)
val pp_print_node : bool -> Format.formatter -> t -> unit 

(** Pretty-print a node *)
val pp_print_node_debug : Format.formatter -> t -> unit 

(** Pretty-print a node call *)
val pp_print_call : bool -> Format.formatter -> node_call -> unit 

(** {1 Node Lists} *)

(** Return the node of the given name from a list of nodes *)
val node_of_name : LustreIdent.t -> t list -> t 

(** Return true if a node of the given name exists in the a list of nodes *)
val exists_node_of_name : LustreIdent.t -> t list -> bool 

(** Return name of the first node annotated with --%MAIN.  Raise
    [Not_found] if no node has a --%MAIN annotation or [Failure
    "find_main"] if more than one node has a --%MAIN annotation.
*)
val find_main : t list -> LustreIdent.t

(** Return the identifier of the top node

    Fail with [Invalid_argument "ident_of_top"] if list of nodes is empty *)
val ident_of_top : t list -> LustreIdent.t 

(** {2 State Variable Instances} *)

(** We keep a map of the variables of a node to variables in called
    nodes to propagate values of a model to the called nodes. A
    variable in a called node gets its value from an state variable in
    the caller, which is an instance of it. 

    A state variable in a node may be the instance of several state
    variables, if a state variable serves as input to multiple
    callees.

    Variables capturing the outputs of a called node are instances of
    the output variables in the callee; variables providing input to
    the caller are instances of the input variables of the
    callee. Stateful local variables of a callee are lifted as state
    variables of the caller, the latter are then instances of the
    former. 

    A state variable may also be an instance of a state variable in
    the same node if an equation between two state variables was
    eliminated. *)

(** Named stream at a position *)
type state_var_instance = position * LustreIdent.t * StateVar.t


(** Return state variables that values of this state variable should
    be propagated to  *)
val get_state_var_instances : StateVar.t -> state_var_instance list

(** Mark state variable as instance of another state variable to
    be able to propagate values of the first to the second

    [set_state_var_instance sv1 pos n sv2] marks the state variable
    [sv1] to be an instance of [sv2], where the latter occurs at
    position [pos] in node [n]. Usually [sv1] is in the caller and
    [sv2] is in the callee. *)
val set_state_var_instance : StateVar.t -> position -> LustreIdent.t -> StateVar.t -> unit

(** {2 Sources} *)

(** Every state variable is either defined in a node, or was
    introduced in pre-processing.

    - [Input], [Output] or [Local] state variables correspond to input,
    output and local streams defined in a node, respectively. 

    - [Abstract] state variables were introduced as definitions during
    pre-processing 

    - [Oracle] state variables are additional input variables
     introduced to non-deterministivcally give a value to unguarded
     [pre] expressions, or to unconstrained streams

    - [Observer] state variables are additional output variables that
     lift the values of properties to the calling node. *)


(** Source of a state variable *)
type state_var_source =
  | Input
  | Output
  | Local
  | Ghost
  | Abstract
  | Oracle
  | Observer


(** Pretty-print a source of a state variable *)
val pp_print_state_var_source : Format.formatter -> state_var_source -> unit 

(** Set source of state variable *)
val set_state_var_source : StateVar.t -> state_var_source -> unit

(** Get source of state variable *)
val get_state_var_source : StateVar.t -> state_var_source

(** Return true if the state variable should be visible to the user,
    false if it was created internally

    Return [true] if the source of the state variable is either
    [Input], [Output], or [Local], and [false] otherwise. *)
val state_var_is_visible : StateVar.t -> bool

(** Return true if the state variable is an input *)
val state_var_is_input : StateVar.t -> bool

(** Return true if the state variable is an output *)
val state_var_is_output : StateVar.t -> bool

(** Return true if the state variable is a local variable *)
val state_var_is_local : StateVar.t -> bool












(*


(** Order the equations of the node such that an equation defining a
   variable always occurs before all equations using the variable *)
val equations_order_by_dep : t list -> t -> t

(** If node contains an equation [x = y], and [y] captures the output
    of a node, substitute [x] in the node call and the equation and the
    definition of [x] if it is local. *)
val solve_eqs_node_calls : t -> t

(** Return all stateful variables from expressions in a node *)
val stateful_vars_of_node : t -> StateVar.StateVarSet.t
*)

(*
(** produces the set of all state variables contained in any of the nodes in the
    given list 
*)
val extract_state_vars : t list -> StateVar.StateVarSet.t
*)
(*
(** Reduce list of nodes to list of nodes called by the node and its
    subnodes, include the given node. The list of nodes is partially
    ordered by dependencies, such that called nodes appear before
    their callers. *)
val reduce_to_coi : t list -> LustreIdent.t -> StateVar.t list -> t list 

val reduce_wo_coi : t list -> LustreIdent.t -> t list 

val reduce_to_props_coi : t list -> LustreIdent.t -> t list 
*)
(*

(** 
reduce_to_separate_property_cois [nodes] [main_name]

Given that [nodes] is the set of nodes in the lustre program and
[main_name] is the name of the main node, return a map which
maps the identifier of each property and assert stream to the
a list of all nodes in that assert or property's cone of influence. 
*)
val reduce_to_separate_property_cois : t list -> LustreIdent.t -> (t list) StateVar.StateVarMap.t 

*)


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
