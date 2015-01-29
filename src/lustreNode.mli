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


(** A call of a node *)
type node_call = 

  { 

    (** Variables capturing the outputs *)
    call_returns : StateVar.t list;

    (** Variables capturing the observer streams *)
    call_observers : StateVar.t list;

    (** Boolean activation condition *)
    call_clock : StateVar.t option;

    (** Name of called node *)
    call_node_name : LustreIdent.t;
    
    (** Position of node call in input file *)
    call_pos : Lib.position;

    (** Expressions for input parameters *)
    call_inputs : StateVar.t list;

    (** Expression for initial return values *)
    call_defaults : LustreExpr.t list;

  }

(** A Lustre node *)
type t = 

  { 

    (** Name of the node *)
    name : LustreIdent.t;

    (** Input variables of node

        The order of the list is important, it is the order the
        parameters in the declaration. *)
    inputs : (StateVar.t * LustreIdent.index) list;

    (** Oracle inputs of node

        The order of the list is important, it is the order the
        parameters in the declaration. *)
    oracles : StateVar.t list;

    (** Output variables of node

        The order of the list is important, it is the order the
        parameters in the declaration. *)
    outputs : (StateVar.t * LustreIdent.index) list;

    (** Observer outputs *)
    observers : StateVar.t list;

    (** Local variables of node

        The order of the list is irrelevant, we are doing dependency
        analysis and cone of influence reduction later. *)
    locals : (StateVar.t * LustreIdent.index) list;

    (** Equations for local and output variables *)
    equations : (StateVar.t * LustreExpr.t) list;

    (** Node calls with activation condition: variables capturing the
        outputs, the Boolean activation condition, the name of the
        called node, expressions for input parameters and expression
        for initialization *)
    calls : node_call list;

    (** Assertions of node *)
    asserts : LustreExpr.t list;

    (** Proof obligations for node *)
    props : (StateVar.t * TermLib.prop_source) list;

    (** Contract for node, assumptions *)
    requires : LustreExpr.t list;

    (** Contract for node, guarantees *)
    ensures : LustreExpr.t list;

    (** Node is annotated as main node *)
    is_main : bool;

    (** Dependencies of the output variables on input variables *)
    output_input_dep : int list list;

    (** Index of last abstraction state variable *)
    fresh_state_var_index : Numeral.t ref;

    (** Index of last oracle state variable *)
    fresh_oracle_index : Numeral.t ref;

    (** Map of state variables to their oracles *)
    state_var_oracle_map : StateVar.t StateVar.StateVarHashtbl.t;

    (** Map of expressions to state variables *)
    expr_state_var_map : StateVar.t LustreExpr.ExprHashtbl.t;

  }

(** The empty node *)
val empty_node : LustreIdent.t -> t

(** Pretty-print a node *)
val pp_print_node : bool -> Format.formatter -> t -> unit 

(** Pretty-print a node call *)
val pp_print_call : bool -> Format.formatter -> node_call -> unit 

(** Return the node of the given name from a list of nodes *)
val node_of_name : LustreIdent.t -> t list -> t 

(** Return the identifier of the top node

    Fail with [Invalid_argument "ident_of_top"] if list of nodes is empty *)
val ident_of_top : t list -> LustreIdent.t 

(** Order the equations of the node such that an equation defining a
   variable always occurs before all equations using the variable *)
val equations_order_by_dep : t list -> t -> t

(** If node contains an equation [x = y], and [y] captures the output
    of a node, substitute [x] in the node call and the equation and the
    definition of [x] if it is local. *)
val solve_eqs_node_calls : t -> t

(** Return all stateful variables from expressions in a node *)
val stateful_vars_of_node : t -> StateVar.StateVarSet.t

(** Return name of the first node annotated with --%MAIN.  Raise
    [Not_found] if no node has a --%MAIN annotation or [Failure
    "find_main"] if more than one node has a --%MAIN annotation.
*)
val find_main : t list -> LustreIdent.t

(*
(** produces the set of all state variables contained in any of the nodes in the
    given list 
*)
val extract_state_vars : t list -> StateVar.StateVarSet.t
*)

(** Reduce list of nodes to list of nodes called by the node and its
    subnodes, include the given node. The list of nodes is partially
    ordered by dependencies, such that called nodes appear before
    their callers. *)
val reduce_to_coi : t list -> LustreIdent.t -> StateVar.t list -> t list 

val reduce_wo_coi : t list -> LustreIdent.t -> t list 

val reduce_to_props_coi : t list -> LustreIdent.t -> t list 

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
  
