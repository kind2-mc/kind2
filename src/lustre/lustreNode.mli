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

(** Internal representation of a Lustre node

    Nodes are normalized for easy translation into a transition
    system, mainly by introducing new variables. 



    The node equations taken together become a map of state variables
    to expressions. All node calls are factored out with fresh state
    variables as inputs and outputs.

    The node signature as input and output variables as well as its
    local variables is in [inputs], [outputs] and [locals],
    respectively. Local constants are propagated and do not need to be
    stored. The inputs of a node can be extended by constant state
    variables in [oracles] for the initial value of unguarded pre
    operations.

    Assertions, properties to prove and contracts as assumptions and
    guarantees are lists of expressions in [asserts], [props],
    contracts fo into [global_contracts] and [mode_contracts].

    The flag [node_is_main] is set if the node has been annotated as
    main, it is not checked if more than one node or no node at all may
    have that annotation. 

    @author Christoph Sticksel
*)

open Lib

(** {1 Types} *)

(** Call condition: activate or restart *)
type call_cond =
  | CActivate of StateVar.t
  | CRestart of StateVar.t

(** A call to a node 

    Calls are uniquely identified by the position, no two calls may
    share the same position, therefore the [call_pos] must not be a
    dummy position. *)
type node_call = {

  call_pos : position;
  (** Position of node call in input file *)

  call_node_name : LustreIdent.t;
  (** Identifier of the called node *)
  
  call_cond : call_cond list;
  (** Boolean activation and/or restart conditions if any *)

  call_inputs : StateVar.t LustreIndex.t;
  (** Variables for actual input parameters 

      The keys of the index match those in the {!t.inputs} field of
      the called node. *)

  call_oracles : StateVar.t list;
  (** Variables providing non-deterministic inputs

      The length of the list is equal to the length of the list in
      the {!t.oracles} field of the called node. *)

  call_outputs : StateVar.t LustreIndex.t;
  (** Variables capturing the outputs 

      The keys of the index match those in the {!t.outputs} field of the
      called node. *)

  call_defaults : LustreExpr.t LustreIndex.t option;
  (** Expressions for initial return values

      This value should be [None] for node calls on the base clock,
      and [Some l] for node calls with a clock. A node call with a
      clock may only have [None] here if it occurs directly under a
      [merge] operator. 

      If the option value is not [None], the keys of the index match
      those in the {!t.outputs} field of the called node. *)

}


(** Source of a state variable *)
type state_var_source =
| Input   (** Declared input variable *)
| Output  (** Declared output variable *)
| Local   (** Declared local variable *)
| KLocal  (** Kind 2 invisible local variable *)
| Call    (** Tied to a node call. *)
| Ghost   (** Declared ghost variable *)
| KGhost  (** Kind 2 invisible ghost variable *)
| Oracle  (** Generated non-deterministic input *)
(*| Alias of
  StateVar.t * state_var_source option (** Alias for another state variable. *) *)


(** A contract. *)
type contract = LustreContract.t


(** Type of left hand side of equations. 

    An equation defines defines the state variable [state_var], and a list
    [bounds] of indexes.

    An array can be defined either only at a given index, or at all
    indexes, when the expression on the right-hand side is interpreted
    as a function of the running variable of the index.  *)
type equation_lhs = StateVar.t * LustreExpr.expr LustreExpr.bound_or_fixed list


(** An equation is a tuple [(eqlhs, expr)] that defines a possibly indexed
    state variable as an expression. *)
type equation = equation_lhs * LustreExpr.t


(** A Lustre node

    Every state variable occurs exactly once in {!t.inputs},
    {!t.outputs}, and {!t.oracles}, and at most once on the left-hand
    side of {!t.calls}. If the state variable is of array type, there
    may be more than one occurrence of it in {!t.equations}, each
    defining the index variable at a different value with
    {!bound_or_fixed.Fixed}. If the state variable is not an array, or
    all its bounds are {!bound_or_fixed.Bound}, then it occurs at most
    once on the left-hand side of {!t.equations}. *)
type t = {

  name : LustreIdent.t;
  (** Name of the node *)

  is_extern : bool;
  (** Is the node extern? *)

  instance : StateVar.t;
  (** Distinguished constant state variable uniquely identifying the
      node instance *)

  init_flag : StateVar.t;
  (** Distinguished state variable to be true in the first
     instant only *)

  inputs : StateVar.t LustreIndex.t;
  (** Input streams defined in the node

      The inputs are considered as a list with an integer indexes
      corresponding to their position in the formal parameters if
      there is more than one input parameter. If there is only one
      input parameter, the list index is omitted, the index is empty
      if there are no input parameters. *)

  oracles : StateVar.t list;
  (** Oracle inputs added to the node inputs

      Input streams added to the node to obtain non-deterministic
      values for the initial values of unguarded pre operators. The
      state variables are constant. *)

  outputs : StateVar.t LustreIndex.t;
  (** Output streams defined in the node

      The outputs are considered as a list with an integer indexes
      corresponding to their position in the formal parameters. *)

  locals : StateVar.t LustreIndex.t list;
  (** Local variables of node

      The order of the list is irrelevant, we are doing dependency
      analysis and cone of influence reduction later. *)

  equations : equation list;
  (** Equations for local and output variables *)

  calls : node_call list;
  (** Node calls inside the node *)

  asserts : (position * StateVar.t) list;
  (** Assertions of node *)

  props : (StateVar.t * string * Property.prop_source) list;
  (** Proof obligations for the node *)

  contract : contract option ;
  (** Contract. *)

  is_main : bool;
  (** Flag node as the top node *)

  is_function : bool;
  (** Node is actually a function *)

  state_var_source_map : state_var_source StateVar.StateVarMap.t;
  (** Map from a state variable to its source 

      Variables that were introduced to abstract expressions do not
      have a source. *)

  oracle_state_var_map : StateVar.t StateVar.StateVarHashtbl.t;
  (** Map from state variables to state variables providing a
      non-deterministic pre-initial value *)

  state_var_expr_map : LustreExpr.t StateVar.StateVarHashtbl.t;

  silent_contracts : string list ;
  (** Contracts that were silently loaded. *)

  assumption_svars: StateVar.StateVarSet.t;

}

(** Instance of state vars as streams with their position *)
type state_var_instance = position * LustreIdent.t * StateVar.t

type contract_item_type =
    | Assumption | WeakAssumption | Guarantee | WeakGuarantee | Require | Ensure
(** A definition of a state variable in the initial Lustre program.
  For a given state var s, it indicates the position p of an expression e that defines s
  as well as the corresponding index i, such that s defined by the value of e at index i. *)
type state_var_def =
  | CallOutput of position * LustreIndex.index
  | ProperEq of position * LustreIndex.index
  | GeneratedEq of position * LustreIndex.index
  | ContractItem of position * LustreContract.svar * contract_item_type
  | Assertion of position

(** Return a node of the given name and is extern flag without inputs, outputs,
    oracles, equations, etc. Create a state variable for the {!t.instance} and
    {!t.init_flag} fields, and set {!t.is_main} to false. *)
val empty_node : LustreIdent.t -> bool -> t

(** {1 Pretty-printers} *)

(** Pretty-print a node equation in Lustre format 

    If the flag in the first argument is [true], print identifiers in
    Lustre syntax. *)
val pp_print_node_equation : bool -> Format.formatter -> equation -> unit

(** Pretty-print a node call in Lustre format 

    If the flag in the first argument is [true], print identifiers in
    Lustre syntax. *)
val pp_print_call : bool -> Format.formatter -> node_call -> unit 

(** Pretty-print a node in Lustre format 

    If the flag in the first argument is [true], print identifiers in
    Lustre syntax. *)
val pp_print_node : bool -> Format.formatter -> t -> unit 

(** Pretty-prints the signature of a node in Lustre format, WITHOUT NODE
KEYWORD AND NAME. (Used in contract generation.) *)
val pp_print_node_signature : Format.formatter -> t -> unit

(** Pretty-print the node as a record with all information  *)
val pp_print_node_debug : Format.formatter -> t -> unit 

(** {1 Node Lists} *)

(** Return the node of the given name from a list of nodes *)
val node_of_name : LustreIdent.t -> t list -> t 

(** Return true if a node of the given name exists in the a list of nodes *)
val exists_node_of_name : LustreIdent.t -> t list -> bool 

(** Return all nodes with --%MAIN annotations *)
val get_main_annotated_nodes : t list -> LustreIdent.t list

(** Return name of all nodes annotated with --%MAIN.  Raise
    [Not_found] if no node has a --%MAIN annotation.
    If the processing mode does not support multiple main nodes,
    then it is the caller's responsibility to ensure there is
    only a single main node.
*)
val find_main : t list -> LustreIdent.t list

(** Return the identifier of the top node

    Fail with [Invalid_argument "ident_of_top"] if list of nodes is empty *)
val ident_of_top : t list -> LustreIdent.t 

(** Return true if the node has a contract with
    at least one guarantee or one mode *)
val has_effective_contract : t -> bool

(** Return a list of tree-like subsystem hierarchies from a flat list of nodes,
    where the names of the top nodes are given as first argument. *)
val subsystems_of_nodes : LustreIdent.t list -> t list -> t SubSystem.t list

(** Return a tree-like subsystem hierarchy from a flat list of nodes,
    where the name of the top node is given as first argument. *)
val subsystem_of_nodes : LustreIdent.t -> t list -> t SubSystem.t

(** Return list of topologically ordered list of nodes from subsystem.
    The top node is the head of the list. *)
val nodes_of_subsystem : t SubSystem.t -> t list

(** Return all stateful variables from expressions in a node *)
val stateful_vars_of_node : t -> StateVar.StateVarSet.t

(** Return the name of the node *)
val name_of_node : t -> LustreIdent.t

(** [ordered_equations_of_node n stateful init]
    Returns the equations of [n], topologically sorted by their base (step)
    expression if [init] ([not init]). *)
val ordered_equations_of_node :
  t -> StateVar.t list -> bool -> equation list

(** Returns the equation for a state variable if any. *)
val equation_of_svar : t -> StateVar.t -> equation option

(** Returns [true] if the node is partially defined, that is,
    there is an output without an equational definition *)
val partially_defined : t -> bool

(** Returns the equation for a state variable if any. *)
val source_of_svar : t -> StateVar.t -> state_var_source option

(** Returns the node call the svar is (one of) the output(s) of, if any. *)
val node_call_of_svar : t -> StateVar.t -> node_call option

(** Return the scope of the node *)
val scope_of_node : t -> Scope.t

(** {2 Iterators} *)

(** Fold bottom-up over node calls together with the transition system 

    [fold_node_calls_with_trans_sys l f n t] evaluates [f m s i a] for each
    node call in the node [n], including [n] itself. The list of nodes [l] must
    at least contain all sub-nodes of [n], and [n] itself, the transition
    system [t] must at least contain subsystem instances for all node
    calls. Both [l] and [t] may contain more nodes and subsystems,
    respectively, only the node calls in [n] are relevant.

    The function [f] is evaluated with the node [m], its transition system [s],
    and the reverse sequence of instantiations [i] that reach the top system
    [t]. The last parameter [a] is the list of evaluations of [f] on the called
    nodes and subsystems of [s]. The sequence of instantiations [i] contains at
    its head a system that has [s] as a direct subsystem, together with the
    instance parameters. For the top system [i] is the empty list. Each element
    of [i] also contains the call activation conditions that effectively sample
    the node.

    The systems are presented in topological order such that each system is
    presented to [f] after all its subsystem instances have been presented.
*)
val fold_node_calls_with_trans_sys :
  t list -> (
    t -> TransSys.t ->
    (TransSys.t * TransSys.instance * call_cond list) list -> 'a list -> 'a
  ) -> t -> TransSys.t -> 'a

(** {2 Sources} *)

(** Every state variable is either defined in a node, or was
    introduced in pre-processing, see {!state_var_source}.

    - [Input], [Output] or [Local] state variables correspond to input,
    output and local streams defined in a node, respectively. 

    - [Oracle] state variables are additional input variables
     introduced to non-deterministivcally give a value to unguarded
     [pre] expressions, or to unconstrained streams.

    - A [Ghost] state variables are is a local variable defined in
      a contract.
*)

(** Pretty-print a source of a state variable *)
val pp_print_state_var_source : Format.formatter -> state_var_source -> unit 

(** Set source of state variable *)
val set_state_var_source : t -> StateVar.t -> state_var_source -> t

(** Set source of state variable if not already defined. *)
val set_state_var_source_if_undef : t -> StateVar.t -> state_var_source -> t

(** Get source of state variable *)
val get_state_var_source : t -> StateVar.t -> state_var_source

(* (** Sets the first svar as alias for the second svar. *)
val set_state_var_alias : t -> StateVar.t -> StateVar.t -> t *)

(** Register state var as tied to a node call if not already registered. *)
val set_state_var_node_call : t -> StateVar.t -> t

(** State variable is identical to a state variable in a node instance *)
val set_state_var_instance :
  StateVar.t -> Lib.position -> LustreIdent.t -> StateVar.t -> unit

val set_oracle_state_var : t -> StateVar.t -> StateVar.t -> unit

val get_oracle_state_var_map : t -> StateVar.t StateVar.StateVarHashtbl.t

val set_state_var_expr : t -> StateVar.t -> LustreExpr.t -> unit

val get_state_var_expr_map : t -> LustreExpr.t StateVar.StateVarHashtbl.t

val get_all_state_vars : t -> StateVar.t list

(** get all instances of a state variable *)
val get_state_var_instances : StateVar.t -> state_var_instance list

(** print state var instances for debug *)
val pp_print_state_var_instances_debug : Format.formatter -> t -> unit

(** Get the definitions (with positions in the Lustre program) of a state variable *)
val get_state_var_defs : StateVar.t -> state_var_def list

(** Add a definition (with positions in the Lustre program) for a state variable *)
val add_state_var_def : StateVar.t -> state_var_def -> unit

val pos_of_state_var_def : state_var_def -> position

val index_of_state_var_def : state_var_def -> LustreIndex.index

(** print state var defs for debug *)
val pp_print_state_var_defs_debug : Format.formatter -> t -> unit

(** Return true if the state variable should be visible to the user,
    false if it was created internally

    Return [true] if the source of the state variable is either
    [Input], [Output], or [Local], and [false] otherwise. *)
val state_var_is_visible : t -> StateVar.t -> bool


(** Return the automaton to which the state variable belongs if any *)
val is_automaton_state_var : StateVar.t -> (string * string) option

(** Return true if the node should be visible to the user,
    false if it was created internally. *)
val node_is_visible : t -> bool

(** Return the state that is handled by the node if any. *)
val node_is_state_handler : t -> string option

(** Return true if the state variable is an input *)
val state_var_is_input : t -> StateVar.t -> bool

(** Return true if the state variable is an output *)
val state_var_is_output : t -> StateVar.t -> bool

(** Return true if the state variable is a local variable *)
val state_var_is_local : t -> StateVar.t -> bool

(** Replace state variables in equation *)
val map_svars_in_equation : (StateVar.t -> StateVar.t) -> equation -> equation

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
