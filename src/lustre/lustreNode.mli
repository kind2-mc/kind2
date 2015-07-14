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

    Nodes are normalized for easy translation into a transition
    system, mainly by introducing new variables. A [LustreExpr.t] does
    not contain node calls, temporal operators or expressions under a
    [pre] operator. 

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

(** A call of a node *)
type node_call = 

  { 

    call_pos : position;
    (** Position of node call in input file *)

    call_node_name : LustreIdent.t;
    (** Name of called node *)
    
    call_clock : StateVar.t option;
    (** Boolean activation condition *)

    call_inputs : StateVar.t LustreIndex.t;
    (** Variables for input parameters *)

    call_oracles : StateVar.t list;
    (** Variables providing non-deterministic inputs *)

    call_outputs : StateVar.t LustreIndex.t;
    (** Variables providing non-deterministic inputs *)

    call_defaults : LustreExpr.t LustreIndex.t;
    (** Expression for initial return values *)

  }


(** Source of a state variable *)
type state_var_source =
  | Input
  | Output
  | Local
  | Ghost
  | Oracle


(** A contract has an identifier and a position in the input, a state
    variable that is the conjunction of its requirements, and one
    state variable for each ensures. 

    The requirement of a global contract may be assumed
    invariant. Each ensures of a global or mode contract is a separate
    proof obligation for the node. 

    The conjunction of the requirements of all global contracts, and
    the disjunction of the requirements of all mode contracts is a
    proof obligation for all calling nodes.
*)
type contract =
  { 

    contract_name : LustreIdent.t;
    (** Identifier of contract *)

    contract_pos: position;
    (** Position of the contract in the input *)

    contract_req : StateVar.t;
    (** Invariant from requirements of contract *)

    contract_enss : StateVar.t list
    (** Invariants from ensures of contract *)

  }

(**  *)
type 'a bound_or_fixed = 
  | Bound of 'a  (** Upper bound for index variable *)
  | Fixed of 'a  (** Fixed value for index variable *)

(** An equation is a triple [(state_var, bounds, expr)] of the
    expression [expr] that defines the state variable [state_var],
    and a list [bounds] of indexes. 

    An array can be defined either only at a given index, or at all
    indexes, when the expression on the right-hand side is interpreted
    as a function of the running variable of the index.  *)
type equation = 
  (StateVar.t * LustreExpr.expr bound_or_fixed list * LustreExpr.t)

(** A Lustre node

    Every state variable occurs exactly once in [inputs], [outputs],
    and [oracles], and at most once on the left-hand side of
    [equations] and [calls]. *)
type t = 

  { 

    name : LustreIdent.t;
    (** Name of the node *)

    instance : StateVar.t;
    (** Distinguished constant state variable uniquely identifying the
        node instance *)

    init_flag : StateVar.t;
    (** Distinguished state variable to be true in the first
       instant only *)

    inputs : StateVar.t LustreIndex.t;
    (** Input streams defined in the node

        The inputs are considered as a list with an integer indexes
        correpsonding to their position in the formal parameters. *)

    oracles : StateVar.t list;
    (** Oracle inputs added to the node inputs

        Input streams added to the node to obtain non-deterministic
        values for the initial values of unguarded pre operators. The
        state variables are constant. *)

    outputs : StateVar.t LustreIndex.t;
    (** Output streams defined in the node

        The inputs are considered as a list with an integer indexes
        correpsonding to their position in the formal parameters. *)

    locals : StateVar.t LustreIndex.t list;
    (** Local variables of node

        The order of the list is irrelevant, we are doing dependency
        analysis and cone of influence reduction later. *)

    equations : equation list;
    (** Equations for local and output variables *)

    calls : node_call list;
    (** Node calls inside the node *)

    asserts : LustreExpr.t list;
    (** Assertions of node *)

    props : (StateVar.t * string * Property.prop_source) list;
    (** Proof obligations for the node *)

    global_contracts : contract list;
    (** Global contracts *)

    mode_contracts :  contract list;
    (** Mode contracts *)

    is_main : bool;
    (** Flag node as the top node *)

    state_var_source_map : state_var_source StateVar.StateVarMap.t 
    (** Map from a state variable to its source *)

  }

(** Return an empty node of the given name *)
val empty_node : LustreIdent.t -> t

(** Pretty-print a node equation in Lustre format 

    If the flag in the first argument is [true], print identifiers in
    Lustre syntax. *)
val pp_print_node_equation : bool -> Format.formatter -> StateVar.t * LustreExpr.expr bound_or_fixed list * LustreExpr.t -> unit

(** Pretty-print a node call in Lustre format 

    If the flag in the first argument is [true], print identifiers in
    Lustre syntax. *)
val pp_print_call : bool -> Format.formatter -> node_call -> unit 

(** Pretty-print a node in Lustre format 

    If the flag in the first argument is [true], print identifiers in
    Lustre syntax. *)
val pp_print_node : bool -> Format.formatter -> t -> unit 

(** Pretty-print the node with all information  *)
val pp_print_node_debug : Format.formatter -> t -> unit 

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

(** Return true if the node has a global or at least one mode
    contract *)
val has_contract : t -> bool

(** Return false if the body of the node is empty, that is, all
    equations are ghost and there are no assertions *)
val has_impl : t -> bool

(** Return a tree-like subsystem hierarchy from a flat list of nodes,
    where the top node is at the head of the list. *)
val subsystem_of_nodes : t list -> t SubSystem.t

(** Return list of topologically ordered list of nodes from subsystem.
    The top node is a the head of the list. *)
val nodes_of_subsystem : t SubSystem.t -> t list

(** Return all stateful variables from expressions in a node *)
val stateful_vars_of_node : t -> StateVar.StateVarSet.t

(** Return the name of the node *)
val name_of_node : t -> LustreIdent.t

(** Return the scope of the node *)
val scope_of_node : t -> Scope.t

(** {2 Iterators} *)

(** Fold bottom-up over node calls together with the transition system 

    [fold_node_calls_with_trans_sys l f n t] evaluates [f m s i a] for
    each node call in the node [n], including [n] itself. The list of
    nodes [l] must at least contain all sub-nodes of [n], and [n]
    itself, the transition system [t] must at least contain subsystem
    instances for all node calls. Both [l] and [t] may contain more
    nodes and subsystems, respectively, only the node calls in [n] are
    relevant.

    The function [f] is evaluated with the node [m], its transition
    system [s], and the reverse sequence of instantiations [i] that
    reach the top system [t]. The last parameter [a] is the list of
    evaluations of [f] on the called nodes and subsystems of [s]. The
    sequence of instantiations [i] contains at its head a system that
    has [s] as a direct subsystem, together with the instance
    parameters. For the top system [i] is the empty list.

    The systems are presented in topological order such that each
    system is presented to [f] after all its subsystem instances have
    been presented.
*)
val fold_node_calls_with_trans_sys : t list -> (t -> TransSys.t -> (TransSys.t * TransSys.instance) list -> 'a list -> 'a) -> t -> TransSys.t -> 'a

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

(** Get source of state variable *)
val get_state_var_source : t -> StateVar.t -> state_var_source

(** Return true if the state variable should be visible to the user,
    false if it was created internally

    Return [true] if the source of the state variable is either
    [Input], [Output], or [Local], and [false] otherwise. *)
val state_var_is_visible : t -> StateVar.t -> bool

(** Return true if the state variable is an input *)
val state_var_is_input : t -> StateVar.t -> bool

(** Return true if the state variable is an output *)
val state_var_is_output : t -> StateVar.t -> bool

(** Return true if the state variable is a local variable *)
val state_var_is_local : t -> StateVar.t -> bool

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
