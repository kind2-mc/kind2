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

(** A node

    Nodes are normalized for easy translation into a transition system,
    mainly by introducing new variables. A LustreExpr.t does not
    contain node calls, temporal operators or expressions under a pre
    operator. Node equations become a map of identifiers to expressions
    in node_eqs, all node calls are in node_calls as a list of tuples
    containing fresh variables the node output is assigned to and the
    expressions for the node input.

    The node signature as input and output variables as well as its
    local variables is in [node_inputs], [node_outputs] and
    [node_vars], respectively. Local constants are propagated and do
    not need to be stored.

    Assertions, properties to prove and contracts as assumptions and
    guarantees are lists of expressions in [node_asserts], [node_props],
    [node_requires], and [node_ensures].

    The flag [node_is_main] is set if the node has been annotated as
    main, it is not checked if more than one node or no node at all may
    have that annotation.

*)
type t = 

  { 

    (** Input variables of node, some flagged as constant

        The order of the list is important, it is the order the
        parameters in the declaration. *)
    inputs : 
      (StateVar.t * bool) list;

    (** Output variables of node

        The order of the list is important, it is the order the
        parameters in the declaration. *)
    outputs : StateVar.t list;

    (** Local variables of node

        The order of the list is irrelevant, we are doing dependency
        analysis and cone of influence reduction later. *)
    locals : StateVar.t list;

    (** Equations for local and output variables *)
    equations : (StateVar.t * LustreExpr.t) list;

    (** Node calls with activation condition: variables capturing the
        outputs, the Boolean activation condition, the name of the
        called node, expressions for input parameters and expression
        for initialization *)
    calls : 
      (StateVar.t list * 
       LustreExpr.t * 
       LustreIdent.t * 
       LustreExpr.t list * 
       LustreExpr.t list) list;

    (** Assertions of node *)
    asserts : LustreExpr.t list;

    (** Proof obligations for node *)
    props : LustreExpr.t list;

    (** Contract for node, assumptions *)
    requires : LustreExpr.t list;

    (** Contract for node, guarantees *)
    ensures : LustreExpr.t list;

    (** Node is annotated as main node *)
    is_main : bool;

    (** Dependencies of the output variables on input variables *)
    output_input_dep : int list list }

(** The empty node *)
val empty_node : t

(** Pretty-print a node *)
val pp_print_node : bool -> LustreIdent.t -> Format.formatter -> t -> unit 

val node_var_dependencies : bool -> (LustreIdent.t * t) list -> t -> (StateVar.t * StateVar.StateVarSet.t) list -> (StateVar.t * StateVar.t list) list -> (StateVar.t * StateVar.StateVarSet.t) list

val output_input_dep_of_var_dep : t -> (StateVar.t * StateVar.StateVarSet.t) list -> int list list

val solve_eqs_node_calls : t -> t

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
