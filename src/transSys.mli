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

(** Representation of a transition system 

    @author Christoph Sticksel
*)



(** The transition system 

    The transition system must be constructed with the function
    {!mk_trans_sys}. Fields of the record are exposed, but accessing
    them is deprecated, use the provided functions below. *)
type t = private

  {

    (** Definitions of uninterpreted function symbols *)
    uf_defs : (UfSymbol.t * (Var.t list * Term.t)) list;

    (** State variables of top node 

       The list of state variables is sorted with regard to
       {!StateVar.compare_state_var} *)
    state_vars : StateVar.t list;

    (** Initial state constraint *)
    init : Term.t;

    (** Transition relation *)
    trans : Term.t;

    (** Propertes to prove invariant *)
    props : (string * Term.t) list; 

    (** Invariants *)
    mutable invars : Term.t list;

    (** Status of property *)
    mutable prop_status : (string * Lib.prop_status) list;

  }


    
(** Create a transition system

    For each state variable of a bounded integer type, add a
    constraint to the invariants. *)
val mk_trans_sys : (UfSymbol.t * (Var.t list * Term.t)) list -> StateVar.t list -> Term.t -> Term.t -> (string * Term.t) list -> t

(** Pretty-print a transition system *)
val pp_print_trans_sys : Format.formatter -> t -> unit

(** Get the required logic for the SMT solver *)
val get_logic : t -> SMTExpr.logic

(** Return the state variables of the transition system *)
val state_vars : t -> StateVar.t list

(** Return the variables at current and previous instants of the
   transition system *)
val vars_of_bounds : t -> Numeral.t -> Numeral.t -> Var.t list

(** Instantiate the initial state constraint to the bound *)
val init_of_bound : t -> Numeral.t -> Term.t

(** Instantiate the transition relation constraint to the bound 

    The bound given is the bound of the state after the transition *)
val trans_of_bound : t -> Numeral.t -> Term.t

(** Instantiate all properties to the bound *)
val props_of_bound : t -> Numeral.t -> Term.t

(** Instantiate all properties to the bound *)
val props_list_of_bound : t -> Numeral.t -> (string * Term.t) list 

(** Instantiate invariants and valid properties to the bound *)
val invars_of_bound : t -> Numeral.t -> Term.t

(** Return uninterpreted function symbols to be declared in the SMT solver *)
val uf_symbols_of_trans_sys : t -> UfSymbol.t list

(** Add an invariant to the transition system *)
val add_invariant : t -> Term.t -> unit

(** Update transition system from events and return new invariants and
    properties with changed status

    For a property status message the status saved in the transition
    system is updated if the status is more general (k-true for a
    greater k, k-false for a smaller k, etc.) 

    Received invariants are stored in the transition system, also
    proved properties are added as invariants.

    Counterexamples are ignored. *)
val update_from_events : t -> (Lib.kind_module * Event.event) list -> (Lib.kind_module * Term.t) list * (Lib.kind_module * (string * Lib.prop_status)) list * (Lib.kind_module * (string list * (StateVar.t * Term.t list) list)) list

(** Return current status of property *)
val prop_status : t -> string -> Lib.prop_status 

(** Mark property as invariant *)
val prop_invariant : t -> string -> unit 

(** Mark property as false *)
val prop_false : t -> string -> unit 

(** Mark property as k-false *)
val prop_kfalse : t -> int -> string -> unit 

(** Mark property as k-true *)
val prop_ktrue : t -> int -> string -> unit 

(** Return true if the property is proved invariant *)
val is_proved : t -> string -> bool 

(** Return true if the property is proved not invariant *)
val is_disproved : t -> string -> bool 

(** Return true if all properties are either valid or invalid *)
val all_props_proved : t -> bool

(** Apply [f] to all uninterpreted function symbols of the transition
    system *)
val iter_state_var_declarations : t -> (UfSymbol.t -> unit) -> unit 
  
(** Apply [f] to all function definitions of the transition system *)
val iter_uf_definitions : t -> (UfSymbol.t -> Var.t list -> Term.t -> unit) -> unit


(** Extract a path in the transition system, return an association
    list of state variables to a list of their values.

    The second argument is a function returning assignments to the
    variables, see {!SolverMethods.S.get_model}. The path is extracted
    from instant zero up to instant [k], which is the third argument. *)
val path_from_model : t -> (Var.t list -> (Var.t * Term.t) list) -> Numeral.t -> (StateVar.t * Term.t list) list


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
