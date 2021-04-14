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

(** Representation of a transition system 

    A transition system is uniquely identified by its scope. A
    transition system can contain subsystems. For each subsystem there
    is a map of all state variables of the subsystem to some state
    variable in this transition system, and a function to guard term
    in the scope of the subsystem to make them valid in this
    transition system. There must be no cycles in the subsystem
    relation, that is, a transition system cannot have itself as a
    subsystem.

    A transition system constrains values of the set of state
    variables of a scope that make up the state of the transition
    system. The state variables in [state_vars] are assumed to be of
    the same scope [scope]. The initial state constraint [init] is a
    term over these state variables at offset [init_base], the
    transition relation [trans] is a term over state variables at
    offsets [trans_base] and [trans_base - 1].

    @author Christoph Sticksel
    @author Adrien Champion
*)


(* Dependencies: initial state predicate may occur in the transition
   relation in condacts, and if we support reset. *)

(** Offset of the current state variables in initial state
    constraint *)
val init_base : Numeral.t

(** Offset of current state variables in transition relation, subtract
    one for the offset of the previous state variables *)
val trans_base : Numeral.t

(** Offset of current state variables in properties and invariants,
    subtract one for the offset of the previous state variables *)
val prop_base : Numeral.t

(** The transition system 

    Constructed with the function {!mk_trans_sys} *)
type t

(** Hash table over transition systems. *)
module Hashtbl : Hashtbl.S with type key = t

(** Predicate definition 

    An uninterpreted function symbols and the pair of its formal
    parameters and its definition, to be used in an association
    list. *)
type pred_def = UfSymbol.t * (Var.t list * Term.t)

(** Instance of a subsystem *)
type instance = 
  {

    pos : Lib.position;
    (** Position as a unique identifier of the instance *)

    map_down : StateVar.t StateVar.StateVarMap.t;
    (** Map from the state variables of this system to the state
        variables of the instance *)

    map_up : StateVar.t StateVar.StateVarMap.t;
    (** Map from state variables of the called system to the state
        variables of this system *)

    guard_clock : Numeral.t -> Term.t -> Term.t;
    (** Add a guard to the Boolean term to make it true whenver the
        the clock of the subsystem instance is false

        [guard_clock t] assumes that [t] is a Boolean term and returns
        the term [c => t] where [c] is the clock of the subsystem
        instance. *)

    assumes: (Term.t list * Term.t) option;
    (** [None] if there is no assumption associated to the call. Otherwise,
        [Some (l,s)] where [l] is the list of instantiated assume terms, and
        [s] is SoFar(conjunction of instantiated assume terms) *)
  }

(** Return [true] if scopes of transition systems are equal *)
val equal_scope : t -> t -> bool

(** Compare transition systems by their scope *)
val compare_scope : t -> t -> int

(** Pretty-print a transition system *)
val pp_print_trans_sys : Format.formatter -> t -> unit

(** Pretty-print a transition system and its subsystems

    [pp_print_subsystems t f s] pretty-prints the top node of
    transition system [s], if parameter [t] is set to true,
    and also all its subsystems.
*)
val pp_print_subsystems : bool -> Format.formatter -> t -> unit

(** Pretty-print the name of a transition system *)
val pp_print_trans_sys_name : Format.formatter -> t -> unit

(** {1 Accessors} *)

(** Close the initial state constraint by binding all instance
    identifiers, and bump the state variable offsets to be at the given
    bound *)
val init_of_bound : (UfSymbol.t -> unit) option -> t -> Numeral.t -> Term.t

(** Close the initial state constraint by binding all instance
    identifiers, and bump the state variable offsets to be at the given
    bound *)
val trans_of_bound : (UfSymbol.t -> unit) option -> t -> Numeral.t -> Term.t 


(** Predicate for the initial state constraint *)
val init_uf_symbol : t -> UfSymbol.t

(** Predicate for the transition relation *)
val trans_uf_symbol : t -> UfSymbol.t


(** Variables in the initial state constraint *)
val init_formals : t -> Var.t list 

(** Variables in the transition relation *)
val trans_formals : t -> Var.t list


(** Builds a call to the initial function on state [k]. *)
val init_fun_of : t -> Numeral.t -> Term.t
  
(** Builds a call to the transition relation function linking state
    [k] and [k']. *)
val trans_fun_of : t -> Numeral.t -> Numeral.t -> Term.t


(** Return the state variable for the init flag *)
val init_flag_state_var : t -> StateVar.t

(** Return the init flag at the given bound *)
val init_flag_of_bound : t -> Numeral.t -> Term.t


(** Return the instance variables of this transition system, the
    initial state constraint at [init_base] and the transition relation
    at [trans_base] with the instance variables free. *)
val init_trans_open : t -> StateVar.t list * Term.t * Term.t

(** Update the init and trans equations of a subsystem *)
val set_subsystem_equations : t -> Scope.t -> Term.t -> Term.t -> t

(** Return the logic fragment needed to express the transition system *)
val get_logic : t -> TermLib.logic

(** Return the scope identifying the transition system *)
val scope_of_trans_sys : t -> Scope.t

(** Returns the properties in a transition system. *)
val get_properties : t -> Property.t list

(** Return current status of all real (not candidate) properties *)
val get_real_properties : t -> Property.t list

(** Return true if the property is a candidate invariant *)
val is_candidate : t -> string -> bool 

(** Return list of candidate invariants *)
val get_candidates : t -> Term.t list

(** Return list of candidate invariants properties *)
val get_candidate_properties : t -> Property.t list

(** Return candidate invariants that have not been proved or disproved yet *)
val get_unknown_candidates : t -> Term.t list

(* Return true if all properties are valid *)
(* val all_props_actually_proved : t -> bool *)


(** Returns the optional assumption term and the mode requirement terms for
each mode.

Used by test generation. *)
val get_mode_requires : t -> Term.t option * (Scope.t * Term.t) list

(** Returns the list of properties in a transition system, split by their
    status as [valid, invalid, unknown]. *)
val get_split_properties :
  t -> Property.t list * Property.t list * Property.t list

(** Returns function symbols declared in the transition system *)
val get_function_symbols : t -> UfSymbol.t list

(** Make a copy of every mutable field of the transition system and its subsystems. *)
val copy : t -> t

val mk_trans_sys :

  (* Start value for fresh instance identifiers *)
  ?instance_var_id_start:int ->
  
  (* Name of the transition system *)
  Scope.t ->

  (* State variable for instance identifier *)
  StateVar.t option ->

  (* State variable for init flag *)
  StateVar.t ->

  (* Global state variables *)
  (StateVar.t * Term.t list) list ->

  (* All state variables including globals and instance identifier *)
  StateVar.t list ->

  (* Input variables whose value is not constrained by assumptions or asserts *)
  StateVar.StateVarSet.t ->

  (* indexes of state variables *)
  (LustreExpr.expr LustreExpr.bound_or_fixed list) StateVar.StateVarHashtbl.t ->

  (* Global free constants *)
  Var.t list  -> 

  (* Declarations of other function symbols *)
  UfSymbol.t list  -> 

  (* Predicate symbol for initial state constraint *)
  UfSymbol.t -> 

  (* Formal parameters of initial state constraint *)
  Var.t list -> 

  (* Initial state constraint *)
  Term.t ->

  (* Predicate symbol for transition relation *)
  UfSymbol.t -> 

  (* Formal parameters of transition relation *)
  Var.t list -> 

  (* Transition relation *)
  Term.t ->

  (* Subsystems and their instances *)
  (t * instance list) list ->

  (* Properties *)
  Property.t list -> 

  (* Assumption and mode requirements for this system (used by test
      generation). *)
  Term.t option * (Scope.t * Term.t) list ->

  (* Invariants. *)
  Invs.t ->

  (* Created transition system and next starting value for fresh
      instance identifiers *)
  t * int



(** Iterate bottom-up over subsystems, including the top level system
    without repeating subsystems already seen 

    [iter_subsystems f t] evaluates [f] for all subsystem of [t]. The
    subsystems are presented bottom-up such that for each evaluation
    [f t] the function [f s] has already been evaluated for each
    subsystem [s] of [t]. If [t] contains a subsystem [s] twice, no
    matter at which level, [f s] is evaluated only once.
*)
val iter_subsystems : ?include_top:bool -> (t -> unit) -> t -> unit

(** Fold bottom-up over subsystems, including or excluding the top
    level system, without repeating subsystems already seen

    [fold_subsystems f t] first evaluates [f a s] for some subsystem
    [s] of [t] that does not have subsystems itself. It then passes
    the result as first argument to [f] with the second argument being
    a subsystem for which all subsystems have been evaluated with
    [f]. If [t] contains a subsystem [s] twice, no matter at which
    level, [f s] is evaluated only once. 

    The systems are passes in topological order such that the each
    system is presented to [f] only after all its subsystems. The
    function [f] is evaluated for the top system last, unless the
    optional labelled parameter [include_top] is set to false.
*)
val fold_subsystems : ?include_top:bool -> ('a -> t -> 'a) -> 'a -> t -> 'a

(** Fold bottom-up over subsystem instances 

    [fold_subsystem_instances f t] evaluates [f s i l] for each
    subsystem instance in the system [t], including [t] itself. The
    function [f] is evaluated with the subsystem [s], the reverse
    sequence of instantiations [i] that reach the top system [t], and
    the evaluations of [f] on the subsystems of [s]. The sequence of
    instantiations [i] contains at its head a system that has [s] as a
    direct subsystem, together with the instance parameters. For the
    top system [i] is the empty list.

    The systems are presented in topological order such that each
    system is presented to [f] after all its subsystem instances have
    been presented.
*)
val fold_subsystem_instances : (t -> (t * instance) list -> 'a list -> 'a) -> t -> 'a

(** Return the direct subsystems of a system *)
val get_subsystems : t -> t list

(** Return the direct subsystems of a system and their instances *)
val get_subsystem_instances : t -> (t * instance list) list

(** Find the named subsystem 

    [find_subsystem_of_scope t s] returns the subsystem of [t] identified
    by the scope [s]. We assume that all subsystems with the same
    scope are identical. The transition system [t] itself is returned
    if [s] is its scope.

    Raise [Not_found] if there is no transition system of scope [s]
    in the subsystems of [t]. *)
val find_subsystem_of_scope : t -> Scope.t -> t

(** Get SoFar expression associated to a given node call (if any),
    and its invariance status

    [get_sofar_term t p] returns [None] if the subsystem instance identified
    by position [p] does not exist or does not have assumptions. Otherwise,
    it returns [Some (t,b)] where [t] corresponds to SoFar(conjunction of
    instantiated assume terms), and [b] is true if the term has proven
    invariant.
*)
val get_sofar_term: t -> Lib.position -> (Term.t * bool) option

val get_max_depth : t -> int

val map_cex_prop_to_subsystem : (Scope.t -> instance -> (StateVar.t * Model.value list) list ->  Model.value list -> Model.value list) -> t -> (StateVar.t * Model.value list) list -> Property.t -> t * instance list * (StateVar.t * Model.value list) list * Property.t 

(** {1 State Variables} *)

(** After 

    {[ define_and_declare_of_bounds 
         t
         (SMTSolver.define_fun s)
         (SMTSolver.declare_fun t) 
         (SMTSolver.declare_sort t) 
         l
         u ]}

    with the solver instance [s], initial state constraint and
    transition relation can be asserted for all offsets between and
    including [l] and [u]. 

    To extend the range of declared offsets to the range including [l]
    and [v], use

    {[ declare_vars_of_bounds
         (SMTSolver.declare_fun t) 
         (Numeral.succ u)
         v  ]}

    Evaluating {!define_and_declare_of_bounds} is only needed once per
    solver instance, and only for the top level transition system. *)

(** Return the state variables of a transition system *)
val state_vars : t -> StateVar.t list

(** Return unconstrained inputs variables of a transition system *)
val unconstrained_inputs : t -> StateVar.StateVarSet.t

(** Add a global constant to the transition system and all the subnodes *)
val add_global_constant : t -> Var.t -> t

(** Return instances of the state variables of the transition system
    between given instants

    [vars_of_bounds t l u] returns the list of instances of the state
    variables of the transition system [t] between and including [l]
    and [u]. Include the state variable for the init flag unless the
    optional labelled argument [with_init_flag] is set to false.
*)
val vars_of_bounds :  ?with_init_flag:bool -> t -> Numeral.t -> Numeral.t -> Var.t list

(** Declare variables of the transition system between given instants

    [declare_vars_of_bounds t f l u] evaluates [f] with the
    uninterpreted function symbol of each state variable of the
    transition system [t] at each instant between and including [l]
    and [u]. Include the state variable for the init flag unless the
    optional labelled argument [declare_init_flag] is set to false.
*)
val declare_vars_of_bounds : ?declare_init_flag:bool -> t -> (UfSymbol.t -> unit) -> Numeral.t -> Numeral.t -> unit

val declare_const_vars : t -> (UfSymbol.t -> unit) -> unit


(** Declare the init flag of the transition system between given instants

    [declare_init_flag_of_bounds t f l u] evaluates [f] with the
    uninterpreted function symbol of the state variable for the init
    flag of the transition system [t] at each instant between and
    including [l] and [u]. 
*)
val declare_init_flag_of_bounds : t -> (UfSymbol.t -> unit) -> Numeral.t -> Numeral.t -> unit

(** Declare the sorts, uninterpreted functions and const variables
   of this system and its subsystems. *)
val declare_sorts_ufs_const :
  t ->
  (UfSymbol.t -> unit) ->
  (Type.t -> unit) -> unit

(** Declare the init and trans functions of the subsystems *)
val define_subsystems :
  t ->
  (UfSymbol.t -> Var.t list -> Term.t -> unit) ->
  unit

(** Define predicates and declare constant and global state variables,
    declare state variables of top system between and including the
    given offsets

    [define_and_declare_of_bounds t f g l u] first evaluates the
    function [f] for the definition of the initial state constraint
    predicate and the transitions relation predicate of the top system
    in the transition system [t] and all its subsystems. It then
    evaluates the function [g] with the declarations of all constant
    and global state variables of the top system, and with the
    declarations of the remaining state variables of the top system
    between and including the offsets [l] and [u]. 

    If [l > u], only declarations of constant and global state are
    passed to [g], and [f] is still evaluated with all definitions.

    If the optional parameter [declare_sub_vars] is [true], it also
    iterates over all subsystems and evaluates [g] with the
    declarations of their constants and global state variables, and
    their state variables between and including [l] and [u]. Thus the
    subsystems can be run in parallel to the top system.

    The signatures of [f] and [g] are those of {!SMTSolver.define_fun}
    and {!SMTSolver.declare_fun}, repsectively, partially evaluated
    with their first argument. *)
val define_and_declare_of_bounds :
  ?declare_sub_vars:bool -> t ->
  (UfSymbol.t -> Var.t list -> Term.t -> unit) ->
  (UfSymbol.t -> unit) ->
  (Type.t -> unit) ->
  Numeral.t -> Numeral.t -> unit

(** Return predicate definitions of initial state and transition
    relation of the top system and all its subsystem in reverse
    topological order

    [uf_defs t] returns a list of predicate definitions of the top
    system [t] and all its subsystems such that the definitions of a
    subsystem precede the definitions of all systems containing it. The
    definition of the initial state predicate precedes the definition
    of the transition relation predicate.
*)
val uf_defs : t -> pred_def list

(** {1 Properties} *)

val property_of_name : t -> string -> Property.t


(** Return term of the property

    [get_prop_term t n] returns the term of the first property of name
    [n] in the transistion system [t]. *)
val get_prop_term : t -> string -> Term.t


(** Return current status of the property

    [get_prop_status t n] returns the status saved in the transition
    system of the first property of name [n]. *)
val get_prop_status : t -> string -> Property.prop_status 


(** Returns true if the input term is a known invariant of the system. *)
val is_inv : t -> Term.t -> bool


(** Return true if the property is proved invariant *)
val is_proved : t -> string -> bool 

(** Return true if the property is proved not invariant *)
val is_disproved : t -> string -> bool 

(** Return current status of all properties excepted candidates

    [get_prop_status t] returns the status saved in the transition
    system of each property along with the name of the property. *)
val get_prop_status_all_nocands : t -> (string * Property.prop_status) list

(** Return current status of all unknown properties

    [get_prop_status_all_unknown t] returns the status saved in the
    transition system of each property which is considered to be
    unknown along with the name of the property.

    According to {!Property.prop_status_known}, a property is known if
    it is invariant, or has a [k]-step counterexample. *)
val get_prop_status_all_unknown : t -> (string * Property.prop_status) list


(** Instantiate all properties to the bound *)
val props_list_of_bound : t -> Numeral.t -> (string * Term.t) list 


(** Update current status of the property

    [set_prop_status t n s] sets the status saved in the transition
    system of the first property of name [n] to [s]. *)
val set_prop_status : t -> string -> Property.prop_status -> unit

(** Mark property as invariant *)
val set_prop_invariant : t -> string -> Certificate.t -> unit

(** Mark property as false *)
val set_prop_false :
  t -> string -> (StateVar.t * Model.value list) list -> unit

(** Mark property as k-true *)
val set_prop_ktrue : t -> int -> string -> unit

val set_prop_unknown : t -> string -> unit

(* Set the list of properties of a subsystem *)
val set_subsystem_properties : t -> Scope.t -> Property.t list -> t

(** Returns true iff sys has at least one real (not candidate) property. *)
val has_real_properties : t -> bool

(** Return true if all properties which are not candidates are either valid or
    invalid *)
val all_props_proved : t -> bool

(** Return true if at least one prop has been falsified *)
val at_least_one_prop_falsified : t -> bool

(** Add properties to the transition system *)
val add_properties : t -> Property.t list -> t

(** Add an invariant to the transition system. *)
val add_invariant : t -> Term.t -> Certificate.t -> bool -> Term.t

(** Add an invariant to the transition system.

Returns the normalized terms and a boolean indicating whether it is one
state. *)
val add_scoped_invariant :
  t -> string list -> Term.t -> Certificate.t -> bool -> Term.t

(** Instantiate invariants and valid properties to the bound *)
val invars_of_bound : ?one_state_only:bool -> t -> Numeral.t -> Term.t list

(** Return invariants with their certificates *)
val get_invariants : t -> Invs.t

(** Returns the invariants for all (sub)systems. *)
val get_all_invariants : t -> Invs.t Scope.Map.t

(** Clear invariants of the top_level system *)
val clear_invariants : t -> unit

(** Clear invariants of all (sub)systems *)
val clear_all_invariants : t -> unit

(** Instantiate a term of a given scope from all instances of the
    system of that scope upwards to the top system

    [instantiate_term_all_levels t i s e ts] instantiates the Boolean term [e]
    of scope [s] in all systems it is a subsystem of, and further upwards until
    the top system [t]. The offset [i] is the offset of the current instant in
    the term [e]. [ts] is true if the invariant is two states.

    Return the top system [s] paired with the instances of the term in
    it, and a list of all systems between the top system [t] and the
    system [s], including [s] but excluding [t], each system paired
    with the instances of [e] in it.

    The offset [i] is needed to properly guard the term [e] for
    clocked system instances. *)
val instantiate_term_all_levels:
  t -> Numeral.t -> Scope.t -> Term.t -> bool ->
  (t * Term.t list) * ((t * Term.t list) list) 


(** Return arrays bounds of state variables of array type used in the system *)
val get_state_var_bounds : t ->
  (LustreExpr.expr LustreExpr.bound_or_fixed list)
    StateVar.StateVarHashtbl.t

    
(** Same as above but with certificates *)
val instantiate_term_cert_all_levels: t -> Numeral.t -> Scope.t ->
  Term.t * Certificate.t -> bool ->
  (t * (Term.t * Certificate.t) list) *
  (t * (Term.t * Certificate.t) list) list



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
