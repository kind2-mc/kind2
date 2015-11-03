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

    To model arrays we use an additional set of global state variables
    outside the scope of the transition system in
    [global_state_vars]. These state variables have an additional
    index that is set to a unique term for the instance of the
    transition system the array occurs in.

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
    (** Map from state variables of the called system to the state
        variables of the this system *)

    map_up : StateVar.t StateVar.StateVarMap.t;
    (** Map from the state variables of this system to the state
        variables of the instance *)

    guard_clock : Numeral.t -> Term.t -> Term.t;
    (** Add a guard to the Boolean term to make it true whenver the
        the clock of the subsystem instance is false

        [guard_clock t] assumes that [t] is a Boolean term and returns
        the term [c => t] where [c] is the clock of the subsystem
        instance. *)

  }

(** Return [true] if scopes of transition systems are equal *)
val equal_scope : t -> t -> bool

(** Compare transition systems by their scope *)
val compare_scope : t -> t -> int

(** Pretty-print a transition system *)
val pp_print_trans_sys : Format.formatter -> t -> unit

(** {1 Accessors} *)

(** Close the initial state constraint by binding all instance
    identifiers, and bump the state variable offsets to be at the given
    bound *)
val init_of_bound : t -> Numeral.t -> Term.t

(** Close the initial state constraint by binding all instance
    identifiers, and bump the state variable offsets to be at the given
    bound *)
val trans_of_bound : t -> Numeral.t -> Term.t 


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


(** Returns the mode requirements for this system as a list of triplets
    [is_mode_global, mode_name, require_term].
    Used by test generation. *)
val get_mode_requires : t -> (bool * string * Term.t) list

(** Returns the list of properties in a transition system, split by their
    status as [valid, invalid, unknown]. *)
val get_split_properties :
  t -> Property.t list * Property.t list * Property.t list


val mk_trans_sys :

  (** Start value for fresh instance identifiers *)
  ?instance_var_id_start:int ->
  
  (** Name of the transition system *)
  Scope.t ->

  (** State variable for instance identifier *)
  StateVar.t option ->

  (** State variable for init flag *)
  StateVar.t ->

  (** Global state variables *)
  (StateVar.t * Term.t list) list ->

  (** All state variables including globals and instance identifier *)
  StateVar.t list ->

  (** Declarations of other function symbols *)
  UfSymbol.t list  -> 

  (** Predicate symbol for initial state constraint *)
  UfSymbol.t -> 

  (** Formal parameters of initial state constraint *)
  Var.t list -> 

  (** Initial state constraint *)
  Term.t ->

  (** Predicate symbol for transition relation *)
  UfSymbol.t -> 

  (** Formal parameters of transition relation *)
  Var.t list -> 

  (** Transition relation *)
  Term.t ->

  (** Subsystems and their instances *)
  (t * instance list) list ->

  (** Properties *)
  Property.t list -> 

  (** Requirements of global and non-global modes for this system (used by
      test generation).
      List of [(is_mode_global, mode_name, require_term)]. *)
  (bool * string * Term.t) list ->


  (** One-state invariants *)
  (Term.t * Certificate.t) list -> 

  (** Two-state invariants *)
  (Term.t * Certificate.t) list -> 

  (** Created transition system and next starting value for fresh
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

    Raise [Not_found] if there is no transistion system of scope [s]
    in the subsystems of [t]. *)
val find_subsystem_of_scope : t -> Scope.t -> t


val get_max_depth : t -> int

val map_cex_prop_to_subsystem : (Scope.t -> instance -> (StateVar.t * Model.term_or_lambda list) list ->  Model.term_or_lambda list -> Model.term_or_lambda list) -> t -> (StateVar.t * Model.term_or_lambda list) list -> Property.t -> t * instance list * (StateVar.t * Model.term_or_lambda list) list * Property.t 

(** {1 State Variables} *)

(** After 

    {[ define_and_declare_of_bounds 
         t
         (SMTSolver.define_fun s)
         (SMTSolver.declare_fun t) 
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
         v  ]}. 

    Evaluating {!define_and_declare_of_bounds} is only needed once per
    solver instance, and only for the top level transition system. *)

(** Return the state variables of a transition system *)
val state_vars : t -> StateVar.t list

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
val define_and_declare_of_bounds : ?declare_sub_vars:bool -> t -> (UfSymbol.t -> Var.t list -> Term.t -> unit) -> (UfSymbol.t -> unit) -> Numeral.t -> Numeral.t -> unit

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


(** Return true if the property is proved invariant *)
val is_proved : t -> string -> bool 

(** Return true if the property is proved not invariant *)
val is_disproved : t -> string -> bool 

(** Return current status of all properties

    [get_prop_status t] returns the status saved in the transition
    system of each property along with the name of the property. *)
val get_prop_status_all : t -> (string * Property.prop_status) list

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

(** Mark current status of property *)
val set_prop_status : t -> string -> Property.prop_status -> unit

(** Mark property as invariant *)
val set_prop_invariant : t -> string -> Certificate.t -> unit

(** Mark property as false *)
val set_prop_false :
  t -> string -> (StateVar.t * Model.term_or_lambda list) list -> unit

(** Mark property as k-true *)
val set_prop_ktrue : t -> int -> string -> unit

(** Return true if all properties are either valid or invalid *)
val all_props_proved : t -> bool

(** Add an invariant to the transition system *)
val add_invariant : t -> Term.t -> Certificate.t -> unit

(** Add an invariant to the transition system *)
val add_scoped_invariant : t -> string list -> Term.t -> Certificate.t -> unit

(** Instantiate invariants and valid properties to the bound *)
val invars_of_bound : ?one_state_only:bool -> t -> Numeral.t -> Term.t list

(** Return invariants with their certificates *)
val get_invariants : t -> (Term.t * Certificate.t) list

(** Instantiate a term of a given scope from all instances of the
    system of that scope upwards to the top system

    [instantiate_term_all_levels t i s e] instantiates the Boolean
    term [e] of scope [s] in all systems it is a subsystem of, and
    further upwards until the top system [t]. The offset [i] is the
    offset of the current instant in the term [e].

    Return the top system [s] paired with the instances of the term in
    it, and a list of all systems between the top system [t] andthe
    system [s], including [s] but excluding [t], each system paired
    with the instances of [e] in it.

    The offset [i] is needed to properly guard the term [e] for
    clocked system instances. *)
val instantiate_term_all_levels:
  t -> Numeral.t -> Scope.t -> Term.t -> (t * Term.t list) * ((t * Term.t list) list)


(** Same as above but with certificates *)
val instantiate_term_cert_all_levels: t -> Numeral.t -> Scope.t ->
  Term.t * Certificate.t ->
  (t * (Term.t * Certificate.t) list) *
  (t * (Term.t * Certificate.t) list) list


(*

(** {1 Constructor} *)

(** Create a transition system. Arguments

    - [scope]
    - [state_variables]
    - [init_pred_def]
    - [trans_pred_def]
    - [subsystems]
    - [properties]
    - [contracts]
    - [abstraction_actlit_option]
    - [source]

    For each state variable of a bounded integer type, add a
    constraint to the invariants. *)
val mk_trans_sys :

  string list ->
  (** Scope. *)

  StateVar.t list ->
  (** State variables. *)

  UfSymbol.t * (Var.t list * Term.t) ->
  (** Init predicate definition. *)

  UfSymbol.t * (Var.t list * Term.t) ->
  (** Trans predicate definition. *)

  t list ->
  (** Subsystems. *)

  (string * TermLib.prop_source * Term.t) list ->
  (** Properties. *)

  (StateVar.t * StateVar.t * contract list) option ->
  (** Contracts. *)

  source ->
  (** Source of the system. *)

  t


(** {1 Properties} *)

(** Status of a property *)
type prop_status =

  (** Status of property is unknown *)
  | PropUnknown

  (** Property is true up to k-th step *)
  | PropKTrue of int

  (** Property is invariant *)
  | PropInvariant of Certificate.t

  (** Property is false at some step *)
  | PropFalse of (StateVar.t * Model.term_or_lambda list) list

(** Return current status of all properties *)
val get_prop_status_all_unknown : t -> (string * prop_status) list

(** Return current status of property *)
val get_prop_status : t -> string -> prop_status

(** Instantiate all unknown properties to the bound *)
val props_list_of_bound_unknown : t -> Numeral.t -> (string * Term.t) list 

(** Return true if all properties are either valid or invalid *)
val all_props_proved : t -> bool

(** Get property by name *)
val named_term_of_prop_name : t -> string -> Term.t
                                               

(** {1 Maintain State} *)

(** Add an invariant to the transition system *)
val add_invariant : t -> Term.t -> unit

(** Add an invariant to the transition system *)
val add_scoped_invariant : t -> string list -> Term.t -> unit


(** {1 Solver initialization} *)

(** Return the scope of the transition system *)
val get_scope : t -> string list

(** Return the name of the transition system *)
val get_name : t -> string

(** Get the required logic for the SMT solver *)
val get_logic : t -> TermLib.logic
                                                       
(** Initializes the solver for a system and an abstraction. *)
val init_solver:
  ?declare_top_vars_only:bool ->
  (** Only declare top level variables. *)

  t ->
  (** Transition system. *)

  (string -> unit) ->
  (** Trace comment. *)

  (UfSymbol.t -> Var.t list -> Term.t -> unit) ->
  (** Define fun. *)

  (UfSymbol.t -> unit) ->
  (** Declare fun. *)

  (Term.t -> unit) ->
  (** Assert fun. *)

  Numeral.t ->
  (** Var declaration lower bound. *)

  Numeral.t ->
  (** Var declaration upper bound. *)

  unit

(** Declares variables of the transition system between two
    offsets. *)
val declare_vars_of_bounds :
  t -> (UfSymbol.t -> unit) ->
  (Term.t -> unit) ->
  Numeral.t -> Numeral.t -> unit


(** {1 Accessors for Elements of Transition System *)

(** Instantiate the initial state constraint to the bound *)
val init_of_bound : t -> Numeral.t -> Term.t

(** Instantiate the transition relation constraint to the bound.  The
    bound given is the bound of the state after the transition *)
val trans_of_bound : t -> Numeral.t -> Term.t
  
(** Instantiate invariants and valid properties to the bound *)
val invars_of_bound : ?one_state_only:bool -> t -> Numeral.t -> Term.t

(** The state variables of a transition system. *)
val state_vars : t -> StateVar.t list

(** Return uninterpreted function symbol definitions in topological
    order. *)
val uf_defs : t -> pred_def list

(** The subsystems of a system. *)
val get_subsystems : t -> t list


(** {1 Instantiation from subsystems} *)

(** Instantiates a term for the top system by going up the system
   hierarchy, for all instantiations of the input system. Returns the
   top system and the corresponding instantiated terms, paired with
   the intermediary systems and term instantiations. Note that the
   input system/term of the function will be in the result, either as
   intermediary or top level. *)
val instantiate_term_all_levels:
  t -> t -> Term.t -> (t * Term.t list) * ((t * Term.t list) list)


(**/**)

(** {1 Possibly obsolete} *)


(** A definition of an uninterpreted predicate *)
type pred_def = (UfSymbol.t * (Var.t list * Term.t)) 

(** Pretty-print a property status *)
val pp_print_prop_status_pt : Format.formatter -> prop_status -> unit

(** Return true if the property is proved or disproved, i.e., for
    [PropInvariant], [PropFalse] and [PropKFalse].  *)
val prop_status_known : prop_status -> bool

(** Return the length of the counterexample *)
val length_of_cex : (StateVar.t * 'a list) list -> int

type contract

val mk_global_contract :
  Lib.position -> StateVar.t -> string -> contract

val mk_mode_contract :
  Lib.position -> StateVar.t -> string -> contract

(** The transition system 

    Constructed with the function {!mk_trans_sys} *)
type t

(** Create a transition system. Arguments

    - [scope]
    - [state_variables]
    - [init_pred_def]
    - [trans_pred_def]
    - [subsystems]
    - [properties]
    - [contracts]
    - [abstraction_actlit_option]
    - [source]

    For each state variable of a bounded integer type, add a
    constraint to the invariants. *)
val mk_trans_sys :

  string list ->
  (** Scope. *)

  StateVar.t list ->
  (** State variables. *)

  UfSymbol.t * (Var.t list * Term.t) ->
  (** Init predicate definition. *)

  UfSymbol.t * (Var.t list * Term.t) ->
  (** Trans predicate definition. *)

  t list ->
  (** Subsystems. *)

  (string * TermLib.prop_source * Term.t) list ->
  (** Properties. *)

  (StateVar.t * StateVar.t * contract list) option ->
  (** Contracts. *)

  source ->
  (** Source of the system. *)

  t

(** Add entry for new system instantiation to the transition
    system. [add_caller callee caller var_map guard] *)
val add_caller : t -> t ->
  (StateVar.t * StateVar.t) list * (Term.t -> Term.t) -> unit

val get_callers : t -> t list

(** Pretty-print a predicate definition *)
val pp_print_uf_def : Format.formatter -> pred_def -> unit

(** Pretty-print a transition system *)
val pp_print_trans_sys : Format.formatter -> t -> unit

(** Get the required logic for the SMT solver *)
val get_logic : t -> TermLib.logic
                       
(** Instantiates a term for the top system by going up the system
   hierarchy, for all instantiations of the input system. Returns the
   top system and the corresponding instantiated terms, paired with
   the intermediary systems and term instantiations. Note that the
   input system/term of the function will be in the result, either as
   intermediary or top level. *)
val instantiate_term_all_levels: t -> Term.t ->
  (t * Term.t list) * (t * Term.t list) list

(** Same as above but with certificates *)
val instantiate_term_cert_all_levels: t -> Term.t * Certificate.t ->
  (t * (Term.t * Certificate.t) list) *
  (t * (Term.t * Certificate.t) list) list

(** Instantiates a term for the top system by going up the system
    hierarchy, for all instantiations of the input system. *)
val instantiate_term_top: t -> t -> Term.t -> Term.t list

(** Number of times this system is instantiated in other systems. *)
val instantiation_count: t -> int

(** Returns true if the system is the top level system. *)
val is_top : t -> bool

(** Predicate for the initial state constraint *)
val init_uf_symbol : t -> UfSymbol.t

(** Predicate for the transition relation *)
val trans_uf_symbol : t -> UfSymbol.t

(** Variables in the initial state constraint *)
val init_vars : t -> Var.t list 

(** Variables in the transition relation *)
val trans_vars : t -> Var.t list

(** Definition of the initial state constraint *)
val init_term : t -> Term.t

(** Definition of the transition relation *)
val trans_term : t -> Term.t

(** Returns [Some(true)] if the contract is global, [Some(false)] if it's not,
   and [None] if the system has no contracts. *)
val contract_is_global : t -> string -> bool option

(** The contracts of a system. *)
val get_contracts :
  t -> (Lib.position * StateVar.t * string) list


(** Returns a triplet of the concrete subsystems, the refined ones, and the
    abstracted ones. Does not contain the input system. *)
val get_abstraction_split : t -> (t list) * (t list) * (t list)

(** For a system, returns [Some true] if all contracts are invariants,
    [Some false] if at least one of the contracts is falsified, and
    [None] otherwise --i.e. some contracts are unknown / k-true. *)
(* val verifies_contracts : t -> bool option *)

(** The contracts of a system, as a list of implications. *)
(* val get_contracts_implications : t -> (string * Term.t) list *)


(** Returns all the subsystems of a system in reverse topological
    order, INCLUDING that system. *)
val get_all_subsystems : t -> t list

(** Return the source used to produce the transition system *)
val get_source : t -> source

(** Return the Luste nodes before slicing *)
val get_original_lustre_nodes : t -> LustreNode.t list

(** Register the Luste nodes before slicing *)
val set_original_lustre_nodes : t -> LustreNode.t list -> unit

(** Return the scope of the transition system *)
val get_scope : t -> string list

(** Finds the subsystem of [t] corresponding to [scope]. *)
val subsystem_of_scope : t -> string list -> t

(** Returns the source name of the transition system. *)
val get_source_name : t -> string

(** Declares constants of the transition system. *)
val declare_consts : t -> (UfSymbol.t -> unit) -> unit

(** Declares variables of the transition system between two offsets. *)
val declare_vars_of_bounds_no_init :
  t -> (UfSymbol.t -> unit) -> Numeral.t -> Numeral.t -> unit

(** Returns the variables of the transition system between two
    bounds. *)
val vars_of_bounds :
  t -> Numeral.t -> Numeral.t ->
  Var.t list

(* Base *)
(** The init flag of a transition system, as a [Var]. *)
val init_flag_of_trans_sys : t -> Numeral.t -> Var.t

(** Instantiate the transition relation constraint to the bound.  The
    bound given is the bound of the state after the transition *)
val trans_of_bound : t -> Numeral.t -> Term.t

(** Builds a call to the initial function on state [k]. *)
val init_fun_of : t -> Numeral.t -> Term.t
  
(** Builds a call to the transition relation function linking state
    [k] and [k']. *)
val trans_fun_of : t -> Numeral.t -> Numeral.t -> Term.t

(** Instantiate all properties to the bound *)
val props_of_bound : t -> Numeral.t -> Term.t

(** Instantiate all not valid properties to the bound *)
val props_of_bound_not_valid : t -> Numeral.t -> Term.t

(** Instantiate all properties to the bound *)
val props_list_of_bound : t -> Numeral.t -> (string * Term.t) list 

(** Instantiate all not valid properties to the bound *)
val props_list_of_bound_not_valid : t -> Numeral.t -> (string * Term.t) list 

(** The list of invariants and valid properties at zero. *)
val get_invars : t -> Term.t list

(** The list of callers of this system *)
val get_callers : t ->
  (t * (((StateVar.t * StateVar.t) list * (Term.t -> Term.t)) list)) list

(** Return uninterpreted function symbols to be declared in the SMT
    solver *)
val uf_symbols_of_trans_sys : t -> UfSymbol.t list

(** Return uninterpreted function symbol definitions as pairs of
    initial state and transition relation definitions, in topological
    order. *)
val uf_defs_pairs : t -> (pred_def * pred_def) list

(** Return [true] if the uninterpreted symbol is a transition relation *)
val is_trans_uf_def : t -> UfSymbol.t -> bool

(** Return [true] if the uninterpreted symbol is an initial state constraint *)
val is_init_uf_def : t -> UfSymbol.t -> bool

(** Add an invariant to the transition system *)
val add_invariant : t -> Term.t -> Certificate.t -> unit

(** Add an invariant to the transition system *)
val add_scoped_invariant : t -> string list -> Term.t -> Certificate.t -> unit

(** Return invariants with their certificates *)
val get_invariants : t -> (Term.t * Certificate.t) list

(** Return current status of all real (not candidate) properties *)
val get_real_properties :
  t -> (string * TermLib.prop_source * Term.t * prop_status) list

(** Return current status of all properties *)
val get_prop_status_all : t -> (string * prop_status) list

(** Returns the source of a property. *)
val get_prop_source : t -> string -> TermLib.prop_source option

(** Mark current status of property *)
val set_prop_status : t -> string -> prop_status -> unit

val set_prop_invariant : t -> string -> Certificate.t -> unit 

(** Mark property as false *)
val set_prop_false : t -> string -> (StateVar.t * Model.term_or_lambda list) list -> unit 

(** Mark property as k-true *)
val set_prop_ktrue : t -> int -> string -> unit

(** Resets properties with a status different from [PropValid] to
    [PropUnknown]. This is used in compositional and modular analysis
    when restarting. *)
val reset_non_valid_props_to_unknown : t -> unit

(** Resets the list of invariants of a system to only the terms of the
    valid properties. *)
val reset_invariants : t -> unit

(** Propagates the validity of the properties of a system to its
    callers. Only properties from annotations and generated ones will
    be lifted. *)
val lift_valid_properties : t -> unit

(** Returns true iff all subrequirement properties of the system are
    invariants. *)
val subrequirements_valid : t -> bool

(** Returns true iff all subrequirements related to a scope are
    invariants. *)
val proved_requirements_of : t -> string list -> bool

(** Returns true if the contract of the input system is an
    invariant. @raise Not_found if the system has no contracts. *)
val is_contract_proved : t -> bool

(** Return true if the property is proved invariant *)
val is_proved : t -> string -> bool 

(** Return true if the property is proved not invariant *)
val is_disproved : t -> string -> bool 

(** Return true if the property is a candidate invariant *)
val is_candidate : t -> string -> bool 

(** Return list of candidate invariants *)
val get_candidates : t -> Term.t list

(** Return list of candidate invariants properties *)
val get_candidate_properties :
    t -> (string * TermLib.prop_source * Term.t * prop_status) list

(** Return candidate invariants that have not been proved or disproved yet *)
val get_unknown_candidates : t -> Term.t list

(** Return true if all properties are valid *)
val all_props_actually_proved : t -> bool

(** Apply [f] to all uninterpreted function symbols of the transition
    system *)
val iter_state_var_declarations : t -> (UfSymbol.t -> unit) -> unit 
  
(* (\** Apply [f] to all function definitions of the transition system *\) *)
(* val iter_uf_definitions : t -> (UfSymbol.t -> Var.t list -> Term.t -> unit) -> unit *)
                                                                 
(** Define uf definitions, declare constant state variables and declare
    variables from [lbound] to [upbound]. *)
val init_define_fun_declare_vars_of_bounds :
      t ->
      (UfSymbol.t -> Var.t list -> Term.t -> unit) ->
      (UfSymbol.t -> unit) ->
      Numeral.t -> Numeral.t ->
      unit


val exists_eval_on_path :
  pred_def list -> (Eval.value -> bool) -> Term.t -> Model.path -> bool


(** {1 Abstraction} *)

(** Describes an abstraction of a system. *)
type abstraction = string list list

(** Pretty prints an abstraction. *)
val pp_print_trans_sys_abstraction:
  Format.formatter -> t -> unit

(* Call from develop branch

(x) done

-- src/base.ml
(x) TransSys.declare_vars_of_bounds
(x) TransSys.get_logic
(x) TransSys.get_prop_status
(x) TransSys.init_define_fun_declare_vars_of_bounds -> define_and_declare_of_bounds
(x) TransSys.init_of_bound
TransSys.invars_of_bound
TransSys.named_term_of_prop_name -> prop
(x) TransSys.PropFalse
(x) TransSys.PropInvariant
(x) TransSys.PropKTrue
TransSys.props_list_of_bound
(x) TransSys.state_vars
(x) TransSys.trans_of_bound
(x) TransSys.uf_defs

-- src/compress.ml
(x) TransSys.state_vars
TransSys.trans_of_bound
(x) TransSys.uf_defs

-- src/event.ml
TransSys.add_invariant
TransSys.add_scoped_invariant
(x) TransSys.get_prop_status
TransSys.get_scope
TransSys.get_source
TransSys.length_of_cex
TransSys.Lustre
TransSys.named_term_of_prop_name
TransSys.Native
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.props_list_of_bound
TransSys.prop_status
TransSys.prop_status_known
TransSys.PropUnknown
TransSys.set_prop_false
TransSys.set_prop_invariant
TransSys.set_prop_ktrue
TransSys.set_prop_status

-- src/horn.ml
TransSys.constr_constr
TransSys.empty
TransSys.init_constr
TransSys.pp_print_trans_sys
TransSys.props

-- src/IC3.ml
TransSys.add_invariant
TransSys.declare_vars_of_bounds
TransSys.exists_eval_on_path
TransSys.get_logic
(x) TransSys.get_prop_status
TransSys.get_scope
TransSys.init_define_fun_declare_vars_of_bounds
TransSys.init_of_bound
TransSys.invars_of_bound
TransSys.is_disproved
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.props_list_of_bound
(x) TransSys.state_vars
TransSys.trans_of_bound
(x) TransSys.uf_defs
TransSys.vars_of_bounds

-- src/interpreter.ml
TransSys.get_logic
TransSys.get_scope
TransSys.init_define_fun_declare_vars_of_bounds
TransSys.init_of_bound
(x) TransSys.state_vars
TransSys.trans_of_bound

-- src/invarManager.ml
TransSys.all_props_proved
(x) TransSys.get_prop_status_all

-- src/invGenCandTermGen.ml
TransSys.get_scope
TransSys.get_subsystems
TransSys.init_of_bound
TransSys.instantiate_term_all_levels
(x) TransSys.state_vars
TransSys.trans_of_bound

-- src/invGenGraph.ml
TransSys.add_invariant
TransSys.get_name
TransSys.get_scope
TransSys.init_flag_var
TransSys.instantiate_term_all_levels
TransSys.named_term_of_prop_name
TransSys.PropInvariant
TransSys.subsystem_of_scope
TransSys.t
(x) TransSys.uf_defs

-- src/kind2.ml
(x) TransSys.get_prop_status_all
TransSys.pp_print_trans_sys
TransSys.PropFalse
TransSys.PropKTrue
TransSys.props_list_of_bound
TransSys.PropUnknown

-- src/lockStepDriver.ml
TransSys.declare_vars_of_bounds_no_init
TransSys.get_logic
TransSys.get_name
TransSys.get_scope
TransSys.get_subsystems
TransSys.init_define_fun_declare_vars_of_bounds
TransSys.init_flag_uf
TransSys.init_of_bound
TransSys.invars_of_bound
TransSys.t
TransSys.trans_of_bound
TransSys.vars_of_bounds

-- src/lustreChecker.ml
TransSys.mk_trans_sys
TransSys.pp_print_trans_sys
TransSys.trans_sys_of_nodes
TransSys.uf_symbols_of_trans_sys

-- src/lustreTransSys.ml
TransSys.add_caller
TransSys.get_source
TransSys.init_base
TransSys.init_flag_svar
TransSys.init_flag_var
TransSys.init_uf_symbol
TransSys.Lustre
TransSys.mk_trans_sys
TransSys.pp_print_trans_sys
TransSys.pp_print_uf_def
TransSys.t
TransSys.trans_base
TransSys.trans_uf_symbol

-- src/nativeInput.ml
TransSys.mk_trans_sys
TransSys.Native
TransSys.pp_print_trans_sys

-- src/nusmv.ml
TransSys.constr
TransSys.init
TransSys.invars
TransSys.props
TransSys.props_invalid
TransSys.trans

-- src/oldParser.ml
TransSys.constr_assign
TransSys.constr_constr
TransSys.constr_dep
TransSys.constr_of_def_list
TransSys.init_assign
TransSys.init_constr
TransSys.invars
TransSys.invars_of_types
TransSys.props
TransSys.props_invalid
TransSys.props_valid
TransSys.trans

-- src/QE.ml
TransSys.declare_vars_of_bounds
TransSys.get_logic
TransSys.init_define_fun_declare_vars_of_bounds
TransSys.iter_uf_definitions
TransSys.vars_of_bounds

-- src/step.ml
TransSys.add_invariant
TransSys.declare_vars_of_bounds
TransSys.get_invars
TransSys.get_logic
(x) TransSys.get_prop_status
TransSys.init_define_fun_declare_vars_of_bounds
TransSys.invars_of_bound
TransSys.iter_state_var_declarations
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.props_list_of_bound
(x) TransSys.state_vars
TransSys.trans_fun_of
TransSys.trans_of_bound
(x) TransSys.uf_defs
TransSys.vars_of_bounds

*)

(* Calls from contracts branch 

-- src/analysis.ml
TransSys.all_props_proved
TransSys.pp_print_trans_sys_name
TransSys.t

-- src/base.ml
TransSys.declare_vars_of_bounds
- TransSys.get_abstraction
TransSys.get_logic
TransSys.get_name
(x) TransSys.get_prop_status
(x) TransSys.get_prop_status_all_unknown
TransSys.get_scope
TransSys.init_of_bound
TransSys.init_solver
TransSys.invars_of_bound
TransSys.named_term_of_prop_name
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.props_list_of_bound_unknown
TransSys.state_vars
TransSys.trans_of_bound
TransSys.uf_defs

-- src/compress.ml
TransSys.state_vars
TransSys.trans_of_bound
TransSys.uf_defs

-- src/event.ml
TransSys.add_invariant
TransSys.add_scoped_invariant
- TransSys.contract_is_global
- TransSys.get_abstraction_split
- TransSys.get_all_subsystems
- TransSys.get_callers
- TransSys.get_name
TransSys.get_prop_source
(x) TransSys.get_prop_status
TransSys.get_scope
TransSys.get_source
TransSys.get_source_name
TransSys.get_source_name,
TransSys.length_of_cex
TransSys.Lustre
TransSys.named_term_of_prop_name
TransSys.Native
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.props_list_of_bound
TransSys.prop_status
TransSys.prop_status_known
TransSys.PropUnknown
TransSys.set_prop_false
TransSys.set_prop_invariant
TransSys.set_prop_ktrue
TransSys.set_prop_status
TransSys.subsystem_of_scope

-- src/interpreter.ml
TransSys.get_abstraction
TransSys.get_logic
TransSys.get_scope
TransSys.init_of_bound
TransSys.init_solver
TransSys.state_vars
TransSys.trans_of_bound

-- src/invGenCandTermGen.ml
TransSys.get_abstraction
TransSys.get_scope
TransSys.get_subsystems
TransSys.init_of_bound
TransSys.instantiate_term_all_levels
TransSys.state_vars
TransSys.trans_of_bound

-- src/invGenGraph.ml
TransSys.add_invariant
TransSys.get_name
TransSys.get_scope
TransSys.init_flag_of_trans_sys
TransSys.instantiate_term_all_levels
TransSys.named_term_of_prop_name
TransSys.PropInvariant
TransSys.subsystem_of_scope
TransSys.t
TransSys.uf_defs

-- src/kind2.ml
TransSys.all_props_actually_proved
TransSys.get_all_subsystems
(x) TransSys.get_prop_status_all
TransSys.lift_valid_properties
TransSys.pp_print_prop_status_pt
TransSys.pp_print_trans_sys
TransSys.pp_print_trans_sys_name
TransSys.PropInvariant
TransSys.props_list_of_bound
TransSys.reset_invariants
TransSys.reset_non_valid_props_to_unknown

-- src/lockStepDriver.ml
TransSys.declare_vars_global_const
TransSys.declare_vars_of_bounds
TransSys.get_abstraction
TransSys.get_invars
TransSys.get_logic
TransSys.get_name
TransSys.get_scope
TransSys.get_subsystems
TransSys.init_of_bound
TransSys.init_solver
TransSys.invars_of_bound
TransSys.t
TransSys.trans_of_bound
TransSys.vars_of_bounds

-- src/log.ml
TransSys.get_abstraction
TransSys.get_all_subsystems
TransSys.get_invars
TransSys.get_name
(x) TransSys.get_prop_status_all
(x) TransSys.get_prop_status_all_unknown
TransSys.is_top
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.PropUnknown
TransSys.t

-- src/PDR.ml
TransSys.add_invariant
TransSys.exists_eval_on_path
TransSys.get_abstraction
TransSys.get_logic
(x) TransSys.get_prop_status
TransSys.get_scope
TransSys.init_of_bound
TransSys.init_solver
TransSys.invars_of_bound
TransSys.is_disproved
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.props_list_of_bound_unknown
TransSys.state_vars
TransSys.trans_of_bound
TransSys.uf_defs
TransSys.vars_of_bounds

-- src/QE.ml
TransSys.declare_vars_of_bounds
TransSys.get_abstraction
TransSys.get_logic
TransSys.get_scope
TransSys.init_solver
TransSys.iter_uf_definitions
TransSys.vars_of_bounds

-- src/refiner.ml
TransSys.get_abstraction
TransSys.get_all_subsystems
TransSys.get_contracts
TransSys.get_scope
TransSys.is_contract_proved
TransSys.proved_requirements_of
TransSys.set_abstraction
TransSys.subrequirements_valid

-- src/step.ml
TransSys.add_invariant
TransSys.declare_vars_of_bounds
TransSys.get_abstraction
TransSys.get_logic
TransSys.get_name
(x) TransSys.get_prop_status
TransSys.get_scope
TransSys.init_define_fun_declare_vars_of_bounds
TransSys.init_solver
TransSys.invars_of_bound
TransSys.iter_state_var_declarations
TransSys.PropFalse
TransSys.PropInvariant
TransSys.PropKTrue
TransSys.props_list_of_bound_unknown
TransSys.state_vars
TransSys.trans_fun_of
TransSys.trans_of_bound
TransSys.uf_defs
TransSys.vars_of_bounds


*)

*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
