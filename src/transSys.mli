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

    @author Christoph Sticksel, Adrien Champion
*)

(** Source format *)
type source = 
  | Lustre of LustreNode.t list  (** Lustre with given nodes *)
  | Native                       (** Native format *)


(** A definition of an uninterpreted predicate *)
type pred_def = (UfSymbol.t * (Var.t list * Term.t)) 

(** Status of a property *)
type prop_status =

  (** Status of property is unknown *)
  | PropUnknown

  (** Property is true up to k-th step *)
  | PropKTrue of int

  (** Property is invariant *)
  | PropInvariant 

  (** Property is false at some step *)
  | PropFalse of (StateVar.t * Term.t list) list

(** Pretty-print a property status *)
val pp_print_prop_status_pt : Format.formatter -> prop_status -> unit

(** Return true if the property is proved or disproved, i.e., for
    [PropInvariant], [PropFalse] and [PropKFalse].  *)
val prop_status_known : prop_status -> bool

(** Return the length of the counterexample *)
val length_of_cex : (StateVar.t * Term.t list) list -> int

(** Offset of state variables in initial state constraint *)
val init_base : Numeral.t

(** Offset of primed state variables in transition relation *)
val trans_base : Numeral.t

(** Offset of primed state variables in properties and invariants *)
val prop_base : Numeral.t

(** The transition system 

    Constructed with the function {!mk_trans_sys} *)
type t

(** Create a transition system

    For each state variable of a bounded integer type, add a
    constraint to the invariants. *)
val mk_trans_sys :
  string list ->
  StateVar.t list ->
  UfSymbol.t * (Var.t list * Term.t) ->
  UfSymbol.t * (Var.t list * Term.t) ->
  t list ->
  (string * TermLib.prop_source * Term.t) list ->
  source ->
  t

(** Add entry for new system instantiation to the transition system *)
val add_caller : t -> t -> (StateVar.t * StateVar.t) list * (Term.t -> Term.t) -> unit

(** Pretty-print a predicate definition *)
val pp_print_uf_def : Format.formatter -> pred_def -> unit

(** Pretty-print a transition system *)
val pp_print_trans_sys : Format.formatter -> t -> unit

(** Get the required logic for the SMT solver *)
val get_logic : t -> Term.logic
                       
(** Instantiates a term for all (over)systems instantiating, possibly
    more than once, the input system. *)
val instantiate_term: t -> Term.t -> (t * Term.t list) list
                                                       
(** Instantiates a term for the top system by going up the system
   hierarchy, for all instantiations of the input system. Returns the
   top system and the corresponding instantiated terms, paired with
   the intermediary systems and term instantiations. Note that the
   input system/term of the function will be in the result, either as
   intermediary or top level. *)
val instantiate_term_all_levels:
  t -> Term.t -> (t * Term.t list) * ((t * Term.t list) list)

(** Instantiates a term for the top system by going up the system
    hierarchy, for all instantiations of the input system. *)
val instantiate_term_top: t -> Term.t -> Term.t list

(** Number of times this system is instantiated in other systems. *)
val instantiation_count: t -> int

(** Returns true if the system is the top level system. *)
val is_top : t -> bool

(** Global init flag state var *)
val init_flag_svar: StateVar.t

(** Instantiate init flag at k *)
val init_flag_var: Numeral.t -> Var.t

val init_flag_uf: Numeral.t -> UfSymbol.t
                                  
(** Tests if a var is an instanciation of the init_flag. *)
val is_var_init_flag: Var.t -> bool
                                  
(** Tests if a uf is an instanciation of the init_flag. *)
val is_uf_init_flag: UfSymbol.t -> bool

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


(** The subsystems of a system. *)
val get_subsystems : t -> t list

(** The state variables of a transition system. *)
val state_vars : t -> StateVar.t list

(** Return the source used to produce the transition system *)
val get_source : t -> source

(** Return the scope of the transition system *)
val get_scope : t -> string list

(** Finds the subsystem of [t] corresponding to [scope]. *)
val subsystem_of_scope : t -> string list -> t

(** Return the name of the transition system *)
val get_name : t -> string

(** Return the variables at current and previous instants of the
   transition system *)
val vars_of_bounds : t -> Numeral.t -> Numeral.t -> Var.t list

(** Declares variables of the transition system between two offsets. *)
val declare_vars_of_bounds : t -> (UfSymbol.t -> unit) -> Numeral.t -> Numeral.t -> unit

(** Declares variables of the transition system between two offsets. *)
val declare_vars_of_bounds_no_init :
  t -> (UfSymbol.t -> unit) -> Numeral.t -> Numeral.t -> unit

(** Instantiate the initial state constraint to the bound *)
val init_of_bound : t -> Numeral.t -> Term.t

(** Instantiate the transition relation constraint to the bound.  The
    bound given is the bound of the state after the transition *)
val trans_of_bound : t -> Numeral.t -> Term.t
  
(** Builds a call to the transition relation function linking state
    [k] and [k']. *)
val trans_fun_of : t -> Numeral.t -> Numeral.t -> Term.t

(** Instantiate all properties to the bound *)
val props_of_bound : t -> Numeral.t -> Term.t

(** Instantiate all properties to the bound *)
val props_list_of_bound : t -> Numeral.t -> (string * Term.t) list 

(** Get property by name *)
val named_term_of_prop_name : t -> string -> Term.t
                                               
(** Instantiate invariants and valid properties to the bound *)
val invars_of_bound : ?one_state_only:bool -> t -> Numeral.t -> Term.t

(** The list of invariants and valid properties at zero. *)
val get_invars : t -> Term.t list

(** Return uninterpreted function symbols to be declared in the SMT
    solver *)
val uf_symbols_of_trans_sys : t -> UfSymbol.t list

(** Return uninterpreted function symbol definitions in topological
    order. *)
val uf_defs : t -> pred_def list

(** Return uninterpreted function symbol definitions as pairs of
    initial state and transition relation definitions, in topological
    order. *)
val uf_defs_pairs : t -> (pred_def * pred_def) list

(** Return [true] if the uninterpreted symbol is a transition relation *)
val is_trans_uf_def : t -> UfSymbol.t -> bool

(** Return [true] if the uninterpreted symbol is an initial state constraint *)
val is_init_uf_def : t -> UfSymbol.t -> bool

(** Add an invariant to the transition system *)
val add_invariant : t -> Term.t -> unit

(** Add an invariant to the transition system *)
val add_scoped_invariant : t -> string list -> Term.t -> unit

(** Return current status of all properties *)
val get_prop_status_all : t -> (string * prop_status) list

(** Return current status of all properties *)
val get_prop_status_all_unknown : t -> (string * prop_status) list

(** Return current status of property *)
val get_prop_status : t -> string -> prop_status 

(** Mark current status of property *)
val set_prop_status : t -> string -> prop_status -> unit

(** Mark property as invariant *)
val set_prop_invariant : t -> string -> unit 

(** Mark property as false *)
val set_prop_false : t -> string -> (StateVar.t * Term.t list) list -> unit 

(** Mark property as k-true *)
val set_prop_ktrue : t -> int -> string -> unit

(** Return true if the property is proved invariant *)
val is_proved : t -> string -> bool 

(** Return true if the property is proved not invariant *)
val is_disproved : t -> string -> bool 

(** Return true if all properties are either valid or invalid *)
val all_props_proved : t -> bool

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


(** Extract a path in the transition system, return an association
    list of state variables to a list of their values.

    The second argument is a function returning assignments to the
    variables, see {!SolverMethods.S.get_model}. The path is extracted
    from instant zero up to instant [k], which is the third argument. *)
val path_from_model : t -> (Var.t list -> (Var.t * Term.t) list) -> Numeral.t -> (StateVar.t * Term.t list) list

val exists_eval_on_path : pred_def list -> (Eval.value -> bool) -> Term.t -> (StateVar.t * Term.t list) list -> bool

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
