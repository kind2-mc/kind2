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

(** Input format *)
type input = 
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

(** The transition system 

    The transition system must be constructed with the function
    {!mk_trans_sys}. Fields of the record are exposed, but accessing
    them is deprecated, use the provided functions below. *)
type t (* = private

  {

    (** Definitions of uninterpreted function symbols for initial
        state constraint and transition relation *)
    pred_defs : (pred_def * pred_def) list;

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

    (* The input which produced this system. *)
    input : input;

    mutable invars : Term.t list;

    (** Status of property *)
    mutable prop_status : (string * prop_status) list;

  }

       *)
    
(** Create a transition system

    For each state variable of a bounded integer type, add a
    constraint to the invariants. *)
val mk_trans_sys : (pred_def * pred_def) list -> StateVar.t list -> UfSymbol.t * (Var.t * Term.t) list -> UfSymbol.t * (Var.t * Term.t) list -> (string * Term.t) list -> input -> t

(** Pretty-print a predicate definition *)
val pp_print_uf_def : Format.formatter -> pred_def -> unit

(** Pretty-print a transition system *)
val pp_print_trans_sys : Format.formatter -> t -> unit

(** Get the required logic for the SMT solver *)
val get_logic : t -> SMTExpr.logic
                       
(** Return topmost predicate definition for initial state with map of
    formal to actual parameters *)
val init_top : t -> UfSymbol.t * (Var.t * Term.t) list

(** Topmost predicate definition for transition relation with map of
    formal to actual parameters *)
val trans_top : t -> UfSymbol.t * (Var.t * Term.t) list

(** Return the state variables of the transition system *)
val state_vars : t -> StateVar.t list

(** Return the input used to produce the transition system *)
val get_input : t -> input

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

(** Get property by name *)
val prop_of_name : t -> string -> Term.t

(** Instantiate invariants and valid properties to the bound *)
val invars_of_bound : t -> Numeral.t -> Term.t

(** Return uninterpreted function symbols to be declared in the SMT solver *)
val uf_symbols_of_trans_sys : t -> UfSymbol.t list

(** Return uninterpreted function symbol definitions *)
val uf_defs : t -> pred_def list

(** Return uninterpreted function symbol definitions as pairs of
    initial state and transition relation definitions *)
val uf_defs_pairs : t -> (pred_def * pred_def) list

(** Return [true] if the uninterpreted symbol is a transition relation *)
val is_trans_uf_def : t -> UfSymbol.t -> bool

(** Return [true] if the uninterpreted symbol is an initial state constraint *)
val is_init_uf_def : t -> UfSymbol.t -> bool

(** Add an invariant to the transition system *)
val add_invariant : t -> Term.t -> unit

(** Return current status of all properties *)
val prop_status_all : t -> (string * prop_status) list

(** Return current status of all properties *)
val prop_status_all_unknown : t -> (string * prop_status) list

(** Return current status of property *)
val prop_status : t -> string -> prop_status 

(** Mark property as invariant *)
val prop_invariant : t -> string -> unit 

(** Mark property as false *)
val prop_false : t -> string -> (StateVar.t * Term.t list) list -> unit 

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

val exists_eval_on_path : pred_def list -> (Eval.value -> bool) -> Term.t -> (StateVar.t * Term.t list) list -> bool

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
