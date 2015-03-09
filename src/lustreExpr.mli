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


(** Lustre expressions 

    A {!LustreExpr.t} does not contain node calls, temporal operators
    or expressions under a pre operator.

    The offsets of state variable instances are zero for the initial
    state and zero for the current state. These are different from the
    offsets in the transition system, because here we want to know if
    the initial and the step expressions are equal without bumping
    offsets.

    Expressions can only be constructed with the constructors which do
    type and clock checking.

    @author Christoph Sticksel *)


(** Types of expressions do not match signature of operator *)
exception Type_mismatch

(** Clocks of expressions are not compatible *)
exception Clock_mismatch

(** A {!Term.t} representing a Lustre expression, state variable
    offsets refer to the current and the previous instant. 

    Cannot be constructed outside this module to enforce invariants
    about allowed offsets of state variable instants. *)
type expr = private Term.t

(** A clock

    Cannot be constructed outside this module to enforce invariants *)
type clock = private unit

(** A Lustre expression

    The [->] operator is moved to the top of the expression, the
    expression is to be interpreted as [expr_init -> expr_step]. *)
type t = private 

  { 

    expr_init: expr;     (** Lustre expression for initial state *)
    
    expr_step: expr;     (** Lustre expression after initial state *)
    
    expr_clock: clock;   (** Clock of expression *)
  
    expr_type: Type.t;   (** Type of expression *)
    
  }

module ExprHashtbl : Hashtbl.S with type key = t

(** Equality of expressions *)
val equal_expr : t -> t -> bool

(** Pretty-print a Lustre type *)
val pp_print_lustre_type : bool -> Format.formatter -> Type.t -> unit 

(** Pretty-print a Lustre variable *)
val pp_print_lustre_var : bool -> Format.formatter -> StateVar.t -> unit 

(** Pretty-print a Lustre variable with its type *)
val pp_print_lustre_var_typed : bool -> Format.formatter -> StateVar.t -> unit 

(** Pretty-print a Lustre expression *)
val pp_print_lustre_expr : bool -> Format.formatter -> t -> unit 


(** {1 Constants} *)

(** The base clock *)
val base_clock : clock

(** The propositional constant true *)
val t_true : t

(** The propositional constant false *)
val t_false : t

(** {1 Constructors} *)

(** Return an expression of an integer numeral *)
val mk_int : Numeral.t -> t

(** Return an expression of a floating point decimal *)
val mk_real : Decimal.t -> t

(** Return an expression of a variable *)
val mk_var : StateVar.t -> clock -> t

(** Return a conversion to an integer numeral *)
val mk_to_int : t -> t

(** Return a conversion to a floating-point decimal *)
val mk_to_real : t -> t

(** Return an if-then-else expression *)
val mk_ite : t -> t -> t -> t

(** Return the Boolean negation of the expression *)
val mk_not : t -> t

(** Return the unary minus of the expression *)
val mk_uminus : t -> t

(** Return the Boolean conjunction of the two expressions *)
val mk_and : t -> t -> t 

(** Return the Boolean disjunction of the two expressions *)
val mk_or : t -> t -> t 

(** Return the Boolean exclusive disjunction of the two expressions *)
val mk_xor : t -> t -> t 

(** Return the Boolean implication of the two expressions *)
val mk_impl : t -> t -> t 

(** Return the integer modulus of the two expressions *)
val mk_mod : t -> t -> t 

(** Return the difference of the two expressions *)
val mk_minus : t -> t -> t 

(** Return the sum of the two expressions *)
val mk_plus : t -> t -> t 

(** Return the quotient of the two expressions *)
val mk_div : t -> t -> t 

(** Return the product of the two expressions *)
val mk_times : t -> t -> t 

(** Return the integer quotient of the two expressions *)
val mk_intdiv : t -> t -> t 

(** Return the equality relation on the two expressions *)
val mk_eq : t -> t -> t 

(** Return the disequality relation on the two expressions *)
val mk_neq : t -> t -> t 

(** Return the less-than-or-equal relation on the two expressions *)
val mk_lte : t -> t -> t 

(** Return the less-than relation on the two expressions *)
val mk_lt : t -> t -> t 

(** Return the greater-than-or-equal relation on the two expressions *)
val mk_gte : t -> t -> t 

(** Return the greater-than relation on the two expressions *)
val mk_gt : t -> t -> t 

(** Apply the followed by operator [->] to the two expressions *)
val mk_arrow : t -> t -> t

(** Apply the [pre] operator to the expression, abstract the
    expression to a fresh variable if it is not a variable at the
    current state

    [mk_pre f d e] returns the expression [e] and list [d] unchanged
    if it is a constant, and the previous state variable if the
    expression is a current state variable, again together [d]
    unchanged.

    Otherwise the expression [e] is abstracted to a fresh variable
    obtained by calling the function [f], the association between the
    fresh variable and the expression is added to [d] and it is
    returned along with an expression of the fresh variable at the
    previous state. *)
val mk_pre : ('a -> t -> StateVar.t * 'a) -> 'a -> t -> t * 'a


(** {1 Conversions to terms} *)

(** These offsets are different from the offsets in the transition
    system, because here we want to know if the initial and the step
    expressions are equal without bumping offsets. *)

(** Offset of state variable at first instant *)
val base_offset : Numeral.t

(** Offset of state variable at current instant *)
val cur_offset : Numeral.t

(** Offset of state variable at previous instant *)
val pre_offset : Numeral.t

(** Instance of state variable at first instant with the given offset
    as zero *)
val base_var_of_state_var : Numeral.t -> StateVar.t -> Var.t

(** Instance of state variable at current instant with the given
    offset as zero *)
val cur_var_of_state_var : Numeral.t -> StateVar.t -> Var.t

(** Instance of state variable at previous instant with the given
    offset as zero*)
val pre_var_of_state_var : Numeral.t -> StateVar.t -> Var.t

(** Term of instance of state variable at first instant with the given
    offset as zero *)
val base_term_of_state_var : Numeral.t -> StateVar.t -> Term.t

(** Term of instance of state variable at current instant with the
    given offset as zero *)
val cur_term_of_state_var : Numeral.t -> StateVar.t -> Term.t

(** Term of instance of state variable at previous instant with the
    given offset as zero *)
val pre_term_of_state_var : Numeral.t -> StateVar.t -> Term.t

(** Term at first instant with the given offset as zero *)
val base_term_of_expr : Numeral.t -> expr -> Term.t

(** Term at current instant with the given offset as zero*)
val cur_term_of_expr : Numeral.t -> expr -> Term.t

(** Term at previous instant with the given offset as zero *)
val pre_term_of_expr : Numeral.t -> expr -> Term.t

(** {1 State variables} *)

(** Source of state variable *)
type state_var_source =
  | Input (** Input stream *)
  | Oracle (** Oracle input stream *)
  | Output (** Output stream *)
  | Observer (** Observer output stream *)
  | Local (** Local defined stream *)
  | Ghost (** Local ghost defined stream *)
  | Abstract (** Local abstracted stream *)


(** Stream from node call at position *)
type state_var_instance =  Lib.position * LustreIdent.t * StateVar.t


(** Pretty-print a source of a state variable *)
val pp_print_state_var_source : Format.formatter -> state_var_source -> unit 


(** Create a state variable of identifier and add it to a map to be
    retrieved with {!state_var_of_ident} 

    [mk_state_var_of_ident i c s v t] creates a state variable through
    {!StateVar.mk_state_var} and marks it as input if [i] is true, as
    constant if [c] is true. The name of the state variable is [v],
    its scope is [s], and its type [t]. 

    The association of the variable to the identifier it was created
    of is memoized in a hash table, so that the identifier can be
    retrieved via {!ident_of_state_var}. *)
val mk_state_var_of_ident : ?is_input:bool -> ?is_const:bool -> ?for_inv_gen:bool -> LustreIdent.index -> LustreIdent.t -> Type.t -> StateVar.t

val mk_fresh_state_var : ?is_input:bool -> ?is_const:bool -> ?for_inv_gen:bool -> LustreIdent.index -> LustreIdent.t -> Type.t -> Numeral.t ref -> StateVar.t

(** Set source of state variable *)
val set_state_var_source : StateVar.t -> state_var_source -> unit

(** Get source of state variable *)
val get_state_var_source : StateVar.t -> state_var_source

(** State variable is identical to a state variable in a node instance *)
val set_state_var_instance : StateVar.t -> Lib.position -> LustreIdent.t -> StateVar.t -> unit


val lift_term :  Lib.position -> LustreIdent.t -> Term.t -> Term.t

(** Return identical state variable in a node instance if any *)
val get_state_var_instances : StateVar.t -> state_var_instance list

(** Return true if the state variable should be visible to the user,
    false if it was created internally *)
val state_var_is_visible : StateVar.t -> bool

(** Return true if the state variable is an input *)
val state_var_is_input : StateVar.t -> bool

(** Return true if the state variable is an output *)
val state_var_is_output : StateVar.t -> bool

(** Return true if the state variable is a local variable *)
val state_var_is_local : StateVar.t -> bool

(** Return previously created state variable of the same identifier

    Raise [Not_found] if there is no state variable of the given
    identifier. *)
val state_var_of_ident : LustreIdent.index -> LustreIdent.t -> StateVar.t

(** Return the identifier of a state variable

    The state variable must have been created through
    {!state_var_of_ident} to obtain the same identifier. Raise
    [Not_found] if the state variable does not have an identifier
    associated. *)
val ident_of_state_var : StateVar.t -> LustreIdent.t * LustreIdent.index

(** Return the state variable of a variable if the variable is a
    variable at the current or previous state *)
val state_var_of_expr : t -> StateVar.t

(** Return state variables that occur as previous state variables *)
val stateful_vars_of_expr : t -> StateVar.StateVarSet.t

(** Return state variables that occur as current state variables *)
val current_vars_of_expr : t -> StateVar.StateVarSet.t

(** Return all state variables that occur in the expression *)
val state_vars_of_expr : t -> StateVar.StateVarSet.t

(** Split a list of Lustre expressions into a list of pairs of
    expressions for the initial step and the transition steps,
    respectively *)
val split_expr_list : t list -> expr list * expr list 

(** Return [true] if there is an unguarded [pre] operator in the
    expression. *)
val pre_is_unguarded : t -> bool

(** Guard unguarded pre expression with a fresh oracle constant

    [oracles_for_unguarded_pres f o e] obtains a fresh constant state
    variable from [f] for each unguarded pre operator and replaces the
    expression with the fresh variable and adds the fresh variable to
    the list [o].

    An unguarded pre is a previous state variable occuring in the
    initial state expression, since the arrow operator has been lifted
    to the top of the expression. *)
val oracles_for_unguarded_pres : Lib.position -> (StateVar.t -> StateVar.t) -> (Lib.position -> string -> unit) ->  StateVar.t list -> t -> t * StateVar.t list

(** {1 Predicates} *)

(** Return true if the expression contains a previous state variable *)
val has_pre_var : Numeral.t -> t -> bool

(** Return true if expression is a current state variable *)
val is_var : t -> bool

(** Return true if expression is a previous state variable *)
val is_pre_var : t -> bool

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
