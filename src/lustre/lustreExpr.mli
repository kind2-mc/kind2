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


(** Internal reperesentation of a Lustre expression

    A {!LustreExpr.t} does not contain node calls, temporal operators
    or expressions under a [pre] operator.

    There is exactly one [->] operator at the top of the expression,
    thus an expression can be represented as a pair of expressions
    [(i, t)] without [->] operators. 

    The argument of a [pre] operator is always a variable, therefore
    an expression [pre x] can be represented by the variable [x] at
    the previous state.

    A non-variable expression under a [pre] has to be abstracted to a
    fresh variable that is defined by this expression. There are no
    node calls in a Lustre expression. They have to be abstracted out
    and the results are captured in fresh variables. See
    {!LustreSimplify} for details about how the input file is
    translates

    The offsets of state variable instances are zero for the initial
    state and zero for the current state, see the constants
    {!init_offset} and {!trans_offset} and {!pre_offset}. These are
    different from the offsets in the transition system, because here
    we want to know if the initial and the step expressions are equal
    without bumping offsets. Use the functions {!base_term_of_expr},
    {!cur_term_of_expr}, and {!pre_term_of_expr} to take the
    expression on one side of the [->] operator and adjust to the
    variable offsets to the given base.

    Expressions can only be constructed with the constructors which do
    type checking and some easy simplifications with constants.

    @author Christoph Sticksel *)


(** Types of expressions do not match signature of operator *)
exception Type_mismatch

(** {1 Types} *)

(** A {!Term.t} representing a Lustre expression, state variable
    offsets refer to the current and the previous instant. 

    Cannot be constructed outside this module to enforce invariants
    about allowed offsets of state variable instants, see the
    constructors below. *)
type expr = private Term.t

(** Type of index in an equation for an array *)
type 'a bound_or_fixed = 
  | Bound of 'a    (** Equation is for each value of the index variable
                       between zero and the upper bound *)
  | Fixed of 'a    (** Fixed value for index variable *)
  | Unbound of 'a  (** unbounded index variable *)


(** Return the type of the expression *)
val type_of_expr : expr -> Type.t

(** Equality of expressions *)
val equal_expr : expr -> expr -> bool

(** Returns true iff the expr is the constant true. *)
val is_true_expr : expr -> bool

(** A Lustre expression

    The [->] operator is moved to the top of the expression, the
    expression is to be interpreted as [expr_init -> expr_step]. *)
type t = private {
  expr_init: expr ;
  (** Lustre expression for initial state *)
  expr_step: expr ;
  (** Lustre expression after initial state *)
  expr_type: Type.t ;
  (** Common type of both initial and the step expression *)
}

(** Hash table over Lustre expressions *)
module LustreExprHashtbl : Hashtbl.S with type key = t

(** Total order on lustre expressions *)
val compare : t -> t -> int

(** Total order on expressions *)
val compare_expr : expr -> expr -> int

(** Equality of expressions *)
val equal : t -> t -> bool

(** Equality of expressions *)
val hash : t -> int

(** Tail-recursive bottom-up right-to-left map on the expression *)
val map : (int -> t -> t) -> t -> t

(** Return the type of the expression *)
val type_of_lustre_expr : t -> Type.t

(** {1 Pretty-printers} 

    All pretty-printers take a Boolean flag as first argument,
    indicating if identifiers should be valid Lustre identifiers. If
    the flag is [false], indexed identifiers are printed with [\[],
    [\]] and [.]. These characters are replaced with [_] if the flag
    is [true].
*)

(** Pretty-print a Lustre type *)
val pp_print_lustre_type : bool -> Format.formatter -> Type.t -> unit 

(** Pretty-print a Lustre variable *)
val pp_print_lustre_var : bool -> Format.formatter -> StateVar.t -> unit 

(** Pretty-print a Lustre variable with its type *)
val pp_print_lustre_var_typed : bool -> Format.formatter -> StateVar.t -> unit 

(** Pretty-print a Lustre expression *)
val pp_print_lustre_expr : bool -> Format.formatter -> t -> unit 

(** Pretty-print a Lustre expression *)
val pp_print_expr : bool -> Format.formatter -> expr -> unit 

(** {1 Predicates} *)

(** Return true if the expression contains a previous state variable *)
val has_pre_var : Numeral.t -> t -> bool

(** Return true if expression is a current state variable *)
val is_var : t -> bool

(** Return true if expression is a constant state variable *)
val is_const_var : t -> bool

(** Return true if expression is a previous state variable *)
val is_pre_var : t -> bool

(** Return [true] if there is an unguarded [pre] operator in the
    expression. *)
val pre_is_unguarded : t -> bool

(** Return true if the expression is constant *)
val is_const_expr : expr -> bool

(** Return true if the expression is constant *)
val is_const : t -> bool

(** {1 Conversions to terms} *)

(** These offsets are different from the offsets in the transition
    system, because here we want to know if the initial and the step
    expressions are equal without bumping offsets. Use the constants
    {!base_offset}, {!cur_offset} or {!pre_offset} of this module, or
    the constants {!TransSys.init_base} and {!TransSys.trans_base} for
    the zero offsets. *)

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

(** Term at first instant with the given offset as zero *)
val base_term_of_t : Numeral.t -> t -> Term.t

(** Term at current instant with the given offset as zero*)
val cur_term_of_t : Numeral.t -> t -> Term.t

(** Term at previous instant with the given offset as zero *)
val pre_term_of_t : Numeral.t -> t -> Term.t

(** Return the state variable of a variable 

    Fail with [Invalid_argument "state_var_of_expr"] if the expression
    is not a variable at the current or previous offset. *)
val state_var_of_expr : t -> StateVar.t

(** Return the free variable of a variable 

    Fail with [Invalid_argument "var_of_expr"] if the expression
    is not a free variable. *)
val var_of_expr : t -> Var.t
  
(** Return all state variables occurring in the expression in a set *)
val state_vars_of_expr : t -> StateVar.StateVarSet.t

val vars_of_expr : t -> Var.VarSet.t

(** Return all state variables of the initial state expression at the
    base instant *)
val base_state_vars_of_init_expr : t -> StateVar.StateVarSet.t

(** Return all state variables of the step expression at the current
    instant *)
val cur_state_vars_of_step_expr : t -> StateVar.StateVarSet.t

val indexes_of_state_vars_in_init : StateVar.t -> t -> expr list list

val indexes_of_state_vars_in_step : StateVar.t -> t -> expr list list

(** Split a list of Lustre expressions into a list of pairs of
    expressions for the initial step and the transition steps,
    respectively *)
val split_expr_list : t list -> expr list * expr list 


(** {1 Constants} *)

(** The propositional constant true *)
val t_true : t

(** The propositional constant false *)
val t_false : t


(** {1 Constructors} *)

(** The constructors do some easy simplifcations, such as arithmetic
    and Boolean operations on constants. If the types of the arguments
    are do not match the signature of the symbol, the
    {!Type_mismatch} exception is raised. *)

(** Return an expression of an integer numeral. *)
val mk_int : Numeral.t -> t

(** Return an expression of a floating point decimal. *)
val mk_real : Decimal.t -> t

(** Return an expression of a variable. *)
val mk_var : StateVar.t -> t

val mk_free_var : Var.t -> t

(** Return an expression for the i-th index variable. *)
val mk_index_var : int -> t

(** Return the number/position of the index variable. *)
val int_of_index_var : t -> int

(** Returns [true] if the expression has index variables. *)
val has_indexes : t -> bool

(** Return a conversion to an integer numeral. *)
val mk_to_int : t -> t

(** Return a conversion to a floating-point decimal. *)
val mk_to_real : t -> t

(** Return an if-then-else expression. *)
val mk_ite : t -> t -> t -> t

(** Return the Boolean negation of the expression. *)
val mk_not : t -> t

(** Return the unary minus of the expression. *)
val mk_uminus : t -> t

(** Return the Boolean conjunction of the two expressions. *)
val mk_and : t -> t -> t 

(** Return the Boolean conjunction of the list of expressions. *)
val mk_and_n : t list -> t 

(** Return the Boolean disjunction of the two expressions. *)
val mk_or : t -> t -> t 

(** Return the Boolean disjunction of the list of expressions. *)
val mk_or_n : t list -> t 

(** Return the Boolean exclusive disjunction of the two expressions. *)
val mk_xor : t -> t -> t 

(** Return the Boolean implication of the two expressions. *)
val mk_impl : t -> t -> t 

(** Return the universal quantification of an expression. *)
val mk_forall : Var.t list -> t -> t 

(** Return the existential quantification of an expression. *)
val mk_exists : Var.t list -> t -> t 

(** Return the integer modulus of the two expressions. *)
val mk_mod : t -> t -> t 

(** Return the difference of the two expressions. *)
val mk_minus : t -> t -> t 

(** Return the sum of the two expressions. *)
val mk_plus : t -> t -> t 

(** Return the quotient of the two expressions. *)
val mk_div : t -> t -> t 

(** Return the product of the two expressions. *)
val mk_times : t -> t -> t 

(** Return the integer quotient of the two expressions. *)
val mk_intdiv : t -> t -> t 

(** Return the equality relation on the two expressions. *)
val mk_eq : t -> t -> t 

(** Return the disequality relation on the two expressions. *)
val mk_neq : t -> t -> t 

(** Return the less-than-or-equal relation on the two expressions. *)
val mk_lte : t -> t -> t 

(** Return the less-than relation on the two expressions. *)
val mk_lt : t -> t -> t 

(** Return the greater-than-or-equal relation on the two expressions. *)
val mk_gte : t -> t -> t 

(** Return the greater-than relation on the two expressions. *)
val mk_gt : t -> t -> t 

(** Apply the followed by operator [->] to the two expressions. *)
val mk_arrow : t -> t -> t

(** Apply the [pre] operator to the expression, abstract the
    expression to a fresh variable if it is not a variable at the
    current state.

    [mk_pre f c b e] returns the expression [e] and context [c] unchanged if it
    is a constant, and the previous state variable if the expression is a
    current state variable, again together with [c] unchanged.

    Otherwise the expression [e] is abstracted to a fresh variable obtained by
    calling the function [f], which returns a fresh state variable and a
    changed context [c] that records the association between the fresh variable
    and the expression. Then return an expression of the fresh state variable
    and the changed context.

    [b] is used to denote that we're in a context where there are unguarded
    pres and so we should always introduce fresh intermediate variables. *)
val mk_pre : ('a -> t -> StateVar.t * 'a) -> ('b -> Term.t) -> 'a -> bool -> t -> t * 'a

(** Select from an array *)
val mk_select : t -> t -> t

(** Returns true if the expression is a selection in an array *)
val is_select : t -> bool

(** Returns true if the expression is a selection of an array variable *)
val is_select_array_var : t -> bool

val var_of_array_select : t -> Var.t
  
(** Store in an array *)
val mk_store : t -> t -> t -> t

(** Returns true if this is a store in an array *)
val is_store : t -> bool

(** Substitute state variable at current instant with expression *)
val mk_let_cur : (StateVar.t * t) list -> t -> t

(** Substitute state variable at previous instant with expression *)
val mk_let_pre : (StateVar.t * t) list -> t -> t

(** Return an expression of a numeral *)
val mk_int_expr : Numeral.t -> expr

(** Return an expression with the same term on both sides of the [->] *)
val mk_of_expr : expr -> t 


(** Return true if the expression is constant *)
val is_const : t -> bool

val is_numeral : expr -> bool

val numeral_of_expr : expr -> Numeral.t

val unsafe_term_of_expr : expr -> Term.t
val unsafe_expr_of_term : Term.t -> expr


val mk_array : t -> t -> t

val mk_let : (Var.t * expr) list -> t -> t

val apply_subst : (Var.t * expr) list -> t -> t

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
