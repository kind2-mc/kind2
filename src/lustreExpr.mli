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

    These Lustre expressions are normalized in the following ways:

    - There is only one [->] operator at the top of the expression,
      therefore an expression is a pair of expressions [(i, t)]
      without [->] operators, to be interpreted as [i -> t].

    - The argument of a [pre] is a variable, therefore variables are
      either at the current state or at the previous state and
      represented as [Var] or [VarPre] constants.

    - The offsets of state variable instances are zero for the initial
      state and zero for the current state. These are different from
      the offsets in the transition system, because here we want to
      know if the initial and the step expressions are equal without
      bumping offsets

    Expressions can only be constructed with the constructors which do
    type and clock checking.

    @author Christoph Sticksel
*)


(** Types of expressions do not match signature of operator *)
exception Type_mismatch

(** Clocks of expressions are not compatible *)
exception Clock_mismatch

(*
(** Unary operators

    The argument to a [pre] is a variable, see [Var] and [VarPre] in
    {!expr}. *)
type unary_op =
  | Not
  | Uminus
  | ToInt
  | ToReal

(** Binary operators 
    
    The [->] operator is moved to the top of the expression, such that
    an expression is effectively a pair of expressions without [->]
    operators. *)
type binary_op =
  | And 
  | Or
  | Xor
  | Impl
  | Mod
  | Minus
  | Plus 
  | Div
  | Times 
  | IntDiv
  | Eq
  | Neq
  | Lte
  | Lt
  | Gte
  | Gt

(** Variadic operators *)
type var_op =
  | OneHot


(** An expression *)
type expr = private
  | Var of LustreIdent.t
  | VarPre of LustreIdent.t
  | True
  | False
  | Int of Numeral.t
  | Real of Decimal.t
  | UnaryOp of unary_op * expr
  | BinaryOp of binary_op * (expr * expr)
  | VarOp of var_op * expr list
  | Ite of expr * expr * expr
*)

type expr

(** A clock *)
type clock = unit


(** A Lustre expression

    The [->} operator is moved to the top of the expression, the
    expression is to be interpreted as [expr_init -> expr_step]. *)
type t = private { 

  expr_init: expr;                     (** Lustre expression for
                                           initial state *)

  expr_step: expr;                     (** Lustre expression after
                                           initial state *)

  expr_clock: clock;                   (** Clock of expression *)

  expr_type: Type.t;             (** Type of expression 

                                     Record type here, this is the
                                     common type of expr_init and
                                     expr_step *)

}

val equal_expr : t -> t -> bool


(** Pretty-print a Lustre variable. *)
val pp_print_lustre_type : bool -> Format.formatter -> Type.t -> unit 


(** Pretty-print a Lustre variable. *)
val pp_print_lustre_var : bool -> Format.formatter -> StateVar.t -> unit 


(** Pretty-print a Lustre expression. *)
val pp_print_lustre_expr : bool -> Format.formatter -> t -> unit 


(** {1 Constants} *)

(** The base clock *)
val base_clock : clock

(** The propositional constant true *)
val t_true : t

(** The propositional constant false *)
val t_false : t

(** {1 Constructors} *)

(** Create or return state variable of identifier *)
val state_var_of_ident : LustreIdent.index -> LustreIdent.t -> Type.t -> StateVar.t

(** Return the identifier of a state variable

    The state variable must have been created through
    {!state_var_of_ident} to obtain the same identifier. *)
val ident_of_state_var : StateVar.t -> LustreIdent.t 

(** Return an integer numeral. *)
val mk_int : Numeral.t -> t

(** Return a floating point decimal. *)
val mk_real : Decimal.t -> t

(** Return a variable *)
val mk_var_of_state_var : StateVar.t -> clock -> t

(** Return a variable.

    [mk_var n t c] returns a variable with name [n], type [t] and
    clock [c]. *)
val mk_var : LustreIdent.index -> LustreIdent.t -> Type.t -> clock -> t

(** Return a variable with a [pre] operator applied to it.

    [mk_var_pre n t c] returns a variable with name [n], type [t] and
    clock [c]. *)
val mk_var_pre : LustreIdent.index -> LustreIdent.t -> Type.t -> clock -> t

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

(** Return the Boolean disjunction of the two expressions. *)
val mk_or : t -> t -> t 

(** Return the Boolean exclusive disjunction of the two expressions. *)
val mk_xor : t -> t -> t 

(** Return the Boolean implication of the two expressions. *)
val mk_impl : t -> t -> t 

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
    expression to a fresh variable if it is not a variable.

    [mk_pre f (v, c, o) e] returns the expression [e] unchanged if it is
    a constant, a [VarPre] expression if [e] is a [Var] expression and
    otherwise abstracts the expression [e] to a new variable and
    returns a [VarPre] expression of this variable. 

    The function [f] is called to obtain a fresh variable name, the
    association between the fresh variable and [e] is added to the
    list [v], the second and third elements of the pair, [c], and [o],
    are left unchanged. *)
val mk_pre : (unit -> LustreIdent.index * LustreIdent.t) -> (StateVar.t * t) list -> t -> (t * (StateVar.t * t) list)


(** {1 Conversions to terms} *)

(** Offset of state variable at first instant *)
val base_offset : Numeral.t

(** Offset of state variable at current instant *)
val cur_offset : Numeral.t

(** Offset of state variable at previous instant *)
val pre_offset : Numeral.t

(** Instance of state variable at first instant *)
val base_var_of_state_var : Numeral.t -> StateVar.t -> Var.t

(** Instance of state variable at current instant *)
val cur_var_of_state_var : Numeral.t -> StateVar.t -> Var.t

(** Instance of state variable at previous instant *)
val pre_var_of_state_var : Numeral.t -> StateVar.t -> Var.t
    
(** Term of instance of state variable at first instant *)
val base_term_of_state_var : Numeral.t -> StateVar.t -> Term.t

(** Term of instance of state variable at current instant *)
val cur_term_of_state_var : Numeral.t -> StateVar.t -> Term.t

(** Term of instance of state variable at previous instant *)
val pre_term_of_state_var : Numeral.t -> StateVar.t -> Term.t

(** Term at first instant *)
val base_term_of_expr : Numeral.t -> expr -> Term.t

(** Term at current instant *)
val cur_term_of_expr : Numeral.t -> expr -> Term.t

(** Term at previous instant *)
val pre_term_of_expr : Numeral.t -> expr -> Term.t


(** {1 Predicates} *)

(** Return true if expression contains a previous state variable *)
val has_pre_var : t -> bool

(** Return [true] if there is an unguarded [pre] operator in the
    expression. *)
val pre_is_unguarded : t -> bool

(** Return true if expression is a current state variable *)
val is_var : t -> bool

(** Return true if expression is a previous state variable *)
val is_pre_var : t -> bool

(** Return the state variable of a variable *)
val state_var_of_expr : t -> StateVar.t

(** Return state variables that occur as previous state variables *)
val stateful_vars_of_expr : t -> StateVar.StateVarSet.t

(** Return all state variables that occur in the expression *)
val state_vars_of_expr : t -> StateVar.StateVarSet.t

(** Split a list of Lustre expressions into a list of pairs of
    expressions for the initial step and the transition steps,
    respectively *)
val split_expr_list : t list -> expr list * expr list 


val oracles_for_unguarded_pres : (unit -> LustreIdent.index * LustreIdent.t) -> StateVar.t list -> t -> t * StateVar.t list

(*
(** Return a list of names of variables in the expression *)
val vars_of_expr : expr -> LustreIdent.t list
*)
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
