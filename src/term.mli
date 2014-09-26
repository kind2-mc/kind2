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

(** Term representation

    Terms are hashconsed for maximal sharing, comparison with physical
    equality and to store type information.

    Terms are lambda trees, see {!Ltree}, with symbols of type
    {!Symbol.t}, free variables of type {!Var.t} and types {!Type.t}.

    The type {!t} is private and cannot be constructed outside
    this module in order to ensure that all equal subterms are
    physically equal for hashconsing.

    Use the constructor functions like {!mk_true}, {!mk_num} etc. to
    construct terms. An exception will be raised if an incorrectly
    typed term is constructed.

    @author Christoph Sticksel
*)


(** {1 Types and hash-consing} *)

module T : Ltree.S
  with type symbol = Symbol.t
  and type var = Var.t
  and type sort = Type.t

(** Terms are hashconsed abstract syntax trees *)
type t = T.t
    
(** {1 Hashtables, maps and sets} *)

(** Comparison function on terms *)
val compare : t -> t -> int

(** Equality function on terms *)
val equal : t -> t -> bool

(** Hashing function on terms *)
val hash : t -> int

(** Hash table over terms *)
module TermHashtbl : Hashtbl.S with type key = t

(** Set over terms *)
module TermSet : Set.S with type elt = t

(** Map over terms *)
module TermMap : Map.S with type key = t


(** {1 Constructors} *)

(** Create a hashconsed term *)
val mk_term : T.t_node -> t

(** Import a term from a different instance into this hashcons table *)
val import : t -> t

(** Create the propositional constant [true] *)
val mk_true : unit -> t

(** Create the propositional constant [false] *)
val mk_false : unit -> t

(** Create an Boolean negation

    Hint: consider using {!negate} to avoid double negations *)
val mk_not : t -> t

(** Create a Boolean implication *)
val mk_implies : t list -> t

(** Create an Boolean conjunction *)
val mk_and : t list -> t

(** Create an Boolean disjunction *)
val mk_or : t list -> t

(** Create an Boolean exclusive disjunction *)
val mk_xor : t list -> t

(** Create an equality *)
val mk_eq : t list -> t

(** Create an pairwise distinct predicate *)
val mk_distinct : t list -> t

(** Create an if-then-else term *)
val mk_ite : t -> t -> t -> t

(** Create an integer numeral *)
val mk_num : Numeral.t -> t

(** Create an integer numeral *)
val mk_num_of_int : int -> t

(** Create a floating point decimal *)
val mk_dec : Decimal.t -> t

(*
(** Create a floating point decimal *)
val mk_dec_of_float : float -> t
*)

(** Create a constant bitvector *)
val mk_bv : Lib.bitvector -> t

(** Create an integer or real difference *)
val mk_minus : t list -> t

(** Create an integer or real sum *)
val mk_plus : t list -> t

(** Create an integer or real product *)
val mk_times : t list -> t

(** Create a real quotient *)
val mk_div : t list -> t

(** Create an integer quotient *)
val mk_intdiv : t list -> t

(** Create an integer modulus *)
val mk_mod : t -> t -> t

(** Create an absolute value *)
val mk_abs : t -> t

(** Create a less-or-equal predicate *)
val mk_leq : t list -> t

(** Create a less-than predicate *)
val mk_lt : t list -> t

(** Create a greater-or-equal predicate *)
val mk_geq : t list -> t

(** Create a greater-than predicate *)
val mk_gt : t list -> t

(** Create a conversion to a real decimal *)
val mk_to_real : t -> t

(** Create a conversion to an integer numeral *)
val mk_to_int : t -> t

(** Create a predicate for coincidence of a real with an integer *)
val mk_is_int : t -> t

(** Create a predicate for divisibility by a constant integer *)
val mk_divisible : Numeral.t -> t -> t

(** Uniquely name a term with an integer and return a named term and
    its name *)
val mk_named : t -> int * t

(** Create an uninterpreted constant or function *)
val mk_uf : UfSymbol.t -> t list -> t
    
(** Create a symbol to be bound to a term *)
val mk_var : Var.t -> t 

(** Create a binding of symbols to terms *)
val mk_let : (Var.t * t) list -> t -> t

(** Return a hashconsed existentially quantified term *)
val mk_exists : Var.t list -> t -> t

(** Return a hashconsed universally quantified term *)
val mk_forall : Var.t list -> t -> t

(** {1 Constant terms} *)

(** The propositional constant [true] *)
val t_true : t 

(** The propositional constant [false] *)
val t_false : t 


(** {2 Prefix and infix operators for term construction} *)

module Abbrev :
sig

  (** Prefix operator to create an numeral *)
  val ( ?%@ ) : int -> t
(*
  (** Prefix operator to create an decimal *)
  val ( ?/@ ) : float -> t
*)
  (** Prefix operator to create an Boolean negation *)
  val ( !@ ) : t -> t

  (** Infix operator to create a Boolean implication *)
  val ( =>@ ) : t -> t -> t

  (** Infix operator to create a Boolean conjunction *)
  val ( &@ ) : t -> t -> t

  (** Infix operator to create a Boolean disjunction *)
  val ( |@ ) : t -> t -> t

  (** Infix operator to create an equality *)
  val ( =@ ) : t -> t -> t 

  (** Prefix operator to create an integer or real negation *)
  val ( ~@ ) : t -> t

  (** Infix operator to create an integer or real difference *)
  val ( -@ ) : t -> t -> t

  (** Infix operator to create an integer or real sum *)
  val ( +@ ) : t -> t -> t

  (** Infix operator to create an integer or real product *)
  val ( *@ ) : t -> t -> t

  (** Infix operator to create a real quotient *)
  val ( //@ ) : t -> t -> t

  (** Infix operator to create an integer quotient *)
  val ( /%@ ) : t -> t -> t

  (** Infix operator to create a less-or-equal predicate *)
  val ( <=@ ) : t -> t -> t

  (** Infix operator to create a less-than predicate *)
  val ( <@ ) : t -> t -> t

  (** Infix operator to create a greater-or-equal predicate *)
  val ( >=@ ) : t -> t -> t

  (** Infix operator to create a greater-than predicate *)
  val ( >@ ) : t -> t -> t

end

(** {1 Additional term constructors} *)

(** Create the propositional constant [true] or [false] *)
val mk_bool : bool -> t 

(** Create a constant *)
val mk_const_of_symbol_node : Symbol.symbol -> t 

(** Create constant of a hashconsed symbol *)
val mk_const : Symbol.t -> t 

(** Create a function application *)
val mk_app_of_symbol_node : Symbol.symbol -> t list -> t

(** Create a function application of a hashconsed symbol *)
val mk_app : Symbol.t -> t list -> t

(** Increment integer or real term by one *)
val mk_succ : t -> t 

(** Decrement integer or real term by one *)
val mk_pred : t -> t

(** Negate term, avoiding double negation *)
val negate : t -> t 

(** Remove top negation from term, otherwise return term unchanged *)
val unnegate : t -> t 

(** {1 Accessor functions} *)

(** Return the type of the term *)
val type_of_term : t -> Type.t

(** Return the node of the hashconsed term *)
(* val node_of_term : t -> T.t_node *)

(** Flatten top node of term *)
val destruct : t -> T.flat

(** Convert a flat term to a term *)
val construct : T.flat -> t

(** Return true if the term is a simple Boolean atom, that is, has
    type Boolean and does not contain subterms of type Boolean *)
val is_atom : t -> bool

(** Return true if the top symbol of the term is a negation *)
val is_negated : t -> bool

(** Return [true] if the term is a free variable *)
val is_free_var : t -> bool

(** Return the variable of a free variable term *)
val free_var_of_term : t -> Var.t

(** Return [true] if the term is a bound variable *)
val is_bound_var : t -> bool

(** Return [true] if the term is a leaf symbol *)
val is_leaf : t -> bool

(** Return the symbol of a leaf term *)
val leaf_of_term : t -> Symbol.t

(** Return [true] if the term is a function application *)
val is_node : t -> bool

(** Return the symbol of a function application *)
val node_symbol_of_term : t -> Symbol.t

(** Return the arguments of a function application *)
val node_args_of_term : t -> t list

(** Return [true] if the term is a let binding *)
val is_let : t -> bool

(** Return [true] if the term is an existential quantifier *)
val is_exists : t -> bool

(** Return true if the term is a universal quantifier *)
val is_forall : t -> bool 

(** Return true if the term is a named term *)
val is_named : t -> bool

(** Return the term of a named term *)
val term_of_named : t -> t

(** Return the name of a named term *)
val name_of_named : t -> int

(** Return true if the term is an integer constant *)
val is_numeral : t -> bool

(** Return integer constant of a term *)
val numeral_of_term : t -> Numeral.t

(** Return true if the term is a decimal constant *)
val is_decimal : t -> bool

(** Return decimal constant of a term *)
val decimal_of_term : t -> Decimal.t

(** Return true if the term is a Boolean constant *)
val is_bool : t -> bool

(** Return Boolean constant of a term *)
val bool_of_term : t -> bool


(** {1 Pretty-printing} *)

(** Pretty-print a term *)
val pp_print_term : Format.formatter -> t -> unit

(** Pretty-print a term to the standard formatter *)
val print_term : t -> unit

(** Return a string representation of a t *)
val string_of_term : t -> string 

(** {1 Conversions} *)

(** Evaluate the term bottom-up and right-to-left. The evaluation
    function is called at each node of the term with the the term
    being evaluated, and the list of values computed for the
    subterms. Let bindings are lazily unfolded. *)
val eval_t : (T.flat -> 'a list -> 'a) -> t -> 'a

(** Tail-recursive bottom-up right-to-left map on the term
    
    Not every subterm is a proper term, since the de Bruijn indexes are
    shifted. Therefore, the function [f] is called with the number of
    let bindings the subterm is under as first argument, so that the
    indexes can be adjusted in the subterm if necessary. *)
val map : (int -> T.t -> T.t) -> t -> t

(** Convert [(= 0 (mod t n))] to [(divisble n t)]

    The term [n] must be an integer numeral. *)
val mod_to_divisible : t -> t

(** Convert [(divisble n t)] to [(= 0 (mod t n))] *)
val divisible_to_mod : t -> t

(** Convert negative numerals and decimals to negations of their
    absolute value *)
val nums_to_pos_nums : t -> t 

(** Add to offset of state variable instances

    Negative values are allowed *)
val bump_state : Numeral.t -> t -> t

(** Apply function to term for instants 0..k *)
val bump_and_apply_k : (t -> unit) -> Numeral.t -> t -> unit

(** Return the state variables occurring in the term *)
val state_vars_of_term : t -> StateVar.StateVarSet.t

(** Return the variables occurring in the term *)
val vars_of_term : t -> Var.VarSet.t

(** Return the state variables at given offset in term *)
val state_vars_at_offset_of_term : Numeral.t -> t -> StateVar.StateVarSet.t

(** Return the state variables at given offset in term *)
val vars_at_offset_of_term : Numeral.t -> t -> Var.VarSet.t

(** Return the minimal and maximal offset of state variable instances

    Return [(None, None)] if there are no state variable instances in
    the term. *)
val var_offsets_of_term : t -> Numeral.t option * Numeral.t option

val stats : unit -> int * int * int * int * int * int

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
