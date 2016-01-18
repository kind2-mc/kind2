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

(** Abstract syntax trees with binders and quantifiers

    An abstract syntax tree with binders extends a basic first-order
    term structure with let bindings and quantifiers. The abstract
    syntax tree is parametrized by the three types of its symbols,
    its free variables and its sorts.

    A basic term is a tree structure, where a term is either a leaf
    containing a symbol or a variable. A term can also be a node
    containing a symbol with one or more subterms. All symbols are
    variadic and arity constraints are not checked or enforced in this
    module.

    For let bindings and quantifiers we add typed lambda abstractions
    and distinguish between free and bound variables. A typed lambda
    abstraction is a term where one or more variables are bound. We do
    nameless abstraction with de Bruijn indexes, hence a bound
    variables is just its index, whereas free variables are values of
    the type of free variables.

    A let binding is a lambda abstraction of [n] bound variables
    together with [n] terms that are to be substituted for the bound
    variables. Quantifiers are just lambda abstractions. 

    In order to maintain invariants about de Bruijn indexes, the type
    of an abstract syntax term is private to this module and terms
    must be created with the appropriate constructors.

    In addition, there is a type of flat terms, where the topmost let
    binding has been evaluated. An abstract syntax term can be
    converted to a flat term with the {!S.destruct} function, which
    distributes let bindings over nodes and ensures that the top
    symbols of the term is a node, a leaf or a variable. Subterms of a
    nodes are abstract syntax terms with binders and {!S.destruct} can
    be repeatedly applied to these subterms.

    Tail-recursive fold and map functions are provided. The
    {!S.eval_t} function presents the subterms bottom-up and
    right-to-left to the folding function and lazily evaluates all let
    bindings. It fails when the term contains quantifiers. The
    {!S.map} function presents all subterms to the function, again
    bottom-up and right-to-left, let bindings are not unfolded. Hence,
    not every subterm is a proper abstract syntax term and the mapping
    function is given the number of let binding the subterm is under
    as an argument.

    @author Christoph Sticksel *)


(** Input signature for functor *)
module type BaseTypes =
sig

  (** Symbol *)
  type symbol
  
  (** Variable *)
  type var
    
  (** Sort *)
  type sort

  (** Attribute *)
  type attr

  (** Hash value of a symbol *)
  val hash_of_symbol : symbol -> int

  (** Hash value of a variable *)
  val hash_of_var : var -> int

  (** Hash value of a sort *)
  val hash_of_sort : sort -> int
    
  (** Hash value of an attribute *)
  val hash_of_attr : attr -> int
    
  (** Return the sort of a variable *)
  val sort_of_var : var -> sort

  val mk_fresh_var : sort -> var

  val import_symbol : symbol -> symbol

  val import_var : var -> var

  val import_sort : sort -> sort

  (** Pretty-print a symbol *)
  val pp_print_symbol : Format.formatter -> symbol -> unit

  (** Pretty-print a variable *)
  val pp_print_var : Format.formatter -> var -> unit

  (** Pretty-print a sort *)
  val pp_print_sort : Format.formatter -> sort -> unit

  (** Pretty-print an attribute *)
  val pp_print_attr : Format.formatter -> attr -> unit

end

(** Output signature of functor *)
module type S =
sig

  (** Symbol *)
  type symbol

  (** Variable *)
  type var

  (** Sort *)
  type sort

  (** Attribute *)
  type attr

  (** Lambda abstraction over symbols, variables and sort of the types
      given. Values of the type cannot be constructed outside this
      module in order to maintain invariants about the data type. *)
  type lambda_node = private L of sort list * t

  (** Hashconsed lambda abstraction *)
  and lambda = private (lambda_node, unit) Hashcons.hash_consed

  (** Abstract syntax term over symbols, variables and sort of the
      types given. Values of the type cannot be constructed outside
      this module in order to maintain invariants about the data
      type. Use the constructors {!mk_var}, {!mk_const}, {!mk_app},
      {!mk_let}, {!mk_exists} and {!mk_forall}. *)
  and t_node = private
      FreeVar of var
    | BoundVar of int
    | Leaf of symbol
    | Node of symbol * t list
    | Let of lambda * t list
    | Exists of lambda
    | Forall of lambda
    | Annot of t * attr

  (** Properties of a term *)
  and t_prop = private { bound_vars : int list } 

  (** Hashconsed abstract syntax term *)
  and t = private (t_node, t_prop) Hashcons.hash_consed

  (** Term over symbols, variables and sort of the types given where
      the topmost symbol is not a binding 

      This type must remain private, because {!construct} does not
      check the invariants and would be a backdoor to construct unsafe
      terms. *)
  and flat = private 
    | Var of var
    | Const of symbol 
    | App of symbol * t list
    | Attr of t * attr

  (** Comparison function on terms *)
  val compare : t -> t -> int

  (** Equality function on terms *)
  val equal : t -> t -> bool

  (** Hash function on terms *)
  val hash : t -> int

  (** Unique identifier for term *)
  val tag : t -> int

  (** Constructor for a lambda expression *)
  val mk_lambda : var list -> t -> lambda

  (** Beta-evaluate a lambda expression *)
  val eval_lambda : lambda -> t list -> t

  (** Partialy Beta-evaluate a lambda expression *)
  val partial_eval_lambda : lambda -> t list -> lambda

  (** Constructor for a term *)
  val mk_term : t_node -> t

  (** Constructor for a free variable with indexes *)
  val mk_var : var -> t

  (** Constructor for a constant *)
  val mk_const : symbol -> t

  (** Constructor for a function application *)
  val mk_app : symbol -> t list -> t

  (** Constructor for a let binding *)
  val mk_let : (var * t) list -> t -> t

  (** Constructor for a let binding *)
  val mk_let_elim : (var * t) list -> t -> t

  (** Constructor for an existential quantification over an indexed
      free variable *)
  val mk_exists : var list -> t -> t

  (** Constructor for a universal quantification over an indexed
      free variable *)
  val mk_forall : var list -> t -> t

  (** Constructor for an annotated term *)
  val mk_annot : t -> attr -> t

  (** Return the node of a hashconsed term *)
  val node_of_t : t -> t_node

  (** Return the node of a hashconsed lamda abstraction *)
  val node_of_lambda : lambda -> lambda_node

  (** Return the sorts of a hashconsed lambda abstraction *)
  val sorts_of_lambda : lambda -> sort list

  (** Return the unique tag of a hashconsed term *)
  val tag_of_t : t -> int

  (** Evaluate the term bottom-up and right-to-left. The evaluation
      function is called at each node of the term with the term being
      evaluated and the list of values computed for the subterms. Let
      bindings are lazily unfolded.  *)
  val eval_t : (flat -> 'a list -> 'a) -> t -> 'a

  (** Tail-recursive bottom-up right-to-left map on the term

      Not every subterm is a proper term, since the de Bruijn indexes are
      shifted. Therefore, the function [f] is called with the number of
      let bindings the subterm is under as first argument, so that the
      indexes can be adjusted in the subterm if necessary. *)
  val map : (int -> t -> t) -> t -> t

  (** Return the top symbol of a term along with its subterms

      If the top symbol of a term is a let binding, the binding is
      distributed over the subterms. *)
  val destruct : t -> flat

  (** Returns [true] if the term has quantifiers *)
  val has_quantifier : t -> bool

  val instantiate : lambda -> t list -> t

  (** Convert the flattened representation back into a term *)
  val construct : flat -> t

  (** Import a term into the hashcons table by rebuilding it bottom
      up *)
  val import : t -> t

  (** Import a lambda abstraction into the hashcons table by
      rebuilding it bottom up *)
  val import_lambda : lambda -> lambda

  (** Pretty-print a term *)
  val pp_print_term : ?db:int -> Format.formatter -> t -> unit
    
  (** Pretty-print a term *)
  val pp_print_term : ?db:int -> Format.formatter -> t -> unit

  val pp_print_lambda_w :
    (?arity:int -> Format.formatter -> symbol -> unit) ->
    (Format.formatter -> sort -> unit) ->
    ?db:int -> Format.formatter -> lambda -> unit

  val pp_print_term_w :
    (?arity:int -> Format.formatter -> symbol -> unit) ->
    (Format.formatter -> sort -> unit) ->
    ?db:int -> Format.formatter -> t -> unit

  (** Pretty-print a term *)
  val print_term : ?db:int -> t -> unit

  (** Pretty-print a lambda abstraction *)
  val pp_print_lambda : ?db:int -> Format.formatter -> lambda -> unit
    
  (** Pretty-print a lambda abstraction *)
  val print_lambda : ?db:int -> lambda -> unit
    
  val stats : unit -> int * int * int * int * int * int
  
end

(** Functor to create a higher-order abstract syntax tree module *)
module Make (T : BaseTypes) :
  (S with type symbol = T.symbol 
      and type var = T.var 
      and type sort = T.sort 
      and type attr = T.attr) 


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
