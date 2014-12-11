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

(** State variables 

    Every state variable is associated with an uninterpreted function
    symbol that is substituted for the state variable when creating
    expressions for the SMT solvers.

    State variables do not occur directly in terms, but as instances
    in a particular state, see {!Var}.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** State variable 

    A state state variable is a pair of its identifier and its scope,
    which is a list of identifiers. *)
type state_var = private string * string list

(** Hashconsed state variable *)
type t


(** {1 Hashtables, maps and sets} *)

(** Comparison function on state variables *)
val compare_state_vars : t -> t -> int

(** Equality function on state variables *)
val equal_state_vars : t -> t -> bool

(** Hashing function on state variables *)
val hash_state_var : t -> int

(** Hash table over state variables *)
module StateVarHashtbl : Hashtbl.S with type key = t

(** Set over state variables *)
module StateVarSet : Set.S with type elt = t

(** Map over state variables *)
module StateVarMap : Map.S with type key = t


(** {1 Constructor} *)

(** [mk_state_var n s t] declares a state variable of name [n] and
    type [t] and flag it as a local definition if [s] is [true]. A
    variable is a local definition if it does not occur under a [pre]
    operator.

    Declaring a state variable again with the same signature is
    harmless and will simply return the previously declared state
    variable. However, re-declaring a state variable with a different
    signature will raise an [Invalid_argument] exception. *)
val mk_state_var : ?is_input:bool -> ?is_const:bool -> string -> string list -> Type.t -> t

(** Import a state variable from a different instance into this
   hashcons table *)
val import : t -> t

(** {1 Accessor functions} *)

(** Return a previously declared state variable *)
val state_var_of_string : string * string list -> t 

(** Return the name of the state variable *)
val name_of_state_var : t -> string

(** Return the name of the state variable *)
val scope_of_state_var : t -> string list

(** Return the type of the variable *)
val type_of_state_var : t -> Type.t

(** Change the type of a state variable *)
val change_type_of_state_var : t -> Type.t -> unit

(** Return the uninterpreted function symbol of the variable *)
val uf_symbol_of_state_var : t -> UfSymbol.t

(** Return the uninterpreted function symbol of the variable *)
val state_var_of_uf_symbol : UfSymbol.t -> t

(** Return true if the state variable is an input *)
val is_input : t -> bool

(** Return true if the state variable is constant *)
val is_const : t -> bool

(** {1 Iterators over defined state variables} *)

(** [fold f a] computes [(f sN tN uN ... (f s2 t2 u2 (f s1 t1 u1
    a))...)], where [sI], [tI] and [uI], respectively are the name of
    the state variable, its types and its associated uninterpreted
    function symbol. *)
val fold : (t -> 'a -> 'a) -> 'a -> 'a 

(** [iter f] calls [f s t u] for every state variable with [s] being
    the name of the variable, [t] its type and [u] its associated
    uninterpreted function symbol. *)
val iter : (t -> unit) -> unit


(** {1 Pretty-printing} *)

(** Pretty-print a state variable *)
val pp_print_state_var : Format.formatter -> t -> unit

(** Return a string representation of a symbol *)
val string_of_state_var : t -> string

val stats : unit -> int * int * int * int * int * int


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
