(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** State variables 

    Every state variable is associated with an uninterpreted function
    symbol that is substituted for the state variable when creating
    expressions for the SMT solvers.

    State variables do not occur directly in terms, but as instances
    in a particular state, see {!Var}.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** State variable *)
type state_var = string

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
val mk_state_var : string -> bool -> Type.t -> t

(** Import a state variable from a different instance into this
   hashcons table *)
val import : t -> t

(** {1 Accessor functions} *)

(** Return a previously declared state variable *)
val state_var_of_string : string -> t 

(** Return a previously declared state variable by its name in the input file *)
val state_var_of_original_name : string -> t 

(** Return the name of the state variable *)
val name_of_state_var : t -> string

(** Return the name of the state variable as it occurred in the
    original input *)
val original_name_of_state_var : t -> string

(** Return the type of the variable *)
val type_of_state_var : t -> Type.t

(** Return the uninterpreted function symbol of the variable *)
val uf_symbol_of_state_var : t -> UfSymbol.t

(** Return the uninterpreted function symbol of the variable *)
val state_var_of_uf_symbol : UfSymbol.t -> t

val is_definition : t -> bool

(** {1 Iterators over defined state variables} *)

(** [fold f a] computes [(f sN tN uN ... (f s2 t2 u2 (f s1 t1 u1
    a))...)], where [sI], [tI] and [uI], respectively are the name of
    the state variable, its types and its associated uninterpreted
    function symbol. *)
(* val fold : (string -> Type.t -> UfSymbol.t -> 'a -> 'a) -> 'a -> 'a *)
val fold : (t -> 'a -> 'a) -> 'a -> 'a 

(** [iter f] calls [f s t u] for every state variable with [s] being
    the name of the variable, [t] its type and [u] its associated
    uninterpreted function symbol. *)
val iter : (t -> unit) -> unit
(* val iter : (string -> Type.t -> UfSymbol.t -> unit) -> unit *)


(** {1 Pretty-printing} *)

(** Pretty-print a state variable *)
val pp_print_state_var : Format.formatter -> t -> unit

(** Pretty-print a state variable as it occurred in the original input *)
val pp_print_state_var_original : Format.formatter -> t -> unit

(** Return a string representation of a symbol *)
val string_of_state_var : t -> string


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
