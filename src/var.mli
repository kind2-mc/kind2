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

(** Variables in terms

    A variable is an instance of a state variable (see {!StateVar}) in
    a state relative to an initial state. A variable can also be a
    temporary free variable that is to be bound in a let expression.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Hashconsed variable *)
type t


(** {1 Hashtables, maps and sets} *)

(** Comparison function on variables *)
val compare_vars : t -> t -> int

(** Equality function on variables *)
val equal_vars : t -> t -> bool

(** Hashing function on variables *)
val hash_var : t -> int

(** Hash table over variables *)
module VarHashtbl : Hashtbl.S with type key = t

(** Set over variables *)
module VarSet : Set.S with type elt = t

(** Map over variables *)
module VarMap : Map.S with type key = t


(** {1 Constructor} *)

(** Return an instance of a state variables *)
val mk_state_var_instance : StateVar.t -> Lib.numeral -> t

(** Return a temporary variable *)
val mk_temp_var : HString.t -> Type.t -> t

(** Import a variable from a different instance into this hashcons table *)
val import : t -> t

(** {1 Accessor functions} *)

(** Return the type of the variable *)
val type_of_var : t -> Type.t

(** Return the state variable of a state variable instance *)
val state_var_of_state_var_instance : t -> StateVar.t

(** Return the offset of a state variable instance *)
val offset_of_state_var_instance : t -> Lib.numeral

(** Return the offset of a state variable instance *)
val hstring_of_temp_var : t -> HString.t

(** Add to the offset of a state variable instance

    Negative values are allowed *)
val bump_offset_of_state_var_instance : Lib.numeral -> t -> t   

(** {1 Pretty-printing} *)

(** Pretty-print a hashconsed variable *)
val pp_print_var : Format.formatter -> t -> unit

(** Pretty-print a hashconsed variable to the standard formatter *)
val print_var : t -> unit

(** Return a string representation of a hashconsed variable *)
val string_of_var : t -> string 

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
