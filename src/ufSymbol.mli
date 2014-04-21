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

(** Uninterpreted function symbols 

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Uninterpreted symbol are just strings of their name *)
type uf_symbol = string

(** Hashconsed uninterpreted symbol *)
type t


(** {1 Hashtables, maps and sets} *)

(** Comparison function on uninterpreted function symbols *)
val compare_uf_symbols : t -> t -> int

(** Equality function on uninterpreted function symbols *)
val equal_uf_symbols : t -> t -> bool

(** Hashing function on uninterpreted function symbols *)
val hash_uf_symbol : t -> int

(** Hash table over uninterpreted function symbols *)
module UfSymbolHashtbl : Hashtbl.S with type key = t

(** Set over uninterpreted function symbols *)
module UfSymbolSet : Set.S with type elt = t

(** Map over uninterpreted function symbols *)
module UfSymbolMap : Map.S with type key = t


(** {1 Constructor} *)

(** Declare an uninterpreted symbol

    [mk_uf_symbol s a r] constructs and returns an uninterpreted
    symbol with its name, the type of its arguments and the type of
    its result.
    
    Uninterpreted symbols can only be constructed with this function
    in order to ensure that they are properly declared. 

    Declaring an uninterpreted function again with the same signature
    is harmless and will simply return the previously declared
    symbol. However, re-declaring an uninterpreted function with a
    different signature will raise an [Invalid_argument]
    exception. *)
val mk_uf_symbol : string -> Type.t list -> Type.t -> t

(** Return a fresh uninterpreted symbol *)
val mk_fresh_uf_symbol : Type.t list -> Type.t -> t

(** Import an uninterpreted symbol from a different instance into this
    hashcons table 

    We may have clashes if we import fresh uninterpreted symbols from
    one instance to another. *)
val import : t -> t

(** {1 Accessor functions} *)

(** Return a previously declared uninterpreted function symbol 

    Raise exception [Not_found] if symbol has not been declared. *)
val uf_symbol_of_string : string -> t

(** Return the name of the uninterpreted function symbol *)
val name_of_uf_symbol : t -> string

(** Return the type of the arguments of the uninterpreted symbol *)
val arg_type_of_uf_symbol : t -> Type.t list

(** Return the type of the result of the uninterpreted symbol *)
val res_type_of_uf_symbol : t -> Type.t


(** {1 Iterators over defined uninterpreted symbols} *)

(** [fold_declarations f a] computes [(f sN aN rN ... (f s2 a2 r2 (f
    s1 a1 r1 a))...)], where [sI], [aI] and [rI], respectively are the
    name of the uninterpreted symbol, the types of its arguments and
    the type of its value. *)
val fold_uf_declarations : (string -> Type.t list -> Type.t -> 'a -> 'a) -> 'a -> 'a

(** [iter_declarations f t] iterates [f] over all declarations,
    calling [f s a r] on each, where [s], [a] and [r], respectively
    are the name of the uninterpreted symbol, the types of its
    arguments and the type of its value. *)
val iter_uf_declarations : (string -> Type.t list -> Type.t -> unit) -> unit


(** {1 Pretty-printing} *)

(** Pretty-print a symbol *)
val pp_print_uf_symbol : Format.formatter -> t -> unit

(** Return a string representation of a symbol *)
val string_of_uf_symbol : t -> string 


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
