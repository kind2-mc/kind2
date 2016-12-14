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

(** Attributes for annotated terms

    An attribute is currently only a name for a term.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Hashconsed attribute *)
type t


(** {1 Hashtables, maps and sets} *)

(** Comparison function on attributes *)
val compare_attrs : t -> t -> int

(** Equality function on attributes *)
val equal_attrs : t -> t -> bool

(** Hashing function on attribute *)
val hash_attr : t -> int

(** Hash table over attributes *)
module AttrHashtbl : Hashtbl.S with type key = t

(** Set over attributes *)
module AttrSet : Set.S with type elt = t

(** Map over attributes *)
module AttrMap : Map.S with type key = t


(** {1 Constructor} *)

(** Return a name attribute *)
val mk_named : string -> int -> t

(** Return a fun-def attribute *)
val fundef : t

(** {1 Accessor functions} *)

(** Return true if the attribute is a name *)
val is_named : t -> bool

(** Return true if the attribute is a name *)
val is_fundef : t -> bool

(** Return the name in a name attribute, raises [Invalid_argument] for
    other attributes *)
val named_of_attr : t -> string * int

(** {1 Pretty-printing} *)

(** Pretty-print a hashconsed attribute *)
val pp_print_attr : Format.formatter -> t -> unit

(** Pretty-print a hashconsed attribute to the standard formatter *)
val print_attr : t -> unit

(** Return a string representation of a hashconsed attribute *)
val string_of_attr : t -> string 

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
