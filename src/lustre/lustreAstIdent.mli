(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

(** encapsulate identifier details.
    This represents a qualified name.

    eg. M::N::t is represented as PIdent (M, PIdent (N, (UIdent t))) 
  
  @author Apoorv Ingle *)

type t

val equal: t -> t -> bool
(** Returns true if the two Identifiers are equal *)

val compare: t -> t -> int
(** Compare two identifiers *)
  
val to_list: t -> string list
(** Returns a list of identifers of the qualified identifiers *)

val from_list: string list -> t
(** Builds a qalified identifier from a list of strings  *)
  
val to_string: t -> string
(** Converts the identifier to a string *)

val from_string: string -> t
(** builds an identifier from the string *)

val pp_print_ident: Format.formatter -> t -> unit
(** print the identifer *)

val add_prefix: string -> t -> t
(** adds a prefix to the base of the identifier *)
  
val add_suffix: string -> t -> t
(** adds a suffix to the base of the identifer *)

val add_qualified_prefix: string -> t -> t
(** increases the scope  *)

val path: t -> t option
(** Path of an identifier. It is None if it is in local scope *)

val get_parent: t -> t option
(** Gets the top most scope of the qualified identifier, None if the it is defined in the current scope *)
  
module IdentSet: sig
    include (Set.S with type elt = t)
    val flatten: t list -> t
end
(** Set of identifiers *)

module IdentMap: sig
  include (Map.S with type key = t)
  val keys: 'a t -> key list
end
(** Map of identifiers *)
