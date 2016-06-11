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

(** Managing of identifier to avoid clashes

    @author Christoph Sticksel *)

(** Identifier 

    This type will become private later *)
type t = string

(** Equality of identifiers *)
val equal : t -> t -> bool

(** Total order of identifiers *)
val compare : t -> t -> int

(** Set of identifiers *)
module IdentSet : Set.S with type elt = t

(** Map of identifiers *)
module IdentMap : Map.S with type key = t

(** Pretty-print an identifier *)
val pp_print_ident : Format.formatter -> t -> unit

(** Construct an identifier from a string *)
val of_string : string -> t

(** Return a string representation of an identifier x*)
val to_string : t -> string 

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
