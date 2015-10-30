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


(** Lustre identifier

    An identifier is a string with a (possibly empty) list of integer
    indexes. 

    This module also provides some pre-defined identifiers that are
    used in the translation.

    @author Christoph Sticksel *)


(** An identifier is a string with integer indexes *)
type t = private Ident.t * int list 

(** Equality on identifiers *)
val equal : t -> t -> bool

(** Hash an identifier *)
val hash : t -> int

(** Total ordering of identifiers *)
val compare : t -> t -> int

(** Hash table over identifiers *)
module Hashtbl : Hashtbl.S with type key = t

(** Set of identifiers *)
module Set : Set.S with type elt = t

(** Map of identifiers *)
module Map : Map.S with type key = t

(** {1 Constructors and Converters} *)

(** Return a string representation of the identifier 

    [string_of_ident safe ident] returns the identifier with the
    indexes appended in [\[] and [\]] if [safe] is [false]. Otherwise
    the indexes are appended separated by [_], which makes the string
    a valid Lustre identifier. *)
val string_of_ident : bool -> t -> string

(** Add the given integer as an index to the identifier *)
val push_index : t -> int -> t 

(** Construct an identifier of a string *)
val mk_string_ident : string -> t

(** Construct an identifier of a scope *)
val of_scope : Scope.t -> t

(** Return a scope of an identifier 

    The indexes of the identifier become separate scope levels. *)
val to_scope : t -> Scope.t

(** Pretty-print an identifier 

    [pp_print_ident safe ident] prints the indexes separated by [_] if
    [safe] is [true] as in {!string_of_ident}. *)
val pp_print_ident : bool -> Format.formatter -> t -> unit 

(** {1 Reserved Identifiers} *)

(** Scope for reserved identifiers *)
val reserved_scope : Scope.t

(** Scope for identifiers in user input *)
val user_scope : Scope.t

(** Identifier for abstracted variables *)
val abs_ident : t

(** Identifier for oracle inputs *)
val oracle_ident : t

(** Identifier for unique identifier for node instance *)
val instance_ident : t

(** Identifier for first instant flag *)
val init_flag_ident : t

(** Identifier for instantiated variables in node calls *)
val inst_ident : t

(** Identifier for index variables in arrays *)
val index_ident : t

(** Identifier of uninterpreted symbol for initial state constraint *)
val init_uf_string : string 

(** Identifier of uninterpreted symbol for transition relation *)
val trans_uf_string : string 


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
