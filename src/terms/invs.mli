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


(** Invariants are stored in two hash tables mapping them to their certificate.
One table is for one-state invariants, the other is for two-state invariants.
*)

(** Stores invariants. *)
type t

val copy: t -> t

(** The empty collection of invariants. *)
val empty : unit -> t

(** True if no invariants. *)
val is_empty : t -> bool

(** Number of invariants (one-state, two-state). *)
val len : t -> int * int

(** Bumps invariants.

If second parameter is [true], include two-state invariants. *)
val of_bound : t -> bool -> Numeral.t -> Term.t list

(** Filters some invariants.

Function takes a boolean flag indicating if the invariant is two state. *)
val filter : (bool -> Term.t -> Certificate.t -> bool) -> t -> t

(** Adds a one-state invariant. *)
val add_os : t -> Term.t -> Certificate.t -> unit

(** Adds a two-state invariant. *)
val add_ts : t -> Term.t -> Certificate.t -> unit

(** Remove all the invariants. *)
val clear : t -> unit

(** The one-state invariants. *)
val get_os : t -> Term.TermSet.t

(** The two-state invariants. *)
val get_ts : t -> Term.TermSet.t

(** Checks if a term is a known invariant. *)
val mem : t -> Term.t -> bool

(** Returns [Some cert] if [term] is a known invariant, or [None] otherwise. *)
val find : t -> Term.t -> Certificate.t option

(** {e Temporary.} Flattens some invariants into a list. *)
val flatten : t -> (Term.t * Certificate.t) list

(** Merges two collections of invariants (non-destructive). *)
val merge : t -> t -> t

(** Formats some invariants. *)
val fmt : Format.formatter -> t -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
