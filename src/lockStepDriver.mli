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

open Lib
open TypeLib
open Actlit

(** Type of a lock step kind context. *)
type t

(** Creates a lock step driver based on a transition system. *)
val create: TransSys.t -> t

(** Deletes a lock step driver. *)
val delete: t -> unit

(** The k of the lock step driver. *)
val get_k: t -> Numeral.t

(** Increments the k of a lock step driver. Basically asserts the
   transition relation and unrolls the invariants one step further. *)
val increment: t -> unit

(** Checks if the current state of the LSD is satisfiable. It only
    consists of transition relations and invariants, so it should
    always be. Crashes if it is not. *)
val check_satisfiability: t -> unit

(** Adds new invariants to a lock step driver. *)
val new_invariants: t -> Term.t list -> unit

(** Checks if some of the input terms are falsifiable k steps from the
    initial states. Returns Some of a model at 0 if some are, None
    otherwise. *)
val query_base: t -> Term.t list -> ((Var.t * Term.t) list) option

(** Checks if some of the input terms are k-inductive. Returns a pair
    composed of the falsifiable terms and the unfalsifiable ones. *)
val query_step: t -> Term.t list -> Term.t list * Term.t list

(** Checks the lock step driver on the system below its implementation
    in the ml file. *)
val test: TransSys.t -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

