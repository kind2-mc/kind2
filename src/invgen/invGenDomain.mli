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


(** Exception thrown when a domain is asked to build a trivial implication. *)
exception TrivialRelation


(** Signature of the modules describing an order relation over some values. *)
module type Domain = sig
  (** Short string description of the values, used in the logging prefix. *)
  val name : string
  (** Type of the values of the candidate terms. *)
  type t
  (** Value formatter. *)
  val fmt : Format.formatter -> t -> unit
  (** Equality over values. *)
  val eq : t -> t -> bool
  (** Ordering relation. *)
  val cmp : t -> t -> bool
  (** Creates the term corresponding to the equality of two terms. *)
  val mk_eq : Term.t -> Term.t -> Term.t
  (** Creates the term corresponding to the ordering of two terms. *)
  val mk_cmp : Term.t -> Term.t -> Term.t
  (** Evaluates a term. *)
  val eval : TransSys.t -> Model.t -> Term.t -> t
  (** Mines a transition system for candidate terms. *)
  val mine : bool -> bool -> Analysis.param -> TransSys.t -> (
    TransSys.t * Term.TermSet.t
  ) list
  (** Representative of the first equivalence class.

  [False] for bool, a random term in the set for arith. *)
  val first_rep_of : Term.TermSet.t -> Term.t * Term.TermSet.t
  (** Returns true iff the input term is bottom. *)
  val is_bot: Term.t -> bool
  (** Returns true iff the input term is top. *)
  val is_top: Term.t -> bool
  (** Returns true iff the one state invgen technique for this domain is
  running. *)
  val is_os_running: unit -> bool
end

(** Boolean domain with implication. *)
module Bool : Domain

(** Integer domain with less than or equal to. *)
module Int : Domain

(** Real domain with less than or equal to. *)
module Real : Domain




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)