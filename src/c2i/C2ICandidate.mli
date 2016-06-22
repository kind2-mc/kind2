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

(** Wraps the candidate invariants with info about their cost etc. *)


(** Contains the info needed for the moves on a candidate. *)
type t

(** Creates a new candidate that can be randomly moved. Should be called only
    once as it mines the init and trans predicates. Use [reset] to launch a new
    C2I run. *)
val mk: TransSys.t -> t

(** Resets a candidate. *)
val reset: t -> t

(** Term of a candidate as a [Term.t list list] (dnf). *)
val terms_of: t -> Term.t list list

(** Term of a candidate as a [Term.t]. *)
val term_of: t -> Term.t

(** Makes a move on a candidate. *)
val move: t -> t

(** A candidate augmented with a cost and a rating. *)
type rated_t

(** The cost of a rated candidate. *)
val cost_of_rated: rated_t -> int

(** The candidate of a rated candidate. *)
val candidate_of_rated: rated_t -> t

(** Computes the cost of a candidate and rates its atoms. *)
val rated_cost_function:
  t -> Model.t list -> (Model.t * Model.t) list -> Model.t list -> rated_t

(** Moves a rated candidate. *)
val rated_move: rated_t -> t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
