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

(** Type of the terms stored in the implication graph. *)
type term = Term.t
(** Set of terms. *)
type term_set = Term.TermSet.t

(** Type of an implication graph. *)
type t

(** Generates one state implication graphs for a transition system,
    and its subsystems if the flags require it. *)
val generate_graphs_one_state: TransSys.t -> (TransSys.t * t) list

(** Generates two state implication graphs for a transition system,
    and its subsystems if the flags require it. *)
val generate_graphs_two_state: TransSys.t -> (TransSys.t * t) list

(** Prints a graph in a file as a dot graph. *)
val to_dot: string -> t -> unit

(** Rewrite a graph using the specified evaluation function. *)
val rewrite_graph: (term -> bool) -> t -> bool * t

(** Creates a graph from a set of terms .*)
val create: term_set -> t

(** Creates a graph from a list of terms .*)
val create_of_list: term list -> t

(** The equivalence classes of a graph. *)
val eq_classes: t -> term_set list

(** The non trivial implications of a graph between its
    representative. *)
val non_trivial_implications: t -> term list

(** The trivial implications of a graph between its representative. *)
val trivial_implications: t -> term list

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

