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


(** Graph representing equivalence classes and ordering between some terms.

There's one graph module per domain we are interested in: bool, int and real.
They're generated by a common functor using the domains from [InvGenDomain].
*)




(** LSD module. *)
module Lsd = LockStepDriver


(** Term. *)
type term = Term.t

(** Maps terms to something. *)
type 'a map = 'a Term.TermHashtbl.t

(** Set of terms. *)
type set = Term.TermSet.t

(** [write_dot_to path name suff fmt graph]
Writes a graph in graphviz to file [<path>/<name>_<suff>.dot]. *)
val write_dot_to : string -> string -> string -> (
  Format.formatter -> 'a -> unit
) -> 'a -> unit

(** Signature of the modules created by the graph functor. *)
module type Graph = sig
  (** Domain with an order relation. *)
  module Domain : InvGenDomain.Domain

  (** A graph. *)
  type graph

  (** Creates a graph from a single equivalence class and its
  representative. *)
  val mk : term -> set -> graph

  (** Checks whether at least one candidate mentions a state variable. *)
  val has_svars : graph -> bool

  (** Mines a system and creates the relevant graphs.
  
  First boolean is [top_only], then [two_state]. Input function is applied to
  each subsystem. It is used to create the pruning checkers. *)
  val mine : bool -> bool -> Analysis.param -> TransSys.t -> (
    TransSys.t -> unit
  ) -> (TransSys.t * graph * set * set) list

  (** Clones a graph. *)
  val clone : graph -> graph

  (** Total number of terms in the graph. *)
  val term_count : graph -> int

  (** Total number of classes in the graph. *)
  val class_count : graph -> int

  (** Returns true if all classes in the graph only have one candidate term. *)
  val is_stale : graph -> bool

  (** Drops a term from the class corresponding to a representative. *)
  val drop_class_member : graph -> term -> term -> unit

  (** Formats a graph in dot format. Only the representatives will appear. *)
  val fmt_graph_dot : Format.formatter -> graph -> unit
  
  (** Formats the eq classes of a graph in dot format. *)
  val fmt_graph_classes_dot : Format.formatter -> graph -> unit

  (** Checks that a graph makes sense. Dumps the graph and its classes in dot
  format in the current directory if the graph does not make sense. *)
  val check_graph : graph -> bool

  (** Minimal list of terms encoding the current state of the graph. Contains
  - equality between representatives and their class, and
  - comparison terms between representatives.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true.

  Used when querying the base instance of the LSD (graph stabilization).
  See also [equalities_of] and [relations_of], used for the step instance
  (induction check). *)
  val terms_of : graph -> (term -> bool) -> term list

  (** Equalities coming from the equivalence classes of a graph.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true.

  Generates a list of pairs [term * (term * term)]. The first term is the
  candidate invariant, while the second element stores the representative
  of the class the candidate comes from, and the term that can be dropped
  from it if the candidate is indeed invariant. *)
  val equalities_of : graph -> (term -> bool) -> (term * (term * term)) list

  (** Appends the relations from a graph to the input term list.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true.

  More precisely, generates implications between representatives and the
  representative and terms of each equivalence class they're a parent of.

  Generates a list of pairs [term * unit]. The useless [unit] second element
  is just there to be compatible with the signature of the lsd step query
  function. This is to accomodate with the information we need to keep around
  for the equalities of a graph (see [equalities_of]). *)
  val relations_of :
    graph -> (term * unit) list -> (term -> bool) -> (term * unit) list

  (** Queries the lsd and updates the graph. Terminates when the graph is
  stable, meaning all terms the graph represents are unfalsifiable in the
  current lsd.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true. *)
  val stabilize : graph -> 'a InputSystem.t -> TransSys.t -> (term -> bool) -> Lsd.base -> unit

  (** Clones the graph, and splits it in step.

  Stabilizes eq classes one by one, communicates invariants at each step.
  Then stabilizes relations, communicating by packs. *)
  val step_stabilize :
    bool -> graph -> 'a InputSystem.t -> TransSys.t -> (term -> bool) -> Lsd.step -> (
      (Term.t * Certificate.t) list -> unit
    ) -> Term.t list
end



(** Graph of booleans with implication. *)
module Bool : Graph

(** Graph of integers with less than or equal. *)
module Int : Graph

(** Graph of int8 with less than or equal. *)
module Int8 : Graph

(** Graph of int16 with less than or equal. *)
module Int16 : Graph

(** Graph of int32 with less than or equal. *)
module Int32 : Graph

(** Graph of int64 with less than or equal. *)
module Int64 : Graph

(** Graph of uint8 with less than or equal. *)
module UInt8 : Graph

(** Graph of uint16 with less than or equal. *)
module UInt16 : Graph

(** Graph of uint32 with less than or equal. *)
module UInt32 : Graph

(** Graph of uint64 with less than or equal. *)
module UInt64 : Graph

(** Graph of reals with less than or equal. *)
module Real : Graph

(** Graph modules for equivalence only. *)
module EqOnly : sig

  (** Graph of booleans. *)
  module Bool : Graph

  (** Graph of integers. *)
  module Int : Graph

  (** Graph of int8s. *)
  module Int8 : Graph

  (** Graph of int16s. *)
  module Int16 : Graph

  (** Graph of int32s. *)
  module Int32 : Graph

  (** Graph of int64s. *)
  module Int64 : Graph

  (** Graph of uint8s. *)
  module UInt8 : Graph

  (** Graph of uint16s. *)
  module UInt16 : Graph

  (** Graph of uint32s. *)
  module UInt32 : Graph

  (** Graph of uint64s. *)
  module UInt64 : Graph

  (** Graph of reals. *)
  module Real : Graph

end




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
