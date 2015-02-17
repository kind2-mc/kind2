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

(** A log is a tree of depth 4.

    The first level is the root and contains the top node as well as
    the kids at depth 2. They represent analyses of a specific
    system. In non modular analysis, depth 2 will only have one node,
    the top level. In modular analysis, then eventually depth 2 will
    have a node for all systems of the hierarchy.

    Nodes at depth 2 contain the system the analysis of which they
    correspond to, and kids at depth 3. These distinguish analyses with
    different subsystem, contract-based abstractions. They contain the
    list of the subsystems (of their depth 2 parent) which have been
    abstracted for the analysis they represent. When not running in
    compositional mode, a depth 2 node can only have one kid with an
    empty list of abstracted nodes.

    The kids of a depth 3 node store detail about property related
    events during the analysis their path corresponds to. They log
    information about invariant and falsified property, as well as
    k-true properties at the end of their analysis. *)

open Lib

(** Type for identifying abstraction sublogs. You get a key by
    creating an abstraction sublog. *)
type abstraction_key = string list list

(** Type for the info related to a list of valid property, proved at
    the same time in conjunction. *)
type valid_props_info =
  { modul: kind_module ;
    (** The kind module which proved this property. *)

    k: Numeral.t ;
    (** The [k] for which it was proved. What that actually means
        depends on the module used for the proof. Might not apply to
        future techniques. *)

    valid_props: string list ;
    (** Valid properties at the time of the proof. *)

    invars: Term.t list
    (** Invariants used for the proof. *) }

(** Info about the status of (a list of) property(ies) at the end of
    an analysis. *)
type prop_info =
  | PropsValid of (string list) * valid_props_info
  (** List of mutually valid properties. *)

  | PropKTrue  of  string       * Numeral.t
  (** A ktrue property. *)

  | PropFalse  of  string       * kind_module * Numeral.t
                                * (StateVar.t * Model.term_or_lambda list) list
  (** A falsified property. *)

(** Sublog on an abstraction for a system. *)
type abstraction_sublog

(** Sublog on a (sub)system. *)
type sys_sublog

(** Logs the results of an analysis. *)
type t =
  { sys: TransSys.t ;
    (** Top most system of the analysis. *)

    sys_sublogs: sys_sublog list
    (** Sub analysis on the (sub)systems. *) }

(** {1 Constructors} *)

(** Creates an analysis log from the list of all systems analysis will
    be ran on.  So, if only analyzing [top], do [mk_log
    top]. Otherwise, one would typically do something like
    [TransSys.get_all_subsystems top |> mk_log]. *)
val mk_log: TransSys.t list -> t

(** Creates a mutually valid property info.
    [mk_valid_props modul k valid_props invars proved_props]:
    - [modul] is the module which proved,
    - [k] the k for which the property was proved,
    - [valid_props] valid properties at the time of proving,
    - [invars] invariants known at that time,
    - [proved_props] the actual properties found mutually valid. *)
val mk_valid_props:
  kind_module ->
  Numeral.t ->
  string list ->
  Term.t list ->
  string list ->
  prop_info

(** {1 Accessors} *)

(** Returns the list of abstracted systems from an abstraction key. *)
val abstracted_systems_of_abstraction_key:
  abstraction_key -> string list list
val key_of_list:
  string list list -> abstraction_key

(** Finds the sublog of a system.
    @raise Not_found if the system has no sublog. *)
val sys_sublog: t -> TransSys.t -> sys_sublog

(** The abstraction sublogs of a system sublog. *)
val abstraction_sublogs: sys_sublog -> abstraction_sublog list

(** Finds the sublog of an abstraction from the sublog of a
    system.
    @raise Not_found if [abstraction] is not present for this
    system. *)
val abstraction_sublog:
      sys_sublog -> abstraction_key -> abstraction_sublog

(** Finds the sublog of an abstraction key for a system from a log.
    @raise Not_found if [sys] or [abstraction_key] is not present. *)
val sys_abstraction_sublog:
      t -> TransSys.t -> abstraction_sublog

(** {1 Modifiers} *)

(** Adds an empty abstraction sublog to a (sub)system sublog of an
    analysis log.
    @raise Not_found if [sys] is not present.
    @raise Illegal_argument if the abstraction sublog already exists.
    @return The abstraction key to the sublog created. *)
val add_abstraction_sublog:
      t -> TransSys.t -> string list list -> abstraction_key

(** Adds a property info to an abstraction sublog of a sys sublog of a
    log. *)
val add_prop_info:
  t -> TransSys.t -> prop_info -> unit

(** Updates a log from a list of events. *)
val update_of_events:
  t -> TransSys.t -> Event.event list -> unit

(** Updates a log from a list of events. *)
val update_of_events:
  t -> TransSys.t ->
  (kind_module * Event.event) list -> unit

(** {1 Pretty printers} *)

(** Pretty prints a [valid_props_info]. *)
val pp_print_valid_props_info:
  Format.formatter -> valid_props_info -> unit

(** Pretty prints a [prop_info]. *)
val pp_print_prop_info:
  Format.formatter -> prop_info -> unit

(** Pretty prints an abstraction key. *)
val pp_print_abstraction_key:
  Format.formatter -> abstraction_key -> unit

(** Pretty prints an [abstraction_sublog]. *)
val pp_print_abstraction_sublog:
  Format.formatter -> abstraction_sublog -> unit

(** Pretty prints a [sys_sublog]. *)
val pp_print_sys_sublog:
  Format.formatter -> sys_sublog -> unit

(** Pretty prints a [t] log. *)
val pp_print_log:
  Format.formatter -> t -> unit

(** Pretty prints a [t] log. *)
val pp_print_log_shy:
  Format.formatter -> t -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
