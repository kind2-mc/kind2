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

(** Module used to keep track of all property related events during a
    (potentially modular and/or contract-based) analysis. *)

open Lib

(** Type for the info related to a list of valid property, proved at
    the same time in conjunction. *)
type prop_valid =
  { modul: kind_module ;
    (** The kind module which proved this property. *)

    k: Numeral.t ;
    (** The [k] for which it was proved. What that actually means
        depends on the module used for the proof. Might not apply to
        future techniques. *)

    in_conj_with: string list list ;
    (** Properties this property was proved in conjunction with. *)

    valid_props: string list list ;
    (** Valid properties at the time of the proof. *)

    invars: Term.t list
    (** Invariants used for the proof. *) }

(** Info about the status of (a list of) property(ies) at the end of
    an analysis. *)
type prop_info =
  | PropValid of (string list) * prop_valid
  (** List of mutually valid properties. *)

  | PropKTrue of  string       * Numeral.t
  (** A ktrue property. *)

  | PropFalse of  string       * kind_module * Numeral.t
  (** A falsified property. *)

(** Sublog on the abstraction depth of the analysis of a system. *)
type depth_sublog

(** Sublog on a (sub)system. *)
type sys_sublog

(** Logs the results of an analysis. *)
type t =
  { sys: TransSys.t ;
    (** Top most system of the analysis. *)

    sys_sublogs: sys_sublog list
    (** Sub analysis on the (sub)systems. *) }

(** {1 Constructor} *)

(** Creates an analysis log from the list of all systems analysis will
    be ran on.  So, if only analyzing [top], do [mk_log
    top]. Otherwise, one would typically do something like
    [TransSys.get_all_subsystems top |> mk_log]. *)
val mk_log: TransSys.t list -> t

(** {1 Accessors} *)

(** Finds the sublog of a system.
    @raise Not_found if the system has no sublog. *)
val sys_sublog: t -> TransSys.t -> sys_sublog

(** The depth sublogs of a system sublog. *)
val depth_sublogs: sys_sublog -> depth_sublog list

(** Finds the sublog of an abstraction depth from the sublog of a
    system.
    @raise Not_found if the depth has no sublog. *)
val depth_sublog: sys_sublog -> int -> depth_sublog

(** Finds the sublog of an abstraction depth for a system from a
    log.
    @raise Not_found if the system or the depth have no sublog. *)
val sys_depth_sublog: t -> TransSys.t -> int -> depth_sublog

(** {1 Modifiers} *)

(** Adds an empty abstraction depth sublog to a (sub)system sublog of
    an analysis log.
    @raise Not_found if the system has no sublog.
    @raise Invalid_argument if the system already has a depth sublog
    for this depth. *)
val add_depth_sublog: t -> TransSys.t -> int -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
