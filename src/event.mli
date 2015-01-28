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

(** Event logging and communication *)

(** Every relevant event must be logged through the functions in this
    module whether in single-process or multi-process mode. The
    subprocesses must not produce any output in multi-process mode and
    shall send their output as messages to the invariant manager
    instead.

    @author Christoph Sticksel
*)

exception Terminate

(** {1 Logging} *)

(** Set log format to plain text *)
val set_log_format_pt : unit -> unit

(** Set log format to XML *)
val set_log_format_xml : unit -> unit

(** Relay log messages to invariant manager *)
val set_relay_log : unit -> unit

(** Log a disproved property

    Should only be used by the invariant manager, other modules must use
    {!prop_status} to send it as a message. *)
val log_disproved : Lib.kind_module -> Lib.log_level -> TransSys.t -> string -> (StateVar.t * Model.term_or_lambda list) list -> unit 

(** Log a proved property

    Should only be used by the invariant manager, other modules must use
    {!prop_status} to send it as a message. *)
val log_proved : Lib.kind_module -> Lib.log_level -> TransSys.t -> int option -> string -> unit
 
(*
(** Log a counterexample for some properties

    Should only be used by the invariant manager, other modules must
    use {!counterexample} to send it as a message. *)
val log_counterexample : Lib.kind_module -> Lib.log_level -> string list -> TransSys.t -> (StateVar.t * Term.t list) list -> unit 
*)

(** Log summary of status of properties

    Should only be used by the invariant manager, other modules must use
    {!prop_status} to send it as a message. *)
val log_prop_status : Lib.log_level -> (string * TransSys.prop_status) list -> unit 

(** Log statistics

    Should only be used by the invariant manager, other modules must use
    {!stat} to send it as a message. *)
val log_stat : Lib.kind_module -> Lib.log_level -> (string * Stat.stat_item list) list -> unit 

(** Terminate log

    Output closing tags for XML output. *)
val terminate_log : unit -> unit 


(** {1 Events} *)

(** Events exposed to callers *)
type event = 
  | Invariant of string list * Term.t 
  | PropStatus of string * TransSys.prop_status

(** Pretty-print an event *)
val pp_print_event : Format.formatter -> event -> unit

(** Return the last statistics received *)
val all_stats : unit -> (Lib.kind_module * (string * Stat.stat_item list) list) list

(** [log m l f v ...] outputs a message from module [m] on level [l],
    formatted with the parameterized string [f] and the values [v
    ...] *)
val log : Lib.log_level -> ('a, Format.formatter, unit) format -> 'a

(** Output the statistics of the module *)
val stat : (string * Stat.stat_item list) list -> unit

(** Output the progress of the module *)
val progress : int -> unit

(** Broadcast a discovered top level invariant *)
val invariant : string list -> Term.t -> unit

(** Broadcast a property status *)
val prop_status : TransSys.prop_status -> TransSys.t -> string -> unit

(** Broadcast an execution path *)
val execution_path : TransSys.t -> (StateVar.t * Model.term_or_lambda list) list -> unit

(** Broadcast a termination message *)
val terminate : unit -> unit 

(** Receive all queued events *)
val recv : unit -> (Lib.kind_module * event) list
                                             
(** Terminates if a termination message was received. Does NOT modified
    received messages. *)
val check_termination: unit -> unit

(** Filter list of invariants with their scope for invariants of empty
    (top) scope *)
val top_invariants_of_invariants :
  TransSys.t ->
  (Lib.kind_module * (string list * Term.t)) list ->
  Term.t list

(** Update transition system from events and return new invariants
    INCLUDING subsystem ones, scoped and properties with changed
    status.

    For a property status message the status saved in the transition
    system is updated if the status is more general (k-true for a
    greater k, k-false for a smaller k, etc.).

    Received invariants are stored in the transition system, also
    proved properties are added as invariants.

    Counterexamples are ignored. *)
val update_trans_sys_sub :
  TransSys.t ->
  (Lib.kind_module * event) list ->
  (Lib.kind_module * (string list * Term.t)) list *
  (Lib.kind_module * (string * TransSys.prop_status)) list

(** Update transition system from events and return new top level
    invariants and properties with changed status.

    For a property status message the status saved in the transition
    system is updated if the status is more general (k-true for a
    greater k, k-false for a smaller k, etc.).

    Received invariants are stored in the transition system, also
    proved properties are added as invariants.

    Counterexamples are ignored. *)
val update_trans_sys :
  TransSys.t ->
  (Lib.kind_module * event) list ->
  Term.t list * 
  (Lib.kind_module * (string * TransSys.prop_status)) list


(** {1 Messaging} *)

(** Setup of the messaging system *)
type messaging_setup

(** Background thread of the messaging system *)
type mthread

(** Set module currently running *)
val set_module : Lib.kind_module -> unit 

(** Get module currently running *)
val get_module : unit -> Lib.kind_module

(** Create contexts and bind ports for all processes *)
val setup : unit -> messaging_setup

(** Start messaging for the invariant manager *)
val run_im : messaging_setup -> (int * Lib.kind_module) list -> (exn -> unit) -> unit 

(** Start messaging for another process *)
val run_process : Lib.kind_module -> messaging_setup -> (exn -> unit) -> mthread

(** Send all queued messages and exit the background thread *)
val exit : mthread -> unit


val pp_print_path_pt : TransSys.t -> 'a -> Format.formatter -> (StateVar.t * Model.term_or_lambda list) list -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
