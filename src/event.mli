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

(** Expose functions from logging module *)
include Log.Sig

(** Logging instantiated with an actual relay function *)
include Log.SLog

(** Relay log messages to invariant manager (overrides function from
    {! Log}) *)
val set_relay_log : unit -> unit


(** Logs a step counterexample.

    Should only be used by step for sending the cex, and invariant manager to
    actually print it. *)
val log_step_cex : Lib.kind_module -> Lib.log_level -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> string -> (StateVar.t * Model.term_or_lambda list) list -> unit

(** Log a disproved property

    Should only be used by the invariant manager, other modules must use
    {!prop_status} to send it as a message. *)
val log_disproved : Lib.kind_module -> Lib.log_level -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> string -> (StateVar.t * Model.term_or_lambda list) list -> unit

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
val log_prop_status : Lib.log_level -> (string * Property.prop_status) list -> unit 

(** Log statistics

    Should only be used by the invariant manager, other modules must use
    {!stat} to send it as a message. *)
val log_stat : Lib.kind_module -> Lib.log_level -> (string * Stat.stat_item list) list -> unit 

(** Terminate log, called at the very end of a run.
    Output closing tags for XML output. *)
val terminate_log : unit -> unit


(** Logs the end of a run.
    [log_run_start results] logs the end of a run. *)
val log_run_end : Analysis.result list -> unit

(** Logs the start of an analysis.
    [log_analysis_start top abs] logs the start of an analysis for top
    system [top] with abstraction [abs]. *)
val log_analysis_start : TransSys.t -> Analysis.param -> unit

(** Logs the end of an analysis.
    [log_analysis_start result] logs the end of an analysis. *)
val log_analysis_end : Analysis.result -> unit

(** Logs the start of a post-analysis treatment. Arguments:
* name of the treatment (concise, for XML)
* title of the treatment (verbose, for pt) *)
val log_post_analysis_start : string -> string -> unit

(** Logs the end of a post-analysis treatment. *)
val log_post_analysis_end : unit -> unit

(** Logs a timeout. Input should be [true] for wallclock, [false] for CPU. *)
val log_timeout : bool -> unit

(** Logs an interruption for some signal. *)
val log_interruption : int -> unit


(** {1 Events} *)

(** Events exposed to callers *)

type event = 
  | Invariant of string list * Term.t * Certificate.t * bool
  | PropStatus of string * Property.prop_status
  | StepCex of string * (StateVar.t * Model.term_or_lambda list) list

(** Pretty-print an event *)
val pp_print_event : Format.formatter -> event -> unit

(** Return the last statistics received *)
val all_stats : unit -> (Lib.kind_module * (string * Stat.stat_item list) list) list

(** Output the statistics of the module *)
val stat : (string * Stat.stat_item list) list -> unit

(** Output the progress of the module *)
val progress : int -> unit

(** Broadcast a discovered top level invariant *)
val invariant : string list -> Term.t -> Certificate.t -> bool -> unit

(** Broadcast a step cex *)
val step_cex : 'a InputSystem.t -> Analysis.param -> TransSys.t -> string -> (StateVar.t * Model.term_or_lambda list) list -> unit

(** Broadcast a property status *)
val prop_status : Property.prop_status -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> string -> unit

(** Broadcast an execution path *)
val execution_path : 'a InputSystem.t -> Analysis.param -> TransSys.t -> (StateVar.t * Model.term_or_lambda list) list -> unit

(** Broadcast a termination message *)
val terminate : unit -> unit 

(** Receive all queued events *)
val recv : unit -> (Lib.kind_module * event) list

(** Notifies the background thread of a new list of child
    processes. Used by the supervisor in a modular analysis when
    restarting. *)
val update_child_processes_list: (int * Lib.kind_module) list -> unit

(** Terminates if a termination message was received. Does NOT modify
    received messages. *)
val check_termination: unit -> unit

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
  'a InputSystem.t -> 
  Analysis.param -> 
  TransSys.t ->
  (Lib.kind_module * event) list ->
  (Term.TermSet.t * Term.TermSet.t) Scope.Map.t *
  (Lib.kind_module * (string * Property.prop_status)) list

(** Update transition system from events and return new top level
    invariants and properties with changed status.

    For a property status message the status saved in the transition
    system is updated if the status is more general (k-true for a
    greater k, k-false for a smaller k, etc.).

    Received invariants are stored in the transition system, also
    proved properties are added as invariants.

    Counterexamples are ignored. *)
val update_trans_sys :
  'a InputSystem.t -> 
  Analysis.param -> 
  TransSys.t ->
  (Lib.kind_module * event) list ->
  (Term.TermSet.t * Term.TermSet.t) * 
  (Lib.kind_module * (string * Property.prop_status)) list


(** {1 Messaging} *)

(** Setup of the messaging system *)
type messaging_setup

(** Background thread of the messaging system *)
type mthread

(** Create contexts and bind ports for all processes *)
val setup : unit -> messaging_setup

(** Start messaging for the invariant manager *)
val run_im :
  messaging_setup -> (int * Lib.kind_module) list -> (exn -> unit) -> unit 

(** Start messaging for another process *)
val run_process : Lib.kind_module -> messaging_setup -> (exn -> unit) -> mthread

(** Send all queued messages and exit the background thread *)
val exit : mthread -> unit


val pp_print_path_pt :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> 'a ->
  Format.formatter -> (StateVar.t * Model.term_or_lambda list) list -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
