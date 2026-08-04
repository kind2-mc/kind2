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

(** Low-level handling of messages between the supervisor and the
    engines of an analysis.

    Engines run in domains of a single process; a message is an OCaml
    value dropped into the in-memory mailbox of the receiver, without
    any serialization. There are no background threads: sending is a
    mutex-protected queue operation and {!S.recv} drains the mailbox of
    the calling domain.

    @author Jason Oxley, Christoph Sticksel *)

exception NotInitialized


(** A message to be relayed to other processes *)
module type RelayMessage =
sig

  (** Message *)
  type t

  (** Pretty-print a message *)
  val pp_print_message : Format.formatter -> t -> unit

end

module type S =
sig

  type relay_message

  (** A message to be output to the user *)
  type output_message =
    | Log of int * string  (** Log message with level *)
    | Stat of string       (** Statistics *)
    | Progress of int      (** Progress *)

  (** A message internal to the messaging system *)
  type control_message =
    | Terminate       (** Request termination of process *)

  (** A message *)
  type message =
    | OutputMessage of output_message     (** Output to user *)
    | ControlMessage of control_message   (** Message internal to the
                                              messaging system *)
    | RelayMessage of relay_message       (** Message to be broadcast
                                              to worker processes *)

  (** Pretty-print a message *)
  val pp_print_message : Format.formatter -> message -> unit

  (** The messaging system of an analysis, created by the supervisor *)
  type ctx

  (** Registration of a worker mailbox *)
  type worker

  (** Create the messaging system in the supervisor. *)
  val init_im : unit -> ctx

  (** Create and register the mailbox of a worker with the given kind
      module and identifier. Call {!run_worker} in the domain of the
      worker afterwards. *)
  val init_worker : Lib.kind_module -> int -> ctx -> worker

  (** Take the supervisor role in the calling domain. *)
  val run_im : ctx -> unit

  (** Take the worker role in the calling domain. *)
  val run_worker : worker -> worker

  (** Broadcast a message to the other engines and, from a worker, to
      the supervisor *)
  val send_relay_message : relay_message -> unit

  (** Send a message to the invariant manager for output to the user *)
  val send_output_message : output_message -> unit

  (** Broadcast a termination message to all engines *)
  val send_term_message : unit -> unit

  (** Send a termination message to the engine with the given
      identifier *)
  val send_term_message_to : int -> unit

  (** Receive the messages queued in the mailbox of the calling domain *)
  val recv : unit -> (Lib.kind_module * message) list

  (** Purge the invariant manager mailbox. Should be called between two
      analyses, after all engines of the previous analysis have
      exited. *)
  val purge_im_mailbox : ctx -> unit

  (** Returns true if a termination message was received. Does NOT
      modify received message in any way. *)
  val check_termination : unit -> bool

  (** Unregister the mailbox of a worker *)
  val exit : worker -> unit

end

(** Functor to instantiate the messaging system with a type of messages *)
module Make (T: RelayMessage) : S with type relay_message = T.t


(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
