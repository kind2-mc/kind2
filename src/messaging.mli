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

(** Low-level handling of messages 

    @author Jason Oxley, Christoph Sticksel *)

exception SocketConnectFailure
exception SocketBindFailure
exception BadMessage
exception InvalidProcessName
exception NotInitialized


(** A message to be relayed to other processes and conversions *)
module type RelayMessage = 
sig

  (** Message *)
  type t

  (** ZMQ's representation of a multipart message *)
  type zmsg = string list

  (** Convert a message to a strings for message frames *)
  val message_of_strings : zmsg -> t

  (** Convert string from message frames to a message *)
  val strings_of_message : t -> zmsg

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
    | Ready           (** Process is ready *)
    | Ping            (** Request reply from process *)
    | Terminate       (** Request termination of process *)
    | Resend of int   (** Request resending of relay message *)

  (** A message *)
  type message = 
    | OutputMessage of output_message     (** Output to user *)
    | ControlMessage of control_message   (** Message internal to the
                                              messaging system *)
    | RelayMessage of int * relay_message (** Message to be broadcast
                                              to worker processes *)

  (** Messaging context *)
  type ctx

  (** Socket *)
  type socket

  (** Thread *)
  type thread

  (** Create a messaging context and bind ports for the invariant
      manager. Return a pair of pub socket and pull socket and pair of
      addresses of pub and pull sockets for workers to connect to. 

      Call this function before forking the processes, the first
      return argument must only be used by the parent process, the
      child processes must use the socket addresses in the second
      return argument. *)
  val init_im : unit -> (ctx * socket * socket) * (string * string)

  (** Create a messaging context and bind given ports for a worker
      process. Return a messaging context and a pair of sub and push
      sockets. *)
  val init_worker : Lib.kind_module -> string -> string -> ctx * socket * socket

  (** Start the background thread for the invariant manager, using the
      given context and sockets. The second parameter is a list of
      PIDs and the kind of worker processes to watch, the third
      argument is the function to call to handle exceptions. *)
  val run_im : ctx * socket * socket -> (int * Lib.kind_module) list -> (exn -> unit) -> unit 

  (** Start the background thread for a worker process, using the
      given context and sockets. The second parameter is type of
      worker process, the third is the function to call to handle
      exceptions. *)
  val run_worker : ctx * socket * socket -> Lib.kind_module -> (exn -> unit) -> thread

  (** Broadcast a message to the worker processes *)
  val send_relay_message : relay_message -> unit

  (** Send a message to the invariant manager for output to the user *)
  val send_output_message : output_message -> unit

  (** Send a termination message to the invariant manager *)
  val send_term_message : unit -> unit

  (** Receive messages queued by the background thread *)
  val recv : unit -> (Lib.kind_module * message) list

  (** Notifies the background thread of a new list of child
      processes. Used by the supervisor in a modular analysis when
      restarting. *)
  val update_child_processes_list : (int * Lib.kind_module) list -> unit

  (** Purge the invariant manager mailbox.
    Should be called before calling update_child_processes_list
    in order to get rid of messages from the previous analysis. *)
  val purge_im_mailbox : ctx * socket * socket -> unit

  (** Returns true if a termination message was received. Does NOT
      modify received message in any way. *)
  val check_termination : unit -> bool

  (** Request the background thread of a worker process to terminate *)
  val exit : thread -> unit

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
