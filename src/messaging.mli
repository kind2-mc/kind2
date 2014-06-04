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

(** Low-level handling of messages 

    @author Jason Oxley, Christoph Sticksel *)

exception No_value
(* exception Terminate *)
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

  (** Convert a message to a strings for message frames *)
  val message_of_strings : (unit -> string) -> t

  (** Convert string from message frames to a message *)
  val strings_of_message : t -> string list

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

  (** Request the background thread of a worker process to terminate *)
  val exit : thread -> unit 

end

(** Functor to instantiate the messaging system with a type of messages *)
module Make (T: RelayMessage) : S with type relay_message = T.t




(*








(** *)
type user_message = 
  | Log of int * string
  | Stat of string
  | Progress of int

type control = READY | PING | TERM

type invariant =
  | INVAR of string * int
  | PROP_KTRUE of string * int * int
  | PROP_INVAR of string * int 
  | PROP_FALSE of string * int
  | PROP_KFALSE of string * int * int
  | PROVED of string * int * int
  | DISPROVED of string * int * int
  | RESEND of int

type induction = BMCSTATE of int * (string list)

type counterexample = COUNTEREXAMPLE of int

type message =
  | UserMessage of user_message
  | ControlMessage of control
  | InvariantMessage of invariant
  | InductionMessage of induction
  (* | CounterexampleMessage of counterexample *)


type ctx
type socket
type thread

(** Get a string representation of a message *)
val string_of_msg : message -> string

(** Create context and bind ports for invariant manager, return pair
    of pub socket and pull socket and pair of addresses of pub and
    pull sockets for workers to connect to *)
val init_im : unit -> (ctx * socket * socket) * (string * string)

val init_worker : Lib.kind_module -> string -> string -> ctx * socket * socket 

val run_im : ctx * socket * socket -> (int * Lib.kind_module) list -> (exn -> unit) -> unit 

val run_worker : ctx * socket * socket -> Lib.kind_module -> (exn -> unit) -> thread

(*
(** Assume the role of the given process and initialize communication with 
    other processes *)
val init : process -> (exn -> unit) -> unit
*)

(** Send a message. Message will be sent to the Invariant Manager if the caller
  is a worker process, to subscribing processes otherwise *)
val send : message -> unit

val send_relay_message : message -> unit

val send_output_message : message -> unit

val send_term_message : unit -> unit


(** Receive waiting messages. Messages are from the Invariant Manager if the 
  caller is a worker, from workers otherwise *)
val recv : unit -> (Lib.kind_module * message) list

val exit : thread -> unit

(*
val messaging_selftest : unit -> unit 
*)

*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
