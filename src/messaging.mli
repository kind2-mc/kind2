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

(** KIND 2 messaging module 

    @author Jason Oxley, Christoph Sticksel *)

exception No_value
(* exception Terminate *)
exception SocketConnectFailure
exception SocketBindFailure
exception BadMessage
exception InvalidProcessName
exception NotInitialized


type user_message = 
  | Log of int * string
  | Stat of string
  | Progress of int

type control = READY | PING | TERM

type invariant =
  | INVAR of string * int
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

(** Receive waiting messages. Messages are from the Invariant Manager if the 
  caller is a worker, from workers otherwise *)
val recv : unit -> (Lib.kind_module * message) list

val exit : thread -> unit

(*
val messaging_selftest : unit -> unit 
*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
