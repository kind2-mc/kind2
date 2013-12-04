(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** KIND 2 messaging module *)

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
