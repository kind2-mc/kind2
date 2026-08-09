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

(* In-memory messaging between the supervisor (invariant manager) and
   the engines of an analysis.

   Historically every engine ran in its own process and messages went
   through ZeroMQ sockets, serialized to strings. Engines now run in
   domains of a single process, so a message is simply an OCaml value
   dropped into the in-memory mailbox of the receiver:

   - an engine sends output messages (log, statistics, progress) to the
     supervisor's mailbox;
   - an engine broadcasts relay messages (invariants, property
     statuses) directly to the mailboxes of the supervisor and of every
     other engine;
   - the supervisor broadcasts control messages (termination) to the
     mailboxes of all engines.

   Terms and other hashconsed values are shared between domains (the
   hashcons tables are protected by locks), so messages are passed by
   reference, without any serialization.

   There are no background threads and no acknowledgement or resend
   protocol: delivery is a mutex-protected queue operation and is
   reliable by construction. [recv] drains the mailbox of the calling
   domain without blocking; [wait_for_message] blocks the calling
   domain until its mailbox is not empty, so that a domain with
   nothing to do until the next message does not have to poll. *)

exception NotInitialized


(* Message and conversions *)
module type RelayMessage =
sig

  (* A message to be relayed to other processes *)
  type t

  (* Pretty-print a message *)
  val pp_print_message : Format.formatter -> t -> unit

end


(* Output signature of functor *)
module type S =
sig

  type relay_message

  type output_message =
    | Log of int * string
    | Stat of string
    | Progress of int

  type control_message =
    | Terminate

  type message =
    | OutputMessage of output_message
    | ControlMessage of control_message
    | RelayMessage of relay_message

  val pp_print_message : Format.formatter -> message -> unit

  (* The messaging system of an analysis. Opaque handle created by the
     supervisor and passed to every engine. *)
  type ctx

  (* Registration of a worker mailbox *)
  type worker

  val init_im : unit -> ctx

  val init_worker : Lib.kind_module -> int -> ctx -> worker

  val run_im : ctx -> unit

  val run_worker : worker -> worker

  val send_relay_message : relay_message -> unit

  val send_output_message : output_message -> unit

  val send_term_message : unit -> unit

  val send_term_message_to : int -> unit

  val recv : unit -> (Lib.kind_module * message) list

  val wait_for_message : unit -> unit

  val purge_im_mailbox : ctx -> unit

  val check_termination : unit -> bool

  val disconnect : worker -> unit

  val exit : worker -> unit

end


(* Functor to instantiate the messaging system with a type of messages *)
module Make (T: RelayMessage) : S with type relay_message = T.t =
struct

  (* Message to be broadcast *)
  type relay_message = T.t


  (* Message to be output to the user *)
  type output_message =

    (* Log message with level *)
    | Log of int * string

    (* Statistics *)
    | Stat of string

    (* Progress *)
    | Progress of int


  (* Message internal to the messaging system *)
  type control_message =

    (* Request termination of process *)
    | Terminate


  (* Message *)
  type message =

    (* Output to user *)
    | OutputMessage of output_message

    (* Message internal to the messaging system *)
    | ControlMessage of control_message

    (* Message to be broadcast to worker processes *)
    | RelayMessage of relay_message


  (* Pretty-print a message *)
  let pp_print_message ppf = function
    | OutputMessage (Log (l, s)) ->
      Format.fprintf ppf "@[<hv>LOG %d@ %s@]" l s

    | OutputMessage (Stat _) ->
      Format.fprintf ppf "@[<v>STAT@,@]"

    | OutputMessage (Progress k) ->
      Format.fprintf ppf "@[<h>PROGRESS %d@]" k

    | ControlMessage Terminate ->
      Format.fprintf ppf "Terminate"

    | RelayMessage m ->
      Format.fprintf ppf "@[<hv>Relay@ %a@]" T.pp_print_message m


  (* ******************************************************************** *)
  (* Thread-safe mailbox                                                  *)
  (* ******************************************************************** *)

  (* A queue with O(1) enqueue: [front] is in order, [back] is
     reversed. [nonempty] is signalled whenever a message is added, so
     that the owner of the mailbox can block until a message arrives
     instead of polling. *)
  type 'a mailbox = {
    lock : Mutex.t ;
    nonempty : Condition.t ;
    mutable front : 'a list ;
    mutable back : 'a list ;
  }

  let mk_mailbox () = {
    lock = Mutex.create () ;
    nonempty = Condition.create () ;
    front = [] ;
    back = [] ;
  }

  let enqueue entry mb =
    Mutex.protect mb.lock (fun () ->
      mb.back <- entry :: mb.back ;
      (* Only the domain owning the mailbox waits on it *)
      Condition.signal mb.nonempty)

  (* Return all messages in order and empty the mailbox *)
  let drain mb =
    Mutex.protect mb.lock (fun () ->
      let msgs = List.rev_append (List.rev mb.front) (List.rev mb.back) in
      mb.front <- [] ;
      mb.back <- [] ;
      msgs)

  (* Block until the mailbox contains a message. Returns immediately
     if the mailbox is not empty. *)
  let wait_nonempty mb =
    Mutex.protect mb.lock (fun () ->
      while mb.front = [] && mb.back = [] do
        Condition.wait mb.nonempty mb.lock
      done)

  (* Check if some message satisfies [f] without consuming anything *)
  let mailbox_exists f mb =
    Mutex.protect mb.lock (fun () ->
      List.exists f mb.front || List.exists f mb.back)


  (* ******************************************************************** *)
  (* Endpoints                                                            *)
  (* ******************************************************************** *)

  (* A worker endpoint: the mailbox of one engine domain.

     An endpoint that the supervisor disconnected is no longer alive:
     the messages it sends are dropped, so an engine that outlives the
     analysis it belongs to cannot disturb the next one. *)
  type endpoint = {
    ep_id : int ;                 (* Identifier of the engine, as in the
                                     supervisor's list of children *)
    ep_mdl : Lib.kind_module ;
    ep_inbox : (Lib.kind_module * message) mailbox ;
    ep_alive : bool Atomic.t ;
  }

  type worker = endpoint

  (* There is one messaging system per process; the handle only makes
     the dependency of workers on the supervisor's setup explicit. *)
  type ctx = unit

  (* Mailbox of the supervisor *)
  let im_inbox : (Lib.kind_module * message) mailbox = mk_mailbox ()

  (* Live worker endpoints. Guarded by [registry_lock]. *)
  let workers : endpoint list ref = ref []
  let registry_lock = Mutex.create ()

  (* The endpoint of the calling domain *)
  type role =
    | Uninitialized
    | Supervisor
    | Worker of endpoint

  let role = Domain.DLS.new_key (fun () -> ref Uninitialized)
  let get_role () = !(Domain.DLS.get role)
  let set_role r = Domain.DLS.get role := r


  (* ******************************************************************** *)
  (* Sending and receiving                                                *)
  (* ******************************************************************** *)

  (* Deliver a message to all worker endpoints except [excep] *)
  let broadcast_to_workers ?excep msg =
    Mutex.protect registry_lock (fun () ->
      !workers |> List.iter (fun w ->
        match excep with
        | Some ep when w == ep -> ()
        | _ -> enqueue msg w.ep_inbox))

  (* Broadcast a message to the worker processes. From a worker, the
     message is also delivered to the supervisor, but not echoed back
     to the sender. *)
  let send_relay_message m =
    match get_role () with
    | Uninitialized -> raise NotInitialized
    | Supervisor ->
      broadcast_to_workers (`Supervisor, RelayMessage m)
    | Worker ep ->
      if Atomic.get ep.ep_alive then (
        let msg = (ep.ep_mdl, RelayMessage m) in
        enqueue msg im_inbox ;
        broadcast_to_workers ~excep:ep msg
      )

  (* Send a message to the invariant manager for output to the user *)
  let send_output_message m =
    match get_role () with
    | Uninitialized -> raise NotInitialized
    | Supervisor ->
      (* The supervisor already outputs directly: sending the message
         to itself would output it twice. *)
      ()
    | Worker ep ->
      if Atomic.get ep.ep_alive then
        enqueue (ep.ep_mdl, OutputMessage m) im_inbox

  (* Send a termination message: broadcast to all workers. A worker
     requesting termination also notifies the other workers, as the
     invariant manager did when it relayed termination requests. *)
  let send_term_message () =
    match get_role () with
    | Uninitialized -> raise NotInitialized
    | Supervisor ->
      broadcast_to_workers (`Supervisor, ControlMessage Terminate)
    | Worker ep ->
      if Atomic.get ep.ep_alive then (
        let msg = (ep.ep_mdl, ControlMessage Terminate) in
        enqueue msg im_inbox ;
        broadcast_to_workers ~excep:ep msg
      )

  (* Send a termination message to the worker with the given identifier *)
  let send_term_message_to id =
    Mutex.protect registry_lock (fun () ->
      !workers |> List.iter (fun w ->
        if w.ep_id = id then
          enqueue (`Supervisor, ControlMessage Terminate) w.ep_inbox))

  (* Receive messages: drain the mailbox of the calling domain *)
  let recv () =
    match get_role () with
    | Uninitialized -> raise NotInitialized
    | Supervisor -> drain im_inbox
    | Worker ep -> drain ep.ep_inbox

  (* Block until a message is queued for the calling domain. Any event
     a domain may wait for arrives as a message, including termination
     requests, so waiting without a timeout cannot delay shutdown. *)
  let wait_for_message () =
    match get_role () with
    | Uninitialized -> raise NotInitialized
    | Supervisor -> wait_nonempty im_inbox
    | Worker ep -> wait_nonempty ep.ep_inbox

  (* Return true if a termination message is queued for the calling
     domain, without consuming any message *)
  let check_termination () =
    let is_term = function
      | (_, ControlMessage Terminate) -> true
      | _ -> false
    in
    match get_role () with
    | Uninitialized -> false
    | Supervisor -> mailbox_exists is_term im_inbox
    | Worker ep -> mailbox_exists is_term ep.ep_inbox


  (* ******************************************************************** *)
  (* Initialization                                                       *)
  (* ******************************************************************** *)

  let init_im () = ()

  (* Take the supervisor role *)
  let run_im () = set_role Supervisor

  (* Create and register the endpoint of a worker *)
  let init_worker mdl id () =
    let ep =
      { ep_id = id ; ep_mdl = mdl ; ep_inbox = mk_mailbox () ;
        ep_alive = Atomic.make true }
    in
    Mutex.protect registry_lock (fun () -> workers := ep :: !workers) ;
    ep

  (* Take the worker role in the calling domain *)
  let run_worker ep = set_role (Worker ep) ; ep

  (* Unregister the endpoint of a worker. Safe to call from any
     domain: the messages the worker sends from now on are dropped,
     and a termination message is left in its mailbox so that it
     unwinds at its next event check. *)
  let disconnect ep =
    Atomic.set ep.ep_alive false ;
    Mutex.protect registry_lock (fun () ->
      workers := List.filter (fun w -> w != ep) !workers) ;
    enqueue (`Supervisor, ControlMessage Terminate) ep.ep_inbox

  (* Unregister the endpoint of a worker, from the worker itself *)
  let exit ep =
    disconnect ep ;
    set_role Uninitialized

  (* Drop the messages of the previous analysis. All workers of the
     previous analysis must have exited. *)
  let purge_im_mailbox () =
    ( match Mutex.protect registry_lock (fun () -> !workers) with
      | [] -> ()
      | _ ->
        Debug.messaging
          "purge_im_mailbox: workers of previous analysis still registered" ) ;
    drain im_inbox |> ignore

end


(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
