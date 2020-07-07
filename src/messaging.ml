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

(* #load "threads.cma" *) (* might be necessary if testing in toplevel *)

open Lib
open Zmq
open Printf


(******************************)
(*  Types                     *)
(******************************)


exception SocketConnectFailure
exception SocketBindFailure
exception BadMessage
exception InvalidProcessName  
exception NotInitialized


(* Return true if the process is the invariant manages *)
let is_invariant_manager = function 
  | `Supervisor -> true
  | _ -> false


(* Pretty-print ZMQ message frames *)
let rec pp_print_zmsg_frames ppf = function
  | [] -> ()
  | x :: xs ->
      Format.fprintf ppf "%s" (String.escaped x);
      if xs != [] then Format.fprintf ppf ";@ ";
      pp_print_zmsg_frames ppf xs

(* Pretty-print a ZMQ message *)
let pp_print_zmsg ppf zmsg =
  (* Copy message and print all frames *)
  Format.fprintf ppf "@[<hv 1>{%a}@]" pp_print_zmsg_frames zmsg


(* Message and conversions *)
module type RelayMessage = 
sig

  (* A message to be relayed to other processes *)
  type t

  (** ZMQ's representation of the message *)
  type zmsg = string list

  (* Convert a message to a strings for message frames *)
  val message_of_strings : zmsg -> t

  (* Convert string from message frames to a message *)
  val strings_of_message : t -> zmsg

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
    | Ready
    | Ping
    | Terminate
    | Resend of int

  type message = 
    | OutputMessage of output_message
    | ControlMessage of control_message
    | RelayMessage of int * relay_message

  type ctx

  type socket

  type thread

  val init_im : unit -> (ctx * socket * socket) * (string * string)

  val init_worker : Lib.kind_module -> string -> string -> ctx * socket * socket

  val run_im : ctx * socket * socket -> (int * Lib.kind_module) list -> (exn -> unit) -> unit 

  val run_worker : ctx * socket * socket -> Lib.kind_module -> (exn -> unit) -> thread

  val send_relay_message : relay_message -> unit

  val send_output_message : output_message -> unit

  val send_term_message : unit -> unit
    
  val recv : unit -> (Lib.kind_module * message) list
    
  val update_child_processes_list : (int * Lib.kind_module) list -> unit

  val purge_im_mailbox : ctx * socket * socket -> unit
    
  val check_termination : unit -> bool

  val exit : thread -> unit 

end


(* Functor to instantiate the messaging system with a type of messages *)
module Make (T: RelayMessage) : S with type relay_message = T.t =
struct

  (* ZeroMQ context *)
  type ctx = Zmq.Context.t

  (* ZeroMQ socket *)
  type socket = [ `Pub | `Sub | `Push | `Pull ] Zmq.Socket.t

  (* Background thread *)
  type thread = Thread.t

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

    (* Process is ready *)
    | Ready

    (* Request reply from process *)
    | Ping

    (* Request termination of process *)
    | Terminate

    (* Request resending of relay message *)
    | Resend of int


  (* Message *)
  type message = 

    (* Output to user *)
    | OutputMessage of output_message

    (* Message internal to the messaging system *)
    | ControlMessage of control_message

    (* Message to be broadcast to worker processes *)
    | RelayMessage of int * relay_message


  (* Pretty-print a message *)
  let pp_print_message ppf = function 
    | OutputMessage (Log (l, s)) -> 
      Format.fprintf ppf "@[<hv>LOG %d@ %s@]" l s
                               
    | OutputMessage (Stat _) -> 
      Format.fprintf ppf "@[<v>STAT@,@]"
        
    | OutputMessage (Progress k) -> 
      Format.fprintf ppf "@[<h>PROGRESS %d@]" k
                                    
    | ControlMessage Ready -> 
      Format.fprintf ppf "Ready"
                                
    | ControlMessage Ping -> 
      Format.fprintf ppf "Ping"
                               
    | ControlMessage Terminate -> 
      Format.fprintf ppf "Terminate"

    | ControlMessage (Resend i) -> 
      Format.fprintf ppf "Resend %d" i

    | RelayMessage (i, m) -> 
      Format.fprintf ppf "@[<hv>Relay %d@ %a@]" i T.pp_print_message m


  (* ******************************************************************** *)
  (* Conversions                                                          *)
  (* ******************************************************************** *)

  (* Return a list of strings of a message *)
  let strings_of_output_message = function 
    | Log (i, s) -> ["LOG"; string_of_int i; s]
    | Stat s -> ["STAT"; s]
    | Progress i -> ["PROGRESS"; string_of_int i]


  (* Return a message of a list of strings *)
  let output_message_of_strings = function
    | "LOG" :: i :: s :: _ -> (try Log (int_of_string i, s) with
        | Invalid_argument _ ->
          raise (Invalid_argument "output_message_of_strings a"))
    | "STAT" :: s :: _ -> Stat s
    | "PROGRESS" :: i :: _ -> (try Progress (int_of_string i) with 
        | Invalid_argument _ -> 
          raise (Invalid_argument "output_message_of_strings b"))
    | x -> ignore (Debug.messaging "MSG:%s" (String.concat "" x)); raise (Invalid_argument "output_message_of_strings c")


  (* Return a list of strings of a message *)
  let strings_of_control_message = function 
    | Ready -> ["READY"]
    | Ping -> ["PING"]
    | Terminate -> ["TERM"]
    | Resend i -> ["RESEND"; string_of_int i]


  (* Return a message of a list of strings *)
  let control_message_of_strings = function
    | "READY" :: _ -> Ready
    | "PING" :: _ -> Ping
    | "TERM" :: _ -> Terminate
    | "RESEND" :: i :: _ -> (try Resend (int_of_string i) with 
        | Invalid_argument _ -> 
          raise (Invalid_argument "control_message_of_strings"))
    | _ -> raise (Invalid_argument "control_message_of_strings")


  (* Return unique tag for message type *)
  let tag_of_message = function
    | OutputMessage _ -> "OUTPUT"
    | ControlMessage _ -> "CONTROL"
    | RelayMessage _ -> "RELAY"


  (* Return a message from strings *)
  let message_of_strings payload = function
    | "OUTPUT" -> OutputMessage (output_message_of_strings payload)
    | "CONTROL" -> ControlMessage (control_message_of_strings payload)
    | "RELAY" -> (
        let i = List.hd payload in
        try
          RelayMessage (int_of_string i, T.message_of_strings (List.tl payload))
        with Invalid_argument _ -> raise BadMessage)
    | _ -> raise BadMessage


  (*        zmsg representation of a message:              *)
  (* top of stack                                          *)
  (* ----------------------------------------------------- *)
  (*  MSG TYPE | SENDER | PAYLOAD | (PAYLOAD) | (PAYLOAD)  *)
  (* ----------------------------------------------------- *)
      
  (* We want the type of the message first, so that workers can
     subscribe to the relevant messages only *)

  (* Create a ZeroMQ message *)
  let zmsg_of_msg msg =
    (* Use the PID of the process as sender *)
    let sender = string_of_int (Unix.getpid ()) in
    let zmsg =
      tag_of_message msg :: sender
      ::
      ( match msg with
      | OutputMessage m -> strings_of_output_message m
      | ControlMessage m -> strings_of_control_message m
      | RelayMessage (i, m) -> string_of_int i :: T.strings_of_message m )
    in
    Debug.messaging "@[<hv>zmsg_of_msg:@ %a@]" pp_print_zmsg zmsg;
    (* Return message *)
    zmsg


  (* Return a message of a ZeroMQ message *)
  let msg_of_zmsg = function
    | tag :: sender :: payload ->
        Debug.messaging "@[<hv>msg_of_zmsg:@ %a@]" pp_print_zmsg
          (tag :: sender :: payload);
        (int_of_string sender, message_of_strings payload tag)
    | _ -> raise BadMessage

  (* ******************************************************************** *)
  (* Threadsafe list option                                               *)
  (* ******************************************************************** *)

  type 'a locking_list_option =
      { lock : Mutex.t ; mutable l_opt : 'a list option }

  let new_locking_list_option () =
    { lock = Mutex.create () ; l_opt = None }

  (* ******************************************************************** *)
  (* Threadsafe locking queue                                             *)
  (* ******************************************************************** *)
        
  type 'a locking_queue = { lock : Mutex.t ; mutable q : 'a list }


  let new_locking_queue () =
    { lock = Mutex.create (); q = [] }
    
  
  let enqueue entry queue =
    
    (* insert at back of queue *)
    Mutex.lock queue.lock;
    
    queue.q <- queue.q @ [entry]; 
    
    (* a tail-recursive append would be more efficient, depending on
       how big queue gets *)
    Mutex.unlock queue.lock


  
  let push_front entry queue = 
    
    (* push to front of queue *)
    Mutex.lock queue.lock;
    
    queue.q <- entry :: queue.q;
    
    Mutex.unlock queue.lock
      
  
  let dequeue queue =
    
    Mutex.lock queue.lock;
    
    let entry =
      match queue.q with 
        | [] -> None
        | h::t -> 
          queue.q <- t; 
          Some(h)
    in
    
    Mutex.unlock queue.lock;
    
    entry
    
  
  (* Return all elements in queue in order, and empty the queue *)
  let empty_list queue = 
    
    Mutex.lock queue.lock;
    
    let res = queue.q in
    
    queue.q <- [];
    
    Mutex.unlock queue.lock;
    
    res
    
  
  (* Checks if a message in 'queue' is such that f. Does not modify
     'queue'. *)
  let queue_exists f queue = 
    
    Mutex.lock queue.lock;

    let res = List.exists f queue.q in
    
    Mutex.unlock queue.lock;
    
    res
    
  (* ******************************************************************** *)
  (*  Globals                                                             *)
  (* ******************************************************************** *)

  (* Fresh incoming messages

     Keep messages in the order received, first message at the head of
     the list *)
  let incoming = new_locking_queue ()

  (* Optional list of new child processes. Used to tell the background
     thread we restarted with new child processes. *)
  let new_workers_option = new_locking_list_option ()

  (* Messages to be sent

     Keep messages in the order received *)
  let outgoing = new_locking_queue ()

  (* Messages to be delivered to worker process

     Keep messages in the order received *)
  let incoming_handled = new_locking_queue ()

  (* messages to receive iteration of the background thread loop *)
  let message_burst_size = 100

  (* how often (in seconds) must workers check in with Invariant
     Manager? *)
  let worker_time_threshold = (1.0 *. 60.)

  (* how soon (in seconds) must invariants be confirmed before workers
     resend them? *)
  let worker_invariant_confirmation_threshold = (0.3 *. 60.)

  (* currently initialized process *)
  let initialized_process = ref None
      
  (* debugging/testing? *)
  let debug_mode = ref false
      
  (* Exit requested? *)
  let exit_flag = ref false
      
  (* ******************************************************************** *)
  (*  Thread Helpers                                                      *)
  (* ******************************************************************** *)

  let im_handle_messages workers worker_status invariant_id invariants = 

    let rec handle_all = function

      | msg :: t ->  

        (* *)
        let sender, payload = msg in

        Debug.messaging
          "Invariant manager received message %a from %d"
          pp_print_message payload 
          sender;

        if List.mem_assoc sender workers then begin

        (match payload with 

          | OutputMessage m -> 

            enqueue 
              ((List.assoc sender workers), payload) 
              incoming_handled

          | ControlMessage m -> 

            (match m with
              | Ready -> ()
              | Ping -> enqueue (ControlMessage(Ready)) outgoing
              | Terminate -> enqueue (ControlMessage(Terminate)) outgoing

              | Resend n -> 

                try 
                  enqueue (Hashtbl.find invariants n) outgoing
                with 
                  | Not_found -> ()

            )

          | RelayMessage (_, m) -> 

            let identified_msg = 
              RelayMessage (!invariant_id, m)
            in

            Hashtbl.add invariants !invariant_id identified_msg;

            enqueue identified_msg outgoing;

            invariant_id := !invariant_id + 1;

            enqueue
              ((List.assoc sender workers), payload) 
              incoming_handled
        );

        (* update the status of the sender *)
        Hashtbl.replace worker_status sender (Unix.time ())
        end ;

        handle_all t;

      | []  -> ()

    in

    let msgs = (empty_list incoming) in

    handle_all msgs
      
  
  let rec worker_request_missing_invariants 
      last_received_invariant_id 
      current_invariant_id =
    
    (* request all invariants between [last_received_invariant_id] and
       [current_invariant_id] *)
    if 
      
      ((!last_received_invariant_id) + 1) >= current_invariant_id 
      
    then
      
      ()
      
    else 
      
      (
        
        last_received_invariant_id := !last_received_invariant_id + 1;

        enqueue
          (ControlMessage (Resend (!last_received_invariant_id))) 
          outgoing;

        worker_request_missing_invariants 
          last_received_invariant_id 
          current_invariant_id

    )


  let worker_handle_messages 
      unconfirmed_invariants 
      confirmed_invariants 
      last_received_invariant_id = 

    (* handle messages in incoming queue of worker process *)

    (* it might be worth looking into efficiency of dealing with
       unconfirmed invariant list *)
    let rec handle_all = function

      | msg :: t ->  

        let sender, payload = msg in

        Debug.messaging
          "Worker received message %a from %d"
          pp_print_message payload 
          sender;

        (match payload with 

          | OutputMessage _ -> ()

          | ControlMessage m  -> 

            (match m with

              | Ready -> ()

              | Ping -> enqueue (ControlMessage Ready) outgoing

              | Terminate -> 

                enqueue
                  (`Supervisor, payload) 
                  incoming_handled

              (* Workers do not resend messages *)
              | Resend n -> ()

            )


          | RelayMessage (i, m) ->

            (* Remove sequence number from message *)
            let payload' = RelayMessage (0, m) in 

            if 

              (* Message is ours and had not been confirmed? *)
              Hashtbl.mem 
                unconfirmed_invariants 
                payload'

            then 

              (

                (* Message is no longer unconfirmed *)
                Hashtbl.remove 
                  unconfirmed_invariants 
                  payload';

                (* Message is confirmed *)
                Hashtbl.add confirmed_invariants i msg

              ) 

            else 

              (

                (* Skip if message has received before *)
                if Hashtbl.mem confirmed_invariants i then () else 

                  (

                    (* Accept message *)
                    enqueue 
                      (`Supervisor, payload) 
                      incoming_handled;

                    (* Store message *)
                    Hashtbl.add confirmed_invariants i msg;

                    if 

                      (* Gap in sequence detected? *)
                      i > ((!last_received_invariant_id) + 1) 

                    then 

                      (

                        (* we've missed at least one invariant,
                           request any not received *)
                        worker_request_missing_invariants 
                          last_received_invariant_id 
                          i

                      );

                    (* Keep sequence for next iteration *)
                    last_received_invariant_id := i

                  )

              )

        );

        handle_all t;

      | [] -> ()

    in 

    handle_all (empty_list incoming)


  let purge_messages sock =
    let rec recv_iter _ = recv_iter (Zmq.Socket.recv_all ~block:false sock) in

    try recv_iter (Zmq.Socket.recv_all ~block:false sock)
    with Unix.Unix_error (Unix.EAGAIN, _, _) -> ()


  let recv_messages sock as_invariant_manager =
    (* receive up to 'message_burst_size' messages from sock *)
    let rec recv_iter i zmsg =
      if i < message_burst_size then (
        ( if as_invariant_manager || not !debug_mode then
          enqueue (msg_of_zmsg zmsg) incoming
        else
          let _, message = msg_of_zmsg zmsg in
          enqueue (`Supervisor, message) incoming_handled );
        recv_iter (i + 1) (Zmq.Socket.recv_all ~block:false sock) )
    in

    try recv_iter 0 (Zmq.Socket.recv_all ~block:false sock)
    with Unix.Unix_error (Unix.EAGAIN, _, _) -> ()


  let im_send_messages sock =
    (* send up to 'message_burst_size' messages in invariant manager's
       outgoing message queue *)
    let rec send_iter i outgoing_msg =
      if i < message_burst_size && outgoing_msg != None then (
        let message = get outgoing_msg in
        let zm = zmsg_of_msg message in
        Zmq.Socket.send_all sock zm;

        send_iter (i + 1) (dequeue outgoing) )
    in

    send_iter 0 (dequeue outgoing)


  let worker_send_messages proc sock unconfirmed_invariants =
    (* send up to 'message_burst_size' messages in worker's outgoing
       message queue *)
    let rec send_iter i outgoing_msg =
      if i < message_burst_size && outgoing_msg != None then (
        let message = get outgoing_msg in

        Debug.messaging "Worker %d sending message %a" (Unix.getpid ())
          pp_print_message message;

        Zmq.Socket.send_all sock (zmsg_of_msg message);

        (* if this message is a relay message, place it in
           unconfirmed list with current timestamp *)
        ( match message with
        | RelayMessage (_, m) ->
            Hashtbl.add unconfirmed_invariants
              (RelayMessage (0, m))
              (Unix.time ())
        | _ -> () );

        send_iter (i + 1) (dequeue outgoing) )
    in

    send_iter 0 (dequeue outgoing)


  let worker_resend_invariants unconfirmed_invariants =
    (* resend unconfirmed invariants *)
    let resend_if_needed invariant timestamp =
      if Unix.time () -. timestamp > worker_invariant_confirmation_threshold
      then (
        enqueue invariant outgoing;

        (* a missed invariant is only resent once *)
        match invariant with
        | RelayMessage (_, m) ->
            Hashtbl.remove unconfirmed_invariants (RelayMessage (0, m))
        | _ -> () )
    in

    Hashtbl.iter resend_if_needed unconfirmed_invariants


  let update_worker_status workers worker_status =
    (* update timestamp of worker status *)
    for i = 0 to ((List.length workers) - 1) do
      Hashtbl.add (worker_status) (List.nth workers i) (Unix.time ());
    done


  let wait_for_workers workers worker_status pub_sock pull_sock =
    (* wait for ready from all workers *)
    let rec wait_iter = function
      (* No more workers to wait for *)
      | [] -> ()
      (* List of workers to wait for is not empty *)
      | workers_remaining -> (
          Debug.messaging "Sending PING to workers";

          (* let workers know invariant manager is ready *)
          Zmq.Socket.send_all pub_sock (zmsg_of_msg (ControlMessage Ping));

          (* Receive message on PULL socket *)
          try
            let msg = Zmq.Socket.recv_all ~block:false pull_sock in

            let sender, payload = msg_of_zmsg msg in

            if payload = ControlMessage Ready then (
              Debug.messaging
                "Received a READY message from %d while waiting for workers"
                sender;

              wait_iter (List.filter (( <> ) sender) workers_remaining) )
            else (
              Debug.messaging
                "Received message from %d while waiting for workers: %a" sender
                pp_print_message payload;

              wait_iter (List.filter (( <> ) sender) workers_remaining) )
          with Unix.Unix_error (Unix.EAGAIN, _, _) ->
            Debug.messaging "No message received, still waiting for workers";

            minisleep 0.1;
            wait_iter workers_remaining )
    in

    wait_iter workers;
    update_worker_status workers worker_status


  let im_check_workers_status workers worker_status pub_sock pull_sock =
    (* ensure that all workers have checked in within
       worker_time_threshold seconds *)
    let rec check_status workers need_ping =
      match workers with
      | h :: t ->
          if
            Unix.time () -. Hashtbl.find worker_status h > worker_time_threshold
          then (
            (* at least one worker has not communicated recently *)
            Hashtbl.replace worker_status h (Unix.time ());

            check_status t true )
          else check_status t need_ping
      | [] -> need_ping
    in

    (* if a worker hasn't communicated in a while, broadcast a ping *)
    if check_status workers false then enqueue (ControlMessage Ping) outgoing


  (* ******************************************************************** *)
  (*  Threads                                                             *)
  (* ******************************************************************** *)

  let im_thread (bg_ctx, pub_sock, pull_sock) workers on_exit =

    let invariant_id = ref 1 in

    let rec init_and_run workers =
      (* List of PIDs only. *)
      let worker_pids = List.map fst workers in

      (* Hashtable to store time each worker was last seen. *)
      let worker_status =
        (Hashtbl.create (List.length worker_pids))
      in

      (* Rewrite this code or remove it.
         Messages are discarded while waiting for workers.

      Debug.messaging
        "Waiting for workers (%a) to become ready."
        (pp_print_list Format.pp_print_int ",@")
        worker_pids;

      (* Waiting for all workers to be ready. *)
      wait_for_workers
        worker_pids worker_status pub_sock pull_sock ;

      Debug.messaging "All workers are ready.";*)

      update_worker_status worker_pids worker_status ;
      
      (* Unique invariant identifier and invariants hash table. *)
      invariant_id := 1 ;
      let invariants = (Hashtbl.create 1000) in

      (* Running with the workers pids, the time hashtable, and the
         invariants. *)
      run workers worker_pids worker_status invariants

    and run workers worker_pids worker_status invariants =

      (* We take the lock to avoid race conditions during restarts,
      especially we want to avoid messages from the previous analysis to be received *)
      Mutex.lock new_workers_option.lock ;

      (* Check for new workers, indicating a restart of the supervisor. *)
      let res = new_workers_option.l_opt in
      new_workers_option.l_opt <- None ;
      match res with
      | Some new_workers -> (
        (* We do not need the lock here
        because init_and_run does not reads the messages *)
        Mutex.unlock new_workers_option.lock ;
        Debug.messaging
          "Child processes update, \
            setting things up and resume running.";
        init_and_run new_workers
      )
      | None -> (
        (* No worker means that the reception of messages is disabled *)
        if worker_pids <> []
        then (
          (* Check on the workers. *)
          im_check_workers_status
            worker_pids worker_status pub_sock pull_sock ;

          (* Get any messages from workers. *)
          recv_messages
            pull_sock true ;

          (* Relay messages. *)
          im_handle_messages
            workers worker_status invariant_id invariants ;

          (* Send any messages in outgoing queue. *)
          im_send_messages pub_sock
        ) ;
        
        (* We free the lock *)
        Mutex.unlock new_workers_option.lock ;

        minisleep 0.01 ;

        run workers worker_pids worker_status invariants
      )

    in

    try

      (* Initializes and runs the background thread. If new workers
         are provided, reinitializes and relaunches itself. *)
      init_and_run workers

    with e -> on_exit e
                

  let worker_thread (bg_ctx, sub_sock, push_sock) (proc, on_exit) =

    try 

      (

        (*let rc =
          zmsg_send 
            (zmsg_of_msg 
               (ControlMessage Ready)) 
            push_sock
        in

        assert (rc = 0);

        (* wait for a message from the IM before sending anything *)
        Debug.messaging
          "Waiting for message from invariant manager in %d" (Unix.getpid ());

        ignore(zmsg_recv sub_sock);*)

        Debug.messaging "Worker is ready to send messages";

        let confirmed_invariants = (Hashtbl.create 1000) in
        let unconfirmed_invariants = (Hashtbl.create 100) in
        let last_received_invariant_id = ref 0 in

        while true do

          if !exit_flag then 

            (

              (* send any messages in outgoing queue *)
              worker_send_messages proc push_sock unconfirmed_invariants;

              Thread.exit ()

            )

          else

            (

              (* get any messages from invariant manager *)
              recv_messages sub_sock (is_invariant_manager proc);

              (* handle incoming messages *)
              if (not !debug_mode) then 

                (

                  worker_handle_messages 
                    unconfirmed_invariants 
                    confirmed_invariants 
                    last_received_invariant_id

                );

              (* send any messages in outgoing queue *)
              worker_send_messages proc push_sock unconfirmed_invariants;

              (* resend any old unconfirmed invariants *)
              worker_resend_invariants unconfirmed_invariants;

              minisleep 0.01

            )

        done)

    with e -> on_exit e


(* ******************************************************************** *)
(*  Public Interface                                                    *)
(* ******************************************************************** *)

  let init_im () =
    (* sockets for communication with worker processes *)
    let bg_ctx = Zmq.Context.create () in

    (* pub socket to send updates to workers *)
    let pub_sock = Zmq.Socket.create bg_ctx Zmq.Socket.pub in
    Zmq.Socket.bind pub_sock "tcp://127.0.0.1:*";
    let bcast_port = Zmq.Socket.get_last_endpoint pub_sock in

    (* pull socket to get updates from workers *)
    let pull_sock = Zmq.Socket.create bg_ctx Zmq.Socket.pull in
    Zmq.Socket.bind pull_sock "tcp://127.0.0.1:*";
    let push_port = Zmq.Socket.get_last_endpoint pull_sock in
    Debug.messaging "PUB socket is at %s, PULL socket is at %s" bcast_port
      push_port;

    (* Return sockets *)
    ( (bg_ctx, pub_sock, pull_sock),
      (* Return broadcast and push ports *)
      (bcast_port, push_port) )


  let init_worker proc bcast_port push_port =
    (* sockets for communication with invariant manager *)
    let bg_ctx = Zmq.Context.create () in

    (* subscribe to updates from invariant manager *)
    let sub_sock = Zmq.Socket.create bg_ctx Zmq.Socket.sub in

    Zmq.Socket.connect sub_sock bcast_port;

    Zmq.Socket.subscribe sub_sock "CONTROL";
    Zmq.Socket.subscribe sub_sock "RELAY";

    (* create push socket for sending updates to the invariant manager *)
    let push_sock = Zmq.Socket.create bg_ctx Zmq.Socket.push in
    Zmq.Socket.connect push_sock push_port;

    Debug.messaging "SUB port for %a is %s, PUSH port is %s"
      pp_print_kind_module proc bcast_port push_port;

    (* Return sockets *)
    (bg_ctx, sub_sock, push_sock)


  let run_im (bg_ctx, pub_sock, pull_sock) workers on_exit =
    try
      let p =
        Thread.create
          (im_thread (bg_ctx, pub_sock, pull_sock) workers)
          (fun exn ->
            Zmq.Socket.close pub_sock;
            Zmq.Socket.close pull_sock;
            Zmq.Context.terminate bg_ctx;
            on_exit exn)
      in

      initialized_process := Some `Supervisor;

      (* thread identifier, might come in handy *)
      ignore p
    with SocketBindFailure -> raise SocketBindFailure


  let run_worker (bg_ctx, sub_sock, push_sock) proc on_exit =
    try
      let p =
        Thread.create
          (worker_thread (bg_ctx, sub_sock, push_sock))
          ( proc,
            fun exn ->
              Zmq.Socket.close sub_sock;
              Zmq.Socket.close push_sock;
              Zmq.Context.terminate bg_ctx;
              on_exit exn )
      in

      initialized_process := Some proc;

      p
    with (* | Terminate -> raise Terminate *)
    | SocketConnectFailure ->
      raise SocketConnectFailure


  let send msg = 
    if !initialized_process = None then raise NotInitialized else
      ( (* minisleep otherwise some messages get lost *)
        (* minisleep 0.001; *)
        enqueue msg outgoing)


  let send_term_message () = send (ControlMessage Terminate)


  let send_output_message msg = send (OutputMessage msg)


  let send_relay_message msg = send (RelayMessage (0, msg))


  let recv () = 
    if !initialized_process = None then raise NotInitialized else
      (empty_list incoming_handled)


  let update_child_processes_list ps =
    Debug.messaging
      "Updating child process list in background thread.";
    if !initialized_process = None
    then raise NotInitialized
    else (
      (* Taking a lock on the list option. *)
      Mutex.lock new_workers_option.lock ;
      (* Setting the new value of the list option. *)
      new_workers_option.l_opt <- Some ps ;
      (* Releasing lock. *)
      Mutex.unlock new_workers_option.lock
    )


  let purge_im_mailbox (_, pub_sock, pull_sock) =
    Debug.messaging "PUB: %s, PULL: %s"
      (Zmq.Socket.get_last_endpoint pub_sock)
      (Zmq.Socket.get_last_endpoint pull_sock);
    if !initialized_process = None
    then raise NotInitialized
    else (
      (* Purging the messages because they refer to the old child processes *)
      purge_messages pull_sock ;
      empty_list incoming |> ignore ;
      empty_list incoming_handled |> ignore ;
      empty_list outgoing |> ignore
    )

  let check_termination () =

    if !initialized_process = None
    then false
    else
      queue_exists
        ( fun msg ->
          match snd msg with
          | ControlMessage Terminate -> true
          | _ -> false )
        incoming_handled


  let exit t = 
    exit_flag := true; 
    Thread.join t

end


(*

(******************************)
(*  Tests                     *)
(******************************)

let messaging_selftest () = 

  let minisleep (sec: float) =
    (* sleep for sec seconds *)
    ignore (Unix.select [] [] [] sec)
  in

  let on_exit e = 
    print_endline (Printexc.to_string e)
  in

  let write_to_file file line = 
    let oc = open_out_gen [Open_creat; Open_text; Open_append; Open_nonblock] 0o640 file in
    output_string oc (line ^ "\n");
    close_out oc;
  in

  let worker_selftest worker_name = 
    let get_messages invariants_received outfile =
      let msgs = recv () in
      let write_msg msg = 
        write_to_file outfile ( worker_name ^ " received " ^ (string_of_msg msg));
      in 
      List.iter write_msg msgs;
      invariants_received := !invariants_received + List.length msgs;
    in
    let send_messages invariants_sent outfile =
      for i = 0 to 20 do
        let outmsg = (InvariantMessage(INVAR((worker_name ^ " invariant " ^ (string_of_int (!invariants_sent))), 0))) in
        send outmsg;
        invariants_sent := !invariants_sent + 1;
        let outmsg = (CounterexampleMessage(COUNTEREXAMPLE((!invariants_sent)))) in
        send outmsg;
        invariants_sent := !invariants_sent + 1;
        (* test BMC messages *)
        let outmsg = (InductionMessage(BMCSTATE(!invariants_sent, [worker_name; (worker_name ^ "x"); ""; "end of list"]))) in
        send outmsg;
        invariants_sent := !invariants_sent + 1;
      done;
    in
    (* overwrite file if it exists *)
    let outfile = ("selftest_out.txt") in
    let oc = open_out outfile in
    output_string oc "Self Test Results\n-----------------\n\n";
    close_out oc;
    write_to_file outfile (worker_name ^ " starting");
    ignore(init (kind_module_of_string worker_name) on_exit);
    let invariants_sent = ref 0 in 
    let invariants_received = ref 0 in
    for i = 0 to 10 do    
      send_messages invariants_sent outfile;
      get_messages invariants_received outfile;
      minisleep 0.01;
    done;
    Unix.sleep 1;
    get_messages invariants_received outfile;
    let resultsfile = "selftest_out.txt" in
    print_endline (worker_name ^ " results:");
    write_to_file resultsfile (worker_name ^ " results:\n" ^ "\t" ^ (string_of_int !invariants_sent) 
                              ^ " messages sent and " 
                              ^ (string_of_int !invariants_received)
                              ^ " messages received."
                              ^ (string_of_float (Sys.time ()))
                              ^ " seconds.");
    print_endline ("\t" ^ (string_of_int !invariants_sent) 
                  ^ " messages sent and " 
                  ^ (string_of_int !invariants_received)
                  ^ " messages received in "
                  ^ (string_of_float (Sys.time ()))
                  ^ " seconds.");
  in

  let im_selftest workers = 
    let outfile = "selftest_out.txt" in
    write_to_file outfile ("InvariantManager starting");
    ignore(init (InvariantManager workers) on_exit);
    while true do
      minisleep 0.01
    done;
  in

  (* begin test *)
  debug_mode := true;
  
  (* for each worker and the IM, spawn a process which will send and receive so many messages *)
  let pids = ref [] in
  (*
  let a = Unix.fork () in
  (match a with
    0   ->  im_selftest (); exit 0;
  | _   ->  pids := a::(!pids)
  );
*)
  let spawn_worker worker_name = 
    let a = Unix.fork () in
    (match a with
      0   ->  worker_selftest worker_name; exit 0; 
    | _   ->  pids := a::(!pids))
  in
  print_endline "Spawning workers and sending messages..";
  List.iter spawn_worker ["BMC"];
  im_selftest !pids; 
  (* wait for first child to exit *)
  let p, stat = Unix.wait () in
  ignore(p);
  ignore(stat); (* useful if you want the reason why the child terminated *)
  Unix.sleep 3;
  (* kill any remaining children *)
  let killprocess signal pid =
    try Unix.kill pid signal with Unix.Unix_error(Unix.ESRCH, "kill", "") -> ();
  in
  List.iter (killprocess 9) !pids;
  print_endline "Self test complete.";
  debug_mode := false;


(* messaging_selftest () *)

*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
