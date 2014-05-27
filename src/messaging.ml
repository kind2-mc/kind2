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

(* #load "threads.cma" *) (* might be necessary if testing in toplevel *)

open Lib
open ZMQ
open Printf


(******************************)
(*  Types                     *)
(******************************)

exception No_value
(* exception Terminate *)
exception SocketConnectFailure
exception SocketBindFailure
exception BadMessage
exception InvalidProcessName  
exception NotInitialized

(*
type process = 
  | InvariantManager of int list
  | BMC
  | InductiveStep
  | PDR
  | InvariantGenerator
*)

let is_invariant_manager = function 
  | `INVMAN -> true
  | _ -> false

type user_message = 
  | Log of int * string
  | Stat of string
  | Progress of int

type control = 
  | READY
  | PING
  | TERM

type invariant = 
  | INVAR of string * int

  | PROP_KTRUE of string * int * int
  | PROP_INVAR of string * int 
  | PROP_FALSE of string * int
  | PROP_KFALSE of string * int * int

  | PROVED of string * int * int
  | DISPROVED of string * int * int

  | RESEND of int

type induction = 
  | BMCSTATE  of int * (string list)

type counterexample = 
  | COUNTEREXAMPLE of int

type message = 
  | UserMessage of user_message
  | ControlMessage of control
  | InvariantMessage of invariant 
  | InductionMessage of induction
(*  | CounterexampleMessage of counterexample *)

type ctx = ZMQ.zctx
type socket = ZMQ.zsocket
type thread = Thread.t

let pp_print_message ppf = function 

  | UserMessage (Log _) -> Format.fprintf ppf "LOG"

  | UserMessage (Stat _) -> Format.fprintf ppf "STAT"

  | UserMessage (Progress _) -> Format.fprintf ppf "PROGRESS"

  | ControlMessage READY -> Format.fprintf ppf "READY"

  | ControlMessage PING -> Format.fprintf ppf "PING"

  | ControlMessage TERM -> Format.fprintf ppf "TERM"

  | InvariantMessage (INVAR (_, n)) -> 
    Format.fprintf ppf "INVAR (_,%d))" n

  | InvariantMessage (PROP_KTRUE (p, k, n)) -> 
    Format.fprintf ppf "PROP_KTRUE (%s,%d,%d))" p k n

  | InvariantMessage (PROP_INVAR (p, n)) -> 
    Format.fprintf ppf "PROP_INVAR (%s,%d))" p n

  | InvariantMessage (PROP_FALSE (p, n)) -> 
    Format.fprintf ppf "PROP_FALSE (%s,%d))" p n

  | InvariantMessage (PROP_KFALSE (p, k, n)) -> 
    Format.fprintf ppf "PROP_KFALSE (%s,%d,%d))" p k n

  | InvariantMessage (DISPROVED (_, k, n)) -> 
    Format.fprintf ppf "DISPROVED (_,%d,%d))" k n

  | InvariantMessage (PROVED (_, k, n)) -> 
    Format.fprintf ppf "PROVED (_,%d,%d))" k n

  | InvariantMessage (RESEND n) -> Format.fprintf ppf "RESEND(%d)" n

  | InductionMessage (BMCSTATE (k, _)) -> 
    Format.fprintf ppf "BMCSTATE(%d, _)" k
(*                                         
  | CounterexampleMessage (COUNTEREXAMPLE n) -> 
    Format.fprintf ppf "COUNTEREXAMPLE(%d)" n
*)

(******************************)
(*  Threadsafe locking queue  *)
(******************************)

type 'a locking_queue = { lock : Mutex.t ; mutable q : 'a list }

let new_locking_queue () =
  { lock = Mutex.create (); q = [] }


let enqueue entry queue =

  (* insert at back of queue *)
  Mutex.lock queue.lock;

  queue.q <- queue.q @ [entry]; 

  (* a tail-recursive append would be more efficient, 
    depending on how big queue gets *)
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


let remove_list queue = 

  (* returns the contents of the queue 
    as a list, empties the queue *)
  Mutex.lock queue.lock;

  let res = queue.q in

  queue.q <- [];

  Mutex.unlock queue.lock;

  res



(******************************)
(*  Utilites                  *)
(******************************)

(*
let string_of_process = function
  | InvariantManager _ -> "InvariantManager"
  | BMC -> "BMC"
  | InductiveStep -> "InductiveStep"
  | PDR -> "PDR"
  | InvariantGenerator -> "InvariantGenerator"


let process_of_string = function
  | "InvariantManager" -> InvariantManager []
  | "BMC" -> BMC
  | "InductiveStep" -> InductiveStep
  | "PDR" -> PDR
  | "InvariantGenerator" -> InvariantGenerator
  | _ -> raise InvalidProcessName       
*)

let get = function
  | Some x -> x
  | None -> raise No_value
              
(* use Pervasives.incr instead
let inc_ref int_ref = 
  int_ref := ((!int_ref) + 1)
*)


(******************************)
(*  Global                    *)
(******************************)

(* Fresh incoming messages *)
let incoming = new_locking_queue ()

(* Messages to be sent *)
let outgoing = new_locking_queue ()

(* Messages to be delivered to worker process *)
let incoming_handled = new_locking_queue ()

(* messages to receive iteration of the background thread loop *)
let message_burst_size = 100

(* worker processes

   This must not be static, use a list of PIDs instead *)
(* let workers = ["BMC"; "InductiveStep"; "PDR"; "InvariantGenerator"] *)
(* let workers = ["BMC"] *)

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

let exit_flag = ref false

(******************************)
(*  message - zmg conversion  *)
(******************************)

(*        zmsg representation of a message:              *)
(* top of stack                                          *)
(* ----------------------------------------------------- *)
(*  MSG TYPE | SENDER | PAYLOAD | (PAYLOAD) | (PAYLOAD)  *)
(* ----------------------------------------------------- *)

let zmsg_of_msg msg = 

  (* Use the PID of the process as sender *)
  let sender = string_of_int (Unix.getpid ()) in

  let zmsg = zmsg_new () in 

  match msg with

    | UserMessage payload -> 

      (match payload with 

        | Log (l, s) ->

          ignore(zmsg_pushstr zmsg s);
          ignore(zmsg_pushstr zmsg (string_of_int l));
          ignore(zmsg_pushstr zmsg "LOG")

        | Stat s ->

          ignore(zmsg_pushstr zmsg s);
          ignore(zmsg_pushstr zmsg "STAT")

        | Progress k ->

          ignore(zmsg_pushstr zmsg (string_of_int k));
          ignore(zmsg_pushstr zmsg "PROGRESS")

      );

      ignore(zmsg_pushstr zmsg sender);
      ignore(zmsg_pushstr zmsg "USER");
      zmsg


    | ControlMessage payload  ->

      let rc = match payload with 
        | READY -> zmsg_pushstr zmsg "READY"
        | PING  -> zmsg_pushstr zmsg "PING"
        | TERM  -> zmsg_pushstr zmsg "TERM"
      in 

      ignore(rc);
      ignore(zmsg_pushstr zmsg sender);
      ignore(zmsg_pushstr zmsg "CONTROL");
      zmsg

    | InvariantMessage payload ->

      (match payload with 

        | INVAR (f, n)  -> 
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushbstr zmsg f (String.length f));
          ignore(zmsg_pushstr zmsg "INVAR")

        | PROP_KTRUE (p, k, n) -> 
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushstr zmsg (string_of_int k));
          ignore(zmsg_pushstr zmsg p);
          ignore(zmsg_pushstr zmsg "PROP_KTRUE")

        | PROP_INVAR (p, n) -> 
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushstr zmsg p);
          ignore(zmsg_pushstr zmsg "PROP_INVAR")

        | PROP_FALSE (p, n) -> 
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushstr zmsg p);
          ignore(zmsg_pushstr zmsg "PROP_KFALSE")

        | PROP_KFALSE (p, k, n) -> 
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushstr zmsg (string_of_int k));
          ignore(zmsg_pushstr zmsg p);
          ignore(zmsg_pushstr zmsg "PROP_KFALSE")

        | PROVED (p, k, n) -> 
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushstr zmsg (string_of_int k));
          ignore(zmsg_pushstr zmsg p);
          ignore(zmsg_pushstr zmsg "PROVED")

        | DISPROVED (p, k, n) -> 
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushstr zmsg (string_of_int k));
          ignore(zmsg_pushstr zmsg p);
          ignore(zmsg_pushstr zmsg "DISPROVED")

        | RESEND n    ->
          ignore(zmsg_pushstr zmsg (string_of_int n));
          ignore(zmsg_pushstr zmsg "RESEND")

      );

      ignore(zmsg_pushstr zmsg sender);
      ignore(zmsg_pushstr zmsg "INVARIANT");
      zmsg

    | InductionMessage payload ->

      (match payload with 

        | BMCSTATE (k, l) ->

          let zmsg_pushstr zmsg str =
            ignore(zmsg_pushstr zmsg str)
          in

          (* push contents of string list *)
          List.iter (zmsg_pushstr zmsg) l;

          (* push length of string list *)
          ignore(zmsg_pushstr zmsg (string_of_int (List.length l)));

          ignore(zmsg_pushstr zmsg (string_of_int k));
          ignore(zmsg_pushstr zmsg "BMCSTATE");

      );

      ignore(zmsg_pushstr zmsg sender);
      ignore(zmsg_pushstr zmsg "INDUCTION");
      zmsg

(*
    | CounterexampleMessage payload ->

      (match payload with

        | COUNTEREXAMPLE (n) ->
          ignore(zmsg_pushstr zmsg (string_of_int n));

      );

      ignore(zmsg_pushstr zmsg sender);
      ignore(zmsg_pushstr zmsg "COUNTEREXAMPLE");
      zmsg
*)


let string_of_msg msg = 

  let str =

    match msg with

      | UserMessage payload ->

        (match payload with 
          | Log _ -> "UserMessage(Log _)"
          | Stat _ -> "UserMessage(Stat _)"
          | Progress _ -> "UserMessage(Progress _)")
      | ControlMessage payload  ->

        (match payload with 
          | READY -> "ControlMessage(READY)"
          | PING -> "ControlMessage(PING)"
          | TERM -> "ControlMessage(TERM)")

      | InvariantMessage (INVAR (_, n)) -> 
        Format.asprintf "InvariantMessage(INVAR (_,%d))" n
          
      | InvariantMessage (PROP_KTRUE (p, k, n)) -> 
        Format.asprintf "InvariantMessage(PROP_KTRUE (%s,%d,%d))" p k n
          
      | InvariantMessage (PROP_INVAR (p, n)) -> 
        Format.asprintf "InvariantMessage(PROP_INVAR (%s,%d))" p n
          
      | InvariantMessage (PROP_FALSE (p, n)) -> 
        Format.asprintf "InvariantMessage(PROP_FALSE (%s,%d))" p n
          
      | InvariantMessage (PROP_KFALSE (p, k, n)) -> 
        Format.asprintf "InvariantMessage(PROP_KFALSE (%s,%d,%d))" p k n
          
      | InvariantMessage (DISPROVED (_, k, n)) -> 
        Format.asprintf "InvariantMessage(DISPROVED (_,%d,%d))" k n
          
      | InvariantMessage (PROVED (_, k, n)) -> 
        Format.asprintf "InvariantMessage(PROVED (_,%d,%d))" k n
          
      | InvariantMessage (RESEND n) -> 
        Format.asprintf "InvariantMessage(RESEND(%d)" n
        
      | InductionMessage payload ->

        (match payload with 
          | BMCSTATE (k, l)    ->

            let rec string_of_bmc_list l s =
              match l with 
                | f::[] -> (s ^ f)
                | f::tl -> string_of_bmc_list tl (s ^ f ^ ", ")    
                | _ -> s
            in 

            "InductionMessage(BMCSTATE(" ^ 
              (string_of_int k) ^
              ", [" ^
              (string_of_bmc_list l "") ^ 
              "]))"
        )

(*
      | CounterexampleMessage payload ->

        (match payload with
          | COUNTEREXAMPLE (n) -> 
            "CounterexampleMessage(" ^ (string_of_int n) ^ ")";
        )
*)

  in 

  str


let msg_of_zmsg zmsg =

  (* returns tuple of sender, message *)
  let msg_type = zmsg_popstr zmsg in
  
  (* Sender is the PID of the sending process *)
  let sender = 
    try int_of_string (zmsg_popstr zmsg) with Failure _ -> raise BadMessage 
  in

  match msg_type with

    | "USER" ->

      let payload = zmsg_popstr zmsg in

      (match payload with 

        | "LOG" -> 

          let l = int_of_string (zmsg_popstr zmsg) in
          let s = zmsg_popstr zmsg in
          (sender, UserMessage (Log (l, s)))

        | "STAT" -> 

          let s = zmsg_popstr zmsg in
          (sender, UserMessage (Stat s))


        | "PROGRESS" -> 

          let k = int_of_string (zmsg_popstr zmsg) in
          (sender, UserMessage (Progress k))

        | _ -> raise BadMessage)

    | "CONTROL"   ->  
      
      let payload = zmsg_popstr zmsg in

      (match payload with 
        | "READY" -> (sender, ControlMessage(READY))
        | "PING" -> (sender, ControlMessage(PING))
        | "TERM" -> (sender, ControlMessage(TERM))
        | _ -> raise BadMessage)

    | "INVARIANT" ->

      let payload = zmsg_popstr zmsg in

      (match payload with 

        | "INVAR" -> 

            (* get F and n *)
            let f = zmsg_popstr zmsg in
            let n = int_of_string (zmsg_popstr zmsg) in
            (sender, InvariantMessage (INVAR (f, n)))

        | "DISPROVED"-> 

            (* get P and n *)
            let p = zmsg_popstr zmsg in
            let k = int_of_string (zmsg_popstr zmsg) in
            let n = int_of_string (zmsg_popstr zmsg) in
            (sender, InvariantMessage (DISPROVED (p, k, n)))

        | "PROVED"-> 

            (* get P and n *)
            let p = zmsg_popstr zmsg in
            let k = int_of_string (zmsg_popstr zmsg) in
            let n = int_of_string (zmsg_popstr zmsg) in
            (sender, InvariantMessage (PROVED (p, k, n)))

        | "RESEND" ->

          let n = int_of_string (zmsg_popstr zmsg) in
          (sender, InvariantMessage(RESEND(n)))

        | _ -> raise BadMessage

      )

    | "INDUCTION" ->   

        let payload = zmsg_popstr zmsg in
        
        (match payload with 

          | "BMCSTATE"  ->  

            let k = (int_of_string (zmsg_popstr zmsg)) in
            let list_size = (int_of_string (zmsg_popstr zmsg)) in
            (* get the list of strings *)
            let rec collect_bmc_strings l i = 
              match i with 
                | 0 -> l
                | _ -> collect_bmc_strings ((zmsg_popstr zmsg)::l) (i-1)
            in
            let l = collect_bmc_strings [] list_size in
            (sender, InductionMessage(BMCSTATE(k, l)))

        | _ -> raise BadMessage)

(*
    | "COUNTEREXAMPLE" ->
      let n = int_of_string (zmsg_popstr zmsg) in
      (sender, CounterexampleMessage(COUNTEREXAMPLE(n)))
*)
    
    | _ -> raise BadMessage
             


(******************************)
(*  Thread Helpers            *)
(******************************)

let im_handle_messages workers worker_status invariant_id invariants = 
  
  let rec handle_all incoming =

    match incoming with

      | msg :: t ->  
        
        let sender, payload = msg in
        
        debug messaging
            "Invariant manager received message %a from %d"
            pp_print_message payload 
            sender
        in

        (match payload with 

          | UserMessage m -> 

            (match m with

              | Log _
              | Stat _ 
              | Progress _ -> 

                enqueue 
                  ((List.assoc sender workers), payload) 
                  incoming_handled)

          | ControlMessage m  -> 

            (match m with
              | READY -> ()
              | PING -> enqueue (ControlMessage(READY)) outgoing
              | TERM -> enqueue (ControlMessage(TERM)) outgoing)
            
          | InvariantMessage(m) -> 

            let mk_identified_msg = function 
              | INVAR(f, _) -> INVAR(f, !invariant_id)
              | PROP_KTRUE (p, k, _) -> PROP_KTRUE (p, k, !invariant_id)
              | PROP_INVAR (p, _) -> PROP_INVAR (p, !invariant_id)
              | PROP_FALSE (p, _) -> PROP_FALSE (p, !invariant_id)
              | PROP_KFALSE (p, k, _) -> PROP_KFALSE (p, k, !invariant_id)
              | PROVED (p, k, _) -> PROVED (p, k, !invariant_id)
              | DISPROVED (p, k, _) -> DISPROVED (p, k, !invariant_id)
              | RESEND _ -> invalid_arg "mk_identified_msg"
            in

            (* assign a unique identifier, add to invariants, send,
               increment identifier *)
            (match m with
              | INVAR _
              | PROP_KTRUE _
              | PROP_INVAR _
              | PROP_FALSE _
              | PROP_KFALSE _
              | PROVED _
              | DISPROVED _ as msg ->

                let identified_msg = 
                  InvariantMessage (mk_identified_msg msg)
                in

                Hashtbl.add invariants !invariant_id identified_msg;
                enqueue identified_msg outgoing;
                invariant_id := !invariant_id + 1;
                enqueue
                  ((List.assoc sender workers), payload) 
                  incoming_handled

              | RESEND (n) -> 
              
                let requested_msg = 
                  try 
                    Some(Hashtbl.find invariants n)
                  with 
                    | Not_found -> None 
                in

                if requested_msg != None then 
                  enqueue (get(requested_msg)) outgoing)

          | InductionMessage(m) -> 

            (* send as is *)
            (match m with

              | BMCSTATE (k, l) -> 

                enqueue payload outgoing;
                enqueue
                  ((List.assoc sender workers), payload) 
                  incoming_handled;

            )

(*
          | CounterexampleMessage(n) ->

            (* send as is *)
            enqueue payload outgoing;
            enqueue 
              ((List.assoc sender workers), payload) 
              incoming_handled

*)

          );

        (* update the status of the sender *)
        Hashtbl.replace worker_status sender (Unix.time ());

        handle_all t;

      | []  -> ()
  in

  let msgs = (remove_list incoming) in

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
      enqueue (InvariantMessage(RESEND(!last_received_invariant_id))) outgoing;
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
  let rec handle_all incoming =
    
    match incoming with

      | msg :: t ->  
        
        let sender, payload = msg in
        
        debug messaging
            "Worker received message %a from %d"
            pp_print_message payload 
            sender
        in
        
        (match payload with 
          
          | UserMessage m -> 
            
            (match m with
              | Log _ 
              | Stat _
              | Progress _ -> ())

          | ControlMessage m  -> 
            
            (match m with

              | READY -> ()

              | PING -> enqueue (ControlMessage(READY)) outgoing

              | TERM -> 

                enqueue
                  (`INVMAN, payload) 
                  incoming_handled)
                  
          | InvariantMessage m ->

            let mk_unidentified_msg = function
              | INVAR(f, n) -> INVAR(f, 0), n
              | PROP_KTRUE (p, k, n) -> PROP_KTRUE (p, k, 0), n
              | PROP_INVAR (p, n) -> PROP_INVAR (p, 0), n
              | PROP_FALSE (p, n) -> PROP_FALSE (p, 0), n
              | PROP_KFALSE (p, k, n) -> PROP_KFALSE (p, k, 0), n
              | PROVED (p, k, n) -> PROVED (p, k, 0), n
              | DISPROVED (p, k, n) -> DISPROVED (p, k, 0), n
              | RESEND _ -> invalid_arg "mk_identified_msg"
            in
            
            (match m with 
              | INVAR _
              | PROP_KTRUE _
              | PROP_INVAR _
              | PROP_FALSE _
              | PROP_KFALSE _
              | PROVED _
              | DISPROVED _ as msg ->

                let unidentified_msg, n = 
                  mk_unidentified_msg msg
                in

                if 

                  Hashtbl.mem 
                    unconfirmed_invariants 
                    (InvariantMessage unidentified_msg)

                then 

                  (
                    
                    Hashtbl.remove 
                      unconfirmed_invariants 
                      (InvariantMessage unidentified_msg);

                    Hashtbl.add confirmed_invariants n msg

                  ) 

                else 
                  
                  (
                  
                    if Hashtbl.mem confirmed_invariants n then () else 

                      (
                        
                        enqueue 
                          (`INVMAN, payload) 
                          incoming_handled;
                        
                        Hashtbl.add confirmed_invariants n msg;

                        if 
                          
                          n > ((!last_received_invariant_id) + 1) 
                              
                        then 
                          
                          (
                            
                            (* we've missed at least one invariant,
                               request any not received *)
                            worker_request_missing_invariants 
                              last_received_invariant_id 
                              n
                              
                          );
                        
                        last_received_invariant_id := n
                          
                      )
                      
                  )

              (* Workers do not resend messages *)
              | RESEND (n) -> ()
                              
            )
            
          (* in all other cases, enqueue to incoming_handled *)
          | InductionMessage _ ->
            (* | CounterexampleMessage _ -> *)
            
            enqueue
              (`INVMAN, payload) 
              incoming_handled
              
        );
        
        handle_all t;

      | [] -> ()
              
  in 
  
  handle_all (remove_list incoming)


let recv_messages sock as_invariant_manager = 

  (* receive up to 'message_burst_size' messages from sock *)
  let rec recv_iter i zmsg =

    if (i < message_burst_size) && (zmsg_size zmsg != 0) then 

      (
      
        if as_invariant_manager || (not !debug_mode) then 

          (

            enqueue (msg_of_zmsg zmsg) incoming

          ) 

        else 

          (

            let sender, message = (msg_of_zmsg (zmsg)) in
            ignore(sender);
            enqueue
              (`INVMAN, message) 
              incoming_handled

          );

        recv_iter (i+1) (zmsg_recv_nowait sock)
          
      )
      
  in
  
  recv_iter 0 (zmsg_recv_nowait sock)


let im_send_messages sock = 
  
  (* send up to 'message_burst_size' messages in Invariant Manager's
      outgoing message queue *)
  let rec send_iter i outgoing_msg =

    if (i < message_burst_size) && (outgoing_msg != None) then 

      (

        let message = get (outgoing_msg) in
        let zm = zmsg_of_msg message in
        let rc = zmsg_send (zm) sock in
        
        if (rc < 0) then push_front message outgoing; 
        send_iter (i+1) (dequeue outgoing)

      ) 

    else 

      ()

  in 
  
  send_iter 0 (dequeue outgoing)


let worker_send_messages proc sock unconfirmed_invariants = 

  (* send up to 'message_burst_size' messages in worker's outgoing
     message queue *)
  let rec send_iter i outgoing_msg =

    if (i < message_burst_size) && (outgoing_msg != None) then 

      (
      
        let message = get (outgoing_msg) in

        debug messaging
            "Worker %d sending message %a"
            (Unix.getpid ())
            pp_print_message message
        in

        let rc = 
          zmsg_send (zmsg_of_msg message) sock 
        in

        if (rc < 0) then push_front message outgoing else 

          (

            (* if this message is a new invariant, place it in
               unconfirmed list with current timestamp *)
            (match message with 
              | InvariantMessage(m) ->
                (match m with 
                  | INVAR (f, n) ->

                    Hashtbl.add 
                      unconfirmed_invariants 
                      (InvariantMessage (INVAR (f, 0)))
                      (Unix.time ())

                  | _ -> ()

                );

              | _ -> ()

            )
          );

        send_iter (i+1) (dequeue outgoing)

      )
  
  in 
  
  send_iter 0 (dequeue outgoing)


let worker_resend_invariants unconfirmed_invariants = 
  
  (* resend unconfirmed invariants *)
  let resend_if_needed invariant timestamp =
    
    if 

      ((Unix.time ()) -. timestamp) > worker_invariant_confirmation_threshold 

    then 

      (
      
        enqueue invariant outgoing;

        (* a missed invariant is only resent once *)
        (match invariant with

          | InvariantMessage(m) ->
            (match m with 
              | INVAR (f, n) ->
                
                Hashtbl.remove 
                  unconfirmed_invariants 
                  (InvariantMessage (INVAR (f, 0)))
                  
              | _ -> ()

            )
          
          | _ -> ()

        )

    )

  in

  Hashtbl.iter resend_if_needed unconfirmed_invariants


let wait_for_workers workers worker_status pub_sock pull_sock =
  
  (* wait for ready from all workers *)
  let rec wait_iter = function 
    
    (* No more workers to wait for *)
    | [] -> () 
            
    (* List of workers to wait for is not empty *)
    | workers_remaining -> 
      
      (
        
        debug messaging "Sending PING to workers" in
        
        (* let workers know invariant manager is ready *)
        let rc = 
          zmsg_send 
            (zmsg_of_msg 
               (ControlMessage PING)) 
            pub_sock
        in
        
        assert (rc = 0);
        
        (* Receive message on PULL socket *)
        let msg = zmsg_recv_nowait pull_sock in
        
        (* Message is empty ? *)
        if (zmsg_size msg) != 0 then 
          
          (
            
            let sender, payload = (msg_of_zmsg msg) in
            
            if payload = ControlMessage READY then 
              
              (
                
                debug messaging 
                    "Received a READY message from %d while waiting for \
                     workers" 
                    sender 
                in
                
                wait_iter (List.filter ((<>) sender) workers_remaining);
                
              )
              
            else
              
              (
                
                
                debug messaging 
                    "Received message from %d while waiting for \
                     workers: %a" 
                    sender 
                    pp_print_message payload
                in
                
                wait_iter (List.filter ((<>) sender) workers_remaining);
                
              )
              
          ) 
          
        else 
          
          (
            
            debug messaging 
                "No message received, still waiting for workers" 
            in
            
            minisleep 0.1;
            wait_iter workers_remaining
              
          )

      ) 

  in
  
  wait_iter workers;

  (* update timestamp of worker status *)
  for i = 0 to ((List.length workers) - 1) do
    Hashtbl.add (worker_status) (List.nth workers i) (Unix.time ());
  done


let im_check_workers_status workers worker_status pub_sock pull_sock = 

  (* ensure that all workers have checked in within
     worker_time_threshold seconds *)
  let rec check_status workers need_ping = 
    
    match workers with
      | h :: t ->
    
        if 

          (Unix.time () -. (Hashtbl.find worker_status h)) > 
          worker_time_threshold 

        then 

          (
            
            (* at least one worker has not communicated recently *)
            Hashtbl.replace (worker_status) h (Unix.time ());
            check_status t true

          ) 

        else 

          (
          
            check_status t need_ping

          )

      | []  -> need_ping

  in
  
  (* if a worker hasn't communicated in a while, broadcast a ping *)
  if check_status workers false then enqueue (ControlMessage(PING)) outgoing



(******************************)
(*  Threads                   *)
(******************************)

let im_thread (bg_ctx, pub_sock, pull_sock) workers on_exit =

  try

    (* List of PIDs only *)
    let worker_pids = List.map fst workers in

    (* Hashtable to store time each worker was last seen *)
    let worker_status = (Hashtbl.create (List.length worker_pids)) in

    (* wait for ready from all workers *)
    debug messaging
        "Waiting for workers (%a) to become ready"
        (pp_print_list Format.pp_print_int ",@ ") worker_pids
    in

    wait_for_workers worker_pids worker_status pub_sock pull_sock;

    (debug messaging
        "All workers are ready"
     in

     (* unique invariant identifier and invariants hash table *)
     let invariant_id = ref 1 in
     let invariants = (Hashtbl.create 1000) in 

     while (true) do

       (* check on the workers *)
       im_check_workers_status 
         worker_pids 
         worker_status 
         pub_sock 
         pull_sock;

       (* get any messages from workers *)
       recv_messages pull_sock true;

       (* relay messages *)
       im_handle_messages workers worker_status invariant_id invariants;

       (* send any messages in outgoing queue *)
       im_send_messages pub_sock;

       minisleep 0.01

     done)

  with e -> on_exit e
                

let worker_thread (bg_ctx, sub_sock, push_sock) (proc, on_exit) =

  try 

    (

      let rc = 
        zmsg_send 
          (zmsg_of_msg 
             (ControlMessage(READY))) 
          push_sock
      in

      assert (rc = 0);

      (* wait for a message from the IM before sending anything *)
      (debug messaging
          "Waiting for message from invariant manager in %d" (Unix.getpid ())
       in  

       ignore(zmsg_recv sub_sock));

      (debug messaging
          "Worker is ready to send messages"
       in

       let confirmed_invariants = (Hashtbl.create 1000) in
       let unconfirmed_invariants = (Hashtbl.create 100) in
       let last_received_invariant_id = ref 0 in

       while (true) do

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

    )

  with e -> on_exit e



(******************************)
(*  Public Interface          *)
(******************************)


let init_im () =

  (* sockets for communication with worker processes *)
  let bg_ctx = zctx_new () in
  
  (* pub socket to send updates to workers *)
  let pub_sock = zsocket_new bg_ctx ZMQ_PUB in
  let bcast_port = zsocket_bind pub_sock "tcp://127.0.0.1:*" in
  
  if bcast_port < 0 then raise SocketBindFailure else
      
    (
      
      (* pull socket to get updates from workers *)
      let pull_sock = (zsocket_new bg_ctx ZMQ_PULL) in 
      let push_port = zsocket_bind pull_sock "tcp://127.0.0.1:*" in
      
      if push_port < 0 then raise SocketBindFailure else
        
        (

          debug messaging
            "PUB socket is at tcp://127.0.0.1:%d, \
             PULL socket is at tcp://127.0.0.1:%d" 
            bcast_port 
            push_port
          in

          (* Return sockets *)
          (bg_ctx, pub_sock, pull_sock), 
          
          (* Return broadcast and push ports *)
          (Format.sprintf "tcp://127.0.0.1:%d" bcast_port,
           Format.sprintf "tcp://127.0.0.1:%d" push_port)

        )
        
    )



let init_worker proc bcast_port push_port = 

  (* sockets for communication with invariant manager *)
  let bg_ctx = zctx_new () in

  (* subscribe to updates from invariant manager *)
  let sub_sock = zsocket_new bg_ctx ZMQ_SUB in

  let rc = 
    zsocket_connect 
      sub_sock 
      bcast_port
  in
  
  if rc < 0 then raise SocketConnectFailure else
    
    (
      
      zsocket_set_subscribe sub_sock "CONTROL";
      zsocket_set_subscribe sub_sock "INVARIANT";
      zsocket_set_subscribe sub_sock "COUNTEREXAMPLE";
      
      (* subscribe to any process-specific updates *)
      (match proc with
        | `BMC 
        | `IND 
        | `PDR ->
          zsocket_set_subscribe sub_sock "INDUCTION"
        | _ -> ());
      
      (* create push socket for sending updates to the invariant manager *)
      let push_sock = zsocket_new bg_ctx ZMQ_PUSH in 
      let rc = 
        zsocket_connect 
          push_sock 
          push_port
      in
      
      if rc < 0 then raise SocketConnectFailure else 

        (

          debug messaging
            "SUB port for %a is %s, PUSH port is %s" 
            pp_print_kind_module proc
            bcast_port 
            push_port
          in

          (* Return sockets *)
          (bg_ctx, sub_sock, push_sock)

        )
                                                     
    )


let run_im (bg_ctx, pub_sock, pull_sock) workers on_exit =

  try           
    
    (
      
      let p = 
        Thread.create (im_thread (bg_ctx, pub_sock, pull_sock) workers) on_exit 
      in
      
      initialized_process := Some(`INVMAN);
      ignore(p) (* thread identifier, might come in handy *)
        
    )
    
  with 
    
    | SocketBindFailure -> raise SocketBindFailure


let run_worker (bg_ctx, sub_sock, push_sock) proc on_exit =

  try 
    
    (
      
      let p = 
        Thread.create 
          (worker_thread (bg_ctx, sub_sock, push_sock)) 
          (proc, on_exit) 
      in
      
      initialized_process := Some(proc);
      p (* thread identifier, might come in handy *)
        
    )
    
  with 
    (* | Terminate -> raise Terminate *)
    | SocketConnectFailure -> raise SocketConnectFailure
      

let send msg = 

  if !initialized_process = None then raise NotInitialized else
    enqueue msg outgoing


let recv () = 

  if !initialized_process = None then raise NotInitialized else
    List.rev (remove_list incoming_handled)


let exit t = 
  exit_flag := true; 
  Thread.join t

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
