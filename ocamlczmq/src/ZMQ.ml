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

(************************)
(* OCaml CZMQ bindings *)
(************************)

(************************)
(* zctx                 *)
(************************)

type zctx

(* Create new context, returns context object *)
external zctx_new : unit -> zctx = "caml_zctx_new"

(* Raise default I/O threads from 1, for crazy heavy applications *)
external zctx_set_iothreads : zctx -> int -> unit = "caml_zctx_set_iothreads"

(*  Set msecs to flush sockets when closing them *)
external zctx_set_linger : zctx -> int -> unit = "caml_zctx_set_linger"

(*  Set HWM value *)
external zctx_set_hwm : zctx -> int -> unit = "caml_zctx_set_hwm"

(* Get HWM value *)
external zctx_hwm : zctx -> int = "caml_zctx_hwm"


(************************)
(* zsocket              *)
(************************)

(* zeromq socket type *)
type zsocket

type zsocket_type  =
	| ZMQ_PAIR   (*  0 *)
	| ZMQ_PUB    (*  1 *)
	| ZMQ_SUB    (*  2 *)
	| ZMQ_REQ    (*  3 *)
	| ZMQ_REP    (*  4 *)
	| ZMQ_DEALER (*  5 *)
	| ZMQ_ROUTER (*  6 *)
	| ZMQ_PULL   (*  7 *)
	| ZMQ_PUSH   (*  8 *)
	| ZMQ_XPUB   (*  9 *)
	| ZMQ_XSUB   (* 10 *)

(* Create a new socket within our CZMQ context *)
external zsocket_new : zctx -> zsocket_type -> zsocket = "caml_zsocket_new"

(* Connect socket to address *)
external zsocket_bind : zsocket -> string -> int = "caml_zsocket_bind"

(* Connect a socket to a formatted endpoint.
    Returns 0 if OK, -1 if the endpoint was invalid *)
external zsocket_connect : zsocket -> string -> int = "caml_zsocket_connect"

(************************)
(* zsocketopt           *)
(************************)

(* Subscribe SUB socket *)
external zsocket_set_subscribe : zsocket -> string -> unit = "caml_zsocket_set_subscribe"
(* Unsubscribe SUB socket *)
external zsocket_set_unsubscribe : zsocket -> string -> unit = "caml_zsocket_set_unsubscribe"


(************************)
(* zstr                 *)
(************************)

(* Receive a string off a socket *)
external zstr_recv : zsocket -> string = "caml_zstr_recv"

(* Receive a string off a socket if socket had input waiting *)
external zstr_recv_nowait : zsocket -> string = "caml_zstr_recv_nowait"

(* Send a string to a socket in 0MQ string format *)
external zstr_send : zsocket -> string -> int = "caml_zstr_send"

(*  Send a string to a socket in 0MQ string format, with MORE flag *)
external zstr_sendm : zsocket -> string -> int = "caml_zstr_sendm"

(************************)
(* zframe               *)
(************************)

(* zeromq zframe type *)
type zframe

(* Create a new frame with optional size, and optional data *)
(* Might be nice to not require passing size from the ocaml side *)
external zframe_new : string -> int -> zframe = "caml_zframe_new"

(* Get a byte array of the data in the frame *)
external zframe_getbytes : zframe -> char array = "caml_zframe_getbytes"

(*  Receive frame from socket. Does a blocking recv *)
external zframe_recv : zsocket -> zframe = "caml_zframe_recv"

(*  Send a frame to a socket, destroy frame after sending. Returns
	non-zero error code on failure *)
external zframe_send : zframe -> zsocket -> int -> int = "caml_zframe_send"

(*  Return number of bytes in frame data *)
external zframe_size : zframe -> int = "caml_zframe_size"

(*  Create a new frame that duplicates an existing frame *)
external zframe_dup : zframe -> zframe = "caml_zframe_dup"

(*  Return frame data encoded as printable hex string *)
external zframe_strhex : zframe -> string = "caml_zframe_strhex"

(*  Return frame data copied into freshly allocated string.
  Binary strings are supported. *)
external zframe_strdup : zframe -> string = "caml_zframe_strdup"

(*  Return true if frame body is equal to string, excluding terminator *)
external zframe_streq : zframe -> string -> bool = "caml_zframe_streq"

(*  Return frame 'more' property *)
external zframe_more : zframe -> int = "caml_zframe_more"

(*  Return true if two frames have identical size and data *)
external zframe_eq : zframe -> zframe -> bool = "caml_zframe_eq"

(*  Print contents of frame to stderr *)
external zframe_print : zframe -> string -> unit = "caml_zframe_print"

(*  Set new contents for frame *)
external zframe_reset : zframe -> string -> int -> unit = "caml_zframe_reset"


(************************)
(* zmsg                 *)
(************************)

(* zeromq zmsg type *)
type zmsg

(* Create a new empty message object *)
external zmsg_new : unit -> zmsg = "caml_zmsg_new"

(* Read 1 or more frames off the socket, into a new message object *)
external zmsg_recv : zsocket -> zmsg = "caml_zmsg_recv"

(* Read 0 or more frames off the socket, into a new message object *)
external zmsg_recv_nowait : zsocket -> zmsg = "caml_zmsg_recv_nowait"

(* Send a message to the socket, and then destroy it *)
external zmsg_send : zmsg -> zsocket -> int = "caml_zmsg_send"

(* Return number of frames in message *)
external zmsg_size : zmsg -> int = "caml_zmsg_size"

(* Return combined size of all frames in message *)
external zmsg_content_size : zmsg -> int = "caml_zmsg_content_size"

(* Push frame to front of message, before first frame *)
external zmsg_push : zmsg -> zframe -> int = "caml_zmsg_push"

(* Pop frame off front of message *)
external zmsg_pop : zmsg -> zframe = "caml_zmsg_pop"

(* Add frame to end of message, after last frame *)
external zmsg_add : zmsg -> zframe -> int = "caml_zmsg_add"

(** Push string as new frame to front of message. Binary strings are supported.
  Returns 0 on success, -1 on error *)
external zmsg_pushstr : zmsg -> string -> int = "caml_zmsg_pushstr"

(** Push string as new frame to front of message. Binary strings are supported.
  Returns 0 on success, -1 on error. This duplicates zmsg_pushstr and can be deleted.*)
external zmsg_pushbstr : zmsg -> string -> int -> int = "caml_zmsg_pushbstr"

(* Push string as new frame to end of message.
	Returns 0 on success, -1 on error *)
external zmsg_addstr : zmsg -> string -> int = "caml_zmsg_addstr"

(* Pop frame off front of message, return as fresh string *)
external zmsg_popstr : zmsg -> string = "caml_zmsg_popstr"

(* Push frame to front of message, before first frame.
	Pushes an empty frame in front of frame *)
external zmsg_wrap : zmsg -> zframe -> unit = "caml_zmsg_wrap"

(* Pop frame off front of message *)
external zmsg_unwrap : zmsg -> zframe = "caml_zmsg_unwrap"

(* Remove frame from message, at any position *)
external zmsg_remove : zmsg -> zframe -> unit = "caml_zmsg_remove"

(* Create copy of message, as new message object *)
external zmsg_dup : zmsg -> zmsg = "caml_zmsg_dup"

(* Print message to stderr, for debugging *)
external zmsg_dump : zmsg -> unit = "caml_zmsg_dump"

(************************)
(* Tests                *)
(************************)

exception SocketBindFailure
exception SocketConnectFailure
exception No_value

(* Selftest of ZMQ module *)
let selftest () =
  (* create sockets and contexts *)
  let ctx = zctx_new() in
  (* PUB, SUB *)
  let pub_sock = zsocket_new ctx ZMQ_PUB in
  let rc = zsocket_bind pub_sock "tcp://*:5556" in
  if rc < 0 then raise SocketBindFailure else
  let sub_sock = (zsocket_new ctx ZMQ_SUB) in 
  let rc = zsocket_connect sub_sock "tcp://localhost:5556" in
  if rc < 0 then raise SocketConnectFailure else
  zsocket_set_subscribe sub_sock "TEST";
  (* PUSH, PULL *)
  let push_sock = zsocket_new ctx ZMQ_PUSH in
  let rc = zsocket_connect push_sock "tcp://localhost:5557" in
  if rc < 0 then raise SocketConnectFailure else
  let pull_sock = (zsocket_new ctx ZMQ_PULL) in 
  let rc = zsocket_bind pull_sock "tcp://*:5557" in
  if rc < 0 then raise SocketBindFailure else
  print_endline "Sockets connected";
  
  let sent = ref 0 in
  let recvd = ref 0 in 
  let rec recv sock msgs = 
    let m = zmsg_recv_nowait sock in
    if ((zmsg_size m) = 0) then
      msgs
    else 
      m :: recv sock msgs
  in
  let rec handle_pull msgs =
    (match msgs with 
      []   -> ()
    | h::t -> ignore(zmsg_send h pub_sock); handle_pull t)
    (*print_endline ((string_of_int rc ) ^ " Message sent over push");*)
  in
  let rec handle_sub msgs recvd = 
    (match msgs with 
      []   -> ()
    | h::t -> 
          recvd := ((!recvd) + 1);
          handle_sub t recvd;)
  in
  for i = 0 to 1000 do 
    (* send new message over push socket *)
    let z = zmsg_new () in
    ignore(zmsg_pushstr z "TEST");
    ignore(zmsg_send z push_sock); 
    sent := !sent + 1;
    (* recv on pull *)
    let msgs = recv pull_sock [] in
    (*print_endline ("pull received " ^ (string_of_int (List.length msgs)) ^ " messages");*)
    handle_pull msgs;
    (* recv on sub *)
    let msgs = recv sub_sock [] in
    handle_sub msgs recvd;
  done;
  (* clean up *)
  print_endline "Cleaning up";
  let ctx = 0 in ignore(ctx);
  let pub_sock = 0 in ignore(pub_sock);
  let sub_sock = 0 in ignore(sub_sock);
  let push_sock = 0 in ignore(push_sock);
  let pull_sock = 0 in ignore(pull_sock);
  Gc.full_major ();
  print_endline "Done";
  print_endline "Results:";
  print_endline ("\t" ^ (string_of_int !sent) ^ " messages sent; " ^ (string_of_int !recvd) ^ " received.");
;;