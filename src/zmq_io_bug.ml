
(* open Lib *)

open ZMQ
open Printf


exception SocketBindFailure


let bg_ctx = zctx_new ();;

(* pub socket, for IM to send updates to workers *)
let pub_sock = zsocket_new bg_ctx ZMQ_PUB;;
let pull_sock = (zsocket_new bg_ctx ZMQ_PULL);;


let thread _ =
  print_endline "thread iteration";
  print_endline (string_of_int (zstr_send pub_sock "hi"));
  (*ignore(zstr_recv_nowait pull_sock);*)
  print_endline "done with iteration";
;;



let init =
  (try           
     (

      (* bind pub socket *)
      let rc = zsocket_bind pub_sock "tcp://*:5556" in
      (*let rc = zsocket_bind pull_sock "inproc://example" in*)
      (*let rc = zsocket_bind pull_sock "epgm://en0;127.0.0.1:5555" in*)
      (*let rc = zsocket_bind pull_sock "ipc://exampleipc" in*)
      
      if (rc < 0) then ( raise SocketBindFailure );
      
      
      Sys.set_signal 
       Sys.sigalrm
       (Sys.Signal_handle thread);

      ignore
       (Unix.setitimer
          Unix.ITIMER_REAL
          { Unix.it_interval = 0.00 ; Unix.it_value = 0.01 });

     )
   with 
     | SocketBindFailure -> raise SocketBindFailure) 
;;
