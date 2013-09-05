
let handle_sigalrm _ = 

  (* ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigalrm]); *)

  Format.printf "Signal handler starting@.";
  Unix.sleep 1;
  Format.printf "Signal handler terminating@."

  (* ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [Sys.sigalrm]) *)

let main () =

  (*
  Sys.set_signal 
    Sys.sigalrm
    (Sys.Signal_handle handle_sigalrm);
*)
  
  Sys.set_signal 
    Sys.sigint
    (Sys.Signal_handle handle_sigalrm);
(*
  ignore
    (Unix.setitimer
       Unix.ITIMER_REAL
       { Unix.it_interval = 1.5 ; Unix.it_value = 1.5 });
  *)

  while true do

    ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigalrm]);
    
    (* Read, no signals here *)
    Format.printf "Main critical section starting@.";
    Unix.sleep 1;
    Format.printf "Main critical section ending@.";

    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [Sys.sigalrm]);

  done;

  Format.printf "Exit@.";
    
;;

main ()
