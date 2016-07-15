(* System signal caught *)
exception Signal of int


(* Raise exception on signal *)
let exception_on_signal signal = raise (Signal signal)


(* Dummy thread that is blocking all signals *)
let dummy_thread () = 

  Format.printf "Dummy thread is #%d@." (Thread.id (Thread.self ())); 

  (* Sleep forever *)
  while true do 

      try 

        Thread.yield () 

      with Signal int -> 

        (Format.printf "Sending signal %d from dummy thread@." int; 

         Unix.kill (Unix.getpid ()) int)
        
  done


(* Entry point *)
let main () = 

  (* Install generic signal handler for SIGINT *)
  Sys.set_signal 
    Sys.sigint 
    (Sys.Signal_handle exception_on_signal);

  (* Install generic signal handler for SIGTERM *)
  Sys.set_signal 
    Sys.sigterm 
    (Sys.Signal_handle exception_on_signal);

  (* Install generic signal handler for SIGQUIT *)
  Sys.set_signal 
    Sys.sigquit 
    (Sys.Signal_handle exception_on_signal);

  (* Fork a child process *)
  match Unix.fork () with 

    (* We are the child process *)
    | 0 -> 

      (

        (* Block signals, they are to be handled by the other thread *)
        let _ = 
          Thread.sigmask 
            Unix.SIG_BLOCK
            [Sys.sigint; Sys.sigterm; Sys.sigquit; Sys.sigalrm]
        in
  
        (* Run dummy thread that is not supposed to get any signals *)
        let _ = Thread.create dummy_thread () in 

        Format.printf "Main thread is #%d@." (Thread.id (Thread.self ())); 

        let child_pid = 
          Unix.create_process 
            "/bin/sleep" 
            [| "sleep"; "300" |] 
            Unix.stdin 
            Unix.stdout
            Unix.stderr
        in

        (* Block signals, they are to be handled by the other thread *)
        let _ = 
          Thread.sigmask 
            Unix.SIG_UNBLOCK
            [Sys.sigint; Sys.sigterm; Sys.sigquit; Sys.sigalrm]
        in
  
        try 

          (* Sleep forever *)
          while true do Thread.yield () done

        with Signal s -> 
          (Format.printf "Signal %d caught@." s; 
           Unix.kill child_pid Sys.sigterm;
           let _ = Unix.wait () in
           exit 0)

      )

    (* We are the parent process *)
    | pid -> 

      (

        Format.printf "Child has PID %d@." pid;

        Unix.sleep 1;

        Unix.kill pid Sys.sigterm;

        let _ = Unix.wait () in ()

      )

;;


main ()
