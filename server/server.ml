(* 
  can test in toplevel with "ocaml -I +threads unix.cma ZMQ.cma"
  and then just #use "server.ml". (need to uncomment the load for threads.cma)

  to compile (from directory containing ZMQ module/libraries):
    ocamlopt.opt /usr/local/lib/ocaml/unix.cmxa ZMQ.cmxa -ccopt -L. server.ml server.mli -o kind2server
*)

(*#load "threads.cma"*)
open ZMQ

exception Checksum_failure

(* ********************************************************************** *)
(* Defaults                                                               *)
(* ********************************************************************** *)

let helpmessage = "usage: kind2_server -[p] [port]"

(* Default port for the server *)
let default_port = 5558

(* command to invoke kind *)
let kind_command = "/usr/local/bin/pkind";;
let kind_default_args = ["-xml"; "-xml-to-stdout"]


(* ********************************************************************** *)
(* Helper functions                                                       *)
(* ********************************************************************** *)

(* Get base l string representation of integer n *)
let base10tol n =

  (* Characters to use *)
  let digits = 
    [|
      '0';'1';'2';'3';'4';'5';'6';'7';'8';'9';
      'A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';
      'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';
(*      'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';
        'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z' *)
    |] 
  in

  (* l is number of characters *)
  let base = Array.length digits in

  (* Convert to base l *)
  let rec base_iter acc = function
    | 0 -> acc
    | n ->
      base_iter 
        ((String.make 1 (Array.get digits (n mod base))) ^ acc)
        (n / base) 
  in  

  (* Conver n to a base l string *)
  base_iter "" n

(* Generate unique identifier from current Unix time *)
let generate_uid () = 

  (* use current unix time to the 100th of a second, in GMT, hash to
     make it look random *)
  base10tol (Hashtbl.hash (int_of_float (Unix.gettimeofday () *. 100.)))


(* Sleep for sec seconds *)
let minisleep sec =
  ignore (Unix.select [] [] [] sec)


(* Pretty-print into a string *)
let string_of_t pp t = 

  (* Create a buffer *)
  let buf = Buffer.create 80 in
  
  (* Create a formatter printing into the buffer *)
  let ppf = Format.formatter_of_buffer buf in

  (* Output into buffer *)
  pp ppf t;
  
  (* Flush the formatter *)
  Format.pp_print_flush ppf ();
  
  (* Return the buffer contents *)
  Buffer.contents buf


(* Pretty-print a list *)
let rec pp_print_list pp sep ppf = function 

  (* Output nothing for the empty list *) 
  | [] -> ()

  (* Output a single element in the list  *) 
  | e :: [] -> 
    pp ppf e

  (* Output a single element and a space *) 
  | e :: tl -> 

    (* Output one element *)
    pp_print_list pp sep ppf [e]; 

    (* Output separator *)
    Format.fprintf ppf sep; 

    (* Output the rest of the list *)
    pp_print_list pp sep ppf tl


(* Output a time *)
let pp_print_time ppf time = 

  (* Month names *)
  let months = [ "Jan"; "Feb"; "Mar"; "Apr"; "May"; "Jun"; 
                 "Jul"; "Aug"; "Sep"; "Oct"; "Nov"; "Dec" ] 
  in

  (* Split local time into components *)
  let 
    { Unix.tm_sec = tm_sec; 
      Unix.tm_min = tm_min;
      Unix.tm_hour = tm_hour;
      Unix.tm_mday = tm_mday;
      Unix.tm_mon = tm_mon;
      Unix.tm_year = tm_year;
      Unix.tm_wday = tm_wday;
      Unix.tm_yday = tm_yday }  =
    
    time

  in
  
  (* Output as "[Jan 01 00:00:00]" *)
  Format.fprintf 
    ppf
    "%s %02d %02d:%02d:%02d" 
    (List.nth months tm_mon)
    tm_mday
    tm_hour
    tm_min
    tm_sec


(* String representation of time *)
let string_of_time = string_of_t pp_print_time 


(* Output a timestamp *)
let pp_print_timestamp ppf = 
  pp_print_time ppf (Unix.localtime (Unix.time ()))


(* Output with timestamp *)
let log fmt = 
  Format.printf ("[%t] " ^^ fmt ^^ "@.") pp_print_timestamp


(* ********************************************************************** *)
(* State of the server                                                    *)
(* ********************************************************************** *)

(* on which port does the server run? *)
let port = 
  match (Array.length Sys.argv) with 
  | 1 -> default_port
  | 3 -> 
    if ((Array.get Sys.argv 1) = "-P" || (Array.get Sys.argv 1 = "-p")) then (
      (try (
        (int_of_string (Array.get Sys.argv 2));
      ) with _ ->  
        print_endline "bad port number";
        exit 1
      );
    ) else (
      print_endline helpmessage;
      exit 1
    )
  | _ -> print_endline helpmessage;
         exit 1


(* print_endline ("launching Kind 2 server on port " ^ (string_of_int port)) *)

(* running_jobs: a Hashtbl of ID -> ( pid * stdin_file * stdout_file *
   stderr_file ) *)

let running_jobs = (Hashtbl.create 50)

(* completed_jobs: a Hashtbl of ID -> completion_time *)
let completed_jobs = (Hashtbl.create 50)

(* how long (in seconds) should a job remain before being purged? *)
let job_lifespan = 2629740 (* about one month *)


(* Location of temporary directory *)
let tmpdir = Format.sprintf "/tmp/kind2-%s" (generate_uid ())

(* Name of log file *)
let logfile = Format.sprintf "%s.log" tmpdir



let write_bytes_to_file data filename = 

  (* write contents of byte array 'data' to a file with name 'filename' *)
  let oc = open_out_bin filename in

  for i = 0 to ((Array.length data) - 1) do

    (* not using output_string for now, need to test results with binary data *)
    output_char oc (Array.get data i);

  done;

  close_out oc


let read_bytes filename =
  let ic = open_in_bin (Filename.concat tmpdir filename) in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  s


(* create new kind job using flags 'server_flags',
    and the content of 'payload'. send results over 'sock' *)
let create_job sock server_flags payload checksum kind_args =
  
  (* Generate a unique job ID *)
  let job_id = generate_uid () in 

  (* Create temporary files for input, output and error output *)
  let stdin_fn = ("kind_job_" ^ job_id ^ "_input") in
  let stdout_fn = ("kind_job_" ^ job_id ^ "_output") in

  (* Write data from client to stdin of new kind process *)
  write_bytes_to_file (zframe_getbytes payload) stdin_fn;

  (* Open file for input *)
  let kind_stdin_in = 
    Unix.openfile stdin_fn [Unix.O_CREAT; Unix.O_RDONLY; Unix.O_NONBLOCK] 0o600 
  in

  (* Open file for output *)
  let kind_stdout_out = 
    Unix.openfile stdout_fn [Unix.O_CREAT; Unix.O_RDWR; Unix.O_NONBLOCK] 0o600 
  in
  
  (* Temporary file for stderr *)
  let stderr_fn, kind_stderr_out = 

    (* Should stdout and stderr be seperated? *)
    if String.contains server_flags 's' then 
      
      (

        (* Separate file for stderr *)
        ("kind_job_" ^ job_id ^ "_error"),
        
        (* Open file *)
        Unix.openfile 
          ("kind_job_" ^ job_id ^ "_error") 
          [Unix.O_CREAT; Unix.O_RDWR; Unix.O_NONBLOCK] 0o600
      ) 

    else 

      (

        (* By default merge stdout and stderr *)
        stdout_fn, kind_stdout_out

      )

  in

  (* Get string of input *)
  let input_string = zframe_strdup payload in

  (* Compute checksum of input *)
  let input_digest = Digest.string input_string in

  (* Checksums differ? *)
  if (input_digest <> checksum) then 

    (
      
      log 
        "Received file with bad MD5sum. Expected MD5sum %s, got %s."
        checksum
        input_digest;

      raise Checksum_failure
        
    );
  
  log 
    "Executing %s %a"
    kind_command
    (pp_print_list Format.pp_print_string " ") kind_args;

  (* Create kind process *)
  let kind_pid = 
    Unix.create_process 
      kind_command
      (Array.of_list (kind_command :: kind_args @ [stdin_fn])) 
      kind_stdin_in
      kind_stdout_out
      kind_stderr_out
  in
  
  (* Close our end of the pipe which has been duplicated by the
     process *)
  if (not (kind_stderr_out == kind_stdout_out)) then 
    (Unix.close kind_stderr_out); 
  
  Unix.close kind_stdin_in;
  Unix.close kind_stdout_out; 
  
  (* Add job to Hashtbl of running jobs and associated files *)
  Hashtbl.add 
    running_jobs job_id 
    (kind_pid, (int_of_float (Unix.time ())), stdin_fn, stdout_fn, stderr_fn);

  (* Send job ID to client *)
  let msg = zmsg_new () in
  ignore(zmsg_pushstr msg job_id);
  ignore(zmsg_send msg sock);
  
  log "Job created with ID %s" job_id;

  (* guarantee that next generated ID is unique *)
  minisleep 0.01


(* Retrieve job *)
let retrieve_job sock server_flags job_id = 

  (* Local log function *)
  let log fmt = 
    log 
      ("Request retrieval of job %s: " ^^ fmt)
      job_id 
  in

  (* New message as reply *)
  let status = zmsg_new () in

  (* String message to client *)
  let output_string = 

    try 

      (

        (* Find job in table of running jobs *)
        let job_pid, timestamp, stdin_fn, stdout_fn, stderr_fn = 
          Hashtbl.find running_jobs job_id 
        in

        (* Check status of job by its PID *)
        let status_pid, job_status = Unix.waitpid [Unix.WNOHANG] job_pid in 

        (* Job has not exited yet? *)
        if job_pid = 0 then 

          (                        

            log "running as PID %d" status_pid;

            (* Message to client *)
            Format.sprintf 
              "<Jobstatus msg=\"inprogress\">\
               Job with ID %s is in progress.\
               </Jobstatus>"
              job_id

          ) 

        else

          (

            let output_string =

              (* Job has terminated *)
              match job_status with

              (* Terminated with signal *)
              | Unix.WSIGNALED signal -> 

                log "killed by signal %d" signal;

                (* Read from stderr *)
                let errors = read_bytes stderr_fn in

                (* Create message to client *)
                Format.sprintf 
                  "<Jobstatus msg=\"aborted\">\
                   Job with ID %s aborted before completion.\
                   Contents of stderr:@\n\
                   %s
                    </Jobstatus>"
                  job_id
                  errors

              (* Stopped by signal *)
              | Unix.WSTOPPED signal -> 

                log "stopped by signal %d" signal;

                (* Read from stderr *)
                let errors = read_bytes stderr_fn in

                (* Create message to client *)
                Format.sprintf 
                  "<Jobstatus msg=\"aborted\">\
                   Job with ID %s aborted before completion.\
                   Contents of stderr:@\n\
                   %s
                    </Jobstatus>"
                  job_id
                  errors

              (* Exited with code *)
              | Unix.WEXITED code ->

                log "exited with code %d" code;

                (* Message to client is from stdout *)
                read_bytes stdout_fn

            in
            
            (* Remove job from table of working jobs *)
            Hashtbl.remove running_jobs job_id;
            
            (* Add to table of completed jobs *)
            Hashtbl.add completed_jobs job_id (Unix.gmtime (Unix.time ()));
            
            (* Delete temp files for process *)
            (try (Sys.remove stdin_fn) with _ -> ());
            (try (Sys.remove stdout_fn) with _ -> ());
            (try (Sys.remove stderr_fn) with _ -> ());

            output_string

          )

      )

    (* Job not found in table of running jobs *)
    with Not_found -> 

      try 

        (

          (* Get time of retrieval *)
          let job_tm = Hashtbl.find completed_jobs job_id in

          log "completed at %a UTC" pp_print_time job_tm;

          Format.sprintf 
            "<Jobstatus msg=\"completed\">\
             Job with ID %s has completed and was retrieved at %s UTC\
             </Jobstatus>"
            job_id
            (string_of_time job_tm)

        ) 

      with Not_found ->

        log "not found";

        Format.sprintf
          "<Jobstatus msg=\"notfound\">\
           Job with ID %s not found.\
           </Jobstatus>"
          job_id

  in

  (* Compute checksum of results *)
  let output_digest = Digest.string output_string in
  
  (* Message frame for output *)
  let output_frame = 
    zframe_new output_string (String.length output_string) 
  in
  
  (* Message frame for digest *)
  let checksum_frame = 
    zframe_new output_digest (String.length output_digest) 
  in
  
  (* Compose message of frames and send *)
  ignore(zmsg_push status checksum_frame);
  ignore(zmsg_push status output_frame);
  ignore(zmsg_send status sock)
    

let purge_jobs () =
  print_endline "purging any old jobs";
  let purge_if_old job_id details = 
    let pid, timestamp, stdin_fn, stdout_fn, stderr_fn = details in
    if ( ((int_of_float (Unix.time ())) - timestamp) > job_lifespan ) then 

      (
        (* job is old *)
        print_endline ("purging old job " ^ job_id);
        (* remove job from table of working jobs *)
        Hashtbl.remove running_jobs job_id;
        (* delete job's temp files *)
        (try (Sys.remove stdin_fn) with _ -> ());
        (try (Sys.remove stdout_fn) with _ -> ());
        (try (Sys.remove stderr_fn) with _ -> ());
      );

  in

  Hashtbl.iter purge_if_old running_jobs


(*
let collect_args msg =

  (* Collect remaining string from msg into a string array *)
  let rec iter argument argv =
    match argument with
      | "" -> argv;
      | _  -> iter (zmsg_popstr msg) (Array.append [|argument|] argv);
  in

  iter (zmsg_popstr msg) [| |]
*)

(* Collect arguments from message frames *)
let rec collect_args msg accum = 

  match zmsg_popstr msg with 

    (* No more arguments: reverse list and append defaults *)
    | "" -> accum

    (* Append argument to list and continue *)
    | arg -> collect_args msg (arg :: accum)



(* Main loop: get requests from socket *)
let rec get_requests sock last_purge =

  (* Catch all errors *)
  try 

    (* Message received *)
    let msg = 

      (* Wait for next message, restart when interrupted *)
      try zmsg_recv sock with 
        | Failure "break" -> get_requests sock last_purge 

    in

    (

      (* First frame contains flags *)
      match zmsg_popstr msg with

        (* Retrieve job *)
        | s when String.contains s 'r' ->

          (* Second part contains job ID *)
          let payload = zmsg_pop msg in

          (* Retrieve job *)
          retrieve_job sock s (zframe_strdup payload)

        (* Creating job? *)
        | s when String.contains s 'c' ->

          (

            (* Second part contains file *)
            let payload = zmsg_pop msg in
            
            (* Third part contains checksum for file *)
            let checksum  = zmsg_popstr msg in
            
            (* Collect arguments from remaining frames *)
            let kind_args = kind_default_args @ (collect_args msg []) in 
            
            try 
              
              create_job sock s payload checksum kind_args;
              
            with Checksum_failure -> 
              
              let error_msg = zmsg_new () in
              ignore(zmsg_pushstr error_msg "checksum match failure.");
              ignore(zmsg_send error_msg sock);
              
          )
          
        | s -> 
          
          log "Bad flags %s in message. Ignoring." s
            
    );

    let last_purge' =

      (* time to purge old jobs, once a day (864000 seconds) *)
      if (((int_of_float (Unix.time ())) - last_purge) > 864000) then 
        
        (
        
          (* Purge old jobs *)
          purge_jobs ();

          (* Old jobs have been purged right now *)
          (int_of_float (Unix.time ()))
          
        )

      else

        (* No purging of jobs yet *)
        last_purge
      
    in

    (* Continue with next message *)
    get_requests sock last_purge'

  (* Catch runtime errors *)
  with e ->

    log 
      "Server caught runtime error %s. Aborting."
      (Printexc.to_string e);
    
    (* Delete all files in temporary directory *)
    let files = Sys.readdir tmpdir in
    Array.iter (Sys.remove) files;
    
    (* Leave temporary directory *)
    Sys.chdir "/";

    (* Delete temporary directory *)
    Unix.rmdir tmpdir;

    (* Exit *)
    exit 0


(* Entry point *)
let main () = 

  (* Double fork to start server as daemon *)
  (match Unix.fork () with 

    | 0 -> 
      
      (* The son exits, the grandson continues *)
      (if Unix.fork() <> 0 then exit 0) 
      
    | pid -> 
  
      (* Reclaim the son *)
      ignore (Unix.waitpid [] pid); exit 0

  );

  (* We are running as a daemon from now on. *)
 
  (* Redirect /dev/null to stdin *)
  let fd = Unix.openfile "/dev/null" [Unix.O_RDONLY] 0 in
  Unix.dup2 fd Unix.stdin;
  Unix.close fd;

  (* Redirect stdout to logfile *)
  let fd = Unix.openfile logfile [Unix.O_CREAT; Unix.O_WRONLY] 0o666 in
  Unix.dup2 fd Unix.stdout;
  Unix.close fd;

  (* Redirect stderr to /dev/null *)
  let fd = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
  Unix.dup2 fd Unix.stderr;
  Unix.close fd;

  log "Server started";

  (* ZeroMQ context *)
  let ctx = zctx_new () in

  (* ZeroMQ reply socket  *)
  let rep_sock = (zsocket_new ctx ZMQ_REP) in

  (* Bind socket to port *)
  let rc = zsocket_bind rep_sock ("tcp://*:" ^ (string_of_int port)) in
  
  (* Successfully bound to port? *)
  if rc < 0 then 

    (
      
      log "Could not bind to port %d. Aborting." port;

      exit 1
      
    );

  log "Server listening on port %d" port;
  
  (try 
     
     (
       
       (* Initialize temporary directory *)
       Unix.mkdir tmpdir 0o700; 
       Sys.chdir tmpdir
         
     ) 
     
   with _ ->
     
     log
       "Could not create temporary directory %s. Aborting."
       tmpdir;
     
     exit 1
       
  );

  (* Enter main loop, last purge of old files was right now *)
  get_requests rep_sock (int_of_float (Unix.time ()));
  
  exit 0
    
;;

main ()
