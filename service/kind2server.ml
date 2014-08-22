(*
can test in toplevel with "ocaml -I +threads unix.cma ZMQ.cma"
and then just #use "server.ml". (need to uncomment the load for threads.cma)

to compile (from directory containing ZMQ module/libraries):
ocamlopt.opt /usr/local/lib/ocaml/unix.cmxa ZMQ.cmxa -ccopt -L. server.ml server.mli -o kind2server
*)

(*#load "threads.cma"*)



type running_job_info =

    {

      (* PID of process *)
      job_pid : int;

      (* Timestamp of job start *)
      job_start_timestamp : int;

      (* Name of file to be fed to standard input *)
      job_stdin_fn : string;

      (* Name of file to write standard output to *)
      job_stdout_fn : string;

      (* Name of file to write standard error to *)
      job_stderr_fn : string;

      (* Last read position in stardard output file *)
      mutable job_stdout_pos : int
      
    }



let asprintf fmt =
  let b = Buffer.create 512 in
  let k ppf =
    Format.pp_print_flush ppf ();
    Buffer.contents b
  in
  let ppf = Format.formatter_of_buffer b in
  Format.kfprintf k ppf fmt


(* Pretty-print a list *)
let rec pp_print_list pp sep ppf = function

  (* Output nothing for the empty list *)
  | [] -> ()

  (* Output a single element in the list *)
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


(* ********************************************************************** *)
(* Defaults *)
(* ********************************************************************** *)

(* Maximum one minute load average *)
let load1_max = ref 8.

(* Maximum five minutes load average *)
let load5_max = ref 4.

(* Maximum 15 minutes load average *)
let load15_max = ref 0.



(* ********************************************************************** *)
(* Helper functions *)
(* ********************************************************************** *)

(* Get base l string representation of integer n *)
let base10tol n =

  (* Characters to use *)
  let digits =
    [|
      '0';'1';'2';'3';'4';'5';'6';'7';'8';'9';
      'A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';
      'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';
(* 'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';
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

  (* Output a single element in the list *)
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
      Unix.tm_yday = tm_yday } =
    
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

 
(* Association list of job ID to PID and timestamp of cancel request *)
let cancel_requested_jobs = ref []

(* Time in seconds after cancel request after which SIGKILL is sent

Must be greater than sigterm_time *)
let cancel_sigkill_time = 5.

(* Time in seconds after cancel request after which SIGTERM is sent

Must be less than sigkill_time *)
let cancel_sigterm_time = 2.
    
(* how long (in seconds) should a job remain before being purged? *)
let job_lifespan = 2629740 (* about one month *)



(* helper function for read a file and returns a string list*)
let read_file filename = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; []
  with End_of_file ->
    close_in chan;
    List.rev !lines


let write_file file1 file2 =

  let oc = open_out file2 in
  let txtline = read_file file1 in
  for i = 0 to ((List.length txtline) - 1) do    
    output_string oc (List.nth txtline i);

  done;

  close_out oc


(* Read bytes from file, starting at given position *)
let read_bytes start filename =

  (* Open file *)
  let ic = open_in_bin filename in

  (* Get length of bytes available to read *)
  let n = (in_channel_length ic) - start in

  (* Characters available to read after start? *)
  if n > 0 then

    (

      (* Go to starting position in file *)
      seek_in ic start;

      (* Create string of fixed size *)
      let s = String.create n in

      (* Read into string *)
      really_input ic s 0 n;

      (* Close input channel *)
      close_in ic;

      (* Return new position and string *)
      (start + n, s)

    )

  else

    (

      (* Close input channel *)
      close_in ic;

      (* Position is unchanged, string is empty *)
      (start, "")

    )





let interpreter_job
    kind
    job_args
    inputFile
    path =
  (* Open file *)
  let loadavg_ch = open_in "/proc/loadavg" in

  (* Read load averages from file *)
  let load1, load5, load15 =
    Scanf.fscanf loadavg_ch "%f %f %f" (fun l1 l5 l15 -> (l1,l5,l15))
  in

  (* Close file *)
  close_in loadavg_ch;

  log
    "Current system load: %.2f %.2f %.2f"
    load1
    load5
    load15;

  if

    (* System load above of limit? *)
    (!load1_max > 0. && load1 > !load1_max) ||
    (!load5_max > 0. && load5 > !load5_max) ||
    (!load15_max > 0. && load15 > !load15_max)

  then
    
    (

      
      let msg =
        asprintf
          "<Jobstatus msg=\"aborted\">\
Job rejected due to high system load. Try again later.\
</Jobstatus>" in
      log "Job rejected due to high system load";
      msg     

    )
  else
    (
      let job_id = generate_uid () in
      (* Create temporary files for input, output and error output *)
      let stdin_fn = (path ^ "kind_job_" ^ job_id ^ "_input") in
      let stdout_fn = (path ^ "kind_job_" ^ job_id ^ "_output") in

      (* Write data from client to stdin of new kind process *)
      Unix.link inputFile stdin_fn;

      log
        "Input file is %s"
	stdin_fn;

      (* Open file for input *)
      let kind_stdin_in =
        Unix.openfile
          stdin_fn
          [Unix.O_CREAT; Unix.O_RDONLY; Unix.O_NONBLOCK] 0o600
      in

      log
        "Input file is openend";

      (* Open file for output *)
      let kind_stdout_out =
        Unix.openfile
          stdout_fn
          [Unix.O_CREAT; Unix.O_RDWR; Unix.O_NONBLOCK] 0o600
      in

      log
        "Output file is openend";

      (* Temporary file for stderr *)
      let stderr_fn, kind_stderr_out =

       (

          (* By default merge stdout and stderr *)
           stdout_fn, kind_stdout_out

        )

      in

      log
        "Executing %s %a"
        kind
        (pp_print_list Format.pp_print_string " ") (kind :: job_args @ [stdin_fn]);

      log "The job is %s" job_id;

      (* Create kind process *)
      let kind_pid =
        Unix.create_process
          kind
          (Array.of_list(kind :: job_args @ [stdin_fn]))
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
      (try ignore (Unix.waitpid [] kind_pid) with _ -> ());
      let _ , msg = read_bytes 0 stdout_fn in
      msg;
      msg 
    )










      
(* create new kind job using flags 'server_flags',
and the content of 'payload'. send results over 'sock' *)
let create_job
    job_command
    job_args 
    payload 
    path =
  (* Open file *)
  let loadavg_ch = open_in "/proc/loadavg" in

  (* Read load averages from file *)
  let load1, load5, load15 =
    Scanf.fscanf loadavg_ch "%f %f %f" (fun l1 l5 l15 -> (l1,l5,l15))
  in

  (* Close file *)
  close_in loadavg_ch;

  log
    "Current system load: %.2f %.2f %.2f"
    load1
    load5
    load15;

  if

    (* System load above of limit? *)
    (!load1_max > 0. && load1 > !load1_max) ||
    (!load5_max > 0. && load5 > !load5_max) ||
    (!load15_max > 0. && load15 > !load15_max)

  then
    
    (

      
      let msg =
        asprintf
          "<Jobstatus msg=\"aborted\">\
Job rejected due to high system load. Try again later.\
</Jobstatus>" in
      log "Job rejected due to high system load";
      msg,generate_uid(),None     

    )

  else

    (
      
      (* Generate a unique job ID *)
      let job_id = generate_uid () in

      (* Create temporary files for input, output and error output *)
      let stdin_fn = (path ^ "kind_job_" ^ job_id ^ "_input") in
      let stdout_fn = (path ^ "kind_job_" ^ job_id ^ "_output") in

      (* Write data from client to stdin of new kind process *)
      Unix.link payload stdin_fn;

      log
        "Input file is %s"
	stdin_fn;

      (* Open file for input *)
      let kind_stdin_in =
        Unix.openfile
          stdin_fn
          [Unix.O_CREAT; Unix.O_RDONLY; Unix.O_NONBLOCK] 0o600
      in

      log
        "Input file is openend";

      (* Open file for output *)
      let kind_stdout_out =
        Unix.openfile
          stdout_fn
          [Unix.O_CREAT; Unix.O_RDWR; Unix.O_NONBLOCK] 0o600
      in

      log
        "Output file is openend";

      (* Temporary file for stderr *)
      let stderr_fn, kind_stderr_out =

       (

          (* By default merge stdout and stderr *)
           stdout_fn, kind_stdout_out

        )

      in

      log
        "Executing %s %a"
        job_command
        (pp_print_list Format.pp_print_string " ") (job_args);

      (* Create kind process *)
      let kind_pid =
        Unix.create_process
          job_command
          (Array.of_list(job_command :: job_args @ [stdin_fn]))
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
      let job_info : running_job_info = 
	  { job_pid = kind_pid;
          job_start_timestamp = int_of_float (Unix.time ());
          job_stdin_fn = stdin_fn;
          job_stdout_fn = stdout_fn;
          job_stderr_fn = stderr_fn;
          job_stdout_pos = 0 } in 

      let msg =
        asprintf
          "<Jobstatus msg=\"started\" jobid=\"%s\">\
Job started with ID %s.\
</Jobstatus>"
          job_id
          job_id
      in
      log "Job created with ID %s" job_id;
	
      msg,job_id,Some(job_info)

    )







(* Return message after job has terminated, factored out from
   {!retrieve_job} and {!cancel_job} *)
let output_of_job_status
    job_id
    ({ job_pid;
       job_stdin_fn;
       job_stdout_fn;
       job_stderr_fn;
       job_stdout_pos } as job_info)
    job_status =
  
  log ("old pos is %d") job_stdout_pos;
  (* Read from standard output file *)
  let new_stdout_pos, stdout_string = read_bytes job_stdout_pos job_stdout_fn in
  log ("new pos is %d") new_stdout_pos;
  (* Update position in file *)
  job_info.job_stdout_pos <- new_stdout_pos;
  let output_string =

    match job_status with

      (* Terminated with signal *)
      | Unix.WSIGNALED signal ->
        
        log ("killed by signal %d" ^^ "") signal;
        
        (* Read from stderr *)
        let _, errors = read_bytes 0 job_stderr_fn in
        
        (* Create message to client *)
        asprintf
          "%s\
<Jobstatus msg=\"aborted\">\
Job with ID %s aborted before completion.\
Contents of stderr:@\n\
%s
</Jobstatus>"
          stdout_string
          job_id
          errors

      (* Stopped by signal *)
      | Unix.WSTOPPED signal ->
	
        log "stopped by signal %d" signal;

        (* Read from stderr *)
        let _, errors = read_bytes 0 job_stderr_fn in
	
        (* Create message to client *)
        asprintf
          "%s\
<Jobstatus msg=\"aborted\">\
Job with ID %s aborted before completion.\
Contents of stderr:@\n\
%s
</Jobstatus>"
          stdout_string
          job_id
          errors
	  
      (* Exited with code *)
      | Unix.WEXITED code ->
	
        log "exited with code %d" code;
	
        (* Message to client is from stdout *)
        stdout_string
	  
  in

  (* Delete temp files for process *)
  (try (Sys.remove job_stdin_fn) with _ -> ());
  (try (Sys.remove job_stdout_fn) with _ -> ());
  (try (Sys.remove job_stderr_fn) with _ -> ());

  output_string

   


(* Retrieve job *)
let retrieve_job job_id job_param status_pid job_status=
  (* Local log function *)
  let log fmt =
    log
      ("Request retrieval of job %s: " ^^ fmt)
      job_id
  in
	
  (* Job has not exited yet? *)
  if status_pid = 0 then
	  
    (
	    
      log ("running as PID %d") status_pid;
      (* Read from standard output file *)
      let new_stdout_pos, stdout_string = 
	read_bytes job_param.job_stdout_pos job_param.job_stdout_fn 
      in
      
            (* Update position in file *)
      job_param.job_stdout_pos <- new_stdout_pos;
	    
          (* Message to client is from stdout *)
      ( stdout_string , job_param)
	      
    )
      
  else
	  
    ((output_of_job_status job_id job_param job_status) ,  job_param)
            
	
let retrieve_complete job_id job_tm = 
    (* job is found in the table of completed jobs*)
  	  	  
       log "completed at %a UTC" pp_print_time job_tm;
	  
       asprintf
          "<Jobstatus msg=\"completed\">\
          Job with ID %s has completed and was retrieved at %s UTC\
          </Jobstatus>"
          job_id (string_of_time job_tm)
	    
let job_not_found_msg job_id = 	
        log "not found";
	
        let msg = asprintf
          "<Jobstatus msg=\"notfound\">\
           Job with ID %s not found.\
           </Jobstatus>"  job_id 
	in  msg;
	msg

	  


(* Register a request to cancel a job *)
let cancel_job job_id job_param status_pid job_status =
  
  (* Local log function *)
  let log fmt =
    log
      ("Request cancelling of job %s: " ^^ fmt)
      job_id
  in
  
  (* String message to client *)


        (* Job has not exited yet? *)
        if status_pid = 0 then

          (

            log "running as PID %d" status_pid;

            (* Read from standard output file *)
           let new_stdout_pos, stdout_string = read_bytes job_param.job_stdout_pos job_param.job_stdout_fn in

            (* Update position in file *)
            job_param.job_stdout_pos <- new_stdout_pos;

            (* Send SIGINT (Ctrl+C) to job *)
            Unix.kill job_param.job_pid Sys.sigint;

            (* Add cancel request to list *)
            cancel_requested_jobs :=
              (job_id, job_param.job_pid, Unix.gettimeofday ()) ::
                         !cancel_requested_jobs;

            (* Message to client *)
            let msg = asprintf
              "%s\
<Jobstatus msg=\"inprogress\">\
Requested canceling of job with ID %s.\
</Jobstatus>"
              stdout_string
              job_id in 
	    ( msg , job_param)

          )

        else
	  (
          ((output_of_job_status job_id job_param job_status) , job_param)
            
	  )

   



(*  
let purge_jobs () =
  
  log "purging any old jobs";
  
  let purge_if_old
      job_id
      { job_pid;
        job_start_timestamp;
        job_stdin_fn;
        job_stdout_fn;
        job_stderr_fn } =
  
    (* Job is old *)
    if ( ((int_of_float (Unix.time ())) - job_start_timestamp) > job_lifespan ) then
      
      (

        log "purging old job %s" job_id;
        
        (* remove job from table of working jobs *)
        Hashtbl.remove running_jobs job_id;
      
        (* delete job's temp files *)
        (try (Sys.remove job_stdin_fn) with _ -> ());
        (try (Sys.remove job_stdout_fn) with _ -> ());
        (try (Sys.remove job_stderr_fn) with _ -> ());
        
      )
        
  in
  
  Hashtbl.iter purge_if_old running_jobs
    

  *)

(*
let collect_args msg =

(* Collect remaining string from msg into a string array *)
let rec iter argument argv =
match argument with
| "" -> argv;
| _ -> iter (zmsg_popstr msg) (Array.append [|argument|] argv);
in

iter (zmsg_popstr msg) [| |]
*)

(*

(* Collect arguments from message frames *)
let rec collect_args msg accum =

  match zmsg_popstr msg with

    (* No more arguments: reverse list and append defaults *)
    | "" -> accum

    (* Append argument to list and continue *)
    | arg -> collect_args msg (arg :: accum)



(* Main loop: get requests from socket rec get_requests ({ command; args } as config) sock last_purge : unit =

  (* Catch all errors *)
  try

    (* Wait for next message, this can fail when interrupted *)
    let msg = zmsg_recv sock in

    (

      (* First frame contains flags *)
      match zmsg_popstr msg with

        (* Retrieve job *)
        | s when String.contains s 'r' ->

          (* Second part contains job ID *)
          let payload = zmsg_pop msg in

          (* Retrieve job *)
          retrieve_job sock s (zframe_strdup payload)

        (* Cancel job *)
        | s when String.contains s 'k' ->

          (* Second part contains job ID *)
          let payload = zmsg_pop msg in

          (* Retrieve job *)
          cancel_job sock s (zframe_strdup payload)

        (* Creating job? *)
        | s when String.contains s 'c' ->

          (

            (* Second part contains file *)
            let payload = zmsg_pop msg in
            
            (* Third part contains checksum for file *)
            let checksum = zmsg_popstr msg in
            
            (* Collect arguments from remaining frames *)
            let job_args = args @ (collect_args msg []) in
            
            try
              
              create_job sock s payload checksum command job_args;
              
            with Checksum_failure ->
              
              let error_msg = zmsg_new () in

              let msg_str =
                asprintf
                  "<Jobstatus msg=\"aborted\">\
Checksum match failure.\
</Jobstatus>"
              in
              
              ignore(zmsg_pushstr error_msg msg_str);
              ignore(zmsg_send error_msg sock);
              
          )
          
        | s ->
          
          log "Bad flags %s in message. Ignoring." s
            
    );
    *)

(*
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

    (* New list of cancel requests *)
    let cancel_requested_jobs' =
      List.fold_left

        (* Cancel job by sending a cascade of signals: SIGINT at t=0,
then wait and send SIGNTERM, finally send SIGKILL and
forget about request *)
        (fun accum ((job_id, job_pid, cancel_timestamp) as r) ->

          (* Get time since cancel request *)
          let time_since_request =
            Unix.gettimeofday () -. cancel_timestamp
          in

          (* Finally: kill with SIGKILL (-9) *)
          if time_since_request > cancel_sigkill_time then
            (log
               "Sending SIGKILL to job %s (PID %d)"
               job_id
               job_pid;
              (try Unix.kill job_pid Sys.sigkill with _ -> ());
              accum)
            
          (* Kill with SIGTERM, then send SIGKILL later *)
          else if time_since_request > cancel_sigterm_time then
            (log
               "Sending SIGTERM to job %s (PID %d)"
               job_id
               job_pid;(try Unix.kill job_pid Sys.sigterm with _ -> ());
              r :: accum)

          (* Wait *)
          else
            r :: accum)
        []
        !cancel_requested_jobs
    in

    (* Continue with new list of cancel requests *)
    cancel_requested_jobs := cancel_requested_jobs';
      
    (* Continue with next message *)
    get_requests config sock last_purge'

  (* Catch runtime errors *)
  with

    (* Raised when polling is interrupted *)
    | Failure "break" -> get_requests config sock last_purge

    | e ->
      
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
*)
*)
