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

(** Job creation, retrieval, and canceling

    @author Jason Oxley, Mingyu Ma, Christoph Sticksel **)

open Lib

(* Information about a running job *)
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

    (* Command executable *)
    job_cmd : string;

    (* Command arguments *)
    job_args : string list;

    (* Last read position in stardard output file *)
    mutable job_stdout_pos : int

  }



(* ********************************************************************** *)
(* Defaults                                                               *)
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

(* Create string identifier for job from request id *)
let generate_uid () = base10tol (Eliom_request_info.get_request_id ()) 
 
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






(* ********************************************************************** *)
(* State shared between instances                                         *)
(* ********************************************************************** *)

(* We need to store the state in a volatile reference to keep it
   persistent between concurrent instances. We could make the
   reference persistent to preserve the state when restarting the
   server. *)
    

(* Hash table for running jobs *)
let running_jobs =
  Eliom_reference.Volatile.eref
    ~scope:Eliom_common.global_scope
    (Hashtbl.create 50)


(* Hash table for completed jobs *)
let completed_jobs =
  Eliom_reference.Volatile.eref
    ~scope:Eliom_common.global_scope
    (Hashtbl.create 50)


(* Add a job to the running jobs *)
let add_running_job jobid jobinfo : unit =

  (* Add to hash table by reading from reference, modifying and
     returning the modified hash table *)
  Eliom_reference.Volatile.modify 
    running_jobs
    (fun tbl -> Hashtbl.add tbl jobid jobinfo; tbl)
    
    
(* Add a job to the completed jobs *)
let add_completed_job jobid time status = 

  (* Add to hash table by reading from reference, modifying and
     returning the modified hash table *)
  Eliom_reference.Volatile.modify
    completed_jobs
    (fun tbl -> Hashtbl.add tbl jobid (time, status); tbl)


(* Get the job info of a running job *)
let find_running_job jobid =
  
  (* Get hash table from reference *)
  let tbl = Eliom_reference.Volatile.get running_jobs in
  
  (* Return value of key if found *)
  Hashtbl.find tbl jobid


(* Modify the job info of a running job *)
let update_running_job jobid jobinfo =

  (* Add hash table by reading from reference, modifying and returning
     the modified hash table *)
  Eliom_reference.Volatile.modify 
    running_jobs 
    (fun tbl -> 
      Hashtbl.replace tbl jobid jobinfo;
      tbl)

(* Remove a a running job from hash table *)
let remove_running_job jobid = 
  Eliom_reference.Volatile.modify
    running_jobs
    (fun tbl -> Hashtbl.remove tbl jobid; tbl)


(* Get the job info of a running job *)
let find_completed_job jobid =

  (* Get hash table from reference *)
  let tbl = Eliom_reference.Volatile.get completed_jobs in

  (* Return value of key if found *)
  Hashtbl.find tbl jobid


(* ********************************************************************** *)
(* Submitting jobs                                                        *)
(* ********************************************************************** *)


(* Start the given job if enough system resources available and call
   continuation function after job has been created *)
let start_job job_cmd job_args input_file after_start = 

  (* Open load averages file *)
  let loadavg_ch = open_in "/proc/loadavg" in

  (* Read load averages from file *)
  let load1, load5, load15 =
    Scanf.fscanf loadavg_ch "%f %f %f" (fun l1 l5 l15 -> (l1,l5,l15))
  in

  (* Close load averages file *)
  close_in loadavg_ch;
  
  if

    (* System load above of limit? *)
    (!load1_max > 0. && load1 > !load1_max) ||
    (!load5_max > 0. && load5 > !load5_max) ||
    (!load15_max > 0. && load15 > !load15_max)

  then

    (


      log ErrorLog
        "Job rejected, system load is: %.2f %.2f %.2f" 
        load1
        load5
        load15;

      Format.asprintf
        "<Jobstatus msg=\"aborted\">\
         Job rejected due to high system load. Try again later.\
         </Jobstatus>" 

    )


  else

    (

      (* Generate a unique identifier for the job *)
      let job_id = generate_uid () in

      (* Create temporary files for input, output and error output *)
      let job_stdin_fn = 
        Filename.concat
          jobs_dir
          (Format.sprintf "%s.in" job_id)
      in

      let job_stdout_fn =
        Filename.concat
          jobs_dir
          (Format.sprintf "%s.out" job_id)
      in

      (* Create hard link to temporary input file *)
      Unix.link input_file job_stdin_fn;

      (* Open file for input *)
      let job_stdin_in =
        Unix.openfile
          job_stdin_fn
          [Unix.O_CREAT; Unix.O_RDONLY; Unix.O_NONBLOCK] 0o600
      in

      (* Open file for output *)
      let job_stdout_out =
        Unix.openfile
          job_stdout_fn
          [Unix.O_CREAT; Unix.O_RDWR; Unix.O_NONBLOCK] 0o600
      in

      (* Merge error output into standard output *)
      let job_stderr_fn, job_stderr_out = job_stdout_fn, job_stdout_out in

      (* Create process writing to and reading from files created *)
      let job_pid =
        Unix.create_process
          job_cmd
          (Array.of_list (job_cmd :: job_args @ [job_stdin_fn]))
          job_stdin_in
          job_stdout_out
          job_stderr_out
      in

      (* Close our end of the pipe which has been duplicated by the
         process *)
      Unix.close job_stdin_in;
      Unix.close job_stdout_out;

      (* Close file for error output if not equal to standard
         output *)
      if not (job_stderr_out = job_stdout_out) then
        Unix.close job_stderr_out;

      (* Initial job information *)
      let job_info =
        { job_pid = job_pid;
          job_start_timestamp = int_of_float (Unix.time ());
          job_stdin_fn = job_stdin_fn;
          job_stdout_fn = job_stdout_fn;
          job_stderr_fn = job_stderr_fn;
          job_cmd = job_cmd;
          job_args = job_args;
          job_stdout_pos = 0 }
      in
 
      (* Call continuation function *)
      after_start job_id job_info

    )


(* Submit a job *)
let submit_job job_cmd job_args input_file = 

  (* Continuation after job has started *)
  let after_start job_id ({ job_pid; job_cmd; job_args } as job_info) = 

    (* Add job to table of running jobs *)
    add_running_job job_id job_info;

    log AccessLog
      "Started job %s with PID %d as %a"
      job_id
      job_pid
      (Lib.pp_print_list Format.pp_print_string " ")
      (job_cmd :: job_args);

    (* Return message *)
    Format.asprintf
      "<Jobstatus msg=\"started\" jobid=\"%s\">\
       Job started with ID %s.\
       </Jobstatus>"
      job_id
      job_id

  in

  (* Start job and add to table of running jobs *)
  start_job job_cmd job_args input_file after_start
  

(* Submit a job and return result immediately *)
let submit_job_immediate job_cmd job_args input_file = 

  (* Continuation after job has started *)
  let after_start job_id { job_pid; job_stdout_fn } = 
    
    log AccessLog
      "Waiting for job %s with PID %d."
      job_id
      job_pid;

    (* Wait for started job to finish *)
    (try ignore (Unix.waitpid [] job_pid) with _ -> ());

    log AccessLog
      "Job %s with PID %d has terminated."
      job_id
      job_pid;

    (* Read all output *)
    let _ , msg = read_bytes 0 job_stdout_fn in

    (* Return output *)
    msg 

  in

  (* Start job and add to table of running jobs *)
  start_job job_cmd job_args input_file after_start


let retrieve_job job_id = 

  try 

    (* Find job in table of running jobs *)
    let { job_pid; job_stdout_fn; job_stdout_pos } as job_info = 
      find_running_job job_id 
    in

    (* Read from standard output file *)
    let new_stdout_pos, stdout_string = 
      read_bytes job_stdout_pos job_stdout_fn 
    in

    log AccessLog 
      "Read %d bytes of output from job %s" 
      (new_stdout_pos - job_stdout_pos)
      job_id;

    (* Update position in file *)
    job_info.job_stdout_pos <- new_stdout_pos;

    (* Update status of running job *)
    update_running_job job_id job_info;

    (* Get exit status of job *)
    let status_pid, job_status =
      Unix.waitpid [Unix.WNOHANG] job_pid 
    in

    (* Job has exited? *)
    if status_pid != 0 then

      (

        log AccessLog 
          "Job %s with PID %d has %a" 
          job_id
          job_pid
          pp_print_process_status job_status;

        (* Remove job from table of running jobs *)
        remove_running_job job_id;

        (* Add job to table of completed jobs *)
        add_completed_job job_id (Unix.gmtime (Unix.time ())) job_status

      );

    (* Return output from job *)
    stdout_string

  (* Job is not running *)
  with Not_found ->

    try

      (* Find job in table of completed jobs *)
      let job_tm, job_status = find_completed_job job_id in

      log AccessLog
        "Job %s was completed at %a UTC" 
        job_id
        pp_print_time job_tm;
      
      Format.asprintf
        "<Jobstatus msg=\"completed\">\
         Job with ID %s has %a and was retrieved at %a UTC\
         </Jobstatus>"
        job_id 
        pp_print_process_status job_status
        pp_print_time job_tm
            
    (* Job is not completed *)
    with Not_found ->
      
      (
        
        log AccessLog
          "Job %s not found" 
          job_id;
        
        Format.asprintf
          "<Jobstatus msg=\"notfound\">\
           Job with ID %s not found.\
           </Jobstatus>" 
          job_id 

      )


(* Register a request to cancel a job *)
let cancel_job job_id =

  try 

    (* Find job in table of running jobs *)
    let { job_pid; job_stdout_fn; job_stdout_pos } as job_info = 
      find_running_job job_id 
    in

    (

      try 

        log AccessLog
          "Sending SIGINT to %s running as PID %d" 
          job_id
          job_pid;

        (* Send SIGINT (Ctrl+C) to job *)
        Unix.kill job_pid Sys.sigint;

        (* Add cancel request to list *)
        cancel_requested_jobs :=
          (job_id, job_pid, Unix.gettimeofday ()) ::
          !cancel_requested_jobs;

        (* Message to client *)
        Format.asprintf
          "<Jobstatus msg=\"inprogress\">\
           Requested canceling of job with ID %s.\
           </Jobstatus>"
          job_id 

      with Unix.Unix_error (_, _, e) ->

        (

          log AccessLog
            "Error canceling job %s with PID %d: %s" 
            job_id
            job_pid
            e;

          (* Message to client *)
          Format.asprintf
            "<Jobstatus msg=\"notfound\">\
             Couldn not cancel job with ID %s. %s.\
             </Jobstatus>"
            job_id 
            e

        )

    )

  (* Job is not running *)
  with Not_found ->

    try

      (* Find job in table of completed jobs *)
      let job_tm, job_status = find_completed_job job_id in

      log AccessLog
        "Attempting to cancel completed job %s" 
        job_id;

      Format.asprintf
        "<Jobstatus msg=\"completed\">\
         Job with ID %s has %a and was retrieved at %a UTC\
         </Jobstatus>"
        job_id 
        pp_print_process_status job_status
        pp_print_time job_tm

    (* Job is not completed *)
    with Not_found ->

      (

        log AccessLog
          "Job %s not found" 
          job_id;

        Format.asprintf
          "<Jobstatus msg=\"notfound\">\
           Job with ID %s not found.\
           </Jobstatus>" 
          job_id 

      )



(* TODO: prune jobs called frequently to kill canceled jobs and to
   clean up *)

(*
   
  



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

  log AccessLog
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


      log ErrorLog
        "Job rejected, system load is: %.2f %.2f %.2f" 
        load1
        load5
        load15;

      Format.asprintf
        "<Jobstatus msg=\"aborted\">\
         Job rejected due to high system load. Try again later.\
         </Jobstatus>" 

    )
  else
    (

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

  (* Generate a unique job ID *)
  let job_id = generate_uid () in

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
        Format.asprintf
          "<Jobstatus msg=\"aborted\">\
Job rejected due to high system load. Try again later.\
</Jobstatus>" in
      log "Job rejected due to high system load";
      msg, job_id, None     

    )

  else

    (
      
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





*)
