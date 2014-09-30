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
    job_start_timestamp : float;

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
      if Hashtbl.mem tbl jobid then Hashtbl.replace tbl jobid jobinfo;
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

  (* Try to get load averages *)
  let load1, load5, load15 = get_loadavg () in

  if

    (* System load above of limit? *)
    (load1_max > 0. && load1 > load1_max) ||
    (load5_max > 0. && load5 > load5_max) ||
    (load15_max > 0. && load15 > load15_max)

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
          job_start_timestamp = Unix.gettimeofday ();
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


(* Submit a job 

   TODO: Schedule jobs instead of rejecting *)
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


(* ********************************************************************** *)
(* Submitting jobs                                                        *)
(* ********************************************************************** *)


(* Return type of retrieve_job *)
type retrieved_job =

  (* Job is running, job information returned *)
  | Running of running_job_info

  (* Job is not running, message returned *)
  | NotRunning of string 

(* Retrieve a job by its ID *)
let retrieve_job job_id = 

  try 

    (* Find job in table of running jobs *)
    let { job_pid; job_stdout_fn; job_stdout_pos } as job_info = 
      find_running_job job_id 
    in

    (* Return output from job *)
    Running job_info

  (* Job is not running *)
  with Not_found ->

    try

      (* Find job in table of completed jobs *)
      let job_tm, job_status = find_completed_job job_id in

      log AccessLog
        "Job %s was completed at %a UTC" 
        job_id
        pp_print_time job_tm;
      
      NotRunning
	(Format.asprintf
           "<Jobstatus msg=\"completed\">\
            Job with ID %s has %a and was retrieved at %a UTC\
            </Jobstatus>"
           job_id 
           pp_print_process_status job_status
           pp_print_time job_tm)
            
    (* Job is not completed *)
    with Not_found ->
      
      (
        
        log AccessLog
          "Job %s not found" 
          job_id;
        
	NotRunning
          (Format.asprintf
             "<Jobstatus msg=\"notfound\">\
              Job with ID %s not found.\
              </Jobstatus>" 
             job_id)

      )


(* Return output since last call *)
let job_output job_id = 

  (* Retrieve job *)
  match retrieve_job job_id with 

    (* Job is running *)
    | Running ({ job_pid; job_stdout_pos; job_stdout_fn } as job_info) ->

      (

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
            add_completed_job job_id (Unix.gettimeofday ()) job_status

	  );

	(* Return output *)
	stdout_string 
	  
      )

    (* Job is not running *)
    | NotRunning msg -> msg

      
(* Register a request to cancel a job *)
let cancel_job job_id =

  (* Retrieve job *)
  match retrieve_job job_id with 

    (* Job is running *)
    | Running { job_pid } ->

      (
	
	log AccessLog
          "Sending SIGINT to %s running as PID %d" 
          job_id
          job_pid;

	try 

          (* Send SIGINT (Ctrl+C) to job *)
          Unix.kill job_pid Sys.sigint;

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
    | NotRunning msg -> msg


(* ********************************************************************** *)
(* Cleaning up                                                            *)
(* ********************************************************************** *)

(* Clean table of running and completed jobs from old jobs *)
let purge_jobs () = 

  (* Remove not retrieved jobs from table of running jobs *)
  Eliom_reference.Volatile.modify
    running_jobs
    (fun tbl -> 
      
      (* Jobs purged because they were not retrieved *)
      let purged_jobs = 

	Hashtbl.fold 
	  
	  (fun job_id { job_start_timestamp; job_pid } accum ->
	    
	    (* Job was started too long ago? *)
	    if (Unix.gettimeofday ()) -. job_start_timestamp > job_purge_time then

	      (

		(try
		   
		   (* Kill job *)
		   Unix.kill job_pid Sys.sigkill;

		   (* Get exit status of job to reap zombie process *)
		   ignore (Unix.waitpid [Unix.WNOHANG] job_pid)
		     
		 (* Error while retrieving job *)
		 with Unix.Unix_error _ -> ());

		(* Remove job from table *)
		job_id :: accum

	      )
		
	    else
	      
	      (* Keep job *)
	      accum)
	  
	  tbl
	  []

      in

      (* Remove purged jobs from table *)
      List.iter (Hashtbl.remove tbl) purged_jobs;
      
      log AccessLog
	"Purged %d old jobs from table of running jobs"
	(List.length purged_jobs);

      tbl);

  (* Remove old jobs from table of completed jobs *)
  Eliom_reference.Volatile.modify
    completed_jobs
    (fun tbl -> 
      
      (* Jobs deleted because they are too old *)
      let purged_jobs = 

	Hashtbl.fold 
	  
	  (fun job_id (job_tm, _)  accum ->
	    
	    (* Job was started too long ago? *)
	    if (Unix.gettimeofday ()) -. job_tm > job_purge_time then

	      (* Remove job from table *)
	      job_id :: accum
		
	    else
	      
	      (* Keep job *)
	      accum)
	  
	  tbl
	  []
	  
      in

      (* Remove purged jobs from table *)
      List.iter (Hashtbl.remove tbl) purged_jobs;

      log AccessLog
	"Purged %d old jobs from table of completed jobs"
	(List.length purged_jobs);

      tbl);

      Format.asprintf
        "Purged old jobs from tables" 

  

    
let status () =       

  Format.asprintf "The system is running" 
