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

(** Web service for job submission

    @author Mingyu Ma, Christoph Sticksel **)

module Eliom_basic_app =
  Eliom_registration.App (
    struct
      let application_name = "kind2-webservice"
    end)

(* ********************************************************************** *)
(* Executables and parameters                                             *)
(* ********************************************************************** *)


(* Map of identifiers to executables *)
let checkers_and_arguments =

  [

    (* Kind 2 *)
    ("kind2", 
     ("/usr/local/bin/kind2", 
      ["-xml"]));

    (* PKind *)
    ("pkind", 
     ("/usr/local/bin/pkind", 
      ["-xml"; "-xml-to-stdout"]));
    
    (* JKind 

       TODO: JKind does not output to stdout, but into a .xml file *)
    ("jkind",
     ("/usr/local/bin/jkind", 
      ["-xml"]))
       
  ]


(* Map of identifiers to executables *)
let interpreters_and_arguments =

  [

    (* Kind 2 *)
    ("kind2", 
     ("/usr/local/bin/kind2", 
      ["-xml"; "--enable"; "interpreter"]))

  ]


(* Return executable and combine arguments with defaults *)
let cmd_and_args cmd_and_args key args = 

  (* Get executable and default arguments *)
  let cmd, default_args = 
    List.assoc key cmd_and_args 
  in

  (* Reverse and filter out empty strings *)
  let args' = List.filter ((<>) "") (List.rev args) in

  (* Return excutable and arguments *)
  (cmd, (default_args @ args'))


(* Return executable and combine arguments with defaults *)
let checker_cmd_and_args checker args = 
  cmd_and_args checkers_and_arguments checker args


(* Return executable and combine arguments with defaults *)
let interpreter_cmd_and_args interpreter args = 
  cmd_and_args interpreters_and_arguments interpreter args


(* Data directory of Ocsigen instance *)
let data_dir = Ocsigen_config.get_datadir ()


(* Path to generated input and output files *)
let jobs_dir = Filename.concat data_dir "jobs"

  
(* Wrap XML body *)
let xmlwrapper msg = 
  Printf.sprintf
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?><title><para>%s</para></title>" 
    msg


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
let add_running_job jobid jobinfo =

  (* Add to hash table by reading from reference, modifying and
     returning the modified hash table *)
  Eliom_reference.Volatile.modify 
    running_jobs
    (fun tbl -> Hashtbl.add tbl jobid jobinfo; tbl)
    
    
(* Add a job to the completed jobs *)
let add_completed_job jobid time = 

  (* Add to hash table by reading from reference, modifying and
     returning the modified hash table *)
  Eliom_reference.Volatile.modify
    completed_jobs
    (fun tbl -> Hashtbl.add tbl jobid time; tbl)


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
let remove_running_job (jobid : string) = 
  Eliom_reference.Volatile.modify
    running_jobs
    (fun tbl -> Hashtbl.remove tbl jobid; tbl)


(* Get the job info of a running job *)
let find_completed_job (jobid : string) =

  (* Get hash table from reference *)
  let tbl = Eliom_reference.Volatile.get completed_jobs in

  (* Return value of key if found *)
  Hashtbl.find tbl jobid




(* ********************************************************************** *)
(* Service handlers                                                       *)
(* ********************************************************************** *)

(* Fallback handler for all services with wrong parameters

   TODO: Allow interaction with the server through HTML forms *)
let main_service_handler () () = 
  Lwt.return (xmlwrapper "The site is under construction", "text/xml")


(* Return server status

   TODO: Allow interaction with the server through HTML forms *)
let status_service_handler () () =
  Lwt.return (xmlwrapper "The system is running","text/xml")


(* Submit a job *)
let submitjob_service_handler () (kind, (args_in, file)) =
  
  (* Get filename of uploaded file for input *)
  let filename = Eliom_request_info.get_tmp_filename file in
  
  (* Get executable and combine arguments with defaults *)
  let cmd, args = checker_cmd_and_args kind args_in in 
  
  (* Create a job *)
  let user_msg, job_id, job_info = 
    Kind2server.create_job cmd args filename jobs_dir 
  in
  
  (

    (* Job was created? *)
    match job_info with
      
    (* Add to table of running jobs *)
    | Some info -> add_running_job job_id info
      
    (* Do not add to table *)
    | None    ->  () 
      
  );
  
  (* Return message to user *)
  Lwt.return (user_msg, "text/xml") 


(* Run the interpreter without input file *)
let interpreter_input_service_handler () (kind, (args_in, file)) =
  
  (* Get filename of uploaded file for input *)
  let input_file_name = Eliom_request_info.get_tmp_filename file in
  
  (* Get executable and combine arguments with defaults *)
  let cmd, args = interpreter_cmd_and_args kind args_in in 
  
  (* Run interpreter without input file *)
  let msg = 
    Kind2server.interpreter_job 
      cmd
      args
      input_file_name 
      jobs_dir 
  in
  
  (* Return result *)
  Lwt.return (msg, "text/xml")


(* Run the interpreter with an input file *)
let interpreter_service_handler () (kind, (args_in, (input_file, csv_file))) =

  (* Get filename of uploaded file for input *)
  let input_file_name = Eliom_request_info.get_tmp_filename input_file in
  
  (* Get filename of uploaded file for input *)
  let csv_file_name = Eliom_request_info.get_tmp_filename csv_file in

  (* Add arguments to input arguments *)
  let args_in' = 
    "--interpreter_input_file" :: csv_file_name :: args_in
  in

  (* Get executable and combine arguments with defaults *)
  let cmd, args = interpreter_cmd_and_args kind args_in in 
  
  (* Run interpreter *)
  let msg = 
    Kind2server.interpreter_job 
      cmd
      args
      input_file_name
      jobs_dir
  in 
  
  (* Return result *)
  Lwt.return (msg, "text/xml")


(* Retrieve results of a running job *)
let retrievejob_service_handler job_id () =
  
  let msg = 

    try

      (* Find job in table of running jobs *)
      let job_info = find_running_job job_id in

      (* Get exit status of job *)
      let status_pid, job_status = 
	Unix.waitpid [Unix.WNOHANG] Kind2server.(job_info.job_pid)
      in

      (* Retrieve results of job *)
      let msg, job_info = 
	Kind2server.retrieve_job job_id job_info status_pid job_status 
      in

      (* Update status of running job *)
      update_running_job job_id job_info;

      (* Job has terminated? *)
      if status_pid != 0 then

	(

          (* Remove job from table of running jobs *)
	  remove_running_job job_id;

          (* Add job to table of completed jobs *)
	  add_completed_job job_id (Unix.gmtime (Unix.time ()))

	);

      (* Return output from job *)
      msg

    (* Job is not running *)
    with Not_found ->

      try
        
        (* Find job in table of completed jobs *)
	let job_tm = find_completed_job job_id in

        (* Return message *)
	Kind2server.retrieve_complete job_id job_tm
          
      (* Job is not completed *)
      with Not_found ->
        
        (* Return message *)
	Kind2server.job_not_found_msg job_id 

  in
  
  (* Return result *)
  Lwt.return (msg, "text/xml")


(* Cancel running job *)
let canceljob_service_handler job_id () =

  let msg = 

    try

      (* Find job in table of running jobs *)
      let job_info = find_running_job job_id in

      (* Get exit status of job *)
      let status_pid, job_status = 
	Unix.waitpid [Unix.WNOHANG] Kind2server.(job_info.job_pid)
      in

      Kind2server.log ("This status_pid is %d") status_pid;

      (* Cancel job *)
      let msg, job_info = 
	Kind2server.cancel_job job_id job_info status_pid job_status
      in 

      (* Update status of running job *)
      update_running_job job_id job_info;

      (* Job has terminated? *)
      if status_pid != 0 then

	(

          (* Remove job from table of running jobs *)
	  remove_running_job job_id;

          (* Add job to table of completed jobs *)
	  add_completed_job job_id (Unix.gmtime (Unix.time ()))

	);

      (* Return output from job *)
      msg

    (* Job is not running *)
    with Not_found ->
    
      try

          (* Find job in table of completed jobs *)
	  let job_tm = find_completed_job job_id in

          (* Return message *)
	  Kind2server.retrieve_complete job_id job_tm

      (* Job is not completed *)
      with Not_found ->

        (* Return message *)
	Kind2server.job_not_found_msg job_id 
  in 

  (* Return result *)
  Lwt.return (msg, "text/xml")


(* ********************************************************************** *)
(* Creation of GET Services                                               *)
(* ********************************************************************** *)


(* Fallback service for submitjob when called with no parameters *)
let submitjob_main_service = 
  Eliom_service.App.service 
    ~path:["submitjob"] 
    ~get_params:Eliom_parameter.unit
    ()

    
(* Fallback service to retrieve job when called with no parameters *)
let retrievejob_main_service =
  Eliom_service.App.service
    ~path:["retrievejob"] 
    ~get_params:Eliom_parameter.unit
    ()


(* Fallback service to retrieve job when called with no parameters *)
let canceljob_main_service =
  Eliom_service.App.service
    ~path:["canceljob"] 
    ~get_params:Eliom_parameter.unit
    ()


(* Fallback service for interpreter when called with no parameters *)
let interpreter_main_service =
  Eliom_service.App.service
    ~path:["interpreter"]
    ~get_params:Eliom_parameter.unit
    ()

    
(* Service to retrieve job, parameter is part of the URI *)
let retrievejob_service =
  Eliom_service.App.service
    ~path:["retrievejob"] 
    ~get_params:Eliom_parameter.(suffix (string "ID"))
    ()


(* Service to cancel job, parameter is part of the URI *)
let canceljob_service = 
  Eliom_service.App.service
    ~path:["canceljob"] 
    ~get_params:Eliom_parameter.(suffix (string "ID"))
    ()
    

(* Service to return system status *)
let status_service = 
  Eliom_service.App.service
    ~path:["status"]
    ~get_params:Eliom_parameter.unit 
    ()


(* ********************************************************************** *)
(* Creation of POST Services                                              *)
(* ********************************************************************** *)

(* Service to submit a job *)
let submitjob_service =
  Eliom_service.App.post_service
    ~fallback:submitjob_main_service
    ~post_params:
    Eliom_parameter.(string "kind" ** 
                       set string "arg" **
                       file "file")
    ()

(* Service to run the interpreter with an input *)
let interpreter_service =
  Eliom_service.App.post_service
    ~fallback:interpreter_main_service
    ~post_params:
    Eliom_parameter.(string "kind" ** 
                       set string "arg" ** 
                       file "inputFile" ** 
                       file "csvFile")
    ()

(* Service to run the interpreter without an input *)
let interpreter_input_service =
  Eliom_service.App.post_service
    ~fallback:interpreter_main_service
    ~post_params:
    Eliom_parameter.(string "kind" ** 
                       set string "arg" ** 
                       file "inputFile")
    ()


(* ********************************************************************** *)
(* Main entry point: Register service handlers                            *)
(* ********************************************************************** *)

(* Registration of services *)
let _ =

  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:submitjob_main_service
    main_service_handler;

  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:retrievejob_main_service
    main_service_handler;

  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:canceljob_main_service
    main_service_handler;

  (* Run main service as fallback *)
  Eliom_registration.String.register
    ~service:interpreter_main_service
    main_service_handler;

  (* Register status service handler *)
  Eliom_registration.String.register
    ~service:status_service
    status_service_handler;
 
  (* Register job submission service handler *)
  Eliom_registration.String.register
    ~service:submitjob_service
    submitjob_service_handler;

   (* Register job retrieval service handler *)
   Eliom_registration.String.register
     ~service:retrievejob_service
     retrievejob_service_handler;

  (* Register job cancel handler *)
   Eliom_registration.String.register
     ~service:canceljob_service
     canceljob_service_handler;

  (* Register interpreter service handler without input *)
   Eliom_registration.String.register
    ~service:interpreter_input_service
     interpreter_input_service_handler;
       
  (* Register interpreter service handler *)
   Eliom_registration.String.register
     ~service:interpreter_service
     interpreter_service_handler

