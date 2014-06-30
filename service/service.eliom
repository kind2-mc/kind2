open Eliom_content.Html5.D
open Eliom_parameter
open Ocsigen_extensions
open Kind2server

(* Configuration of a program *)


let configured_programs =

  [

    (* Test *)
    ("retrievetest", "/home/mma1/kind2/service/retrieveTest.py");
    
    (* PKind *)
    ("pkind", "/usr/local/bin/pkind" );
    
    (* Kind 2 *)
    ("kind2","/usr/local/bin/kind2" )  ]


(* Hash table for running jobs *)
let running_jobs : ((string, running_job_info) Hashtbl.t, [ `Volatile ]) Eliom_reference.eref' = 
  Eliom_reference.Volatile.eref
    ~scope:Eliom_common.global_scope
    (Hashtbl.create 50)

(* Hash table for completed jobs *)
let completed_jobs : ((string, Unix.tm) Hashtbl.t, [ `Volatile ]) Eliom_reference.eref' = 
  Eliom_reference.Volatile.eref
    ~scope:Eliom_common.global_scope
    (Hashtbl.create 50)


(* Add a job to the running jobs *)
let add_running_job (jobid : string) (jobinfo : running_job_info)  =
    Eliom_reference.Volatile.modify 
       running_jobs
       (fun tbl -> Hashtbl.add tbl jobid jobinfo; tbl)

(* Add a job to the completed jobs *)
let add_completed_job (jobid : string) (time : Unix.tm) = 
  Eliom_reference.Volatile.modify
    completed_jobs
    (fun tbl -> Hashtbl.add tbl jobid time; tbl)

(* Get the job info of a running job *)
let find_running_job (jobid : string) : running_job_info =
  let tbl = Eliom_reference.Volatile.get running_jobs in
     Hashtbl.find tbl jobid

(* Modify the job info of a running job *)
let update_running_job (jobid : string) (f : running_job_info -> running_job_info) =
  Eliom_reference.Volatile.modify 
    running_jobs 
    (fun tbl -> 
      let job_info = Hashtbl.find tbl jobid in
      let job_info' = f job_info in
      Hashtbl.replace tbl jobid job_info';
      tbl)

(* Remove a a running job from hashtable *)
let remove_running_job (jobid : string) = 
  Eliom_reference.Volatile.modify
    running_jobs
    (fun tbl -> Hashtbl.remove tbl jobid; tbl)

(* Get the job info of a running job *)
let find_completed_job (jobid : string) =
  let tbl = Eliom_reference.Volatile.get completed_jobs in
     Hashtbl.find tbl jobid


(* ********************************************************************** *)
(* Helper functions *)
(* ********************************************************************** *)


(* Helper function to extract optional value *)
let extract = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Option.get")

(* Helper function to look up job_command *)
let command_look cmd = List.assoc cmd configured_programs

(* define path for placing the generated input and output files *)
let head = Ocsigen_config.get_datadir ()
let path = head ^ "/jobs/"

let xmlwrapper msg = Printf.sprintf "<?xml version=\"1.0\" encoding=\"UTF-8\"?><title><para>%s</para></title>" msg

let process_arg args = List.filter (fun s -> s <> "") (List.rev args)

(*get the default argument*)
let extra_args kind = match kind with 
    "kind2" -> ["-xml"]
  | "pkind"-> [ "-xml";"-xml-to-stdout"]
  | _ -> []


(* ********************************************************************** *)
(* ********************************************************************** *)

(* Services *)
(* main service *)
let submitjob_main_service = 
  Eliom_service.service ~path:["submitjob"] ~get_params:unit ()

(* get services *)
let retrievejob_service =
  Eliom_service.service
    ~path:["retrievejob"] ~get_params:(suffix (string "ID")) ()

let canceljob_service = 
  Eliom_service.service
    ~path:["canceljob"] ~get_params:(suffix (string "ID")) ()

(* post service that takes three parameters kind, arguments, file*)
let submitjob_service =
  Eliom_service.post_service
    ~fallback:submitjob_main_service
    ~post_params:((string "kind" **  set string "arg" ** file "file"))
    ()


(* For testing: call /usr/bin/true and /usr/bin/false *)


(* Registration of services *)
let _ =
  Eliom_registration.String.register
    ~service:submitjob_main_service
    (fun () () ->
      Lwt.return ("The site is under construction", "text/xml"));

   Eliom_registration.String.register
    ~service:submitjob_service
    (fun () (kind, (args, file)) ->
      let command : string  = command_look kind in
      let cmd_args : string list = process_arg args in
      let filename : string = file.tmp_filename in
      let default_args :string list = extra_args kind in 
      let user_msg, job_id, job_info = create_job command (default_args @ cmd_args) filename path in  
      add_running_job job_id (extract job_info);
     Lwt.return 
       ( user_msg, "text/xml")); 


   Eliom_registration.String.register
     ~service:retrievejob_service
     (fun id () -> 
       let msg = 
       try
	 (
	   let job_info =
             find_running_job id
	   in
	   let status_pid, job_status = 
	     Unix.waitpid [Unix.WNOHANG] job_info.job_pid
	   in
	   (* check if the job is still running *)
	   let msg, new_job_info = 
	     retrieve_job id job_info status_pid job_status in
	   update_running_job id ( fun job_info -> new_job_info );
	   if ( status_pid != 0 ) then
	     (
	       remove_running_job id;
	       add_completed_job id (Unix.gmtime(Unix.time()))
	     );
	   msg
	     
	 )
       with Not_found ->
	 try
	   (
	     let job_tm = 
	       find_completed_job id
	     in
	     retrieve_complete id job_tm
	   )
	 with Not_found ->
	   job_not_found_msg id in
       Lwt.return 
	     (msg, "text/xml"));

   Eliom_registration.String.register
     ~service:canceljob_service
     (fun id () -> 
       let msg = 
	 try
	   (
	     let job_info = 
	       find_running_job id
	     in
	     let status_pid, job_status = 
	       Unix.waitpid [Unix.WNOHANG] job_info.job_pid
	     in
	     log ("This status_pid is %d") status_pid;
	     let msg , new_job_info = 
	       cancel_job id job_info status_pid job_status
	     in 
	     update_running_job id ( fun job_info -> new_job_info );
	     if ( status_pid != 0 ) then
	     (
	       remove_running_job id;
	       add_completed_job id (Unix.gmtime(Unix.time()))
	     );
	     msg
	   )
	 with Not_found ->
	   try
	     (
	       let job_tm = 
		 find_completed_job id
	       in
	       retrieve_complete id job_tm
	     )
	   with Not_found ->
	     job_not_found_msg id in 
       Lwt.return (msg, "text/xml"));

