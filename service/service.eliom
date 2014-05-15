open Eliom_content.Html5.D
open Eliom_parameter
open Ocsigen_extensions
open Kind2server


(* Configuration of a program *)


let configured_programs =

  [

    (* PKind *)
    ("pkind", "/usr/local/bin/pkind");
    
    (* Kind 2 *)
    ("kind2","/usr/local/bin/kind2")  ]


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

(* Get the job info of a running job *)
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
let find_completed_job (jobid : string) (time : Unix.tm) =
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

let xmlWrapper msg = 
  Printf.sprintf "<xml><title>%s</title></xml> " msg



(* Services *)
let submitjob_main_service = 
  Eliom_service.service ~path:["submitjob"] ~get_params:unit ()

let retrievejob_service =
  Eliom_service.service
    ~path:["retrievejob"] ~get_params:(suffix (string "ID")) ()

let canceljob_service = 
  Eliom_service.service
    ~path:["canceljob"] ~get_params:(suffix (string "ID")) ()

let submitjob_service =
  Eliom_service.post_service
    ~fallback:submitjob_main_service
    ~post_params:((string "kind" **  set string "arg" ** file "file"))
    ()


(*
let create_job cmd args file =
  "Job is created", generate_uid (),
  Some { job_pid = 1;
	 job_start_timestamp = 2;
	 job_stdin_fn = "hello";
	 job_stdout_fn = "world";
	 job_stderr_fn = "error";
	 job_stdout_pos = 3;},
  (sleep 10)
*)

(* For testing: call /usr/bin/true and /usr/bin/false *)


(* Registration of services *)
let _ = 
  Eliom_registration.String.register
    ~service:submitjob_main_service
    (fun () () ->
      Lwt.return ("<xml><title> The site is under construction </title></xml>","text/xml"));


   Eliom_registration.String.register
    ~service:submitjob_service
    (fun () (kind, (args, file)) ->

      let command : string = command_look kind in
      let cmd_args : string list = args in
      let filename : string = file.tmp_filename in       
      let user_msg, job_id, job_info = create_job command cmd_args filename in
      add_running_job job_id (extract job_info);
     Lwt.return 
       (xmlWrapper job_id, "text/xml")); 


   Eliom_registration.String.register
     ~service:retrievejob_service
     (fun id () ->
       let { job_pid = job_pid; 
	     job_stdout_fn = job_stdout_fn; 
	     job_stdout_pos = job_stdout_pos } as job_param =
         find_running_job id
       in
	let job_tm = find_completed_job id in
	 Lwt.return (
	   xmlWrapper (retrieve_job id job_pid job_stdout_fn job_stdout_pos job_tm), "text/xml"));

   Eliom_registration.String.register
     ~service:canceljob_service
     (fun id () -> 
       Lwt.return (xmlWrapper cancel_job id, "text/xml"));


(*

   Eliom_registration.Html5.register
    ~service:canceljob_service
    (fun id () ->
      Lwt.return
        (html (head (title (pcdata id)) [])
              (body [h1 [pcdata id];
                     p [pcdata (response (List.nth msg 6)); br();
			pcdata (Printf.sprintf "Requested cancelling of job with ID %s" id); br();
			pcdata "</jobstatus>"; br();]])))



*)
