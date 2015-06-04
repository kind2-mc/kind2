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

open Lib
open Lwt

(* ********************************************************************** *)
(* Service handlers                                                       *)
(* ********************************************************************** *)

(* Fallback handler for all services with wrong parameters

   TODO: Allow interaction with the server through HTML forms *)
let main_service_handler () () = 
  Lwt.return ("The site is under construction", "text/plain")


(* Return server status

   TODO: Allow interaction with the server through HTML forms *)
let status_service_handler () () =

  let msg = Jobs.status () in
  
  Lwt.return (msg, "text/plain")

let pullrequest_main_service_handler () () = 
  Lwt.return ("Pullrequest testing url", "text/plain")

(* Submit a job *)
let submitjob_service_handler () (kind, (args_in, file)) =
  
  (* Get filename of uploaded file for input *)
  let input_file_name = Eliom_request_info.get_tmp_filename file in
  
  (* Get executable and combine arguments with defaults *)
  let cmd, args = checker_cmd_and_args kind args_in in 
  
  (* Create a job *)
  let msg = Jobs.submit_job cmd args input_file_name in
  
  (* Return message to user *)
  Lwt.return (msg, "text/xml") 


(* Run the interpreter without input file *)
let interpreter_input_service_handler () (kind, (args_in, file)) =
  
  (* Get filename of uploaded file for input *)
  let input_file_name = Eliom_request_info.get_tmp_filename file in
  
  (* Get executable and combine arguments with defaults *)
  let cmd, args = interpreter_cmd_and_args kind args_in in 
  
  (* Run interpreter without input file *)
  let msg = Jobs.submit_job_immediate cmd args input_file_name in
  
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
    csv_file_name :: "--interpreter_input_file" :: args_in
  in

  (* Get executable and combine arguments with defaults *)
  let cmd, args = interpreter_cmd_and_args kind args_in' in 
  
  (* Run interpreter *)
  let msg = Jobs.submit_job_immediate cmd args input_file_name in 
  
  (* Return result *)
  Lwt.return (msg, "text/xml")


(* Retrieve results of a running job *)
let retrievejob_service_handler job_id () =

  (* Get output of job *)
  let msg = Jobs.job_output job_id in
  
  (* Return result *)
  Lwt.return (msg, "text/xml")


(* Cancel running job *)
let canceljob_service_handler job_id () =

  (* Schedule canceling of job *)
  let msg = Jobs.cancel_job job_id in
  
  (* Return result *)
  Lwt.return (msg, "text/xml")


(* Cancel running job *)
let purge_jobs_service_handler () () =

  (* Schedule canceling of job *)
  let msg = Jobs.purge_jobs () in
  
  (* Return result *)
  Lwt.return (msg, "text/plain")



(* helper function to respond with error codes *)
let send_error ~code error_message =
  Eliom_registration.String.send ~code (error_message, "text/plain")

(* helper functions to respond with success code *)
    
let send_success () =
  Eliom_registration.String.send ~code:200 ("", "")

let send_success_str str =
  Eliom_registration.String.send ~code:200 (str, "text/plain")

(* helper function to read data sent to the server *)
let read_raw_content ?(length = 1048576) raw_content =
  let content_stream = Ocsigen_stream.get raw_content in
  Ocsigen_stream.string_of_stream length content_stream

(* function that handles requests for pull requests hooks *)
let pullrequest_test_service_handler () (content_type, raw_content_opt) =

  match raw_content_opt with
  | None -> 
    send_error ~code:400 "Body content is missing"
      
  | Some raw_content ->

    read_raw_content raw_content >>= fun payload ->

    (* Parse message *)
    let json = Yojson.Basic.from_string payload in
    let open Yojson.Basic.Util in

    let action = json |> member "action" |> to_string in
    let pr = json |> member "pull_request" in

    let base_ref = pr |> member "base" |> member "ref" |> to_string in

    match action with
    (* only run tests if a pull request is opened or updated and the base branch
       is not the github web page *)
    | ("opened" | "reopened" | "synchronize") when base_ref <> "gh_pages" ->

      let pr_nb = pr |> member "number" |> to_int in
      let statuses_url = pr |> member "statuses_url" |> to_string in
      let html_url = pr |> member "html_url" |> to_string in
      let pr_user = pr |> member "user" |> member "login" |> to_string in

      (* Execute command on cvc cluster through ssh.
         The user ocsigen must have an ssh key that is only allowed to run 
         the neessary command, here we just pass the arguments. *)
      let cmd = Format.sprintf
          "ssh -i /var/lib/ocsigenserver/.ssh/id_rsa_restricted \
           amebsout@@cvc.cs.uiowa.edu \
           \"%d %s %s %s\" &"
          pr_nb base_ref statuses_url html_url
      in
      
      if Sys.command cmd = 0 then
        send_success ()
      else
        send_error ~code:400 "Could not contact CVC cluster"


    | _ -> send_success_str "Hook ignores pull request"


(* ********************************************************************** *)
(* Creation of GET Services                                               *)
(* ********************************************************************** *)


(* Fallback service for submitjob when called with no parameters *)
let submitjob_main_service = 
  Eliom_service.Http.service 
    ~path:["submitjob"] 
    ~get_params:Eliom_parameter.unit
    ()

    
(*
(* Fallback service to retrieve job when called with no parameters *)
let retrievejob_main_service =
  Eliom_service.Http.service
    ~path:["retrievejob"] 
    ~get_params:Eliom_parameter.unit
    ()

(* Fallback service to retrieve job when called with no parameters *)
let canceljob_main_service =
  Eliom_service.Http.service
    ~path:["canceljob"] 
    ~get_params:Eliom_parameter.unit
    ()
*)

(* Fallback service for interpreter when called with no parameters *)
let interpreter_main_service =
  Eliom_service.Http.service
    ~path:["interpreter"]
    ~get_params:Eliom_parameter.unit
    ()

    
(* Service to retrieve job, parameter is part of the URI *)
let retrievejob_service =
  Eliom_service.Http.service
    ~path:["retrievejob"] 
    ~get_params:Eliom_parameter.(suffix (string "ID"))
    ()


(* Service to cancel job, parameter is part of the URI *)
let canceljob_service = 
  Eliom_service.Http.service
    ~path:["canceljob"] 
    ~get_params:Eliom_parameter.(suffix (string "ID"))
    ()
    

(* Service to return system status *)
let status_service = 
  Eliom_service.Http.service
    ~path:["status"]
    ~get_params:Eliom_parameter.unit 
    ()


(* Service to return system status *)
let purge_jobs_service = 
  Eliom_service.Http.service
    ~path:["purgejobs"]
    ~get_params:Eliom_parameter.unit 
    ()

(* Fallback service for pullrequest_test when called with no parameters *)
let pullrequest_main_service = 
  Eliom_service.Http.service 
    ~path:["pullrequest_test"] 
    ~get_params:Eliom_parameter.unit
    ()

(* ********************************************************************** *)
(* Creation of POST Services                                              *)
(* ********************************************************************** *)

(* Service to submit a job *)
let submitjob_service =
  Eliom_service.Http.post_service
    ~fallback:submitjob_main_service
    ~post_params:
    Eliom_parameter.(string "kind" ** 
                       set string "arg" **
                       file "file")
    ()

(* Service to run the interpreter with an input *)
let interpreter_service =
  Eliom_service.Http.post_service
    ~fallback:interpreter_main_service
    ~post_params:
    Eliom_parameter.(string "kind" ** 
                       set string "arg" ** 
                       file "inputFile" ** 
                       file "csvFile")
    ()

(* Service to run the interpreter without an input *)
let interpreter_input_service =
  Eliom_service.Http.post_service
    ~fallback:interpreter_main_service
    ~post_params:
    Eliom_parameter.(string "kind" ** 
                       set string "arg" ** 
                       file "inputFile")
    ()


let pullrequest_test_service =
  Eliom_service.Http.post_service
    ~fallback: pullrequest_main_service
    ~post_params: Eliom_parameter.raw_post_data ()

(* ********************************************************************** *)
(* Main entry point: Register service handlers                            *)
(* ********************************************************************** *)

(* Registration of services *)
let _ =

  let () =
    log AccessLog
      "Directory for jobs is %s"
      jobs_dir
  in

  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:submitjob_main_service
    main_service_handler;

(*
  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:retrievejob_main_service
    main_service_handler;

  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:canceljob_main_service
    main_service_handler;
*)

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
     interpreter_service_handler;

  (* Register interpreter service handler *)
   Eliom_registration.String.register
     ~service:purge_jobs_service
     purge_jobs_service_handler;

  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:pullrequest_main_service
    pullrequest_main_service_handler;
  
  (* Register pull request service handler *)
   Eliom_registration.Any.register
     pullrequest_test_service
     pullrequest_test_service_handler

