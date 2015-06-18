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

(** Web service for pullrequest testing from github's webhooks

    @author Alain Mebsout **)


open Lwt


(* Logging *)


(* Server logfiles *)
type server_log = 
  | AccessLog
  | ErrorLog
  | WarningLog


(* Log a message to the given logfile *)
let log l fmt =

  (* Create buffer for output of message *)
  let b = Buffer.create 80 in

  (* Formatter printing into the buffer *)
  let ppf = Format.formatter_of_buffer b in

  (* Continuation after printing to formatter *)
  let k ppf =

    (* Flush the pretty-printer to the buffer *)
    Format.pp_print_flush ppf ();

    (* Get string contents of buffer *)
    let s = Buffer.contents b in

    (* Write string as log message to the chosen logfile *)
    match l with 
      | AccessLog -> Ocsigen_messages.accesslog s
      | ErrorLog -> Ocsigen_messages.errlog s
      | WarningLog -> Ocsigen_messages.warning s

  in

  (* Print message to log with continuation *)
  Format.kfprintf k ppf fmt


(* ********************************************************************** *)
(* Service handlers                                                       *)
(* ********************************************************************** *)

let pullrequest_main_service_handler () () = 
  Lwt.return ("Pullrequest testing url", "text/plain")


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

      let clone_url = json |> member "repository"
                      |> member "clone_url" |> to_string in
      let pr_nb = pr |> member "number" |> to_int in
      let statuses_url = pr |> member "statuses_url" |> to_string in
      let html_url = pr |> member "html_url" |> to_string in
      let pr_user = pr |> member "user" |> member "login" |> to_string in
      let sha = pr |> member "head" |> member "sha" |> to_string in
      let base_sha = pr |> member "base" |> member "sha" |> to_string in

      (* Execute command on cvc cluster through ssh.
         The user ocsigen must have an ssh key that is only allowed to run 
         the neessary command, here we just pass the arguments. *)
      let cmd = Format.sprintf
          "ssh -i /var/lib/ocsigenserver/.ssh/id_rsa_restricted \
           amebsout@@cvc.cs.uiowa.edu \
           \"%d %s %s %s %s %s %s\" &"
          pr_nb base_ref statuses_url html_url clone_url sha base_sha
      in

      log AccessLog
        "Pullrequest hook: Sending command %s."
        cmd;
      
      if Sys.command cmd = 0 then
        send_success ()
      else
        send_error ~code:400 "Could not contact CVC cluster"

    | "closed" when base_ref = "develop" && pr |> member "merged" |> to_bool ->

      (* Execute command on cvc cluster through ssh.
         The user ocsigen must have an ssh key that is only allowed to run 
         the neessary command, here we just pass the arguments. *)
      let cmd =
        "ssh -i /var/lib/ocsigenserver/.ssh/id_rsa_gendoc \
           amebsout@@cvc.cs.uiowa.edu \"0\" &"
      in

      log AccessLog
        "Pullrequest hook on merge: Sending command to generate ocamldoc %s."
        cmd;
      
      if Sys.command cmd = 0 then
        send_success ()
      else
        send_error ~code:400 "Could not contact CVC cluster"


    | _ -> send_success_str "Hook ignores pull request"


(* ********************************************************************** *)
(* Creation of GET Services                                               *)
(* ********************************************************************** *)

(* Fallback service for pullrequest_test when called with no parameters *)
let pullrequest_main_service = 
  Eliom_service.Http.service 
    ~path:["pullrequest_test"] 
    ~get_params:Eliom_parameter.unit
    ()

(* ********************************************************************** *)
(* Creation of POST Services                                              *)
(* ********************************************************************** *)

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
      "Setting pullrequest hooks"
  in

  (* Register main service as fallback *)
  Eliom_registration.String.register
    ~service:pullrequest_main_service
    pullrequest_main_service_handler;
  
  (* Register pull request service handler *)
   Eliom_registration.Any.register
     pullrequest_test_service
     pullrequest_test_service_handler

