(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Lib


(* Termination message received *)
exception Terminate


(* ********************************************************************** *)
(* Events passed on to callers                                            *)
(* ********************************************************************** *)


(* Events exposed to the processes *)
type event = 
  | Invariant of kind_module * Term.t 
  | Proved of kind_module * string 
  | Disproved of kind_module * string 
  | BMCState of int * (string list)


(* Pretty-print a message *)
let pp_print_event ppf = function 

  | Invariant (m, t) -> 

    Format.fprintf 
      ppf 
      "@[<hv>Invariant@ %a@ by %a@]" 
      Term.pp_print_term t
      pp_print_kind_module m

  | Proved (m, p) -> 
    Format.fprintf 
      ppf 
      "@[<hv>Proved@ %s@ by %a@]" 
      p 
      pp_print_kind_module m

  | Disproved (m, p) -> 
    Format.fprintf 
      ppf 
      "@[<hv>Disproved@ %s@ by %a@]" 
      p 
      pp_print_kind_module m

  | BMCState (k, p) -> 
    Format.fprintf ppf 
      "@[<hv>BMC status@ k=%d@ %a@]" 
      k 
      (pp_print_list Format.pp_print_string ",@ ") p


(* ********************************************************************** *)
(* Log levels                                                             *)
(* ********************************************************************** *)


(* Levels of log messages *)
type log_level =
  | L_off
  | L_fatal
  | L_error
  | L_warn
  | L_info
  | L_debug
  | L_trace


(* Associate an integer with each level to induce a total ordering *)
let int_of_log_level = function 
  | L_off -> -1 
  | L_fatal -> 0
  | L_error -> 1
  | L_warn -> 2
  | L_info -> 3
  | L_debug -> 4
  | L_trace -> 5

let log_level_of_int = function 
  | -1 -> L_off 
  | 0 -> L_fatal
  | 1 -> L_error
  | 2 -> L_warn
  | 3 -> L_info
  | 4 -> L_debug
  | 5 -> L_trace
  | _ -> raise (Invalid_argument "log_level_of_int")

(* Compare two levels *)
let compare_levels l1 l2 = 
  Pervasives.compare (int_of_log_level l1) (int_of_log_level l2)


(* Current log level *)
let log_level = ref L_warn


(* Set log level *)
let set_log_level l = log_level := l


(* Level is of higher or equal priority than current log level? *)
let output_on_level level = compare_levels level !log_level <= 0


(* Return Format.fprintf if level is is of higher or equal priority
   than current log level, otherwise return Format.ifprintf *)
let ignore_or_fprintf level = 
  if output_on_level level then Format.fprintf else Format.ifprintf


(* ********************************************************************** *)
(* Output target                                                          *)  
(* ********************************************************************** *)


(* Current formatter for output *)
let log_ppf = ref Format.std_formatter


(* Set file to write log messages to *)
let log_to_file f = 

  (* Open channel to logfile *)
  let oc = 
    try open_out f with
      | Sys_error _ -> failwith "Could not open logfile"
  in 
  
  (* Create and store formatter for logfile *)
  log_ppf := Format.formatter_of_out_channel oc


(* Write messages to standard output *)
let log_to_stdout () = log_ppf := Format.std_formatter


(* ********************************************************************** *)
(* Plain text output                                                      *)
(* ********************************************************************** *)


(* Level as string for plain text output *)
let pt_string_of_level = function 
  | L_off -> assert false
  | L_fatal -> "FATAL"
  | L_error -> "ERROR"
  | L_warn -> "WARNING"
  | L_info -> "INFO"
  | L_debug -> "DEBUG"
  | L_trace -> "TRACE"


(* Pretty-print level for plain text output *)
let pp_print_level_pt ppf l = Format.fprintf ppf "%s" (pt_string_of_level l)


(* Kind module as string for plain text output *)
let pt_string_of_kind_module = function
  | `PDR -> "PDR"
  | `BMC -> "BMC"
  | `IND -> "inductive step"
  | `INVGEN -> "invariant generator"
  | `INVMAN -> "invariant manager"
  | `Interpreter -> "interpreter"


(* Pretty-print kind module  for plain text output *)
let pp_print_kind_module_pt ppf m = 
  Format.fprintf ppf "%s" (pt_string_of_kind_module m)


(* Output message as plain text *)
let printf_pt mdl level fmt = 

  (ignore_or_fprintf level)
    !log_ppf 
    (* ("@[<hov>%a (%a):@ " ^^ fmt ^^ "@]@.@.") *)
    ("@[<hov>" ^^ fmt ^^ "@]@.@.") 
    (* pp_print_level_pt level *)
    (* pp_print_kind_module_pt mdl *)
    

(* Output proved property as plain text *)
let proved_pt mdl prop = 

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hov>Success: Property %s is valid in %a@.@.") 
    prop
    pp_print_kind_module_pt mdl


(* Output disproved property as plain text *)
let disproved_pt mdl prop = 

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hov>Failure: Property %s is invalid in %a@.@.") 
    prop
    pp_print_kind_module_pt mdl


(* Output statistics section as plain text *)
let stat_pt mdl stats =

  Format.fprintf 
    !log_ppf 
    "@[<v>Statistics for %a@,@,%a@]@."
    pp_print_kind_module mdl
    (pp_print_list
       (function ppf -> function (section, items) -> 
          Format.fprintf ppf "[%s]@,%a@," 
            section
            Stat.pp_print_stats items)
       "@,")
    stats



(* Output statistics section as plain text *)
let progress_pt mdl k =

  Format.fprintf 
    !log_ppf 
    "@[<v>Progress in %a: %d@]@."
    pp_print_kind_module mdl
    k

(* ********************************************************************** *)
(* XML output                                                             *)
(* ********************************************************************** *)


(* Level to class attribute of log tag *)
let xml_cls_of_level = function
  | L_off -> assert false
  | L_fatal -> "fatal"
  | L_error -> "error"
  | L_warn -> "warn"
  | L_info -> "info"
  | L_debug -> "debug"
  | L_trace -> "trace"
  

(* Pretty-print level as class attribute of log tag *)
let pp_print_level_xml_cls ppf l = 
  Format.fprintf ppf "%s" (xml_cls_of_level l)


(* Kind module as source attribute of log tag *)
let xml_src_of_kind_module = function
  | `PDR -> "pdr"
  | `BMC -> "bmc"
  | `IND -> "indstep"
  | `INVGEN -> "invgen"
  | `INVMAN -> "invman"
  | `Interpreter -> "interpreter"


(* Pretty-print kind module as source attribute of log tag *)
let pp_print_kind_module_xml_src ppf m = 
  Format.fprintf ppf "%s" (xml_src_of_kind_module m)


(* Output message as XML *)
let printf_xml mdl level fmt = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<hv 2><log class=\"%a\" source=\"%a\">@,@[<hov>" ^^ 
       fmt ^^ 
       "@]@;<0 -2></log>@]@.") 
    pp_print_level_xml_cls level
    pp_print_kind_module_xml_src mdl


(* Output proved property as XML *)
let proved_xml mdl prop = 

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hv 2><property name=\"%s\">@,\
      <answer source=\"%a\">valid</answer>@;<0 -2>\
      </property>@]@.") 
    prop
    pp_print_kind_module_xml_src mdl


(* Output disproved property as XML*)
let disproved_xml mdl prop = 

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hv 2><property name=\"%s\">@,\
      <answer source=\"%a\">invalid</answer>@;<0 -2>\
      </property>@]@.") 
    prop
    pp_print_kind_module_xml_src mdl
  

(* Output statistics section as XML *)
let stat_xml mdl stats =

  Format.fprintf
    !log_ppf
    "@[<hv 2><stat source=\"%a\">@,%a@;<0 -2></stat>@]@."
    pp_print_kind_module_xml_src mdl
    (pp_print_list
       (function ppf -> function (section, items) ->
          Format.fprintf ppf 
            "@[<hv 2><section>@,<name>%s</name>@,%a@;<0 -2></section>@]"
            section
            Stat.pp_print_stats_xml items)
       "@,")
    stats


(* Output progress as XML *)
let progress_xml mdl k =

  Format.fprintf
    !log_ppf
    "@[<hv 2><progress source=\"%a\">%d@;<0 -2></stat>@]@."
    pp_print_kind_module_xml_src mdl
    k


(* ********************************************************************** *)
(* Relay output to invariant manager                                      *)
(* ********************************************************************** *)


(* Send an event to the log *)
let log (mdl : kind_module) (lvl : log_level) (msg : string) = 

  try 

    (* Send log event message *)
    Messaging.send 
      (Messaging.UserMessage (Messaging.Log (int_of_log_level lvl, msg)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Send message to invariant manager *)
let printf_relay mdl level fmt = 

  Format.kfprintf 
    (function ppf -> 

      let s = Format.flush_str_formatter () in

      if compare_levels level !log_level > 0 then () else
        log mdl level s)

    Format.str_formatter
    fmt


(* Send statistics *)
let stat_relay stats =

  try 

    (* Send statistics message *)
    Messaging.send 
      (Messaging.UserMessage 
         (Messaging.Stat (Marshal.to_string stats [])))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Send progress indicator *)
let progress_relay k =

  try 

    (* Send progress message *)
    Messaging.send 
      (Messaging.UserMessage 
         (Messaging.Progress k))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* ********************************************************************** *)
(* State of the logger                                                    *)
(* ********************************************************************** *)


(* Log formats *)
type log_format = 
  | F_pt
  | F_xml
  | F_relay


(* Current log format *)
let log_format = ref F_pt

(* Set log format to plain text *)
let set_log_format_pt () = log_format := F_pt

(* Set log format to XML *)
let set_log_format_xml () = log_format := F_xml

(* Relay log messages to invariant manager *)
let set_relay_log () = log_format := F_relay


(* ********************************************************************** *)
(* Generic logging functions                                              *)
(* ********************************************************************** *)

(* Log a message with source and log level *)
let log mdl level fmt = 
  match !log_format with 
    | F_pt -> printf_pt mdl level fmt
    | F_xml -> printf_xml mdl level fmt
    | F_relay -> printf_relay mdl level fmt


(* Log a message with source and log level *)
let log_proved mdl prop =
  match !log_format with 
    | F_pt -> proved_pt mdl prop
    | F_xml -> proved_xml mdl prop
    | F_relay -> ()


(* Log a message with source and log level *)
let log_disproved mdl prop =
  match !log_format with 
    | F_pt -> disproved_pt mdl prop
    | F_xml -> disproved_xml mdl prop
    | F_relay -> ()


(* Output statistics of a section of a source *)
let stat mdl stats =
  match !log_format with 
    | F_pt -> stat_pt mdl stats
    | F_xml -> stat_xml mdl stats
    | F_relay -> stat_relay stats
  

(* Output progress indicator of a source *)
let progress mdl k = 
  match !log_format with 
    | F_pt -> ()
    | F_xml -> progress_xml mdl k
    | F_relay -> progress_relay k
  

(* ********************************************************************** *)
(* Initialization for the messaging system                                *)
(* ********************************************************************** *)


(* Setup of the messaging: context and sockets of the invariant
   manager, ports to connect to for the workers *)
type messaging_setup = 
  (Messaging.ctx * Messaging.socket * Messaging.socket) * (string * string)

type mthread = Messaging.thread

(* Create contexts and bind ports for all processes *)
let setup () = 

  (* Create context for invariant manager *)
  let im_context, (b, m) = Messaging.init_im () in

  (* Return contexts *)
  (im_context, (b, m))


(* Start messaging for a process *)
let run_process proc (_, (bcast_port, push_port)) on_exit = 

  (* Initialize messaging for process *)
  let ctx = Messaging.init_worker proc bcast_port push_port in

  (* Run messaging for process *)
  Messaging.run_worker ctx proc on_exit


(* Start messaging for invariant manager *)
let run_im (ctx, _) pids on_exit = 
  Messaging.run_im ctx pids on_exit


(* ********************************************************************** *)
(* Events                                                                 *)
(* ********************************************************************** *)


(* Broadcast an invariant *)
let invariant mdl (term : Term.t) = 
  
  (* Serialize term to string *)
  let term_string = Marshal.to_string term [Marshal.No_sharing] in

  try
    
    (* Send invariant message *)
    Messaging.send 
      (Messaging.InvariantMessage 
         (Messaging.INVAR (term_string, 0)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a disproved property *)
let disproved mdl prop = 

  (* Output property as disproved *)
  log_disproved mdl prop;

  try

    (* Send invariant message *)
    Messaging.send 
      (Messaging.InvariantMessage 
         (Messaging.DISPROVED (prop, 0)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a proved property as an invariant *)
let proved mdl (prop, term) = 

  (* Output property as proved *)
  log_proved mdl prop;

  try

    (* Send invariant message *)
    Messaging.send 
      (Messaging.InvariantMessage 
         (Messaging.PROVED (prop, 0)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast status of BMC *)
let bmcstate k props =

  try

    (* Send BMC status message *)
    Messaging.send 
      (Messaging.InductionMessage 
         (Messaging.BMCSTATE (k, props)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast termination message *)
let terminate () = 

  try

    (* Send termination message *)
    Messaging.send (Messaging.ControlMessage Messaging.TERM);

    minisleep 0.1

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()



(* ********************************************************************** *)
(* Receiving events                                                       *)
(* ********************************************************************** *)


(* Receive all queued messages *)
let recv () = 

  try

    List.fold_left 
      (function accum -> 
        (function 

          (* Terminate on TERM message *)
          | _, Messaging.ControlMessage Messaging.TERM -> raise Terminate

          | mdl, Messaging.UserMessage (Messaging.Log (lvl, msg)) ->

            (debug event 
                "Received LOG message %s"
                msg
             in
             
             log mdl (log_level_of_int lvl) "%s" msg; 
             
             accum)

          | mdl, Messaging.UserMessage (Messaging.Stat stats) -> 

            stat 
              mdl 
              (Marshal.from_string stats 0 : 
                 (string * Stat.stat_item list) list);

            accum

          | mdl, Messaging.UserMessage (Messaging.Progress k) -> 

            progress mdl k;

            accum

          (* Drop control messages *)
          | _, Messaging.ControlMessage _ 
          | _, Messaging.CounterexampleMessage _ 
          | _, Messaging.InvariantMessage (Messaging.RESEND _) -> accum 

          (* Pass BMC status messages *)
          | _, Messaging.InductionMessage (Messaging.BMCSTATE (k, props)) -> 

            BMCState (k, props) :: accum

          (* Pass invariant messages as term without serial number *)
          | mdl, Messaging.InvariantMessage (Messaging.INVAR (f, _)) ->

            (* Hashcons term *)
            let t = Term.import (Marshal.from_string f 0 : Term.t) in 

            Invariant (mdl, t) :: accum

          (* Pass disproved messages as string without serial number *)
          | mdl, Messaging.InvariantMessage (Messaging.PROVED (p, _)) ->

            Proved (mdl, p) :: accum

          (* Pass disproved messages as string without serial number *)
          | mdl, Messaging.InvariantMessage (Messaging.DISPROVED (p, _)) ->

            Disproved (mdl, p) :: accum

        )
      )
      []
      (List.rev (Messaging.recv ()))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> []


let exit t = Messaging.exit t


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
