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

open Lib


(* Termination message received *)
exception Terminate

(* ********************************************************************** *)
(* Helper functions                                                       *)
(* ********************************************************************** *)


(* Reduce nodes to cone of influence of property *)
let reduce_nodes_to_coi trans_sys nodes prop_name =

  debug event
    "Reducing to coi for %s"
    prop_name
  in

  (* Name of main node *)
  let main_name = LustreNode.find_main (List.rev nodes) in

  (* Properties are always state variables *) 
  let prop = 
    try TransSys.named_term_of_prop_name trans_sys prop_name
    with Not_found -> assert false
  in 

  (* Undo instantiation of state variable in calling nodes and return
     state variable in scope of node defining it *)
  let instance_of_state_var sv = 
    match LustreExpr.get_state_var_instances sv with
      | [] -> sv 
      | [(_, _, sv')] -> 
        debug event
            "State variable %a is an instance of %a" 
            StateVar.pp_print_state_var sv 
            StateVar.pp_print_state_var sv'
        in
        sv'
      | _ -> 
        debug event
            "State variable %a has more than one instance" 
        StateVar.pp_print_state_var sv
        in
        assert false
  in

  (* Get state variable in scope of main node *)
  let prop' = 
    Term.map
      (function _ -> function 
         | t when Term.is_free_var t -> 
           let v = Term.free_var_of_term t in
           if 
             Var.is_state_var_instance v
           then 
             let o = Var.offset_of_state_var_instance v in
             let sv = Var.state_var_of_state_var_instance v in
             let sv' = instance_of_state_var sv in
             Term.mk_var
               (Var.mk_state_var_instance sv' o)
           else 
             t
         | t -> t)
      prop 
  in

  debug event
    "Property %a contains state variables %a"
    Term.pp_print_term prop'
    (pp_print_list StateVar.pp_print_state_var ",@ ")
    (StateVar.StateVarSet.elements (Term.state_vars_of_term prop'))
  in

  (* Reduce nodes to cone of influence of property *)
  let nodes' = 
    LustreNode.reduce_to_coi 
      nodes
      main_name
      (StateVar.StateVarSet.elements (Term.state_vars_of_term prop'))
  in

  debug event
      "@[<v>Full input:@,%a@,Reduced input for property %a (%a):@,%a@]"
      (pp_print_list (LustreNode.pp_print_node false) "@,")
      nodes
      Term.pp_print_term prop'
      (LustreIdent.pp_print_ident false) main_name
      (pp_print_list (LustreNode.pp_print_node false) "@,")
      nodes'
  in

  (* Return nodes reduced to cone of influence of property *)
  nodes'


(* ********************************************************************** *)
(* Events passed on to callers                                            *)
(* ********************************************************************** *)


(* Messages to be relayed between processes *)
type event = 
  | Invariant of string list * Term.t 
  | PropStatus of string * TransSys.prop_status


(* Pretty-print an event *)
let pp_print_event ppf = function 

  | Invariant (s, t) -> 
    Format.fprintf ppf "@[<hv>Invariant for %a@ %a@]" 
      (pp_print_list Format.pp_print_string ".") s
      Term.pp_print_term t

  | PropStatus (p, TransSys.PropUnknown) -> 
    Format.fprintf ppf "@[<hv>Property %s is unknown@]" p 

  | PropStatus (p, TransSys.PropKTrue k) -> 
    Format.fprintf ppf "@[<hv>Property %s true for %d steps@]" p k

  | PropStatus (p, TransSys.PropInvariant) -> 
    Format.fprintf ppf "@[<hv>Property %s invariant@]" p

  | PropStatus (p, TransSys.PropFalse []) -> 
    Format.fprintf ppf "@[<hv>Property %s false@]" p

  | PropStatus (p, TransSys.PropFalse cex) ->
    Format.fprintf 
      ppf
      "@[<hv>Property %s false at step %d@]" 
      p
      (TransSys.length_of_cex cex)


(* Module as input to Messaging.Make functor *)
module EventMessage = 
struct

  type t = event 

  (* Convert strings to a message *)
  let message_of_strings pop = match pop () with 

    | "INVAR" ->  

      let f = pop () in

      let t = Term.import (Marshal.from_string f 0 : Term.t) in 

      let f = pop () in

      let l = (Marshal.from_string f 0 : string list) in 

      Invariant (l, t)

    | "PROP_UNKNOWN" -> 

      let p = pop () in

      PropStatus (p, TransSys.PropUnknown)

    | "PROP_KTRUE" -> 

      let p = pop () in

      let k = try int_of_string (pop ()) with 
        | Failure _ -> raise Messaging.BadMessage 
      in 

      PropStatus (p, TransSys.PropKTrue k)

    | "PROP_INVAR" -> 

      let p = pop () in

      PropStatus (p, TransSys.PropInvariant)

    | "PROP_FALSE" -> 

      let p = pop () in

      let cex_string = pop () in
      
      let cex : (StateVar.t * Term.t list) list = 
        Marshal.from_string cex_string 0
      in
      
      let cex' =
        List.map
          (fun (sv, t) -> (StateVar.import sv, List.map Term.import t))
          cex
      in

      PropStatus (p, TransSys.PropFalse cex')

    | s -> 

      (debug event 
        "Bad message %s"
        s
       in
       raise Messaging.BadMessage)


  (* Convert a message to strings *)
  let strings_of_message = function 

    | Invariant (s, t) -> 

      (* Serialize term to string *)
      let term_string = Marshal.to_string t [Marshal.No_sharing] in
      
      (* Serialize scope to string *)
      let scope_string = Marshal.to_string s [Marshal.No_sharing] in
      
      [scope_string; term_string; "INVAR"]

    | PropStatus (p, TransSys.PropUnknown) -> 

      [p; "PROP_UNKNOWN"]

    | PropStatus (p, TransSys.PropKTrue k) -> 

      [string_of_int k; p; "PROP_KTRUE"]

    | PropStatus (p, TransSys.PropInvariant) -> 

      [p; "PROP_INVAR"]

    | PropStatus (p, TransSys.PropFalse cex) ->

      (* Serialize counterexample to string *)
      let cex_string = Marshal.to_string cex [Marshal.No_sharing] in
      
      [cex_string; p; "PROP_FALSE"]

  (* Pretty-print a message *)
  let pp_print_message = pp_print_event

end

(* Instantiate messaging system with event messages *)
module EventMessaging = Messaging.Make (EventMessage)


(* ********************************************************************** *)
(* Initialization for the messaging system                                *)
(* ********************************************************************** *)


(* Module currently running *)
let this_module = ref `Parser

(* Set module currently running *)
let set_module mdl = this_module := mdl 

(* Get module currently running *)
let get_module () = !this_module

(* Setup of the messaging: context and sockets of the invariant
   manager, ports to connect to for the workers *)
type messaging_setup = 
  (EventMessaging.ctx * EventMessaging.socket * EventMessaging.socket) * (string * string)

type mthread = EventMessaging.thread

(* Create contexts and bind ports for all processes *)
let setup () = 

  (* Create context for invariant manager *)
  let im_context, (b, m) = EventMessaging.init_im () in

  (* Return contexts *)
  (im_context, (b, m))


(* Start messaging for a process *)
let run_process proc (_, (bcast_port, push_port)) on_exit = 

  (* Initialize messaging for process *)
  let ctx = EventMessaging.init_worker proc bcast_port push_port in

  (* Run messaging for process *)
  EventMessaging.run_worker ctx proc on_exit


(* Start messaging for invariant manager *)
let run_im (ctx, _) pids on_exit = 
  EventMessaging.run_im ctx pids on_exit


(* ********************************************************************** *)
(* Received statistics                                                    *)
(* ********************************************************************** *)


(* Map of kind_module *)
module MdlMap = 
  Map.Make
    (struct 
      type t = kind_module 
      let int_of_kind_module = function
        | `Parser -> -3
        | `Interpreter -> -2
        | `INVMAN -> -1
        | `BMC -> 1
        | `IND -> 2
        | `PDR -> 3
        | `INVGEN -> 4        
        | `INVGENOS -> 5
        | `Interpolator -> 5
          
      let compare m1 m2 = 
        compare (int_of_kind_module m1) (int_of_kind_module m2)
    end)


(* Association list of module to last statistics message *)
let last_stats = ref MdlMap.empty

(* Return last statistics in order *)
let all_stats () = 
  List.rev
    (MdlMap.fold
       (fun mdl stats accum -> (mdl, stats) :: accum)
       !last_stats
       [])
       

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
  | `INVGEN -> "two state invariant generator"
  | `INVGENOS -> "one state invariant generator"
  | `INVMAN -> "invariant manager"
  | `Interpreter -> "interpreter"
  | `Parser -> "parser"
  | `Interpolator -> "interpolator"


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
let proved_pt mdl level trans_sys k prop = 

  (* Only ouptut if status was unknown *)
  if 

    not (TransSys.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then 

    (ignore_or_fprintf level)
      !log_ppf 
      ("@[<hov><Success> Property %s is valid %tby %a after %.3fs.@.@.") 
      prop
      (function ppf -> match k with
         | None -> ()
         | Some k -> Format.fprintf ppf "for k=%d " k)
      pp_print_kind_module_pt mdl
      (Stat.get_float Stat.total_time)

(* Pretty-print a counterexample *)
let pp_print_counterexample_pt level trans_sys prop_name ppf = function

  | [] -> ()

  | cex -> 

    (

      (* Distinguish between input formats *)
      match TransSys.get_source trans_sys with

        (* Lustre input *)
        | TransSys.Lustre nodes ->

          debug event
              "Nodes in transition system: %a"
              (pp_print_list (fun ppf { LustreNode.name } -> LustreIdent.pp_print_ident false ppf name) "@ ") nodes
          in

          (* Reduce nodes to cone of influence of property *)
          let nodes' = reduce_nodes_to_coi trans_sys nodes prop_name in

          (* Output counterexample *)
          Format.fprintf ppf 
            "Counterexample:@,%a"
            (LustrePath.pp_print_path_pt nodes' true) cex

        (* Native input *)
        | TransSys.Native ->

          assert false

      (*
          (* Output counterexample *)
          Format.fprintf ppf 
            "Counterexample:@,%a"
            NativeInput.pp_print_path_pt cex
*)

    )


(* Output execution path without slicing *)
let pp_print_path_pt trans_sys init ppf path = 

  (* Distinguish between input formats *)
  match TransSys.get_source trans_sys with
        
    (* Lustre input *)
    | TransSys.Lustre nodes ->
      
      (* Output path *)
      Format.fprintf ppf 
        "%a"
        (LustrePath.pp_print_path_pt nodes true) path
          
    (* Native input *)
    | TransSys.Native ->

      (*
      
      (* Output path *)
      Format.fprintf ppf 
        "%a"
        NativeInput.pp_print_path_pt path

      *)

      assert false

(* Output execution path as XML *)
let execution_path_pt level trans_sys path = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<v>Execution:@,\
      %a@]@.")
    (pp_print_path_pt trans_sys true) path
  

(* Output disproved property as plain text *)
let disproved_pt mdl level trans_sys prop cex = 

  (* Only ouptut if status was unknown *)
  if 

    not (TransSys.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then 

    (ignore_or_fprintf level)
      !log_ppf 
      ("@[<v><Failure> Property %s is invalid by %a %tafter %.3fs.@,@,%a@]@.") 
      prop
      pp_print_kind_module_pt mdl
      (function ppf -> match cex with
         | [] -> ()
         | ((_, c) :: _) -> Format.fprintf ppf "for k=%d " (List.length c))
      (Stat.get_float Stat.total_time)
      (pp_print_counterexample_pt level trans_sys prop) cex

  else

    (debug event "Status of property %s already known" prop in ())


(* Output statistics section as plain text *)
let stat_pt mdl level stats =

  (ignore_or_fprintf level)
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
let progress_pt mdl level k =

  (ignore_or_fprintf level)
    !log_ppf 
    "@[<v>Progress by %a: %d@]@."
    pp_print_kind_module mdl
    k

(* Pretty-print a list of properties and their status *)
let prop_status_pt level prop_status =


  (ignore_or_fprintf level)
    !log_ppf
    "@[<v>%a@,Summary_of_properties:@,@,%a@,@]@."
    pp_print_hline ()
    (pp_print_list 
       (fun ppf (p, s) -> 
          Format.fprintf 
            ppf
            "@[<h>%s: %a@]"
            p
            (function ppf -> function 
               | TransSys.PropUnknown -> 
                 Format.fprintf ppf "unknown"

               | TransSys.PropKTrue k -> 
                 Format.fprintf ppf "true up to %d steps" k

               | TransSys.PropInvariant -> 
                 Format.fprintf ppf "valid"

               | TransSys.PropFalse [] -> 
                 Format.fprintf ppf "invalid"

               | TransSys.PropFalse cex -> 
                 Format.fprintf 
                   ppf
                   "invalid after %d steps"
                   (TransSys.length_of_cex cex))
            s)
       "@,")
    prop_status
          

(* ********************************************************************** *)
(* XML output                                                             *)
(* ********************************************************************** *)

(* Level to class attribute of log tag *)
let xml_cls_of_level = function
  | L_off -> "off"
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
  | `INVGENOS -> "invgenos"
  | `INVMAN -> "invman"
  | `Interpreter -> "interpreter"
  | `Parser -> "parser"
  | `Interpolator -> "interpolator"


(* Pretty-print kind module as source attribute of log tag *)
let pp_print_kind_module_xml_src ppf m = 
  Format.fprintf ppf "%s" (xml_src_of_kind_module m)


(* XML at the beginning the output *)
let print_xml_header () = 

  Format.fprintf 
    !log_ppf 
    "@[<v><?xml version=\"1.0\"?>@,\
     <Results xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">@]@."


(* XML at the end of the output *)
let print_xml_trailer () = 

  Format.fprintf !log_ppf "</Results>@."


(* Output message as XML *)
let printf_xml mdl level fmt = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<hv 2><Log class=\"%a\" source=\"%a\">@,@[<hov>" ^^ 
       fmt ^^ 
       "@]@;<0 -2></Log>@]@.") 
    pp_print_level_xml_cls level
    pp_print_kind_module_xml_src mdl


(* Output proved property as XML *)
let proved_xml mdl level trans_sys k prop = 

  (* Only ouptut if status was unknown *)
  if 

    not (TransSys.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then 

    (ignore_or_fprintf level)
      !log_ppf 
      ("@[<hv 2><Property name=\"%s\">@,\
        <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
        %t\
        <Answer source=\"%a\">valid</Answer>@;<0 -2>\
        </Property>@]@.") 
      prop
      (Stat.get_float Stat.total_time)
      (function ppf -> match k with 
         | None -> () 
         | Some k -> Format.fprintf ppf "<K>%d</K>@," k)
      pp_print_kind_module_xml_src mdl


(* Pretty-print a counterexample *)
let pp_print_counterexample_xml trans_sys prop_name ppf = function

  | [] -> ()

  | cex -> 

    (

      (* Distinguish between input formats *)
      match TransSys.get_source trans_sys with

        (* Lustre input *)
        | TransSys.Lustre nodes ->

          (* Reduce noes to cone of influence of property *)
          let nodes' = reduce_nodes_to_coi trans_sys nodes prop_name in

          (* Output counterexample *)
          Format.fprintf ppf 
            "@[<hv 2><Counterexample>@,%a@;<0 -2></Counterexample>@]"
            (LustrePath.pp_print_path_xml nodes' true) cex

        (* Native input *)
        | TransSys.Native ->

(*
          (* Output counterexample *)
          Format.fprintf ppf 
            "@[<hv 2><Counterexample>@,%a@;<0 -2></Counterexample>@]"
            NativeInput.pp_print_path_xml cex
*)

          assert false

    )


(* Output execution path without slicing *)
let pp_print_path_xml trans_sys init ppf path = 

  (* Distinguish between input formats *)
  match TransSys.get_source trans_sys with
        
    (* Lustre input *)
    | TransSys.Lustre nodes ->
      
      (* Output path *)
      Format.fprintf ppf 
        "%a"
        (LustrePath.pp_print_path_xml nodes true) path
          
    (* Native input *)
    | TransSys.Native ->
      
(*
      (* Output path *)
      Format.fprintf ppf 
        "%a"
        NativeInput.pp_print_path_xml path
*)

      assert false

(* Output execution path as XML *)
let execution_path_xml level trans_sys path = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<hv 2><Execution>@,\
      %a@;<0 -2>\
      </Execution>@]@.")
    (pp_print_path_xml trans_sys true) path
  

(* Output disproved property as XML *)
let disproved_xml mdl level trans_sys prop cex = 

  (* Only ouptut if status was unknown *)
  if 

    not (TransSys.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then 

    (ignore_or_fprintf level)
      !log_ppf 
      ("@[<hv 2><Property name=\"%s\">@,\
        <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
        %t\
        <Answer source=\"%a\">falsifiable</Answer>@,\
        %a@;<0 -2>\
        </Property>@]@.") 
      prop
      (Stat.get_float Stat.total_time)
      (function ppf -> match cex with 
         | [] -> () 
         | cex -> Format.fprintf ppf "<K>%d</K>@," (TransSys.length_of_cex cex))
      pp_print_kind_module_xml_src mdl
      (pp_print_counterexample_xml trans_sys prop) cex
  

(* Output statistics section as XML *)
let stat_xml mdl level stats =

  (ignore_or_fprintf level)
    !log_ppf
    "@[<hv 2><Stat source=\"%a\">@,%a@;<0 -2></Stat>@]@."
    pp_print_kind_module_xml_src mdl
    (pp_print_list
       (function ppf -> function (section, items) ->
          Format.fprintf ppf 
            "@[<hv 2><Section>@,<name>%s</name>@,%a@;<0 -2></Section>@]"
            section
            Stat.pp_print_stats_xml items)
       "@,")
    stats


(* Output progress as XML *)
let progress_xml mdl level k =

  (ignore_or_fprintf level)
    !log_ppf
    "@[<hv 2><Progress source=\"%a\">%d@;<0 -2></Progress>@]@."
    pp_print_kind_module_xml_src mdl
    k

(* Pretty-print a list of properties and their status *)
let prop_status_xml level prop_status =

  (ignore_or_fprintf level)
    !log_ppf
    "@[<v>%a@]@."
    (pp_print_list 
       (fun ppf (p, s) -> 

          (* Only output properties with status unknonw *)
          if not (TransSys.prop_status_known s) then
            
            Format.fprintf 
              ppf
              "@[<hv 2><Property name=\"%s\">@,\
               @[<hv 2><Answer>@,%a@;<0 -2></Answer>@]@,\
               %a@,\
               @;<0 -2></Property>@]"
              p
              (function ppf -> function 
                 | TransSys.PropUnknown
                 | TransSys.PropKTrue _ -> Format.fprintf ppf "unknown"
                 | TransSys.PropInvariant -> Format.fprintf ppf "valid"
                 | TransSys.PropFalse [] 
                 | TransSys.PropFalse _ -> Format.fprintf ppf "falsifiable")
              s
              (function ppf -> function
                 | TransSys.PropUnknown
                 | TransSys.PropInvariant 
                 | TransSys.PropFalse [] -> ()
                 | TransSys.PropKTrue k -> 
                   Format.fprintf 
                     ppf 
                     "@,@[<hv 2><TrueFor>@,%d@;<0 -2></TrueFor>@]"
                     k
                 | TransSys.PropFalse cex -> 
                   Format.fprintf 
                     ppf 
                     "@,@[<hv 2><FalseAt>@,%d@;<0 -2></FalseAt>@]"
                     (TransSys.length_of_cex cex))
              s)
       "@,")
    prop_status


(* ********************************************************************** *)
(* Relay output to invariant manager                                      *)
(* ********************************************************************** *)


(* Send an event to the log *)
let log (mdl : kind_module) (lvl : log_level) (msg : string) = 

  try 

    (* Send log event message *)
    EventMessaging.send_output_message 
      (EventMessaging.Log (int_of_log_level lvl, msg))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Send message to invariant manager *)
let printf_relay mdl level fmt = 

  Format.kfprintf 
    (function ppf -> 

      let s = Format.flush_str_formatter () in

      if output_on_level level then log mdl level s)

    Format.str_formatter
    fmt


(*
(* Send statistics *)
let stat_relay stats =

  try 

    (* Send statistics message *)
    EventMessaging.send_output_message
      (EventMessaging.Stat (Marshal.to_string stats []))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()

*)

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
let set_log_format_xml () = 

  log_format := F_xml;

  (* Print XML header *)
  print_xml_header ()
               

(* Relay log messages to invariant manager *)
let set_relay_log () = log_format := F_relay


(* ********************************************************************** *)
(* Generic logging functions                                              *)
(* ********************************************************************** *)

(* Log a message with source and log level *)
let log level fmt = 

  let mdl = get_module () in

  match !log_format with 
    | F_pt -> printf_pt mdl level fmt
    | F_xml -> printf_xml mdl level fmt
    | F_relay -> printf_relay mdl level fmt


(* Log a message with source and log level *)
let log_proved mdl level trans_sys k prop =
  match !log_format with 
    | F_pt -> proved_pt mdl level trans_sys k prop
    | F_xml -> proved_xml mdl level trans_sys k prop
    | F_relay -> ()


(* Log a message with source and log level *)
let log_disproved mdl level trans_sys prop cex =
  match !log_format with 
    | F_pt -> disproved_pt mdl level trans_sys prop cex 
    | F_xml -> disproved_xml mdl level trans_sys prop cex
    | F_relay -> ()


(* Log an exection path *)
let log_execution_path mdl level trans_sys path =

  (match !log_format with 
    | F_pt -> execution_path_pt level trans_sys path
    | F_xml -> execution_path_xml level trans_sys path 
    | F_relay -> ())


(* Output summary of status of properties *)
let log_prop_status level prop_status =
  match !log_format with 
    | F_pt -> prop_status_pt level prop_status
    | F_xml -> prop_status_xml level prop_status
    | F_relay -> ()


(* Output statistics of a section of a source *)
let log_stat mdl level stats =

  match !log_format with 
    | F_pt -> stat_pt mdl level stats
    | F_xml -> stat_xml mdl level stats
    | F_relay -> ()
  

(* Output progress indicator of a source *)
let log_progress mdl level k = 
  match !log_format with 
    | F_pt -> ()
    | F_xml -> progress_xml mdl level k
    | F_relay -> ()
  

(* Terminate log output *)
let terminate_log () = 
  match !log_format with 
    | F_pt -> ()
    | F_xml -> print_xml_trailer ()
    | F_relay -> ()


(* ********************************************************************** *)
(* Events                                                                 *)
(* ********************************************************************** *)


(* Broadcast a scoped invariant *)
let invariant scope term = 
  
  try
    
    (* Send invariant message *)
    EventMessaging.send_relay_message (Invariant (scope, term))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a property status *)
let prop_status status trans_sys prop = 
  
  let mdl = get_module () in

  (match status with
    | TransSys.PropInvariant -> log_proved mdl L_warn trans_sys None prop
    | TransSys.PropFalse cex -> log_disproved mdl L_warn trans_sys prop cex
    | _ -> ());

  (* Update status of property in transition system *)
  TransSys.set_prop_status trans_sys prop status;

  try
    
    (* Send invariant message *)
    EventMessaging.send_relay_message (PropStatus (prop, status))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a counterexample for some properties *)
let execution_path trans_sys path = 

  let mdl = get_module () in

  log_execution_path mdl L_warn trans_sys path


(* Send progress indicator *)
let progress k =

  let mdl = get_module () in

  log_progress mdl L_info k;

  try 

    (* Send progress message *)
    EventMessaging.send_output_message
         (EventMessaging.Progress k)

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Send statistics *)
let stat stats = 

  let mdl = get_module () in

  log_stat mdl L_info stats;

  try

    (* Send message *)
    EventMessaging.send_output_message
      (EventMessaging.Stat (Marshal.to_string stats []))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()
  

(*


(* Broadcast a disproved property *)
let disproved mdl k prop = 

  (* Output property as disproved *)
  log_disproved mdl k prop;

  try

    (* Send invariant message *)
    EventMessaging.send_relay_message
      (match k with 
        | None -> PropStatus (prop, PropFalse) 
        | Some k -> PropStatus (prop, PropKFalse k))


  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a proved property as an invariant *)
let proved mdl k (prop, term) = 

  (* Output property as proved *)
  log_proved mdl k prop;

  try

    (* Send invariant message *)
    EventMessaging.send_relay_message (PropStatus (prop, PropInvariant))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast status of BMC *)
let bmcstate k props = ()

(*
  try

    (* Send BMC status message *)
    Messaging.send 
      (Messaging.InductionMessage 
         (Messaging.BMCSTATE (k, props)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()
*)

*)


(* Broadcast termination message *)
let terminate () = 

  try

    (* Send termination message *)
    EventMessaging.send_term_message ();

    minisleep 0.1

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()



(* ********************************************************************** *)
(* Receiving events                                                       *)
(* ********************************************************************** *)


(* Receive all queued messages *)
let recv () = 

  Stat.update_time Stat.total_time;
  
  try

    List.rev
      (List.fold_left 
         (function accum -> 
           (function 

             (* Terminate on TERM message *)
             | (_, EventMessaging.ControlMessage EventMessaging.Terminate) -> 

               raise Terminate

             (* Drop other control messages *)
             | _, EventMessaging.ControlMessage _ -> accum 

             (* Output log message *)
             | mdl, 
               EventMessaging.OutputMessage (EventMessaging.Log (lvl, msg)) ->

               log (log_level_of_int lvl) "%s" msg; 

               (* No relay message *)
               accum

             (* Output statistics *)
             | mdl, EventMessaging.OutputMessage (EventMessaging.Stat stats) -> 

               (* Unmarshal statistics *)
               let stats : (string * Stat.stat_item list) list = 
                 Marshal.from_string stats 0
               in

               (* Output on log levels info and below *)
               log_stat mdl L_debug stats;

               (* Store last received statistics *)
               last_stats := MdlMap.add mdl stats !last_stats;

               (* No relay message *)
               accum

             (* Output progress *)
             | mdl, EventMessaging.OutputMessage (EventMessaging.Progress k) -> 

               log_progress mdl L_info k;

               (* No relay message *)
               accum

             (* Return event message *)
             | mdl, EventMessaging.RelayMessage (_, msg) ->

               (* Return relay message *)
               (mdl, msg) :: accum

           )
         )
         []
         (EventMessaging.recv ()))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> []

(* Terminates if a termination message was received. Does NOT modified
   received messages. *)
let check_termination () =
  if EventMessaging.check_termination ()
  then raise Terminate else ()


(* Update transition system from event list *)
let update_trans_sys_sub trans_sys events = 

  (* Tail-recursive iteration *)
  let rec update_trans_sys' trans_sys invars prop_status = function 

    (* No more events, return new invariants and changed property status *)
    | [] -> (invars, prop_status)

    (* Invariant discovered *)
    | (m, Invariant (s, t)) :: tl -> 

      (* Property status if received invariant is a property *)
      let tl' =
        List.fold_left

          (fun accum (p, t') -> 

             (* Invariant is equal to property term? *)
             if Term.equal t t' then

               (* Inject property status event *)
               ((m, PropStatus (p, TransSys.PropInvariant)) :: accum)

             else

               accum)

          tl
          (TransSys.props_list_of_bound trans_sys Numeral.zero)

      in
      
      (* Add invariant to transtion system *)
      TransSys.add_scoped_invariant trans_sys s t ;

      (* Continue with invariant added to accumulator *)
      update_trans_sys'
        trans_sys
        ((m, (s, t)) :: invars)
        prop_status
        tl'

    (* Property found unknown *)
    | (_, PropStatus (p, TransSys.PropUnknown)) :: tl -> 

      (* Continue without changes *)
      update_trans_sys' trans_sys invars prop_status tl

    (* Property found true for k steps *)
    | (m, PropStatus (p, (TransSys.PropKTrue k as s))) :: tl -> 

      (* Change property status in transition system *)
      TransSys.set_prop_ktrue trans_sys k p;

      (* Continue with propert status added to accumulator *)
      update_trans_sys'
        trans_sys
        invars
        ((m, (p, s)) :: prop_status) 
        tl

    (* Property found invariant *)
    | (m, PropStatus (p, (TransSys.PropInvariant as s))) :: tl -> 

      (* Output proved property *)
      log_proved m L_warn trans_sys None p;
          
      (* Change property status in transition system *)
      TransSys.set_prop_invariant trans_sys p;

      (try 

         (* Add proved property as invariant *)
        TransSys.add_invariant 
          trans_sys
          (List.assoc p (TransSys.props_list_of_bound trans_sys Numeral.zero))

       (* Skip if named property not found *)
       with Not_found -> ());

      (* Continue with property status added to accumulator *)
      update_trans_sys'
        trans_sys 
        invars
        ((m, (p, s)) :: prop_status)
        tl

    (* Property found false *)
    | (m, PropStatus (p, (TransSys.PropFalse cex as s))) :: tl -> 

      (* Output disproved property *)
      log_disproved m L_warn trans_sys p cex;

      (* Change property status in transition system *)
      TransSys.set_prop_false trans_sys p cex;

      (* Continue with property status added to accumulator *)
      update_trans_sys' 
        trans_sys
        invars
        ((m, (p, s)) :: prop_status) 
        tl

  in

  update_trans_sys' trans_sys [] [] events


(* Filter list of invariants with their scope for invariants of empty
   (top) scope *)
let top_invariants_of_invariants sys invariants = 

  let top = TransSys.get_scope sys in

  (* Only keep invariants with empty scope *)
  (List.fold_left
     (fun accum (_, (scope, t)) ->
      if scope = top then t :: accum else accum)
     []
     invariants)
     
  (* Return in original order *)
  |> List.rev

let update_trans_sys trans_sys events =
  match
    (* Calling the scoped update function. *)
    update_trans_sys_sub trans_sys events
  with
  | invs,valids ->
    (* Filtering top level invariants. *)
    top_invariants_of_invariants trans_sys invs, valids


let exit t = EventMessaging.exit t


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
