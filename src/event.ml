(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

open Pretty
open Lib

module TSet = Term.TermSet
module SMap = Scope.Map

include Log

(* Termination message received *)
exception Terminate

(* Indicates an [AnalysisStart] tag has been printed but [AnalysisStop] was
   not. *)
let analysis_start_not_closed = ref false



(* ********************************************************************** *)
(* Events passed on to callers                                            *)
(* ********************************************************************** *)


(* Warning issued if model reconstruction triggers a division by zero. *)
let div_by_zero_text prop_name = [
  "Division by zero detected in model reconstruction." ;
  Format.sprintf
    "Counterexample for property \"%s\" may be inconsistent."
    prop_name
]

(* Messages to be relayed between processes *)
type event = 
  | Invariant of string list * Term.t * Certificate.t * bool
  | PropStatus of string * Property.prop_status
  | StepCex of string * (StateVar.t * Model.value list) list


(* Pretty-print an event *)
let pp_print_event ppf = function 

  | Invariant (s, t, _, two_state) -> 
    Format.fprintf ppf "@[<hv>Invariant for %a%s@ %a@]"
      (pp_print_list Format.pp_print_string ".") s
      (if two_state then " (2-state)" else "")
      Term.pp_print_term t

  | PropStatus (p, Property.PropUnknown) -> 
    Format.fprintf ppf "@[<hv>Property %s is unknown@]" p 

  | PropStatus (p, Property.PropKTrue k) -> 
    Format.fprintf ppf "@[<hv>Property %s true for %d steps@]" p k

  | PropStatus (p, Property.PropInvariant (k, _)) -> 
    Format.fprintf ppf "@[<hv>Property %s invariant (%d-inductive)@]" p k

  | PropStatus (p, Property.PropFalse []) -> 
    Format.fprintf ppf "@[<hv>Property %s false@]" p

  | PropStatus (p, Property.PropFalse cex) ->
    Format.fprintf 
      ppf
      "@[<hv>Property %s false at step %d@]" 
      p
      ((Property.length_of_cex cex) - 1)

  | StepCex (p, cex) ->
    Format.fprintf 
      ppf
      "@[<hv>Step cex for property %s at step %d@]" 
      p
      (Property.length_of_cex cex)


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

      let f = pop () in

      let phi = Term.import (Marshal.from_string f 0 : Term.t) in 

      let k = try int_of_string (pop ()) with 
        | Failure _ -> raise Messaging.BadMessage 
      in

      let ts = (Marshal.from_string (pop ()) 0 : bool) in

      Invariant (l, t, (k, phi), ts)

    | "PROP_UNKNOWN" -> 

      let p = pop () in

      PropStatus (p, Property.PropUnknown)

    | "PROP_KTRUE" -> 

      let p = pop () in

      let k = try int_of_string (pop ()) with 
        | Failure _ -> raise Messaging.BadMessage 
      in 

      PropStatus (p, Property.PropKTrue k)

    | "PROP_INVAR" -> 

      let p = pop () in

      let k = try int_of_string (pop ()) with 
        | Failure _ -> raise Messaging.BadMessage 
      in 

      let f = pop () in

      let phi = Term.import (Marshal.from_string f 0 : Term.t) in 

      PropStatus (p, Property.PropInvariant (k, phi))

    | "PROP_FALSE" -> 

      let p = pop () in

      let cex_string = pop () in
      
      let cex : (StateVar.t * Model.value list) list = 
        Marshal.from_string cex_string 0
      in
      
      let cex' =
        List.map
          (fun (sv, t) -> 
             (StateVar.import sv, 
              List.map Model.import_value t))
          cex
      in

      PropStatus (p, Property.PropFalse cex')

    | "STEP_CEX" -> 

      let p = pop () in

      let cex_string = pop () in
      
      let cex : (StateVar.t * Model.value list) list = 
        Marshal.from_string cex_string 0
      in
      
      let cex' =
        List.map
          (fun (sv, t) -> 
             (StateVar.import sv, 
              List.map Model.import_value t))
          cex
      in

      StepCex (p, cex')

    | s -> 

      Debug.event "Bad message %s" s;
      raise Messaging.BadMessage


  (* Convert a message to strings *)
  let strings_of_message = function 

    | Invariant (s, t, (k, phi), two_state) ->

      (* Serialize term to string *)
      let term_string = Marshal.to_string t [Marshal.No_sharing] in

      (* Serialize term to string *)
      let phi_string = Marshal.to_string phi [Marshal.No_sharing] in
      
      (* Serialize scope to string *)
      let scope_string = Marshal.to_string s [Marshal.No_sharing] in

      (* Serialize two state flag to string. *)
      let ts_string = Marshal.to_string two_state [Marshal.No_sharing] in
      
      [
        ts_string ;
        string_of_int k ;
        phi_string ;
        scope_string ;
        term_string ;
        "INVAR"
      ]

    | PropStatus (p, Property.PropUnknown) -> 

      [p; "PROP_UNKNOWN"]

    | PropStatus (p, Property.PropKTrue k) -> 

      [string_of_int k; p; "PROP_KTRUE"]

    | PropStatus (p, Property.PropInvariant (k, phi)) -> 

      (* Serialize term to string *)
      let phi_string = Marshal.to_string phi [Marshal.No_sharing] in
      
      [phi_string; string_of_int k; p; "PROP_INVAR"]

    | PropStatus (p, Property.PropFalse cex) ->

      (* Serialize counterexample to string *)
      let cex_string = Marshal.to_string cex [Marshal.No_sharing] in
      
      [cex_string; p; "PROP_FALSE"]

    | StepCex (p, cex) ->

      (* Serialize counterexample to string *)
      let cex_string = Marshal.to_string cex [Marshal.No_sharing] in
      
      [cex_string; p; "STEP_CEX"]

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


(* Kind module as string for plain text output *)
let pt_string_of_kind_module =
  Format.asprintf "%a" pp_print_kind_module


(* Pretty-print kind module for plain text output *)
let pp_print_kind_module_pt =
  pp_print_kind_module


(* Output message as plain text *)
let printf_pt mdl level fmt =
  (ignore_or_fprintf level)
    !log_ppf ("%a @[<hov>" ^^ fmt ^^ "@]@.@.") tag_of_level level


(* Unconditional printing as plain text. *)
let printf_pt_uncond mdl fmt =
  Format.fprintf !log_ppf ("@[<hov>" ^^ fmt ^^ "@]@.@.@?")



(* Output proved property as plain text *)
let proved_pt mdl level trans_sys k prop = 

  (* Only ouptut if status was unknown *)
  if 

    not (Property.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then 

    (ignore_or_fprintf level)
      !log_ppf
      ("@[<hov>%t %s @{<blue_b>%s@} is valid %tby %a after %.3fs.@.@.")
      success_tag
      (if TransSys.is_candidate trans_sys prop then
         "Candidate" else "Property")
      prop
      (function ppf -> match k with
         | None -> ()
         | Some k -> Format.fprintf ppf "for k=%d " k)
      pp_print_kind_module_pt mdl
      (Stat.get_float Stat.analysis_time)

(* Pretty-print a counterexample *)
let pp_print_counterexample_pt 
  level input_sys analysis trans_sys prop_name disproved ppf
= function
| [] -> ()
| cex -> (
  (* Get property by name *)
  let prop =
    TransSys.property_of_name trans_sys prop_name
  in

  (* Slice counterexample and transitions system to property *)
  let trans_sys, instances, cex, prop_term, input_sys =
    InputSystem.slice_to_abstraction_and_property
      input_sys
      analysis
      trans_sys
      cex
      prop
  in

  (* Output counterexample *)
  Format.fprintf ppf 
    "@{<red>Counterexample@}:@,  @[<v>%a@]"
    (InputSystem.pp_print_path_pt input_sys trans_sys instances disproved)
    (Model.path_of_list cex)
)


(* Output execution path without slicing *)
let pp_print_path_pt input_sys _ trans_sys init ppf path = 

  (* Output path *)
  Format.fprintf ppf 
    "%a"
    (InputSystem.pp_print_path_pt input_sys trans_sys [] true)
    (Model.path_of_list path)


(* Output execution path as XML *)
let execution_path_pt level input_sys analysis trans_sys path = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<v>@{<b>Execution@}:@,\
      %a@]@.")
    (pp_print_path_pt input_sys analysis trans_sys true) path

(* Output cex for a property as plain text *)
let cex_pt mdl level input_sys analysis trans_sys prop cex disproved =

  (* Only ouptut if status was unknown *)
  if 

    not (Property.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then (
    (* Reset division by zero indicator. *)
    Simplify.has_division_by_zero_happened () |> ignore ;

    (* Don't show counterexamples for candidates *)
    if TransSys.is_candidate trans_sys prop then begin
      if disproved then
        (ignore_or_fprintf level)
          !log_ppf 
          "@[<v>%t Candidate %s disproved by %a %tafter %.3fs.@]@.@."
          warning_tag
          prop
          pp_print_kind_module_pt mdl
          (function ppf -> match cex with
             | [] -> ()
             | ((_, c) :: _) -> Format.fprintf ppf "for k=%d " (List.length c))
          (Stat.get_float Stat.analysis_time)
          (* (pp_print_counterexample_pt *)
          (*    (log_level_of_int (int_of_log_level level + 2)) *)
          (*    input_sys analysis trans_sys prop disproved) *)
          (* cex *)
    end
    else

      (* Output cex. *)
      (ignore_or_fprintf level)
        !log_ppf 
      "@[<v>%t Property @{<blue_b>%s@} %s %tafter %.3fs.@,@,%a@]@."
        (if disproved then failure_tag else warning_tag)
        prop
        (
          if disproved then
            Format.asprintf "is invalid by %a" pp_print_kind_module_pt mdl
          else
            "has a step k-induction counterexample"
        )
        (function ppf -> match cex with
           | [] -> ()
         | ((_, c) :: _) ->
           (List.length c) - 1 |> Format.fprintf ppf "for k=%d ")
        (Stat.get_float Stat.analysis_time)
        (pp_print_counterexample_pt
           level input_sys analysis trans_sys prop disproved)
        cex ;

    (* Output warning if division by zero happened in simplification. *)
    if Simplify.has_division_by_zero_happened () then
      div_by_zero_text prop
      |> printf_pt mdl L_warn
        "%t @[<v> %a@]"
        warning_tag
        (pp_print_list Format.pp_print_string "@,")

  ) else

    Debug.event "Status of property %s already known" prop


(* Output statistics section as plain text *)
let stat_pt mdl level stats =

  (ignore_or_fprintf level)
    !log_ppf 
    "@[<v>@{<b>Statistics for %a@}@,@,%a@]@."
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
    "@[<v>@{<b>Progress by %a@}: %d@]@."
    pp_print_kind_module mdl
    k

(* Pretty-print a list of properties and their status *)
let prop_status_pt level prop_status =

  (ignore_or_fprintf level)
    !log_ppf
    "@[<v>%a@{<b>Summary of properties@}:@,%a%a@,%a@]@."
    Pretty.print_line ()
    Pretty.print_line ()
    (pp_print_list 
       (fun ppf (p, s) -> 
          Format.fprintf 
            ppf
            "@[<h>@{<blue_b>%s@}: %a@]"
            p
            (function ppf -> function 
               | Property.PropUnknown -> 
                 Format.fprintf ppf "@{<red>unknown@}"

               | Property.PropKTrue k -> 
                 Format.fprintf ppf "@{<yellow>true up to %d steps@}" k

               | Property.PropInvariant (k, _) -> 
                 Format.fprintf ppf "@{<green_b>valid (at %d)@}" k

               | Property.PropFalse [] -> 
                 Format.fprintf ppf "@{<red_b>invalid@}"

               | Property.PropFalse cex -> 
                 Format.fprintf 
                   ppf
                   "@{<red_b>invalid after %d steps@}"
                   ((Property.length_of_cex cex) - 1))
            s)
       "@,")
    prop_status
    Pretty.print_double_line ()
          

(* ********************************************************************** *)
(* XML specific functions                                                 *)
(* ********************************************************************** *)

let escape_xml_name s =
  let ltr = Str.regexp "<" in
  let gtr = Str.regexp ">" in
  s |> Str.global_replace ltr "&lt;"
    |> Str.global_replace gtr "&gt;"

(* Level to class attribute of log tag *)
let xml_cls_of_level = string_of_log_level

let prop_attributes_xml trans_sys prop_name =
  let prop = TransSys.property_of_name trans_sys prop_name in

  let pp_print_fname ppf fname =
    if fname = "" then () else
    Format.fprintf ppf " file=\"%s\"" fname
  in

  let rec get_attributes = function
    | Property.PropAnnot pos ->
        let fname, lnum, cnum = file_row_col_of_pos pos in
        Format.asprintf " line=\"%d\" column=\"%d\"%a"
        lnum cnum pp_print_fname fname
    | Property.Generated _ -> ""
    | Property.Candidate None -> ""
    | Property.Candidate (Some source) -> get_attributes source
    | Property.Instantiated (scope,_) ->
        Format.asprintf " scope=\"%s\"" (String.concat "." scope)
    | Property.Assumption (pos, scope) ->
        let fname, lnum, cnum = file_row_col_of_pos pos in
        Format.asprintf " line=\"%d\" column=\"%d\" scope=\"%s\"%a"
          lnum cnum (String.concat "." scope) pp_print_fname fname
    | Property.Guarantee (pos, scope) ->
        let fname, lnum, cnum = file_row_col_of_pos pos in
        Format.asprintf " line=\"%d\" column=\"%d\" scope=\"%s\"%a"
          lnum cnum (String.concat "." scope) pp_print_fname fname
    | Property.GuaranteeOneModeActive (pos, scope) ->
        let fname, lnum, cnum = file_row_col_of_pos pos in
        Format.asprintf " line=\"%d\" column=\"%d\" scope=\"%s\""
          lnum cnum (String.concat "." scope)
    | Property.GuaranteeModeImplication (pos, scope) ->
        let fname, lnum, cnum = file_row_col_of_pos pos in
        Format.asprintf " line=\"%d\" column=\"%d\" scope=\"%s\"%a"
          lnum cnum (String.concat "." scope) pp_print_fname fname
  in

  get_attributes prop.Property.prop_source


(* Output proved property as XML *)
let proved_xml mdl level trans_sys k prop = 

  (* Only ouptut if status was unknown *)
  if 

    not (Property.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then 

    (ignore_or_fprintf level)
      !log_ppf 
      ("@[<hv 2><Property name=\"%s\"%s>@,\
        <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
        %t\
        <Answer source=\"%a\">valid</Answer>@;<0 -2>\
        </Property>@]@.")
      (escape_xml_name prop) (prop_attributes_xml trans_sys prop)
      (Stat.get_float Stat.analysis_time)
      (function ppf -> match k with 
         | None -> () 
         | Some k -> Format.fprintf ppf "<K>%d</K>@," k)
      pp_print_kind_module_xml_src mdl


(* Pretty-print a counterexample *)
let pp_print_counterexample_xml 
    input_sys
    analysis
    trans_sys
    prop_name
    disproved
    ppf =

  function

    | [] -> ()

    | cex -> 

      (

        (* Get property by name *)
        let prop =
          TransSys.property_of_name trans_sys prop_name
        in

        (* Slice counterexample and transitions system to property *)
        let trans_sys', instances, cex', prop_term, input_sys' =
          InputSystem.slice_to_abstraction_and_property
            input_sys
            analysis
            trans_sys
            cex
            prop
        in

        let tag = "CounterExample" in

        try
          (* Output counterexample *)
          Format.fprintf ppf
            "@[<hv 2>\ <%s>%a@]@,</%s>"
            tag
            (InputSystem.pp_print_path_xml input_sys' trans_sys' instances true)
            (Model.path_of_list cex')
            tag
        with TimeoutWall -> (
          Format.fprintf ppf "@]@,</%s>@;<0 -2></Property>@]@." tag
        )
      )


(* Output execution path without slicing *)
let pp_print_path_xml input_sys analysis trans_sys init ppf path = 

  (* Output path *)
  Format.fprintf ppf 
    "%a"
    (InputSystem.pp_print_path_xml input_sys trans_sys [] true)
    (Model.path_of_list path)


(* Output execution path as XML *)
let execution_path_xml level input_sys analysis trans_sys path = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<hv 2><Execution>@,\
      %a@;<0 -2>\
      </Execution>@]@.")
    (pp_print_path_xml input_sys analysis trans_sys true) path
  

(* Output disproved property as XML *)
let cex_xml
mdl level input_sys analysis trans_sys prop (
  cex : (StateVar.t * Model.value list) list
) disproved = 

  (* Only ouptut if status was unknown *)
  if 

    not (Property.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then (
    (* Reset division by zero indicator. *)
    Simplify.has_division_by_zero_happened () |> ignore ;

    let answer =
      match mdl with
      | `IND -> "unknown"
      | _ -> "falsifiable"
    in

    (* Output cex. *)
    (ignore_or_fprintf level)
      !log_ppf 
      ("@[<hv 2><Property name=\"%s\"%s>@,\
        <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
        %t\
        <Answer source=\"%a\">%s</Answer>@,\
        %a@;<0 -2>\
        </Property>@]@.") 
      (escape_xml_name prop) (prop_attributes_xml trans_sys prop)
      (Stat.get_float Stat.analysis_time)
      (function ppf -> match cex with 
         | [] -> () 
         | cex ->
          (Property.length_of_cex cex) - 1 |> Format.fprintf ppf "<K>%d</K>@,")
      pp_print_kind_module_xml_src mdl
      answer
      (pp_print_counterexample_xml input_sys analysis trans_sys prop disproved)
      cex ;

    (* Output warning if division by zero happened in simplification. *)
    if Simplify.has_division_by_zero_happened () then
      div_by_zero_text prop
      |> printf_xml mdl L_warn
        "@[<v>%a@]"
        (pp_print_list Format.pp_print_string "@,")
  )
  

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

  (* Filter unknown properties. *)
  prop_status
  |> List.filter (fun (prop,status) ->
    not (Property.prop_status_known status)
  ) |> (ignore_or_fprintf level)
    !log_ppf
    "@[<v>%a@]@."
    (pp_print_list 
       (fun ppf (p, s) -> 

            Format.fprintf 
              ppf
              "@[<hv 2><Property name=\"%s\">@,\
               @[<hv 2><Answer>@,%a@;<0 -2></Answer>@]@,\
               %a@,\
               @;<0 -2></Property>@]"
              (escape_xml_name p)
              (function ppf -> function 
                 | Property.PropUnknown
                 | Property.PropKTrue _ -> Format.fprintf ppf "unknown"
                 | Property.PropInvariant _ -> Format.fprintf ppf "valid"
                 | Property.PropFalse [] 
                 | Property.PropFalse _ -> Format.fprintf ppf "falsifiable")
              s
              (function ppf -> function
                 | Property.PropUnknown
                 | Property.PropInvariant _
                 | Property.PropFalse [] -> ()
                 | Property.PropKTrue k -> 
                   Format.fprintf 
                     ppf 
                     "@,@[<hv 2><TrueFor>@,%d@;<0 -2></TrueFor>@]"
                     k
                 | Property.PropFalse cex -> 
                   Format.fprintf 
                     ppf 
                     "@,@[<hv 2><FalseAt>@,%d@;<0 -2></FalseAt>@]"
                     ((Property.length_of_cex cex) - 1))
              s)
       "@,")



(* ********************************************************************** *)
(* JSON specific functions                                                *)
(* ********************************************************************** *)

let pp_print_list_attrib pp ppf = function
  | [] -> Format.fprintf ppf " []"
  | lst -> Format.fprintf ppf
    "@,[@[<v 1>@,%a@]@,]" (pp_print_list pp ",@,") lst


let prop_attributes_json ppf trans_sys prop_name =
  let prop = TransSys.property_of_name trans_sys prop_name in

  let rec get_attributes = function
    | Property.PropAnnot pos ->
        let _, lnum, cnum = file_row_col_of_pos pos in
        Format.fprintf ppf "\"line\" : %d,@,\"column\" : %d,@," lnum cnum
    | Property.Instantiated (scope,_) ->
        Format.fprintf ppf "\"scope\" : \"%s\",@," (String.concat "." scope)
    | Property.Assumption (pos, scope)
    | Property.Guarantee (pos, scope)
    | Property.GuaranteeOneModeActive (pos, scope)
    | Property.GuaranteeModeImplication (pos, scope) ->
        let _, lnum, cnum = file_row_col_of_pos pos in
        Format.fprintf ppf
          "\"scope\" : \"%s\",@,\"line\" : %d,@,\"column\" : %d,@,"
          (String.concat "." scope) lnum cnum
    | Property.Generated _
    | Property.Candidate None -> ()
    | Property.Candidate (Some source) -> get_attributes source
  in

  get_attributes prop.Property.prop_source


(* Output proved property as JSON *)
let proved_json mdl level trans_sys k prop =

  (* Only ouptut if status was unknown *)
  if

    not (Property.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then

    (ignore_or_fprintf level)
      !log_ppf
      ",@.{@[<v 1>@,\
        \"objectType\" : \"property\",@,\
        \"name\" : \"%s\",@,\
        %t\
        \"runtime\" : {\
          \"unit\" : \"sec\", \
          \"timeout\" : false, \
          \"value\" : %.3f\
        },@,\
        %t\
        \"answer\" : {\
          \"source\" : \"%s\", \
          \"value\" : \"valid\"\
        }\
        @]@.}@.\
      "
      prop
      (function ppf -> prop_attributes_json ppf trans_sys prop)
      (Stat.get_float Stat.analysis_time)
      (function ppf -> match k with
         | None -> ()
         | Some k -> Format.fprintf ppf "\"k\" : %d,@," k)
      (short_name_of_kind_module mdl)


(* Pretty-print a counterexample *)
let pp_print_counterexample_json
    input_sys
    analysis
    trans_sys
    prop_name
    disproved
    ppf =

  function

    | [] -> ()

    | cex ->

      (

        (* Get property by name *)
        let prop =
          TransSys.property_of_name trans_sys prop_name
        in

        (* Slice counterexample and transitions system to property *)
        let trans_sys', instances, cex', prop_term, input_sys' =
          InputSystem.slice_to_abstraction_and_property
            input_sys
            analysis
            trans_sys
            cex
            prop
        in

        try
          (* Output counterexample *)
          Format.fprintf ppf
            "\"counterExample\" :%a"
            (InputSystem.pp_print_path_json input_sys' trans_sys' instances true)
            (Model.path_of_list cex')
        with TimeoutWall -> (
          Format.fprintf ppf " []@.}@.";
          raise TimeoutWall
        )
      )


(* Output disproved property as JSON *)
let cex_json mdl level input_sys analysis trans_sys prop cex disproved =

  (* Only output if status was unknown *)
  if

    not (Property.prop_status_known (TransSys.get_prop_status trans_sys prop))

  then (
    (* Reset division by zero indicator. *)
    Simplify.has_division_by_zero_happened () |> ignore ;

    let answer =
      match mdl with
      | `IND -> "unknown"
      | _ -> "falsifiable"
    in

    (* Output cex. *)
    (ignore_or_fprintf level)
      !log_ppf
      ",@.{@[<v 1>@,\
        \"objectType\" : \"property\",@,\
        \"name\" : \"%s\",@,\
        %t\
        \"runtime\" : {\
          \"unit\" : \"sec\", \
          \"timeout\" : false, \
          \"value\" : %.3f\
        },@,\
        %t\
        \"answer\" : {\
          \"source\" : \"%s\", \
          \"value\" : \"%s\"\
        },@,\
        %a\
        @]@.}@.\
      "
      prop
      (function ppf -> prop_attributes_json ppf trans_sys prop)
      (Stat.get_float Stat.analysis_time)
      (function ppf -> match cex with
         | [] -> ()
         | cex -> let k = (Property.length_of_cex cex) - 1 in
           Format.fprintf ppf "\"k\" : %d,@," k)
      (short_name_of_kind_module mdl) answer
      (pp_print_counterexample_json input_sys analysis trans_sys prop disproved)
      cex
      ;

    (* Output warning if division by zero happened in simplification. *)
    if Simplify.has_division_by_zero_happened () then
      div_by_zero_text prop
      |> printf_json mdl L_warn
        "@[<v>%a@]"
        (pp_print_list Format.pp_print_string "@,")
  )


(* Output execution path without slicing as JSON *)
let execution_path_json level input_sys analysis trans_sys path =

  (ignore_or_fprintf level)
    !log_ppf
    ",@.{@[<v 1>@,\
        \"objectType\" : \"execution\",@,\
        \"trace\" :@,[@[<v 1>%a@]@,]\
       @]@.}@.\
    "
    (InputSystem.pp_print_path_json input_sys trans_sys [] true)
    (Model.path_of_list path)


(* Pretty-print a list of properties and their status *)
let prop_status_json level prop_status =

  (* Filter unknown properties. *)
  let unknown_props = prop_status
    |> List.filter (fun (prop,status) ->
      not (Property.prop_status_known status)
    )
  in

  if unknown_props <> [] then (
    (ignore_or_fprintf level)
      !log_ppf
      "@[<v>%a@]@."
      (pp_print_list
         (fun ppf (p, s) ->
           Format.fprintf
             ppf
             ",@.{@[<v 1>@,\
               \"objectType\" : \"property\",@,\
               \"name\" : \"%s\",@,\
               %t\
               \"answer\" : {\
                 \"value\" : \"unknown\"\
               }\
               @]@.}\
             "
             p
             (function ppf -> match s with
                | Property.PropKTrue k ->
                  Format.fprintf ppf "\"trueFor\" : %d,@," k
                | _ -> ()
             )
         )
       "@,")
       unknown_props
  )


(* Output statistics section as JSON *)
let stat_json mdl level stats =

  (ignore_or_fprintf level)
    !log_ppf
    ",@.{@[<v 1>@,\
        \"objectType\" : \"stat\",@,\
        \"source\" : \"%s\",@,\
        \"sections\" :%a\
      @]@.}@.\
    "
    (short_name_of_kind_module mdl)
    (pp_print_list_attrib (fun ppf (section, items) ->
      Format.fprintf ppf
        "{@[<v 1>@,\
         \"name\" : \"%s\",@,\
         \"items\" :%a\
         @]@,}\
        "
        section Stat.pp_print_stats_json items
      )
    )
    stats


(* Output progress as JSON *)
let progress_json mdl level k =

  (ignore_or_fprintf level)
    !log_ppf
    ",@.{@[<v 1>@,\
        \"objectType\" : \"progress\",@,\
        \"source\" : \"%s\",@,\
        \"k\" : \"%d\"\
      @]@.}@.\
    "
    (short_name_of_kind_module mdl) k



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


(* (\* Relay log messages to invariant manager *\) *)
(* let set_relay_log () = Log.set_relay_log printf_relay *)


module ELog = Log.Make (struct let printf_relay = printf_relay end)
include ELog


(* ********************************************************************** *)
(* Specialized logging functions                                          *)
(* ********************************************************************** *)

(* Log a message with source and log level *)
let log_proved mdl level trans_sys k prop =
  match get_log_format () with 
    | F_pt -> proved_pt mdl level trans_sys k prop
    | F_xml -> proved_xml mdl level trans_sys k prop
    | F_json -> proved_json mdl level trans_sys k prop
    | F_relay -> ()

(* Warning issued if model reconstruction triggers a division by zero. *)
let div_by_zero_text = "division by zero detected, model may be inconsistent"

(* Log a message with source and log level *)
let log_cex disproved mdl level input_sys analysis trans_sys prop cex =
  match get_log_format () with 
  | F_pt ->
    cex_pt mdl level input_sys analysis trans_sys prop cex disproved
  | F_xml ->
    cex_xml mdl level input_sys analysis trans_sys prop cex disproved
  | F_json ->
    cex_json mdl level input_sys analysis trans_sys prop cex disproved
  | F_relay -> ()

(* Log a message with source and log level *)
let log_disproved mdl level input_sys analysis trans_sys prop cex =
  log_cex true mdl level input_sys analysis trans_sys prop cex

(* Log a step counterexample. *)
let log_step_cex mdl level input_sys analysis trans_sys prop cex =
  log_cex false mdl level input_sys analysis trans_sys prop cex


(* Log an exection path *)
let log_execution_path mdl level input_sys analysis trans_sys path =

  (match get_log_format () with 
    | F_pt -> execution_path_pt level input_sys analysis trans_sys path
    | F_xml -> execution_path_xml level input_sys analysis trans_sys path 
    | F_json -> execution_path_json level input_sys analysis trans_sys path
    | F_relay -> ())


(* Output summary of status of properties *)
let log_prop_status level prop_status =
  match get_log_format () with 
    | F_pt -> prop_status_pt level prop_status
    | F_xml -> prop_status_xml level prop_status
    | F_json -> prop_status_json level prop_status
    | F_relay -> ()


(* Output statistics of a section of a source *)
let log_stat mdl level stats =

  match get_log_format () with 
    | F_pt -> stat_pt mdl level stats
    | F_xml -> stat_xml mdl level stats
    | F_json -> stat_json mdl level stats
    | F_relay -> ()
  

(* Output progress indicator of a source *)
let log_progress mdl level k = 
  match get_log_format () with 
    | F_pt -> ()
    | F_xml -> progress_xml mdl level k
    | F_json -> progress_json mdl level k
    | F_relay -> ()
  

(* Logs the end of a run. *)
let log_run_end results =
  match get_log_format () with
  | F_pt ->
    (* Printing a short, human readable version of all the results. *)
    if Flags.Contracts.compositional () then
      Format.fprintf !log_ppf
        "@{<b>%a@}@{<b>Analysis breakdown, total runtime %.3fs seconds@}:@   \
          @[<v>%a@]@.@.\
        "
        Pretty.print_line ()
        (Stat.get_float Stat.total_time)
        (pp_print_list Analysis.pp_print_result_quiet "@ ") (
          results
          |> if Flags.modular () then List.filter (
            fun { Analysis.sys } ->
              (TransSys.get_split_properties sys) <> ([], [], [])
          ) else identity
        )

  | F_xml -> ()

  | F_json -> ()

  | F_relay -> failwith "can only be called by supervisor"


let split_abstract_and_concrete_systems sys info =
  Scope.Map.fold (fun sys is_abstract (a,c) ->
    if is_abstract then sys :: a, c else a, sys :: c
  ) info.Analysis.abstraction_map ([],[])


let number_of_subsystem_assumptions info =
  info.Analysis.assumptions
  |> Analysis.assumptions_fold (fun map key _ ->
    let cpt = try (Scope.Map.find key map) + 1 with Not_found -> 1 in
    Scope.Map.add key cpt map
  ) Scope.Map.empty
  |> Scope.Map.bindings


(* Logs the start of an analysis. *)
let log_analysis_start sys param =
  let param = Analysis.shrink_param_to_sys param sys in
  let info = Analysis.info_of_param param in
  match get_log_format () with
  | F_pt ->
    if Flags.log_level () = L_off |> not then
      Format.fprintf !log_ppf "\
        @.@.%a@{<b>Analyzing @{<blue>%a@}@}@   with %a\
      @.@."
      Pretty.print_double_line ()
      Scope.pp_print_scope info.Analysis.top
      (Analysis.pp_print_param false) param

  | F_xml ->
    (* Splitting abstract and concrete systems. *)
    let abstract, concrete = split_abstract_and_concrete_systems sys info in
    (* Counting the number of assumption for each subsystem. *)
    let assumption_count = number_of_subsystem_assumptions info in
    (* Opening [analysis] tag and printing info. *)
    Format.fprintf !log_ppf "@.@.\
        <AnalysisStart \
          top=\"%a\" \
          concrete=\"%a\" \
          abstract=\"%a\" \
          assumptions=\"%a\"\
        />@.@.\
      "
      Scope.pp_print_scope info.Analysis.top
      (pp_print_list Scope.pp_print_scope ",") concrete
      (pp_print_list Scope.pp_print_scope ",") abstract
      (pp_print_list (fun fmt (scope, cpt) ->
          Format.fprintf fmt "(%a,%d)" Scope.pp_print_scope scope cpt
        )
        ","
      ) assumption_count ;
    analysis_start_not_closed := true

  | F_json ->
    let pp_print_scope_str fmt scope =
      Format.fprintf fmt "\"%a\"" Scope.pp_print_scope scope
    in
    (* Splitting abstract and concrete systems. *)
    let abstract, concrete = split_abstract_and_concrete_systems sys info in
    (* Counting the number of assumption for each subsystem. *)
    let assumption_count = number_of_subsystem_assumptions info in
    (* Opening [analysis] tag and printing info. *)
    Format.fprintf !log_ppf "\
        ,@.{@[<v 1>@,\
        \"objectType\" : \"analysisStart\",@,\
        \"top\" : \"%a\",@,\
        \"concrete\" :%a,@,\
        \"abstract\" :%a,@,\
        \"assumptions\" :%a\
        @]@.}@.\
      "
      Scope.pp_print_scope info.Analysis.top
      (pp_print_list_attrib pp_print_scope_str) concrete
      (pp_print_list_attrib pp_print_scope_str) abstract
      (pp_print_list_attrib (fun fmt (scope, cpt) ->
          Format.fprintf fmt "[%a,%d]" pp_print_scope_str scope cpt
        )
      ) assumption_count;
    analysis_start_not_closed := true

  | F_relay -> failwith "can only be called by supervisor"

(** Logs the end of an analysis.
    [log_analysis_start result] logs the end of an analysis. *)
let log_analysis_end result =
  match get_log_format () with
  | F_pt -> ()
  | F_xml ->
    if !analysis_start_not_closed then (
      (* Closing [analysis] tag. *)
      Format.fprintf !log_ppf "<AnalysisStop/>@.@." ;
      analysis_start_not_closed := false
    ) ;

  | F_json ->
    if !analysis_start_not_closed then (
      Format.fprintf !log_ppf ",@.{\"objectType\" : \"analysisStop\"}@." ;
      analysis_start_not_closed := false
    ) ;

  | F_relay -> failwith "can only be called by supervisor"

(** Logs the start of a post-analysis treatment. *)
let log_post_analysis_start name title =
  match get_log_format () with
  | F_pt ->
    Format.fprintf !log_ppf "%a@{<b>Post-analysis@}: @{<blue>%s@}@.@."
      Pretty.print_line () title
  | F_xml ->
    Format.fprintf !log_ppf "<PostAnalysisStart name=\"%s\"/>@.@."
      name
  | F_json ->
    Format.fprintf !log_ppf
      ",@.{@[<v 1>@,\
        \"objectType\" : \"postAnalysisStart\",@,\
        \"name\" : \"%s\"\
        @]@.}@.\
      "
      name
  | F_relay -> failwith "can only be called by supervisor"

(** Logs the end of a post-analysis treatment. *)
let log_post_analysis_end () =
  match get_log_format () with
  | F_pt ->
    Format.fprintf !log_ppf "%a@." Pretty.print_line ()
  | F_xml ->
    Format.fprintf !log_ppf "<PostAnalysisEnd/>@.@."
  | F_json ->
    Format.fprintf !log_ppf ",@.{\"objectType\" : \"postAnalysisEnd\"}@."
  | F_relay -> failwith "can only be called by supervisor"

(* Terminate log output *)
let terminate_log () = 
  match get_log_format () with 
    | F_pt -> Format.print_flush ()
    | F_xml ->
      log_analysis_end () ;
      print_xml_trailer () ;
      Format.print_flush ()
    | F_json ->
      log_analysis_end () ;
      Format.fprintf !log_ppf "]@.";
      Format.print_flush ()
    | F_relay -> ()

(** Logs a timeout. *)
let log_timeout b =
  let pref = if b then "Wallclock" else "CPU" in
  match get_log_format () with
  | F_pt ->
    if Flags.log_level () = L_off |> not then
      Format.printf "%t %s timeout.@.@." timeout_tag pref 
  | F_xml ->
    log L_fatal "%s timeout." pref
  | F_json ->
    log L_fatal "%s timeout." pref
  | F_relay -> failwith "can only be called by supervisor"

(** Logs a timeout. *)
let log_interruption signal =
  let txt =
    Format.sprintf "Caught signal%s. Terminating." (
      match signal with
      | 0 -> ""
      | _ -> Format.asprintf " %s" (string_of_signal signal)
    )
  in
  match get_log_format () with
  | F_pt ->
    if Flags.log_level () = L_off |> not then
      Format.printf "%t %s@.@." interruption_tag txt
  | F_xml ->
    log L_fatal "%s" txt
  | F_json ->
    log L_fatal "%s" txt
  | F_relay -> failwith "can only be called by supervisor"




(* ********************************************************************** *)
(* Events                                                                 *)
(* ********************************************************************** *)


(* Broadcast a scoped invariant *)
let invariant scope term cert two_state = 
  (* Update time in case we are not running in parallel mode *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  try
    (* Send invariant message *)
    Invariant (scope, term, cert, two_state)
    |> EventMessaging.send_relay_message
  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()



(* Broadcast a property status *)
let prop_status status input_sys analysis trans_sys prop =
  
  (* Update time in case we are not running in parallel mode *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  
  let mdl = get_module () in

  (match status with
    | Property.PropInvariant _ -> log_proved mdl L_warn trans_sys None prop
    | Property.PropFalse cex -> 
      log_cex true mdl L_warn input_sys analysis trans_sys prop cex

    | _ -> ());

  (* Update status of property in transition system *)
  TransSys.set_prop_status trans_sys prop status;

  try
    
    (* Send status message *)
    EventMessaging.send_relay_message (PropStatus (prop, status))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()



(* Broadcast a step cex *)
let step_cex input_sys analysis trans_sys prop cex =
  
  (* Update time in case we are not running in parallel mode *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;

  log_cex true (get_module ()) L_warn input_sys analysis trans_sys prop cex ;

  try
    
    (* Send status message *)
    EventMessaging.send_relay_message (StepCex (prop, cex))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a counterexample for some properties *)
let execution_path trans_sys path = 

  (* Update time in case we are not running in parallel mode *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  
  let mdl = get_module () in

  log_execution_path mdl L_warn trans_sys path


(* Send progress indicator *)
let progress k =

  (* Update time in case we are not running in parallel mode *)
  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  
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

  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  
  let mdl = get_module () in

  log_stat mdl L_info stats;

  try

    (* Send message *)
    EventMessaging.send_output_message
      (EventMessaging.Stat (Marshal.to_string stats []))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()
  

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

  Stat.update_time Stat.total_time ;
  Stat.update_time Stat.analysis_time ;
  
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

               let lines = Str.(split (regexp "\n") msg) in

               log (log_level_of_int lvl) "@[<hov>%a@]" (
                pp_print_list Format.pp_print_string "@ "
               ) lines ;

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

(* Notifies the background thread of a new list of child
   processes. Used by the supervisor in a modular analysis when
   restarting. *)
let update_child_processes_list new_process_list =
  try
    EventMessaging.update_child_processes_list
      new_process_list
  with Messaging.NotInitialized -> ()

(* Terminates if a termination message was received. Does NOT modified
   received messages. *)
let check_termination () =
  if EventMessaging.check_termination ()
  then raise Terminate else ()


(* Update transition system from event list *)
let update_trans_sys_sub input_sys analysis trans_sys events =
  let insert_inv scope map two_state term =
    let sets =
      ( try SMap.find scope map with Not_found -> TSet.empty, TSet.empty )
      |> fun (os, ts) ->
        if two_state then os, TSet.add term ts else TSet.add term os, ts
    in
    SMap.add scope sets map
  in

  (* Tail-recursive iteration *)
  let rec update_trans_sys' trans_sys invars prop_status = function 

    (* No more events, return new invariants and changed property status *)
    | [] -> (invars, prop_status)

    (* Invariant discovered *)
    | (m, Invariant (s, t, cert, two_state)) :: tl -> 

      (* Property status if received invariant is a property *)
      let tl' =
        TransSys.props_list_of_bound trans_sys Numeral.zero
        |> List.fold_left (
          fun accum (p, t') -> 
            (* Invariant is equal to property term? *)
            if Term.equal t t' then
              (* Inject property status event *)
              (m, PropStatus (p, Property.PropInvariant cert)) :: accum
            else
              accum
        ) tl
      in
      
      let invars =
        (* Add invariant to transtion system *)
        TransSys.add_scoped_invariant trans_sys s t cert two_state
        |> insert_inv s invars two_state
      in

      (* Continue with invariant added to accumulator *)
      update_trans_sys'
        trans_sys
        invars
        prop_status
        tl'

    (* Property found unknown *)
    | (_, PropStatus (p, Property.PropUnknown)) :: tl -> 

      (* Continue without changes *)
      update_trans_sys' trans_sys invars prop_status tl

    (* Property found true for k steps *)
    | (m, PropStatus (p, (Property.PropKTrue k as s))) :: tl -> 

      (* Change property status in transition system *)
      TransSys.set_prop_ktrue trans_sys k p;

      (* Continue with propert status added to accumulator *)
      update_trans_sys'
        trans_sys
        invars
        ((m, (p, s)) :: prop_status) 
        tl

    (* Property found invariant *)
    | (m, PropStatus (p, (Property.PropInvariant cert as s))) :: tl -> 

      (* Output proved property *)
      log_proved m L_warn trans_sys None p;
          
      (* Change property status in transition system *)
      TransSys.set_prop_invariant trans_sys p cert;

      let term =
        TransSys.props_list_of_bound trans_sys Numeral.zero
        |> List.assoc p
      in

      (* Retrieve scope to add to invariants. *)
      let scope = TransSys.scope_of_trans_sys trans_sys in

      let invars =
        try (* Add proved property as invariant *)
          TransSys.add_invariant trans_sys term cert false
          |> insert_inv scope invars false
        with Not_found -> (* Skip if named property not found *)
          invars
      in

      (* Continue with property status added to accumulator *)
      update_trans_sys'
        trans_sys 
        invars
        ( (m, (p, s)) :: prop_status )
        tl

    (* Property found false *)
    | (m, PropStatus (p, (Property.PropFalse cex as s))) :: tl -> 

      (* Output disproved property *)
      log_cex true m L_warn input_sys analysis trans_sys p cex ;

      (* Change property status in transition system *)
      TransSys.set_prop_false trans_sys p cex;

      (* Continue with property status added to accumulator *)
      update_trans_sys' 
        trans_sys
        invars
        ((m, (p, s)) :: prop_status) 
        tl

    (* Property found false *)
    | (m, StepCex (p, cex)) :: tl -> 

      (* remove uninterresting first state for step counterexamples *)
      let cex = List.map (function
          | (sv, []) as c -> c
          | (sv, _::vl) -> sv, vl) cex
      in
      
      (* Output disproved property *)
      log_cex false m L_warn input_sys analysis trans_sys p cex ;

      (* Continue with unchanged accumulator *)
      update_trans_sys' 
        trans_sys
        invars
        prop_status
        tl

  in

  update_trans_sys' trans_sys SMap.empty [] events


(* Filter list of invariants with their scope for invariants of empty
   (top) scope *)
let top_invariants_of_invariants sys invariants = 
  let top = TransSys.scope_of_trans_sys sys in
  try
    SMap.find top invariants
  with Not_found -> TSet.empty, TSet.empty

let update_trans_sys input_sys analysis trans_sys events =
  match
    (* Calling the scoped update function. *)
    update_trans_sys_sub input_sys analysis trans_sys events
  with
  | invs, valids ->
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
