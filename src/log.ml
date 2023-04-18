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


(* Signature of module for reuse in Event *)
module type Sig = sig
  type 'a log_printer =
    Lib.log_level ->
    ('a, Format.formatter, unit) format -> 'a
  type 'a m_log_printer =
    Lib.kind_module -> 'a log_printer
  val set_module : Lib.kind_module -> unit 
  val get_module : unit -> Lib.kind_module
  type log_format = | F_pt | F_xml | F_json | F_relay
  val get_log_format : unit -> log_format
  val set_log_format : log_format -> unit
  val set_log_format_pt : unit -> unit
  val set_log_format_xml : unit -> unit
  val set_log_format_json : unit -> unit
  val set_relay_log : unit -> unit
  val unset_relay_log : unit -> unit
  val pp_print_kind_module_xml_src : Format.formatter -> Lib.kind_module -> unit
  val print_xml_trailer : unit -> unit
  val printf_xml : 'a m_log_printer
  val printf_json : 'a m_log_printer
  val pp_print_level_xml_cls: Format.formatter -> Lib.log_level -> unit
  val first_log_flag: bool ref
end



(* ********************************************************************** *)
(* Initialization for the messaging system                                *)
(* ********************************************************************** *)

type 'a log_printer =
  Lib.log_level -> ('a, Format.formatter, unit) format -> 'a

type 'a m_log_printer =
  Lib.kind_module -> 'a log_printer

(* Module currently running *)
let this_module = ref `Parser

(* Set module currently running *)
let set_module mdl = this_module := mdl 

(* Get module currently running *)
let get_module () = !this_module


(* ********************************************************************** *)
(* State of the logger                                                    *)
(* ********************************************************************** *)


(* Log formats *)
type log_format = 
  | F_pt
  | F_xml
  | F_json
  | F_relay


(* Current log format *)
let log_format = ref F_pt
let prev_log_format = ref !log_format

let get_log_format () = !log_format
let set_log_format l = log_format := l

let first_log_flag = ref true


(* ********************************************************************** *)
(* Plain text output                                                      *)
(* ********************************************************************** *)

(* Output message as plain text *)
let printf_pt level fmt =
  (ignore_or_fprintf level)
    !log_ppf ("%a @[<hov>" ^^ fmt ^^ "@]@.@.") tag_of_level level


(* Unconditional printing as plain text. *)
let printf_pt_uncond fmt =
  Format.fprintf !log_ppf ("@[<hov>" ^^ fmt ^^ "@]@.@.")



(* ********************************************************************** *)
(* XML output                                                             *)
(* ********************************************************************** *)

(* Level to class attribute of log tag *)
let xml_cls_of_level = string_of_log_level

(* XML at the beginning the output *)
let print_xml_header () =
  Format.fprintf !log_ppf "<?xml version=\"1.0\"?>@."


(* Pretty-print level as class attribute of log tag *)
let pp_print_level_xml_cls ppf l = 
  Format.fprintf ppf "%s" (xml_cls_of_level l)

(* Kind module as source attribute of log tag *)
let xml_src_of_kind_module = short_name_of_kind_module

(* Pretty-print kind module as source attribute of log tag *)
let pp_print_kind_module_xml_src ppf m = 
  Format.fprintf ppf "%s" (xml_src_of_kind_module m)


(* XML at the end of the output *)
let print_xml_trailer () = 
  Format.fprintf !log_ppf "@.@.</Results>@."


(* Output message as XML *)
let printf_xml_string mdl level s =

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<hv 2><Log class=\"%a\" source=\"%a\">@,\
      @[<hov>%s@]@;<0 -2></Log>@]@.")
    pp_print_level_xml_cls level
    pp_print_kind_module_xml_src mdl s


let printf_xml mdl level fmt =

  (ignore_or_kfprintf level)
    (function _ ->
      let s =
        Format.flush_str_formatter ()
        |> Lib.escape_xml_string
      in
      printf_xml_string mdl level s
    )

    Format.str_formatter
    fmt


(* ********************************************************************** *)
(* JSON output                                                            *)
(* ********************************************************************** *)

let printf_json_string mdl level s =
  (ignore_or_fprintf level)
    !log_ppf
    ( (if !first_log_flag then
         (first_log_flag := false; "")
       else
         ",@."
      ) ^^
      "{@[<v 1>@," ^^
      "\"objectType\" : \"log\",@," ^^
      "\"level\" : \"%s\",@," ^^
      "\"source\" : \"%s\",@," ^^
      "\"value\" : @[<h>\"%s\"@]" ^^
      "@]@.}@.")
    (string_of_log_level level)
    (short_name_of_kind_module mdl) s

(* Output message as JSON *)
let printf_json mdl level fmt =

  (ignore_or_kfprintf level)
    (function _ ->
      let s =
        Format.flush_str_formatter ()
        |> Lib.escape_json_string
      in
      printf_json_string mdl level s
    )

    Format.str_formatter
    fmt

(*****************************************************************)
(* Setup                                                         *)
(*****************************************************************)
  
(* Set log format to plain text *)
let set_log_format_pt () = log_format := F_pt

(* Set log format to XML *)
let set_log_format_xml () = 
  log_format := F_xml;
  (* Print XML header *)
  print_xml_header ()

(* Set log format to JSON *)
let set_log_format_json () = log_format := F_json

(* Relay log messages to invariant manager *)
let set_relay_log () =
  prev_log_format := !log_format;
  log_format := F_relay


let unset_relay_log () = log_format := !prev_log_format

module type SLog = sig
  val log : 'a log_printer
  val log_uncond : ('a, Format.formatter, unit) format -> 'a
  val log_result : (Format.formatter -> 'a -> unit)
    -> (Format.formatter -> 'a -> unit)
    -> (Format.formatter -> 'a -> unit)
    -> 'a
    -> unit
end

module Make (R : sig val printf_relay : 'a m_log_printer end) : SLog = struct

  (* ********************************************************************** *)
  (* Generic logging functions                                              *)
  (* ********************************************************************** *)

  (* Log a message with source and log level *)
  let log level fmt =

    let mdl = get_module () in

    match !log_format with 
    | F_pt -> printf_pt level fmt
    | F_xml -> printf_xml mdl level fmt
    | F_json -> printf_json mdl level fmt
    | F_relay -> R.printf_relay mdl level fmt


  (* Unconditionally logs a message. *)
  let log_uncond fmt =

    let mdl = get_module () in

    match !log_format with 
    | F_pt -> printf_pt_uncond fmt
    | F_xml -> printf_xml mdl L_info fmt
    | F_json -> printf_json mdl L_info fmt
    | F_relay -> R.printf_relay mdl L_info fmt

  (* Logs the result of a post-analysis. *)
  let log_result pt xml json a =

    let fmt = !Lib.log_ppf in
    let print =
      (*Format.fprintf fmt "%a"*)
      Lib.ignore_or_fprintf L_note fmt "%a"
    in

    match !log_format with 
    | F_pt -> print pt a
    | F_xml -> print xml a
    | F_json -> print json a
    | F_relay -> ()
 
end


include Make (struct let printf_relay _ _ _ = failwith "Uninitialized" end)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
