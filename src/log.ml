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
    ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
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
  val parse_log_xml : Lib.log_level -> Lib.position -> string -> unit
  val parse_log_json : Lib.log_level -> Lib.position -> string -> unit
end



(* ********************************************************************** *)
(* Initialization for the messaging system                                *)
(* ********************************************************************** *)

type 'a log_printer =
  Lib.log_level ->
  ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a

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




(* ********************************************************************** *)
(* Plain text output                                                      *)
(* ********************************************************************** *)


(* Pretty-print kind module for plain text output *)
let pp_print_kind_module_pt =
  pp_print_kind_module


(* Output message as plain text *)
let printf_pt mdl level fmt =
  (ignore_or_fprintf level)
    !log_ppf ("%a @[<hov>" ^^ fmt ^^ "@]@.@.") tag_of_level level


(* Unconditional printing as plain text. *)
let printf_pt_uncond mdl fmt =
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
let printf_xml mdl level fmt = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<hv 2><Log class=\"%a\" source=\"%a\">@,@[<hov>" ^^ 
     fmt ^^ 
     "@]@;<0 -2></Log>@]@.") 
    pp_print_level_xml_cls level
    pp_print_kind_module_xml_src mdl


let parse_log_xml level pos msg =
  let pp_print_fname ppf fname =
    if fname = "" then () else
    Format.fprintf ppf " file=\"%s\"" fname
  in
  let file, lnum, cnum = file_row_col_of_pos pos in
  (ignore_or_fprintf level)
    !log_ppf
    "@[<hv 2><ParseLog class=\"%a\" line=\"%d\" column=\"%d\"%a>%s</ParseLog>@]@."
    pp_print_level_xml_cls level lnum cnum pp_print_fname file msg


(* ********************************************************************** *)
(* JSON output                                                            *)
(* ********************************************************************** *)

let escape_json_string s =
  let backslash = Str.regexp "\\" in
  let double_quotes = Str.regexp "\"" in
  let newline = Str.regexp "\n" in
  s |> Str.global_replace backslash "\\\\"
    |> Str.global_replace double_quotes "\\\""
    |> Str.global_replace newline "\\n"

(* Output message as JSON *)
let printf_json mdl level fmt =

  (ignore_or_fprintf level)
    !log_ppf
    (",@.{@[<v 1>@," ^^
      "\"objectType\" : \"log\",@," ^^
      "\"level\" : \"%s\",@," ^^
      "\"source\" : \"%s\",@," ^^
      "\"value\" : \"" ^^ fmt ^^ "\"" ^^
      "@]@.}@.")
    (string_of_log_level level)
    (short_name_of_kind_module mdl)

let parse_log_json level pos msg =
  let pp_print_fname ppf fname =
    if fname = "" then () else
    Format.fprintf ppf "\"file\" : \"%s\",@," fname
  in
  let file, lnum, cnum = file_row_col_of_pos pos in
  (ignore_or_fprintf level)
    !log_ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"parseLog\",@,\
     \"class\" : \"%s\",@,\
     %a\
     \"line\" : %d,@,\
     \"column\" : %d,@,\
     \"value\" : \"%s\"\
     @]@.}@.\
    "
    (string_of_log_level level)
    pp_print_fname file
    lnum cnum msg


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
end

module Make (R : sig val printf_relay : 'a m_log_printer end) : SLog = struct

  (* ********************************************************************** *)
  (* Generic logging functions                                              *)
  (* ********************************************************************** *)

  (* Log a message with source and log level *)
  let log level fmt =

    let mdl = get_module () in

    match !log_format with 
    | F_pt -> printf_pt mdl level fmt
    | F_xml -> printf_xml mdl level fmt
    | F_json -> printf_json mdl level fmt
    | F_relay -> R.printf_relay mdl level fmt


  (* Unconditionally logs a message. *)
  let log_uncond fmt =

    let mdl = get_module () in

    match !log_format with 
    | F_pt -> printf_pt_uncond mdl fmt
    | F_xml -> printf_xml mdl L_info fmt
    | F_json -> printf_json mdl L_info fmt
    | F_relay -> R.printf_relay mdl L_info fmt
                   
end


include Make (struct let printf_relay _ _ _ = failwith "Uninitialized" end)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
