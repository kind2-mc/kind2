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

(** Logging and messaging *)

(** Every relevant event must be logged through the functions in this module
    but only for ingle-process mode. Use {! Event} for multi-process mode.

    @author Christoph Sticksel, Alain Mebsout
*)

module type Sig = sig

  type 'a log_printer =
    Lib.log_level ->
    ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
  
  type 'a m_log_printer =
    Lib.kind_module -> 'a log_printer
  
  (** {1 Logging} *)

  (** Set module currently running *)
  val set_module : Lib.kind_module -> unit 

  (** Get module currently running *)
  val get_module : unit -> Lib.kind_module

  (** Format of log messages *)
  type log_format = 
    | F_pt    (** Plain text *)
    | F_xml   (** XML *)
    | F_json  (** JSON *)
    | F_relay (** Relayed *) 

  (** Returns the log format *)
  val get_log_format : unit -> log_format

  (** Chooses the log format *)
  val set_log_format : log_format -> unit

  (** Set log format to plain text *)
  val set_log_format_pt : unit -> unit

  (** Set log format to XML *)
  val set_log_format_xml : unit -> unit

  (** Set log format to JSON *)
  val set_log_format_json : unit -> unit

  (** Relay log messages to invariant manager, takes printing function as
      argument for relay messages. *)
  val set_relay_log : unit -> unit

  (** Cancel relaying of log messages *)
  val unset_relay_log : unit -> unit


  (** {1 Auxiliary functions} *)

  val pp_print_kind_module_xml_src : Format.formatter -> Lib.kind_module -> unit

  val print_xml_trailer : unit -> unit

  val printf_xml : 'a m_log_printer

  val printf_json : 'a m_log_printer

  val parse_log_xml : Lib.log_level -> Lib.position -> string -> unit

  val parse_log_json : Lib.log_level -> Lib.position -> string -> unit

end

(** Logging functions accessible directly *)
include Sig

module type SLog = sig

  (** [log m l f v ...] outputs a message from module [m] on level [l],
      formatted with the parameterized string [f] and the values [v ...] *)
  val log : 'a log_printer

  (** [log_uncond m f v ...] outputs a message from module [m] unconditionally,
      formatted with the parameterized string [f] and the values [v ...] *)
  val log_uncond : ('a, Format.formatter, unit) format -> 'a

end


(** Create a logging module parameterized by a relay function *)
module Make (R : sig val printf_relay : 'a m_log_printer end) : SLog


(** One instance without relay is available directly *)
include SLog




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
