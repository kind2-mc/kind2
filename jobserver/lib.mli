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

(** Common functions 

    @author Jason Oxley, Christoph Sticksel **)

(** Pretty-print a list with given separator 

    [pp_print_list p s f l] pretty-prints the elements in the list [l]
    by calling the pretty-printer [p] on each, separating the elements
    by printing the string [s].

    In order to get line breaks between the elements, do not use a
    line feed character [\n] as separator, this might mess up
    indentation. Instead wrap the list into a vertical box with the
    format string [@\[<v>%a@\]] and the empty string as separator.
*)
val pp_print_list : (Format.formatter -> 'a -> unit) ->
('b, Format.formatter, unit) format -> Format.formatter -> 'a list -> unit


(** Get base 36 string representation of given 64-bit integer for
    unique identifiers *)
val base10tol : int64 -> string

(** Pretty-print a time as Jan 01 00:00:00 *)
val pp_print_time : Format.formatter -> float -> unit

(** Pretty-print a timestamp as [Jan 01 00:00:00] *)
val pp_print_timestamp : Format.formatter -> unit

(** Pretty-print status of a process *)
val pp_print_process_status : Format.formatter -> Unix.process_status -> unit

(** Server logfiles *)
type server_log = 
  | AccessLog
  | ErrorLog
  | WarningLog


(** Log a message to the given logfile *)
val log : server_log -> ('a, Format.formatter, unit) format -> 'a

(** Read until the end of the file, start at given position. Return
    string of bytes read and new position in file *)
val read_bytes : int -> string -> int * string 

val jobs_dir : string

val checker_cmd_and_args : string -> string list -> string * string list

val interpreter_cmd_and_args : string -> string list -> string * string list

val generate_uid : unit -> string

(** Get load average in a pseudo-portable way

   Try [/proc/loadavg] first (Linux), then execute [sysctl -n vm.loadavg] (Mac OS X) *)
val get_loadavg : unit -> float * float * float 

val load1_max : float

val load5_max : float

val load15_max : float

val job_purge_time : float 
