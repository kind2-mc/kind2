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

(** Type for the renderer context. *)
type t

(** Ininializes rendering. *)
val init : Lib.kind_module list -> t

(** Updates the slider of the renderer. *)
val update_slider : t -> unit

(** Updates the global statistics. *)
val update_master_stats : t -> TransSys.t -> unit

(** Updates the renderer with a new log message. *)
val printf_rendr :
  t -> Lib.kind_module -> Lib.log_level ->
  ('a, Format.formatter, unit) format ->
  'a

(** Updates the renderer with a proved property. *)
val proved_rendr :
  t -> Lib.kind_module -> Lib.log_level ->
  TransSys.t -> int option -> string ->
  unit

(** Updates the renderer with a disproved property. *)
val disproved_rendr :
  t -> Lib.kind_module -> Lib.log_level ->
  TransSys.t -> string -> (StateVar.t * Term.t list) list ->
  unit

(** Updates the statistics of a module. *)
val progress_rendr :
  t -> Lib.kind_module -> Lib.log_level -> int -> unit

(** Also updates the statistics of a module. *)
val stats_rendr :
  t -> Lib.kind_module -> Lib.log_level -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

