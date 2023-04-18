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

(** Prefix for logging testgen related things. *)
val log_prefix: string

(** Entry point. *)
val main :
  Analysis.param -> _ InputSystem.t -> TransSys.t -> string -> string list

(** Logs the top level XML glue file. *)
val log_test_glue_file:
  string ->
  string ->
  (string * (Position.position * int) list * (string * Position.position * int) list) ->
  string ->
  string list ->
  unit

(** Clean exit. *)
val on_exit: 'a -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
