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

(** Result returned by an analysis. *)
type analysis_result =
  | Ok | Timeout | Error

(** Exit status for errors. *)
val status_error : int

(** Runs an analysis on a transition system with a list of modules to
    run. Handles spawning and destruction of the kid processes. *)
val run :
  TransSys.t ->
  Log.t ->
  Event.messaging_setup ->
  kind_module list -> analysis_result

(** Panic exit callable from the outside.  As of today only the
    background thread and the Kind 2 top module should use this. *)
val panic_exit : exn -> unit

(** Returns the exit code from an exception. *)
val status_of_exn : exn -> int

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
