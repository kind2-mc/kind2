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

(** Stores IO things to log testcases to xml. *)
type _ t

(* [mk sys root name title] creates a new IO struct for system [sys], in
   directory [root]. [name] is an ident-like description of the testgen
   strategy and [title] is a more verbose description. *)
val mk: 'a InputSystem.t -> TransSys.t -> string -> string -> string -> 'a t


(** Closes internal file descriptors. *)
val rm: 'a t -> unit

(** The number of testcases generated. *)
val testcase_count: 'a t -> int

(** The number of errors generated. *)
val error_count: 'a t -> int

(** [log_testcase t modes model k] logs a test case of length [k]
    represented by model [model] and activating modes [modes] using the info
    in [t]. *)
val log_testcase: 'a t -> Scope.t list list -> Model.t -> Numeral.t -> unit

(** [log_deadlock t modes model k] logs a deadlock trace of length [k]
    represented by model [model] and activating modes [modes] using the info
    in [t]. *)
val log_deadlock: 'a t -> Scope.t list list -> Model.t -> Numeral.t -> unit

(** Logs the top level XML glue file. *)
val log_test_glue_file:
  string ->
  string ->
  (string * (Lib.position * int) list * (string * Lib.position * int) list) ->
  string ->
  string list ->
  unit



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
