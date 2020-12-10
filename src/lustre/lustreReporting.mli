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

(** 
    Error and warning Reporting functions 

 *)

val fail_at_position_pt: Lib.position -> string -> unit
(** Ouput a fail message  *)

val fail_at_position : Lib.position -> string -> 'a
(** Output a fatal error at position and raise an error *)

val warn_at_position_pt: Lib.log_level -> Lib.position -> string -> unit 
(** Output a warning at position at a given level  *)
  
val warn_at_position : Lib.position -> string -> unit 
(** Output a warning at position *)

val fail_no_position : string -> 'a
(** Output a fatal error without reporting a position and raise an error *)

val warn_no_position : string -> unit 
(** Output a warning without a position *)

val note_at_position: Lib.position -> string -> unit
(**  Ouput a note *)
