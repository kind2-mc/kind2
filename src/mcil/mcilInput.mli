(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

(** Parse a file in MCIL format into a transition system 

    @author Kian Weimer
*)

type subsystem_scope = string list
type sys_var_mapping = (subsystem_scope * StateVar.t list) list

type subsystem_instance_name_data = {
  map: (Lib.position * Dolmen.Std.Id.t) list;
  counter: int;
}

(* Additional data needed for counter example printing *)
(* May want to reduce this information in the future. *)
type metadata = {
  name_map: subsystem_instance_name_data;
  sys_var_mapping: (string list * StateVar.t list) list;
  enum_defs: DolmenUtils.enum list;
}

(** Parse from the file *)
val of_file : string -> 
  (TransSys.t SubSystem.t * metadata, [> McilErrors.error]) result
  (* (TransSys.t SubSystem.t, [> McilErrors.error]) result TODO Temporary return type switch back when finished *)
