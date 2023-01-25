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
type model_path_as_list = (StateVar.t * Model.value list) list

(** Output a counterexample as a Lustre execution in JSON format *)
val pp_trail : _ InputSystem.t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit

val pp_model : TransSys.t -> Format.formatter -> model_path_as_list -> unit
