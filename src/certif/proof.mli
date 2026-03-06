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
(** Set the logic used by the proof generations mechanism *)
val set_proof_logic : TermLib.logic -> unit

val proofname_cpc : string

val frontend_proofname_cpc : string

val construct_kind_2_proof:   string -> string -> string -> string -> int -> unit

val construct_frontend_proof: string -> string -> string -> string -> int -> unit

val construct_safety_proof: string -> unit
