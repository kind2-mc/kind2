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

(** Filename of the final proof of safety *)
val safety_proofname_cpc : string

(** Creates the kind 2 CPC proofs of base, induction , and implication. 
Also outputs the combined "Safety CPC" proof of Kind 2 *)
val construct_kind_2_proof:   string -> string -> string -> string -> int -> unit

(** Creates the frontend (JKind) CPC proofs of base, induction , and implication. 
Also outputs the combined "Safety CPC" proof of the frontend  *)
val construct_frontend_proof: string -> string -> string -> string -> int -> unit

(** Combines the kind 2 and frontend safety CPC proofs into one proof of Safety in Safety CPC*)
val construct_safety_proof: string -> unit
