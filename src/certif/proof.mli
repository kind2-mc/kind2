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

(** Should we use abstract indexes for the proof generation *)
val abstr_index : unit -> bool

(** The file to store the LFSC proof of the properties. *)
val proofname : string

(** The file to store the LFSC proof the frontend *)
val frontend_proofname : string

(** The file to store the LFSC trusted formulas. *)
val trustfname : string

(** Generate the LFSC proof of invariance for the original properties and write
    it in the file [!proofname]. *)
val generate_inv_proof : Certificate.invariant -> unit

(** Generate the LFSC proof of safey by producing an intermediate proofs of
    observational equivalence for the frontend. The proof is written in the file
    [!frontend_proofname]. *)
val generate_frontend_proof : Certificate.invariant -> unit
