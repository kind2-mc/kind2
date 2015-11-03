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



(** Generate a certificate from a (possibly) proved system. It is written in
    the file <input_file>.certificate.smt2 placed in the current directory by
    default. It is bundled with an SMT2 script to check its validity. *)
val generate_certificate : TransSys.t -> string -> unit


(** Generate a certificate for the frontend translation / simplification phases
    as a system in native input. To be verified, this certificate is expected
    to be fed back to Kind 2. *)
val generate_frontend_certificate : 'a InputSystem.t -> TransSys.t -> string -> unit


(** Generate all certificates in the directory given by {!Flags.certif_dir}. *)
val generate_all_certificates : 'a InputSystem.t -> TransSys.t -> unit
