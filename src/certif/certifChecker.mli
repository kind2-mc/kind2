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

(** Error the certification can raise. *)
exception CouldNotProve of (Format.formatter -> unit)

(** Generate a certificate from a (possibly) proved system. It is written in
    the file <input_file>.certificate.smt2 placed in the current directory by
    default. It is bundled with an SMT2 script to check its validity. *)
val generate_certificate : TransSys.t -> string -> unit


(** Generate a system for observational equivalence for the frontend
    translation / simplification phases as a system in native input. To be
    verified, this certificate is expected to be fed back to Kind 2. *)
(* val generate_frontend_obs : 'a InputSystem.t -> TransSys.t -> string -> unit *)


(** Generate intermediate SMT-LIB 2 certificates in the directory given by
    {!Flags.output_dir}. *)
val generate_smt2_certificates : 'a InputSystem.t -> TransSys.t -> unit


(** Generate LFSC proofs in the directory given by {!Flags.output_dir}. *)
val generate_all_proofs : int -> 'a InputSystem.t -> TransSys.t -> unit

(** Minimization of certificate: returns the minimum bound for k-induction and
  a list of useful invariants for this preservation step.

  The second parameter is an optional list of properties
  (if None, all the safe properties are considered).

  The third parameter is an optional predicate that forces the minimization
  to only consider invariants that evaluates to true. *)
val minimize_invariants : TransSys.t -> Term.t list option ->
    (Term.t -> bool) option -> int * Term.t list

(** Returns true if the term contains at least two different var offsets *)
val is_two_state : Term.t -> bool
