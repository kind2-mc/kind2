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


(** Certificates for Kind 2. This contains the base type as well as some
    combinators for certificates.

    @author Alain Mebsout
*)


(** The type of certificates *)
type t = int * Term.t

type symbols = {
  vars : UfSymbol.t list;  (** Names of state variables for the system *)
  phi : string;  (** Name of function symbol for k-inductive invariant *)
  init : string;  (** Name of function symbol for init *)
  prop : string;  (** Name of function symbol for property *)
  trans : string;  (** Name of function symbol for transition relation *)
}

(** The type of certificates outputs, these are file names for the intermediate
    SMT-LIB 2 certificates *)
type out = {
  k: int;               (** k of certificate *)
  names: symbols;       (** names for I, T, P and PHI *)
  dirname : string;     (** Directory where certificates and proofs are
                            produced *)
  proofname : string;    (** Name for the final LFSC proof *)

  base : string;        (** File name for base case check *)
  induction : string;   (** File name for inductive case check *)
  implication : string; (** File name for implication of property check *)
  dummy_trace : string; (** File name for dummy file to trace function
                            definitions in LFSC *)
}


type system = {
  names : symbols;
  smt2_file : string;
  smt2_lfsc_trace_file : string;
}

type invariant = {
  k : int;
  name : string;
  dirname : string;
  phi_file : string;
  phi_lfsc_trace_file : string;
  base : string;        (** File name for base case check *)
  induction : string;   (** File name for inductive case check *)
  implication : string; (** File name for implication of property check *)
  for_system : system;
  kind2_system : system;
  jkind_system : system;
  obs_system : system;
}

(** Merge certificates into one. The resulting certificate is a certificate for
    the conjunction of the original invariants. *)
val merge : t list -> t


(** Split a certificate following the boolean strucutre of its inductive
    invariant *)
val split : t -> t list


(** Split a list of certificates *)
val split_certs : t list -> t list


(** Gives a measure to compare the size of the inductive invariants contained
    in a certificate. *)
val size : t -> int
