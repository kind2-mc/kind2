(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(** Realizability of a function contract with temporal operators by a
    function, which is applied to its input streams pointwise *)

(** A trace of the inputs of a function *)
type trace = (StateVar.t * Model.value list) list

type result =
  | Realizable of (StateVar.t * Term.t) list
  (** A definition of each output by a term over the current values of the
      inputs, at offset zero, that realizes the contract *)
  | Unrealizable of (int * trace) list
  (** Input traces, with their lengths, on which no function satisfies the
      contract *)
  | Unknown

(** Whether the contract-check analysis [param] is that of a function whose
    contract has state, for which realizability by a reactive component
    does not imply realizability by a function *)
val applies : 'a InputSystem.t -> Analysis.param -> bool

(** [check analyze in_sys param] checks whether the contract of the
    function of the contract-check analysis [param] is realizable by a
    function. It is meant to be run once the contract is known to be
    realizable by a reactive component. *)
val check :
  'a Realizability.analyze_func -> 'a InputSystem.t -> Analysis.param -> result

(** Print the definitions of the outputs of a function *)
val pp_print_witness :
  'a InputSystem.t -> TransSys.t -> Format.formatter ->
  (StateVar.t * Term.t) list -> unit

(** Print a certificate that no function realizes a contract, in plain
    text, JSON, and XML *)
val pp_print_certificate_pt : Format.formatter -> (int * trace) list -> unit
val pp_print_certificate_json : Format.formatter -> (int * trace) list -> unit
val pp_print_certificate_xml : Format.formatter -> (int * trace) list -> unit
