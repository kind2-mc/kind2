(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020-2021 by the Board of Trustees of the University of Iowa

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

(** Checking of realizability of contracts and other sanity checks over contracts

    @author Daniel Larraz
*)

(** Result of a realizability check *)
type realizability_result =
  | Realizable
  | Unrealizable
  | Unknown

(** Checks whether there exists an implementation that satisfies a given specification

    [check_contract_realizability i s] checks whether the contract represented by
    transition system [s] is realizable or not. It assumes [s] was generated from
    the contract of the subsystem in [i] which has the same scope than [s].
*)
val check_contract_realizability: 'a InputSystem.t -> TransSys.t -> realizability_result

(** Result of a satisfiability check *)
type satisfiability_result =
  | Satisfiable
  | Unsatisfiable
  | Unknown

(** Checks whether a given specification is satisfiable

    [check_contract_satisfiability i s] checks whether the contract represented by
    transition system [s] is satisfiable or not.
*)
val check_contract_satisfiability: TransSys.t -> satisfiability_result
