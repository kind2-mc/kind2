(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

type error =
  | UnexpectedChar of Lib.position * char
  | SyntaxError of Lib.position
  | TypeError of MoxiTypeChecker.error
  | Unsupported of Lib.position * string
    (** A well-sorted construct that kmoxi does not translate *)

(** Print an error as [file:line:column: error: message] *)
val pp_print_error : Format.formatter -> error -> unit

type system_check = TransSys.t SubSystem.t

(** How the reachability conditions of a query are encoded in its property,
    which a trail of the query depends on *)
type encoding =
  | Current_state_condition
    (** One condition over the current state, which the property is the
        negation of one step later: a counterexample has a last state that
        is not part of the witness *)
  | Next_state_condition
    (** One condition that may use next-state variables, which the property
        is the negation of in the transition to a state *)
  | Flags
    (** Several conditions, each recorded by a flag of whether it has held:
        a counterexample is the witness *)

(** The systems of a [check-system] command, one per group of its queries
    with the same assumptions and initiality condition, and the names of
    the queries with how each is encoded, in the order of the script. Each
    query is a property of the system of its group, named after the
    query. *)
type check =
{
  systems: system_check list ;
  queries: (string * encoding) list
}

(** Parse and type check the script in a file, without translating it *)
val check_file : string -> (unit, error) result

(** The MoXI name of a function defined with [define-fun], given the symbol
    it is translated to, which has a fresh name *)
val moxi_name_of_uf : UfSymbol.t -> string option

(** The name of a subsystem call, given the caller and the instance of the
    call. Raises [Failure] if the call has no name, which every call kmoxi
    builds has. *)
val call_name : TransSys.t -> TransSys.instance -> string

(** Parse, type check and translate the script in a file into the checks
    of its [check-system] commands, in the order of the script, and the
    logic set with [set-logic], if any *)
val of_file : string -> (check list * string option, error) result

(** The systems of checks *)
val subsystems_of_checks : check list -> system_check list
