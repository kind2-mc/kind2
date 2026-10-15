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

(** Parse and type check the script in a file, without translating it *)
val check_file : string -> (unit, error) result

(** The MoXI name of a function defined with [define-fun], given the symbol
    it is translated to, which has a fresh name *)
val moxi_name_of_uf : UfSymbol.t -> string option

(** The name of a subsystem call of a system, given the system and the
    instance of the call *)
val call_name : TransSys.t -> TransSys.instance -> string

(** Parse, type check and translate the script in a file into one
    transition system per [check-system] command, in the order of the
    script, each with the names of
    its properties that are current-state formulas, and the logic set
    with [set-logic], if any *)
val of_file :
  string ->
  ((system_check * string list) list * string option, error) result
