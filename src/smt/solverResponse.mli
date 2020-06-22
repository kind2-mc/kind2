(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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



(** {1 Solver commands and responses} *)


(** Type of reponses for errors *)
type error_response = [ `Error of string | `Timeout ]
                      
type no_response = [ `NoResponse ]

(** Type of reponses for declaration and definition commands *)
type decl_response = [
  | no_response
  | `Unsupported
  | `Success 
  | error_response
]

(** Type of reponses for check-sat commands *)
type check_sat_response = [
  | `Sat
  | `Unsat
  | `Unknown
  | error_response
]

(** Type of reponses for get-value commands. It carries the model. *)
type get_value_response = [
  | `Values of (Term.t * Term.t) list
  | error_response
]

(** Type of reponses for get-model commands. It carries the model. *)
type get_model_response = [
  | `Model of (UfSymbol.t * Model.value) list
  | error_response
]

(** Type of reponses for get-unsat-core commands. It carries the unsat core. *)
type get_unsat_core_response = [
  | `Unsat_core of string list
  | error_response
]

(** Type of reponses for custom commands *)
type custom_response = [
  | `Custom of HStringSExpr.t list
  | error_response
]

(** Type of all possible responses of a solver *)
type response = [
  | decl_response
  | check_sat_response
  | get_value_response
  | get_model_response
  | get_unsat_core_response
  | custom_response
]


(** Pretty-print a response to a command *)
val pp_print_response : Format.formatter -> response -> unit
