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


module type S = sig

  (** {2 Solver configuration options} *)

  (** Command line options *)
  val cmd_line : TermLib.logic -> bool -> bool -> bool -> bool -> string array

  (** Internal command for check-sat with timeout in milliseconds*)
  val check_sat_limited_cmd : int -> string
    
  (** Returns [true] if check-sat-assuming functionality is supported *)
  val check_sat_assuming_supported : unit -> bool
    
  (** Special command for check-sat-assuming *)
  val check_sat_assuming_cmd : unit -> string

  (** Solver specific headers to add at the beginning of the file *)
  val headers : unit -> string list

  (** Solver specific commands to add at the beginning of the file *)
  val prelude : string list

  (** File extension for traces *)
  val trace_extension : string

  (** Begin / end delimiters for comments *)
  val comment_delims : string * string

  (** {2 Sort conversions } *)

  (** Can interpret type in a supported sort. Fails on unsupported sorts. *)
  val interpr_type : Type.t -> Type.t

  (** Print a sort *)
  val pp_print_sort : Format.formatter -> Type.t -> unit

  (** Return an SMTLIB string expression of a sort *)
  val string_of_sort : Type.t -> string

  (** Return an SMTLIB string expression for the logic *)
  val string_of_logic : TermLib.logic -> string 

  (** Pretty-print a logic in SMTLIB format *)
  val pp_print_logic : Format.formatter -> TermLib.logic -> unit

  (** Pretty-print a symbol *)
  val pp_print_symbol :  ?arity:int -> Format.formatter -> Symbol.t -> unit

  (** Return a string representation of a symbol *)
  val string_of_symbol : ?arity:int -> Symbol.t -> string 

  (** Pretty-print an expression *)
  val pp_print_expr : Format.formatter -> Term.t -> unit

  (** Pretty-print an expression to the default formatter *)
  val print_expr : Term.t -> unit

  (** Return a string representation of an expression *)
  val string_of_expr : Term.t -> string

end
