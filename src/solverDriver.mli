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


module type S = sig

  (** {2 Solver configuration options }*)

  (** Command line options *)
  val cmd_line : unit -> string array

  (** Internal command for check-sat with timeout in milliseconds*)
  val check_sat_limited_cmd : int -> string
    
  (** Returns [true] if check-sat-assuming functionality is supported *)
  val check_sat_assuming_supported : unit -> bool
    
  (** Special command for check-sat-assuming *)
  val check_sat_assuming_cmd : unit -> string


  (** Solver spcific headers to add at the beginning of the file *)
  val headers : unit -> string list

  (** File extension for traces *)
  val trace_extension : string

  (** Begin / end delimiters for comments *)
  val comment_delims : string * string

  (** Association list of strings to function symbols *) 
  val string_symbol_list : (string * Symbol.t) list

  (** Reserved words that are not supported *)
  val reserved_word_list : HString.t list

  (** Line comment delimiters *)
  val comment_delims : string * string


  (** {2 Sort conversions } *)

  (** Can interpret type in a supported sort. Fails on unsupported sorts. *)
  val interpr_type : Type.t -> Type.t

  (** Print a sort *)
  val pp_print_sort : Format.formatter -> Type.t -> unit

  (** Return an SMTLIB string expression of a sort *)
  val string_of_sort : Type.t -> string

  (** Convert an S-expression of strings to a type *)
  val type_of_string_sexpr : HStringSExpr.t -> Type.t


  (** Return an SMTLIB string expression for the logic *)
  val string_of_logic : Term.logic -> string 

  (** Pretty-print a logic in SMTLIB format *)
  val pp_print_logic : Format.formatter -> Term.logic -> unit



  (** Pretty-print a symbol *)
  val pp_print_symbol :  ?arity:int -> Format.formatter -> Symbol.t -> unit

  (** Return a string representation of a symbol *)
  val string_of_symbol : ?arity:int -> Symbol.t -> string 

  
end
