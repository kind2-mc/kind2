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

(** Datatypes and helper function for the SMT solver interface

    @author Christoph Sticksel *)

(** {1 Logics} *)

(** The defined logics in SMTLIB *)
type logic = 
  [ `detect
  | `AUFLIA
  | `AUFLIRA
  | `AUFNIRA
  | `LRA 
  | `LIA
  | `QF_ABV
  | `QF_AUFBV
  | `QF_AUFLIA
  | `QF_AX
  | `QF_BV
  | `QF_IDL
  | `QF_LIA
  | `QF_LRA
  | `QF_NIA
  | `QF_NRA
  | `QF_RDL
  | `QF_UF
  | `QF_UFBV
  | `QF_UFIDL
  | `QF_UFLIA
  | `QF_UFLRA
  | `QF_UFNRA
  | `UFLIA
  | `UFLRA
  | `UFNIA
  ]


(** {1 Sorts} *)

(** An SMT sort is of type {!Type.t} *)
type sort = Type.t

(** An SMT expression is of type {!Term.t} *)
type t = Term.t


(** {1 Solver commands and responses} *)


(** Arguments to a custom command *)
type custom_arg = 
  | ArgString of string  (** String argument *)
  | ArgExpr of t      (** Expression argument *)


(** Solver response from a command *)
type response =
  | NoResponse
  | Unsupported
  | Success 
  | Error of string

     
(** Solver response from a [(check-sat)] command *) 
type check_sat_response =
  | Response of response
  | Sat
  | Unsat
  | Unknown


(** {1 Conversions between SMT expressions and terms} *)

(** Convert a variable to an SMT expression *)
val smtexpr_of_var : Var.t -> t

(** Convert a term to an SMT expression *)
val smtexpr_of_term : t -> t

(** Convert a term to an SMT expression, quantifying over the given variables 

    [quantified_smtexpr_of_term q v t] returns the SMT expression
    [exists (v) t] or [forall (v) t] if q is true or false,
    respectively, where all variables in [t] except those in [v] are
    converted to uninterpreted functions. *)
val quantified_smtexpr_of_term : bool -> Var.t list -> t -> t

(** Convert an SMT expression to a variable *)
val var_of_smtexpr : t -> Var.t

(** Convert an SMT expression to a term *)
val term_of_smtexpr : t -> t

(** Declare uninterpreted symbols in the SMT solver *)
val declare_smt_symbols : (string -> sort list -> sort -> response) -> response

(** {1 Conversions from S-expressions} *)

(** Convert an S-expression of strings to a term *)
val type_of_string_sexpr : HStringSExpr.t -> sort

(** Convert an S-expression of strings to a term *)
val expr_of_string_sexpr : HStringSExpr.t -> t

(** Convert an S-expression of strings to a command response *)
val response_of_sexpr : HStringSExpr.t -> response

(** Convert an S-expression of strings to a check-sat command response *)
val check_sat_response_of_sexpr : HStringSExpr.t -> check_sat_response

(** Convert an S-expression of strings to a get-value response *)
val get_value_response_of_sexpr : HStringSExpr.t -> response * (t * t) list

(** Convert an S-expression of strings to a get-unsat-core response *)
val get_unsat_core_response_of_sexpr : HStringSExpr.t -> response * (string list)

(** Convert an S-expression of strings to a response for a custom command *)
val get_custom_command_response_of_sexpr : HStringSExpr.t -> response


(** {1 Pretty-printing and String Conversions} *)

(** Return an SMTLIB string expression for the logic *)
val string_of_logic : logic -> string 

(** Pretty-print a logic in SMTLIB format *)
val pp_print_logic : Format.formatter -> logic -> unit

(** Pretty-print a sort in SMTLIB format *)
val pp_print_sort : Format.formatter -> sort -> unit

(** Return an SMTLIB string expression of a sort *)
val string_of_sort : sort -> string

(** Pretty-print a term in SMTLIB format *)
val pp_print_expr : Format.formatter -> t -> unit

(** Pretty-print a term in SMTLIB format to the standard formatter *)
val print_expr : t -> unit

(** Return an SMTLIB string expression of a term *)
val string_of_expr : t -> string

(** Pretty-print a custom argument *)
val pp_print_custom_arg : Format.formatter -> custom_arg -> unit

(** Return an string representation of a custom argument  *)
val string_of_custom_arg : custom_arg -> string

(** Pretty-print a response to a command *)
val pp_print_response :  Format.formatter -> response -> unit

(** Pretty-print a response to a check-sat command *)
val pp_print_check_sat_response :  Format.formatter -> check_sat_response -> unit

(** Pretty-print a response to a get-value command *)
val pp_print_get_value_response :  Format.formatter -> response * (t * t) list -> unit

(** Pretty-print a response to a get-unsat-core command *)
val pp_print_get_unsat_core_response :  Format.formatter -> response * (string list) -> unit

(** Pretty-print a response to a custom command *)
val pp_print_custom_command_response :  Format.formatter -> response * (HStringSExpr.t list) -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
