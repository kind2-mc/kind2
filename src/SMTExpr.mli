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

    @author Alain Mebsout, Christoph Sticksel *)

open SolverResponse

(** {1 Sorts} *)

(** An SMT sort is of type {!Type.t} *)
type sort = Type.t

(** An SMT expression is of type {!Term.t} *)
type t = Term.t

(** An SMT variable is of type {!Var.t} *)
type var = Var.t


(** Arguments to a custom command *)
type custom_arg = 
  | ArgString of string  (** String argument *)
  | ArgExpr of t      (** Expression argument *)


(** {1 Pretty-printing and String Conversions} *)

module type Conv =
sig 

  (** {2 Conversions between SMT expressions and terms} *)

  (** Convert a variable to an SMT expression *)
  val smtsort_of_type : Type.t -> sort

  (** Convert a variable to an SMT expression *)
  val smtexpr_of_var :  Var.t -> Term.t list -> t

  (** {2 Pretty-printing and String Conversions} *)

  (** Return an SMTLIB string expression for the logic *)
  val string_of_logic : Term.logic -> string 

  (** Pretty-print a logic in SMTLIB format *)
  val pp_print_logic : Format.formatter -> Term.logic -> unit

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

  (** Convert a term to an SMT expression *)
  val smtexpr_of_term : t -> t

  (** Convert a term to an SMT expression, quantifying over the given
      variables [quantified_smtexpr_of_term q v t] returns the SMT expression
      [exists (v) t] or [forall (v) t] if q is true or false, respectively,
      where all variables in [t] except those in [v] are converted to
      uninterpreted functions. *)
  val quantified_smtexpr_of_term : bool -> Var.t list -> t -> t

  (** Convert an SMT expression to a variable *)
  val var_term_of_smtexpr : t -> t

  (** Convert an SMT expression to a term *)
  val term_of_smtexpr : t -> t

  (** Pretty-print a custom argument *)
  val pp_print_custom_arg : Format.formatter -> custom_arg -> unit

  (** Return an string representation of a custom argument  *)
  val string_of_custom_arg : custom_arg -> string

end


module Converter : functor (D : SolverDriver.S) -> Conv


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
