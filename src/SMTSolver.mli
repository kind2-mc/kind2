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

(** High-level methods for an SMT solver 

    @author Alain Mebsout, Christoph Sticksel *)


(** Type of a solver instance *)
type t

(** {1 Creating and finalizing a solver instance} *)

(** Create a new instance of an SMT solver of the given kind and with
    the given flags *)
val create_instance :
  ?produce_assignments:bool ->
  ?produce_proofs:bool ->
  ?produce_cores:bool ->
  TermLib.logic ->
  Flags.smtsolver ->
  t

(** Delete an instance of an SMT solver *)
val delete_instance : t -> unit

(** Return the unique identifier of the solver instance *)
val id_of_instance : t -> int
  
(** {1 Declarations} *)

(** Define uninterpreted symbol *)
val declare_fun : t -> UfSymbol.t -> unit

(** Define uninterpreted symbol *)
val define_fun : t -> UfSymbol.t -> Var.t list -> Term.t -> unit


(** {1 Primitives} *)

(** Assert an SMT expression in the current context *)
val assert_expr : t -> SMTExpr.t -> unit

(** Convert a term to an SMT expression and assert *)
val assert_term : t -> Term.t -> unit

(** Name a term, convert a term to an SMT expression and assert *)
val assert_named_term : t -> SMTExpr.t -> unit

(** Push a new scope to the context stack *)
val push : ?n:int -> t -> unit

(** Pop one scope from the context stack *)
val pop : ?n:int -> t -> unit

(** Check satisfiability of the current context 

    The optional parameter [timeout] limits the maximum runtime to
    the given number of milliseconds. *)
val check_sat : ?timeout:int -> t -> bool

(** Return a model of the current context if satisfiable *)
val get_model : t -> Model.t

(** Return a values of the terms in the current context if
    satisfiable *)
val get_var_values : t -> Var.t list -> Model.t

(** Return a values of the terms in the current context if
    satisfiable *)
val get_term_values : t -> Term.t list -> (Term.t * Term.t) list

(** Return an unsatisfiable core of named expressions if the current
    context is unsatisfiable *)
val get_unsat_core_of_names : t -> Term.t list

(** Interpret unsatisfiable core as names and return corresponing terms *)
val get_unsat_core_of_names : t -> Term.t list
  
(** Interpret unsatisfiable core as literals and return as terms *)
val get_unsat_core_lits : t -> Term.t list


(** {1 Higher-level functions} *)

(** Checks satisfiability of the current context assuming the given
    list of literals, and evaluate one of two continuation functions
    depending on the result

    [check_sat_assuming s t f l] assumes each of the literals in [l]
    to be true, and checks satisfiablilty of the context of the SMT
    solver instance [s]. If the solver returns satisfiable, the
    continuation [t] is evaluated, and if the solver returns
    unsatisfiable, the continuation [f] is evaluated.

    The list [l] should contain only positive Boolean constants,
    although this is not enforced. If the solver does not support the
    [check-sat-assuming] command it is simulated by asserting the
    literals on a new context. *)
val check_sat_assuming : t ->

  (* If sat. *)
  (unit -> 'a) ->

  (* If unsat. *)
  (unit -> 'a) ->

  (* Literals to assert. *)
  Term.t list ->

  'a

(** Execute the a custom command with the given arguments, and expect
    the given number of S-expressions as a result *)
val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int ->
  SolverResponse.custom_response

(** Execute the a custom command in place of check-sat *)
val execute_custom_check_sat_command :
  string -> t -> SolverResponse.check_sat_response


(** {1 Utility functions} *)

val converter : t -> (module SMTExpr.Conv)

val kind : t -> Flags.smtsolver

(** Output a comment into the trace *)
val trace_comment : t -> string -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
