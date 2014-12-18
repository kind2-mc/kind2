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

    @author Christoph Sticksel *)



(** Type of a solver instance *)
type t

(** {1 Creating and finalizing a solver instance} *)

(** Create a new instance of an SMT solver, declare all currently
    created uninterpreted function symbols *)
val create_instance :
  ?produce_assignments:bool ->
  ?produce_proofs:bool ->
  ?produce_cores:bool ->
  Term.logic ->
  Flags.smtsolver ->
  t

(** Delete an instance of an SMT solver *)
val delete_instance : t -> unit

(** {1 Declarations} *)

(** Define uninterpreted symbol *)
val declare_fun : t -> UfSymbol.t -> unit

(** Define uninterpreted symbol *)
val define_fun : t -> UfSymbol.t -> Var.t list -> Term.t -> unit


(** {1 Primitives} *)

(** Raise an exception if the response is not success *)
val fail_on_smt_error : SolverResponse.response -> unit

(** Assert an smt expression in the current context *)
val assert_expr : t -> SMTExpr.t -> unit

(** Assert a formula in the current context *)
val assert_term : t -> Term.t -> unit

(** Assert the expression, naming it internally to retrieve it from
    an unsatisfiable core later *)
val assert_named_term : t -> SMTExpr.t -> unit

(** Push a new scope to the context stack *)
val push : ?n:int -> t -> unit

(** Pop one scope from the context stack *)
val pop : ?n:int -> t -> unit

(** Check satisfiability of the current context 

    The optional parameter [timeout] limits the maximum runtime to
    the given number of milliseconds *)
val check_sat : ?timeout:int -> t -> bool

(** Return a model of the current context if satisfiable *)
val get_model : t -> Var.t list -> (Var.t * Term.t) list

(** Return a values of the terms in the current context if
    satisfiable *)
val get_values : t -> Term.t list -> (Term.t * Term.t) list

(** Return an unsatisfiable core of named expressions if the current
    context is unsatisfiable *)
val get_unsat_core : t -> Term.t list

(** {1 Higher-level functions} 

    These functions operate on a new scope level that is popped at
    the end of the functions. Hence, there are no side-effects on
    the context. *)

(** Check satisfiability of the formula in the current context

    The optional parameter [timeout] limits the maximum runtime to
    the given number of milliseconds *)
val check_sat_term : ?timeout:int -> t -> Term.t list -> bool

val check_sat_assuming : t ->
  (* If sat. *)
  (unit -> 'a) ->
  (* If unsat. *)
  (unit -> 'a) ->
  (* Literals to assert. *)
  Term.t list ->
  'a

(** Check satisfiability of the formula in the current context and
    return a model

    The optional parameter [timeout] limits the maximum runtime to
    the given number of milliseconds *)
val check_sat_term_model :
  ?timeout:int -> t -> Term.t list -> bool * (Var.t * Term.t) list 

(** Check entailment of the second formula by the conjunction of the
    first formulas in the current context

    The optional parameter [timeout] limits the maximum runtime to
    the given number of milliseconds *)
val check_entailment : ?timeout:int -> t -> Term.t list -> Term.t -> bool

(** Check entailment of the second formula by conjunction of the
    first formulas in the current context and return a
    counterexample if the entailment is not valid

    The optional parameter [timeout] limits the maximum runtime to
    the given number of milliseconds *)
val check_entailment_cex :
  ?timeout:int -> t -> Term.t list -> Term.t -> bool * (Var.t * Term.t) list 


val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int ->
  SolverResponse.custom_response

val execute_custom_check_sat_command :
  string -> t -> SolverResponse.check_sat_response


(** {1 Utility functions} *)

(** For a model return a conjunction of equations representing the model *)
val term_of_model : (Var.t * Term.t) list -> Term.t


val converter : t -> (module SMTExpr.Conv)

val kind : t -> Flags.smtsolver

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
