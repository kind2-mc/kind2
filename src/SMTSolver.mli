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


(** A generic SMT solver

    Use the functor {!Make} to create an SMT solver module
    instantiated to a concrete solver interface. Currently only a
    solver that is passed SMTLIB2 commands on standard output is
    available, see the module {!SMTLIBSolver}.

    The solver does not have explicit constructors for expressions,
    instead data structure for input and output is {!SMTExpr.t}.

    @author Christoph Sticksel
*)

(** Input signature to the {!Make} functor *)
module type Solver = 
sig 

  (** {1 Types} *)

  (** Solver instance *)
  type t

  (** {1 Create and delete solver instances} *)

  (** [create_instance l] creates a new instance of the SMT solver,
      initialized to the logic [l] and produces assignments if the
      optional labelled argument [produce_assignments] is [true],
      models if [produce_models] is true, proofs if [produce_proofs]
      is true and unsatisfiable cores if [produce_cores] is true. *)
  val create_instance : 
    ?produce_assignments:bool -> 
    ?produce_models:bool -> 
    ?produce_proofs:bool -> 
    ?produce_cores:bool -> 
    SMTExpr.logic -> 
    t

  (** [delete_instance s] deletes the solver instance [s] *)
  val delete_instance : t -> unit

  (** {1 Declarations} *)

  (** Declare a new function symbol *)
  val declare_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.response

  (** Define a new function symbol as an abbreviation for an expression *)
  val define_fun : t -> string -> SMTExpr.var list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  (** {1 Commands} *)
    
  (** Assert the expression *)
  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  (** Push a number of empty assertion sets to the stack *)
  val push : t -> int -> SMTExpr.response 

  (** Pop a number of assertion sets from the stack *)
  val pop : t -> int -> SMTExpr.response 

  (** Check satisfiability of the asserted expressions 

      The optional parameter [timeout] limits the maximum runtime to the
      given number of milliseconds *)
  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

  (** Check satisfiability of the asserted expressions plus the input
      literals.

      The optional parameter [timeout] limits the maximum runtime to the
      given number of milliseconds *)
  val check_sat_assuming :
    ?timeout:int -> t -> SMTExpr.t list -> SMTExpr.check_sat_response

  (** Get the assigned values of expressions in the current model *)
  val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list

  (** Get an unsatisfiable core of named expressions *)
  val get_unsat_core : t -> SMTExpr.response * string list

  (** Execute a custom command and return its result 

      [execute_custom_command s c a r] sends a custom command [s] with
      the arguments [a] to the solver instance [s]. The command
      expects [r] S-expressions as result in case of success and
      returns a pair of the success response and a list of
      S-expressions. *)
  val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

  val execute_custom_check_sat_command : string -> t -> SMTExpr.check_sat_response

end

val smtsolver_module : unit -> (module Solver)


(** Output signature of the {!Make} functor *)
module type S =
sig

  type solver_t 

  (** Solver instance *)
  type t

  (** {1 Create and delete solver instances} *)

  (** [create_instance l] creates a new instance of the SMT solver,
      initialized to the logic [l] and produces assignments if the
      optional labelled argument [produce_assignments] is [true],
      models if [produce_models] is true, proofs if [produce_proofs]
      is true and unsatisfiable cores if [produce_cores] is true. *)
  val create_instance : 
    ?produce_assignments:bool -> 
    ?produce_models:bool -> 
    ?produce_proofs:bool -> 
    ?produce_cores:bool -> 
    SMTExpr.logic -> 
    t

  (** [delete_instance s] deletes the solver instance [s] *)
  val delete_instance : t -> unit

  (** {1 Declarations} *)

  (** Declare a new function symbol *)
  val declare_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.response

  (** Define a new function symbol as an abbreviation for an expression *)
  val define_fun : t -> string -> SMTExpr.var list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  (** {1 Commands} *)
    
  (** Assert the expression *)
  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  (** Push a number of empty assertion sets to the stack *)
  val push : t -> int -> SMTExpr.response 

  (** Pop a number of assertion sets from the stack *)
  val pop : t -> int -> SMTExpr.response 

  (** Check satisfiability of the asserted expressions *)
  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

  (** Check satisfiability of the asserted expressions *)
  val check_sat_assuming : ?timeout:int -> t -> SMTExpr.t list -> SMTExpr.check_sat_response

  (** Get the assigned values of expressions in the current model *)
  val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list

  (** Get an unsatisfiable core of named expressions *)
  val get_unsat_core : t -> SMTExpr.response * string list

  (** Execute a custom command and return its result 

      [execute_custom_command s c a r] sends a custom command [s] with
      the arguments [a] to the solver instance [s]. The command
      expects [r] S-expressions as result in case of success and
      returns a pair of the success response and a list of
      S-expressions. *)
  val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

  (** Execute a custom check-sat command and return its result *)
  val execute_custom_check_sat_command : string -> t -> SMTExpr.check_sat_response

end

(** Functor to create a generic SMT solver *)
module Make (S : Solver) : S with type solver_t = S.t 

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
