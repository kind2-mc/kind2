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

open SolverResponse

(** Solver paramters *)
module type Params = sig

  val produce_assignments : bool

  val produce_cores : bool

  val produce_proofs : bool

  (* The scope of the (sub)system under analysis. *)
  val scope : string list

  (* The current abstraction. *)
  val abstraction : string list list

  val logic : Term.logic

  val id : int

end



(** Sigature of a solver instance *)
module type Inst = sig

  module Conv: SMTExpr.Conv

  (** Delete and stops the instance of the solver *)
  val delete_instance : unit -> unit

  (** {1 Declarations} *)

  (** Declare a new function symbol *)
  val declare_fun : string -> SMTExpr.sort list -> SMTExpr.sort -> decl_response

  (** Define a new function symbol as an abbreviation for an expression *)
  val define_fun : string -> SMTExpr.var list -> SMTExpr.sort -> SMTExpr.t ->
    decl_response

  (** {1 Commands} *)

  (** Assert the expression *)
  val assert_expr : SMTExpr.t -> decl_response

  (** Push a number of empty assertion sets to the stack *)
  val push : int -> decl_response 

  (** Pop a number of assertion sets from the stack *)
  val pop : int -> decl_response 

  (** Check satisfiability of the asserted expressions 

      The optional parameter [timeout] limits the maximum runtime to the given
      number of milliseconds *)
  val check_sat : ?timeout:int -> unit -> check_sat_response

  (** Check satisfiability of the asserted expressions assuming the input
      literals. *)
  val check_sat_assuming : SMTExpr.t list -> check_sat_response

  (** Indicates whether the solver supports the check-sat-assuming command. *)
  val check_sat_assuming_supported: unit -> bool

  (** Get the assigned values of expressions in the current model *)
  val get_value : SMTExpr.t list -> get_value_response

  (** Get the assigned values of expressions in the current model *)
  val get_model : unit -> get_model_response

  (** Get an unsatisfiable core of named expressions *)
  val get_unsat_core : unit -> get_unsat_core_response

  (** Execute a custom command and return its result 

      [execute_custom_command s c a r] sends a custom command [s] with
      the arguments [a] to the solver instance [s]. The command
      expects [r] S-expressions as result in case of success and
      returns a pair of the success response and a list of
      S-expressions. *)
  val execute_custom_command : string -> SMTExpr.custom_arg list -> int ->
    custom_response

  val execute_custom_check_sat_command : string -> check_sat_response
  
  val trace_comment : string -> unit
  
end


module type S = sig


  (** {1 Managing solver instances} *)

  (** The functor [Create] creates a new instance of the SMT solver with
      paramters passed as its arguments. The parameter argument [P] conataints
      a unique identifier [id], initialized to the logic [l] and produces
      assignments if the optional labelled argument [produce_assignments] is
      [true], proofs if [produce_proofs] is true and unsatisfiable cores if
      [produce_cores] is true. *)
  module Create : functor (P : Params) -> Inst

end



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
