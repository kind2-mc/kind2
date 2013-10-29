(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
  val define_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

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


(** Input signature of the {!Make} functor *)
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
  val define_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  (** {1 Commands} *)
    
  (** Assert the expression *)
  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  (** Push a number of empty assertion sets to the stack *)
  val push : t -> int -> SMTExpr.response 

  (** Pop a number of assertion sets from the stack *)
  val pop : t -> int -> SMTExpr.response 

  (** Check satisfiability of the asserted expressions *)
  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

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
