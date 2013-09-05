(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
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

(** An interface to any SMT solver that accepts the SMTLIB 1.2
    benchmark files. 

    The SMTLIB 1.2 language is not incremental and does not support
    obtaining models. Therefore, a solver instance is unusable after a
    check-sat command and in fact should terminate. 

    If the solver produces output after a command, use the custom
    command instead and give the number of expected S-expressions as a
    parameter.

    Use this module as input to the {!SMTSolver.Make} functor 

    @author Christoph Sticksel
*)

(** {1 Basic types} *)

(** A solver instance *)
type t 


(** Configuration *)
type config = 
    { solver_cmd : string array;  (** Command line for the solver
                                      
                                      The executable must be the first
                                      element in the array, each
                                      subsequent string is an argument
                                      that is passed to
                                      [Unix.open_process] as is. *)

    }


(** {1 Managing solver instances} *)

(** [create_instance c l] creates a new instance of the a generic
    SMTLIB solver that is executed as [c], initialized to the logic
    [l] and produces assignments if the optional labelled argument
    [produce_assignments] is [true], models if [produce_models] is
    true, proofs if [produce_proofs] is true and unsatisfiable cores
    if [produce_cores] is true. *)
val create_instance : 
  ?produce_assignments:bool -> 
  ?produce_models:bool -> 
  ?produce_proofs:bool -> 
  ?produce_cores:bool -> 
  config -> 
  SMTExpr.logic -> 
  t

(** [delete_instance s] deletes the solver instance [s] by sending the
    exit command and waiting for the solver process to exit *)
val delete_instance : t -> unit


(** {1 Declaring Sorts and Functions} *)

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
val check_sat : t -> SMTExpr.check_sat_response

(** Get the assigned values of expressions in the current model *)
val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list


(** Execute a custom command and return its result

    [execute_custom_command s c a r] sends a custom command [s] with
    the arguments [a] to the solver instance [s]. The command
    expects [r] S-expressions as result in case of success and
    returns a pair of the success response and a list of
    S-expressions. *)
val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

(** Execute a custom check-sat command and return its result *)
val execute_custom_check_sat_command : t -> string -> SMTExpr.check_sat_response

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
