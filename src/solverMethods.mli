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

(** High-level methods for an SMT solver 

    @author Christoph Sticksel *)


(** Output signature of the {!Make} functor *)
module type S =
sig

  (** Solver returned an unknown as result *)
  exception Unknown

  (** The encapsulated module for lower level access to the solver *)
  module T : SMTSolver.S

  (** Type of a solver instance *)
  type t

  (** {1 Creating and finalizing a solver instance} *)

  (** Create a new instance of an SMT solver, declare all currently
      created uninterpreted function symbols *)
  val new_solver : ?produce_assignments:bool -> ?produce_models:bool -> ?produce_proofs:bool -> ?produce_cores:bool -> SMTExpr.logic -> t
    
  (** Delete an instance of an SMT solver *)
  val delete_solver : t -> unit
    
  (** {1 Primitives} *)

  (** Raise an exception if the response is not success *)
  val fail_on_smt_error : SMTExpr.response -> unit

  (** Assert a formula in the current context *)
  val assert_term : t -> Term.t -> unit

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

  (** Return an unsatisfiable core of named expressions if the current
      context is unsatisfiable *)
  val get_unsat_core : t -> int list

  (** {1 Higher-level functions} 

      These functions operate on a new scope level that is popped at
      the end of the functions. Hence, there are no side-effects on
      the context. *)

  (** Check satisfiability of the formula in the current context

      The optional parameter [timeout] limits the maximum runtime to
      the given number of milliseconds *)
  val check_sat_term : ?timeout:int -> t -> Term.t list -> bool

  (** Check satisfiability of the formula in the current context and
      return a model

      The optional parameter [timeout] limits the maximum runtime to
      the given number of milliseconds *)
  val check_sat_term_model : ?timeout:int -> t -> Term.t list -> bool * (Var.t * Term.t) list 

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
  val check_entailment_cex : ?timeout:int -> t -> Term.t list -> Term.t -> bool * (Var.t * Term.t) list 


  (** {1 Utility functions} *)

  (** For a model return a conjunction of equations representing the model *)
  val term_of_model : (Var.t * Term.t) list -> Term.t

end

(** Create high-level methods for a certain solver module *)
module Make (S : SMTSolver.S) : S with type t = S.t and type T.t = S.t  


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
