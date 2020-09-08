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

(**
  Wraps a solver and provides a convenient interface for test generation.

  The goal is to be able to trigger the transition relations up to some [k].
  The wrapper thus maintains a list of actlits [a0 ; a1 ; a2 ; ... ; aN] such
  that, in the solver:
    a0 => Init(0)
    a1 => (and a0 T(0,1))
    a2 => (and a1 T(1,2))
    ...
    aN => (and aN-1 T(N-1,N))

  The client does not see this however, only the [k] at which the query should
  be made is specified. The wrapper unrolls the transition relation lazily
  whenever it is needed. See [nth_actlit_of].

  Note: [a0] is not really needed but is here for consistency.
*)

(* Stores the transition system, the solver, and the list of actlits. *)
type t

(** Creates a new solver wrapper. The first actlit activates init@0. *)
val mk: TransSys.t -> t

(** Destroys the underlying solver. *)
val rm: t -> unit

(** Restarts a solver. *)
val restart: t -> t

(** Comment trace for the underlying solver. *)
val comment: t -> string -> unit


(** [checksat t n term actlits terms]
    Checks the satisfiability of term [term] in conjunction with activation
    literals [actlits] with the system unrolled up to [n]. A fresh actlit is
    created for [term], and a check-sat with assumptions [term :: actlits] will
    be performed. The fresh actlit is deactivated at the end of the check.

    If sat, returns some of an association list yielding the values of [terms].
    Returns none otherwise.  *)
val checksat:
  t -> Numeral.t -> Term.t -> Term.t list -> ('a * Term.t) list
  -> (SMTSolver.t -> 'b)
  -> (('a * Term.t) list * 'b) option

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
