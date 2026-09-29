(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(** Evaluation of recursive functions at concrete arguments

    The functions are defined, with SMT-LIB [define-funs-rec], in a solver
    of their own that knows nothing else of the system: recursive
    definitions are more than a solver can handle in the queries on a whole
    system, while an application at concrete arguments is unfolded in no
    time. The solver is started on the first evaluation, and started again
    after one that lost it, unless it failed on the definitions. *)

(** An evaluator *)
type t

(** [create ~logic ~timeout_ms define] is an evaluator whose solver is
    started with the logic [logic], gives every evaluation [timeout_ms]
    milliseconds when it takes a timeout per query (Z3 and cvc5), and is
    given the definitions of the functions, and the declarations of what
    they apply, by [define] *)
val create :
  logic:TermLib.logic -> timeout_ms:int -> (SMTSolver.t -> unit) -> t

(** The value of the functional symbol at the concrete arguments: [`Value v]
    if it has the one value [v], [`Not_unique] if it may take several, and
    [`Unknown] if the solver cannot tell in time. A definition that applies
    a symbol it does not define, such as the value of a call whose
    termination checks fail, may leave the value not unique. *)
val evaluate :
  t -> UfSymbol.t -> Term.t list ->
  [ `Value of Term.t | `Not_unique | `Unknown ]

(** Stop the solver of the evaluator, if it was started *)
val delete : t -> unit

(** Give every query of the solver a timeout of [ms] milliseconds, and
    return [true], if the solver takes a timeout per query (Z3 and cvc5);
    return [false] otherwise, the other solvers only taking a timeout for
    the whole of their life *)
val set_per_query_timeout : ms:int -> SMTSolver.t -> bool
