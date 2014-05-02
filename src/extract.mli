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

(** Extract an active path from a formula given a model

    @author Christoph Sticksel *)

(** Extract an active path from a formula and return a conjunction
    that is true in the model given.

    Assumption: the formula is satisfiable under the given partial
    assignment. Then, return an active path [g] in the formula [f],
    that is, a formula [g] that must be satisfied if the formula [f] is
    satisfied. *)
val extract : (UfSymbol.t * (Var.t list * Term.t)) list -> (Var.t * Term.t) list -> Term.t -> Term.t list * Term.t list

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
