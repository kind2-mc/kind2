(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015-2018 by the Board of Trustees of the University of Iowa

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

(** Term simplifier 

    Simplify a term by evaluating operations with constants. 

    Integer and real terms are converted to polynomials, terms in that
    cannot be reduced to addition or linear multiplication become new
    variables in the polynomials.

    Boolean terms are converted to negation normal form, such that
    only the operators conjunction, disjunction and negation occur.

    Relations between polynomials such as [c + a*x > d + b*y] are
    converted to [c - d + a*x - b*y > 0] where [c-d > 0] or [c-d = 0]
    and [a>0] if term [x] is ordered before term [y]m otherwise [b>0].

    Let bindings are unfolded. In order to evaluate a term with a
    partial model for its variables, bind each variable in the model
    to its value or use the convenience function
    {!simplify_term_model}. To make a model total, give a function in
    the optional argument [~default_of_var] that returns the value to
    assign to the variable given as parameter.

    @author Christoph Sticksel
    @author Adrien Champion
    @author Alain Mebsout
    @author Daniel Larraz
*)

(** Returns true iff a division by zero happened in a simplification since
    this function was last called. *)
val has_division_by_zero_happened: unit -> bool

(** Simplify a term *)
val simplify_term : (UfSymbol.t * (Var.t list * Term.t)) list -> Term.t -> Term.t

(** Simplify a term given an assignment to variables

    The optional parameter [default_of_var] may be a function that
    assigns a default value per variable, for example, to smooth a
    partially defined model. The defaults for variables must not be
    circular, otherwise the simplification will cycle. *)
val simplify_term_model : ?default_of_var:(Var.t -> Term.t) -> (UfSymbol.t * (Var.t list * Term.t)) list -> Model.t -> Term.t -> Term.t

(** Remove some ITE applications without introducing new symbols *)
val remove_ite : Term.t -> Term.t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
