(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015-2020 by the Board of Trustees of the University of Iowa

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

(** Quantifier elimination

    @author Christoph Sticksel
    @author Adrien Champion
    @author Alain Mebsout
    @author Daniel Larraz
*)

exception QuantifiedTermFound of Term.t

(** The functions in this module are stafeful. They reuse
    the same solver instance and initial declarations unless
    [on_exit] is called in between
*)

(** Set the upper bound used in the initial declaration of the variables *)
val set_ubound : Numeral.t -> unit

(** Get the upper bound used in the initial declaration of the variables *)
val get_ubound : unit -> Numeral.t

(** [generalize f m] evaluates the term [f] with the model [m] and
    returns a term [g] that is implied by the model [m] and that
    implies the term f with the post-state variables existentially
    quantified. The returned term [g] contains only pre-state
    variables.

    [M |= g]

    [g |= exists y f\[y\]]

    with [y] being the vector of post-state variables in f.
    
*)
val generalize : TransSys.t -> (UfSymbol.t * (Var.t list * Term.t)) list -> Model.t -> Var.t list -> Term.t -> Term.t list

type response = Valid of Term.t | Invalid of Term.t

(** [ae_val s p v c] returns [Valid t] if (\forall vars(p). p => \exists v. c)
    is valid, otherwise it returns [Invalid t]. In both cases, [t] is such that
    (\forall vars(p). p => t <=> \exists v. c)
*)
val ae_val : TransSys.t -> Term.t -> Var.t list -> Term.t -> response

(** Cleanup before exit *)
val on_exit : unit -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
