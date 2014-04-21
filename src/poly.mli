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

(** Polynomials
    
    The basic data structure used in Cooper quantifier elimination

    @author Ruoyu Zhang
*)

(** psummand is a constant or a variable with coefficient *)
type psummand = Numeral.t * (Var.t option)

(** poly is a list of psummands *)
type poly = psummand list

(** For a polynomial p and integer i, a Presburger Atom could be p > 0, p = 0, p != 0, i | p, i !| p *)
type preAtom =
   | GT of poly
   | EQ of poly
   | INEQ of poly
   | DIVISIBLE of (Numeral.t * poly)
   | INDIVISIBLE of (Numeral.t * poly)

(** cformula is a list of Presburger Atom conjuncted together *)
type cformula = preAtom list

(** Print a polynomial *)
val pp_print_poly : Format.formatter -> poly -> unit

(** Print a cformula *)
val pp_print_cformula : Format.formatter -> cformula -> unit

(** Return true when the polynomial is a constant, false otherwise *)
val poly_is_constant : poly -> bool

(** Return the coefficient of a variable in a polynomial *)
val get_coe_in_poly : Var.t -> poly -> Numeral.t

(** Multiply two polynomials, one of them must be constant *)
val multiply_two_polys : poly -> poly -> poly

(** Add two polynomials with a ordering of varialbes and a accumulator*)
val add_two_polys : (Var.t -> Var.t -> int) -> poly -> poly -> poly -> poly

(** Negate a polynomial *)
val negate_poly : poly -> poly

(** Return true when the psummand contains the variable, false otherwise *)
val psummand_contains_variable : Var.t -> psummand -> bool

(** Return true when the cformula contains the variable, false otherwise *)
val cformula_contains_variable : Var.t -> cformula -> bool

(** Comparison of variables: variables to be eliminated earlier are
    smaller, compare as terms if none is to be eliminated *)
val compare_variables : Var.t list -> Var.t -> Var.t -> int

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
