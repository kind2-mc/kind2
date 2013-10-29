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

(** Polynomials
    
    The basic data structure used in Cooper quantifier elimination

    @author Ruoyu Zhang
*)

(** psummand is a constant or a variable with coefficient *)
type psummand = int * (Var.t option)

(** poly is a list of psummands *)
type poly = psummand list

(** For a polynomial p and integer i, a Presburger Atom could be p > 0, p = 0, p != 0, i | p, i !| p *)
type preAtom =
   | GT of poly
   | EQ of poly
   | INEQ of poly
   | DIVISIBLE of (int * poly)
   | INDIVISIBLE of (int * poly)

(** cformula is a list of Presburger Atom conjuncted together *)
type cformula = preAtom list

(** Print a polynomial *)
val pp_print_poly : Format.formatter -> poly -> unit

(** Print a cformula *)
val pp_print_cformula : Format.formatter -> cformula -> unit

(** Return true when the polynomial is a constant, false otherwise *)
val poly_is_constant : poly -> bool

(** Return the coefficient of a variable in a polynomial *)
val get_coe_in_poly : Var.t -> poly -> int

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
