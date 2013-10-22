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

(** Term evaluator

    @author Christoph Sticksel *)

(** Type of value of a term *)
type value =
  | ValBool of bool
  | ValInt of int
  | ValReal of float
  | ValTerm of Term.t

(** Cast a value to a Boolean, raise [Invalid_argument] if value is
    not a Boolean *)
val bool_of_value : value -> bool

(** Cast a value to an integer, raise [Invalid_argument] if value is
    not an integer *)
val int_of_value : value -> int

(** Cast a value to a float, raise [Invalid_argument] if value is
    not a float *)
val float_of_value : value -> float

(** Cast a value to a term, raise [Invalid_argument] if value is
    unknown *)
val term_of_value : value -> Term.t

(** Check if the value is unknown *)
val value_is_unknown : value -> bool



(** Evaluate a term to a value, given an assignment to all free
    variables *)
val eval_term : Term.t -> (Var.t * Term.t) list -> value

(*
(** Evaluate all subterms of the term to values and add to the hash
    table *)
val eval_subterms : value Term.TermNodeHashtbl.t -> Term.t -> (Var.t * Term.t) list -> unit
*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
