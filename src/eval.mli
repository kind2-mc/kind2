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

(** Term evaluator

    @author Christoph Sticksel *)

(** Type of value of a term *)
type value =
  | ValBool of bool
  | ValNum of Numeral.t
  | ValDec of Decimal.t
  | ValTerm of Term.t

(** Cast a value to a Boolean, raise [Invalid_argument] if value is
    not a Boolean *)
val bool_of_value : value -> bool

(** Cast a value to an integer, raise [Invalid_argument] if value is
    not an integer *)
val num_of_value : value -> Numeral.t

(** Cast a value to a float, raise [Invalid_argument] if value is
    not a float *)
val dec_of_value : value -> Decimal.t

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
