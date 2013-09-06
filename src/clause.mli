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

(** Clauses: sets of literals 

    A clause is really just a set of terms which is to be understood
    as a disjunction. There is no guarantee that the terms are
    actually literals, see {!Literal} and {!CNF}.

    The sets do not contain duplicate literals, all function of a set
    from the standard library are supported. 

    @author Christoph Sticksel *)


(** A set of literals *)
type t  

(** The empty clause *)
val empty : t

(** The empty clause *)
val top : t

(** Return [true] if the clause is empty *)
val is_empty : t -> bool

(** Return [true] if the literal is the clause *)
val mem : Literal.t -> t -> bool

(** Add the literal to a clause *)
val add : Literal.t -> t -> t

(** Return the unit clause containing only the literal *)
val singleton : Literal.t -> t

(** Remove the literal from the clause *)
val remove : Literal.t -> t -> t

(** Return the union of two sets of literals *)
val union : t -> t -> t

(** Return the clause only containing literals in both clauses *)
val inter : t -> t -> t

(** Return the clause only containing the literals in the first but
    not in the second clause *)
val diff : t -> t -> t

(** Total ordering on sets of literals *)
val compare : t -> t -> int

(** Equality predicate on sets of literals *)
val equal : t -> t -> bool

(** Return [true] if all literals in the first clause are in the
    second clause *)
val subset : t -> t -> bool

(** Apply the function to each literal in the clause, the order of
    literals is not guaranteed *)
val iter : (Literal.t -> unit) -> t -> unit

(** Fold the literals in the clause with the function, the order of
    literals is not guaranteed *)
val fold : (Literal.t -> 'a -> 'a) -> t -> 'a -> 'a

(** Return [true] if the predicate is true for all literals in the clause *)
val for_all : (Literal.t -> bool) -> t -> bool

(** Return [true] if the predicate is true for some literal in the clause *)
val exists : (Literal.t -> bool) -> t -> bool

(** Return the clause containing only the literals the predicate is
    [true] for *)
val filter : (Literal.t -> bool) -> t -> t

(** Return a pair of clauses, where the literals in the first clause
    satisfy the predicate and the literals in the second do not *)
val partition : (Literal.t -> bool) -> t -> t * t

(** Return the number of distinct literals in the clause *)
val cardinal : t -> int

(** Return the literals of the clause as a list *)
val elements : t -> Literal.t list

(** Return one literal of the clause *)
val choose : t -> Literal.t

(** Apply [f] to each literal and return a new clause *)
val map : (Literal.t -> Literal.t) -> t -> t 

(** Return the clause containing all literals in the list *)
val of_literals : Literal.t list -> t

(** If the the top symbol of the term is a disjunction, return the
    clause containing the disjuncts as literals. Otherwise return a
    unit clause containing only the term. If the term contains nested
    disjunctions, they are flattened. *)
val of_term : Term.t -> t

(** Return the disjunction of the literals in the clause *)
val to_term : t -> Term.t

(** Pretty-print a clause *)
val pp_print_clause : Format.formatter -> t -> unit

(** Pretty-print a clause to the standard formatter *)
val print_clause : t -> unit 

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
