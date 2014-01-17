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
