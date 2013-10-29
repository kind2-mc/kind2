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

(** Conjunctive normal forms: sets of clauses 

    A CNF is really just a set of terms which is to be understood as a
    conjunction. There is no guarantee that the terms are actually
    disjunctions, see {!Clause} and {!Literal}.

    The sets do not contain duplicate clauses, all function of a set
    from the standard library are supported. In addition, the
    functions {!add_subsume} and {!union_subsume} use the function
    {!Clause.subset} to do syntactic forward and backward subsumption.

    @author Christoph Sticksel *)

(** A set of clauses *)
type t  

(** The empty set *)
val empty : t

(** Return [true] if the set is empty *)
val is_empty : t -> bool

(** Forward subsumption: [fwd_subsume c s] returns [true] if a clause
    in [s] subsumes the new clause [c] *)
val fwd_subsume : Clause.t -> t -> bool

(** Backward subsumption: [bwd_subsume c s] returns the set [s] with
    the clauses removed that are subsumed by the new clause [c] *)
val bwd_subsume : Clause.t -> t -> t

(** Return [true] if the clause is in the set *)
val mem : Clause.t -> t -> bool

(** Add the clause to the set *)
val add : Clause.t -> t -> t

(** [add_subsume c s] adds the clause [c] to the set [s] unless [c] is
    subsumed by some clause in [c] and removes all clauses from [s]
    that are subsumed by [c]. *)
val add_subsume : Clause.t -> t -> t

(** Return the set containing only the clause *)
val singleton : Clause.t -> t

(** Remove the clause from the set *)
val remove : Clause.t -> t -> t

(** Return the union of the two sets of clauses *)
val union : t -> t -> t

(** [union_subsume c1 c2] adds all clauses of [c1] to the set [c2]
    unless a clause in [c1] is subsumed by some clause in [c2] and
    removes all clauses from [c2] that are subsumed by some clause in
    [c1]. *)
val union_subsume : t -> t -> t

(** Return the set only containing the clauses in the first but not
   in the second set *)
val inter : t -> t -> t

(** Return the difference between the first and the second set of clauses *)
val diff : t -> t -> t

(** Total ordering on sets of clauses *)
val compare : t -> t -> int

(** Equality predicate on sets of clauses *)
val equal : t -> t -> bool

(** Return [true] if all clauses of the first set are members of the
    second set *)
val subset : t -> t -> bool

(** Apply the function to each clause in the set, the order of clauses
    is not guaranteed *)
val iter : (Clause.t -> unit) -> t -> unit

(** Fold the clauses in the set with the function, the order the
    clauses is not guaranteed *)
val fold : (Clause.t -> 'a -> 'a) -> t -> 'a -> 'a

(** Return [true] if the predicate is [true] for all clauses in the set *)
val for_all : (Clause.t -> bool) -> t -> bool

(** Return [true] if the predicate is [true] for some clause in the set *)
val exists : (Clause.t -> bool) -> t -> bool

(** Return the set containing only the clauses the predicate is
    [true] for *)
val filter : (Clause.t -> bool) -> t -> t

(** Return a pair of sets, where the clauses in the first set satify
    the predicate and the clauses in the second do not *)
val partition : (Clause.t -> bool) -> t -> t * t

(** Return the number of distinct members of the set *)
val cardinal : t -> int

(** Return the members of the set as a list *)
val elements : t -> Clause.t list

(** Return one element in the set *)
val choose : t -> Clause.t

(** Return a set containting all elements of the list *)
val of_list : Clause.t list -> t

(** Return the conjunction of all clauses in the set *)
val to_term : t -> Term.t 

(** Pretty-print a set of clauses *)
val pp_print_cnf : Format.formatter -> t -> unit

(** Pretty-print a set of clauses to the standard formatter *)
val print_cnf : t -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
