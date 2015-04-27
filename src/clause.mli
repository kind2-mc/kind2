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

(** Clause, properties and activation literals for PDR

    @author Christoph Sticksel *)

(** Origin of clause *)
type source =
  | PropSet (** Pseudo clause for property set *)
  | BlockFrontier (** Reaches an error state in one step *)
  | BlockRec of int (** Reaches an error state in n steps *)
  | IndGen of t (** Inductive generalization of clause *)

(** Clause *)
and t


(** A trie of literals *)
module ClauseTrie : Trie.S with type key = Term.t list 

  
(** Set of properties *)
type prop_set

(** Type of activation literal *)
type actlit_type = 
  | Actlit_p0  (** positive unprimed *)
  | Actlit_n0  (** negative unprimed *)
  | Actlit_p1  (** positive primed *)
  | Actlit_n1  (** negative primed *)

(** {1 Activation literals} *)

(** Create a fresh activation literal, declare it in the solver, and
    assert a term guarded with it

    [create_and_assert_fresh_actlit s h t a] declares a fresh
    uninterpreted Boolean constant in the solver instance [s], and
    asserts the term [t] guarded by this activation literal in the
    same solver instance. The parameter [h] is a tag used to name the
    constant, together with a counter that is maintained per tag. *)
val create_and_assert_fresh_actlit : SMTSolver.t -> string -> Term.t -> actlit_type -> Term.t

(** {1 Clauses} *)

(** Create a clause from a set of literals, create a fresh activation
    literal for the clause, and assert the clause guarded with the
    activation literal in the solver instance. The second parameter is
    the parent clause that this clause was derived from.

    For every clause [C = L1, ..., Ln] two activation literals [p0]
    and [p1] are generated per clause, in addition also two activation
    literals [n0i] and [n1i] per literal Li. The following terms are
    then asserted:

    {{ 
    p0 => C
    p1 => C'
    n01 => ~L1
    n11 => ~L1'
    ...
    n0n => ~Ln
    n1n => ~Ln'
    }}

    where the C' and Li' are the clause and the literals,
    respectively, at the next instant.
    
*)
val mk_clause_of_literals : SMTSolver.t -> source -> Term.t list -> t

(** Return a copy of the clause with a fresh activation literal and
    copy all its parents with fresh activation literals. *)
val copy_clause : SMTSolver.t -> t -> t
  
(** Return the clauses this clause was obtained from

    The list may be empty *)
val parents_of_clause : t -> t list

(** Return the number of literals in the clause 

    Since duplicate literals are eliminated, this is not necessarily
    equal to the number of literals given when creating the clause. *)
val length_of_clause : t -> int

(** Return the conjunction of all literals in the clause *)
val term_of_clause : t -> Term.t

(** Return the literals in the clause 

    Since duplicate literals are eliminated and ordered, this is not
    necessarily equal to the list of literals given when creating the
    clause. *)
val literals_of_clause : t -> Term.t list

(** Return the activation literal for the positive clause *)
val actlit_p0_of_clause : t -> Term.t

(** Return the activation literal for the positive primed clause *)
val actlit_p1_of_clause : t -> Term.t

(** Return the activation literals for the negated literals *)
val actlits_n0_of_clause : t -> Term.t list

(** Return the activation literals for the negated, primed literals *)
val actlits_n1_of_clause : t -> Term.t list

(** {1 Property sets} *)

(** Create a property set from a list of named properties 

    The conjunction of properties is viewed as a single literal of a
    clause, and this clause is asserted with activation literals in
    the given solver instance. *)
val prop_set_of_props : SMTSolver.t -> (string * Term.t) list -> prop_set

(** Return the unit clause containing the conjunction of the
    properties as a literals *)
val clause_of_prop_set : prop_set -> t

(** Return the conjunction of the properties *)
val term_of_prop_set : prop_set -> Term.t

(** Return the named properties of the property set *)
val props_of_prop_set : prop_set -> (string * Term.t) list
  
(** Return the activation literal for the positive conjunction of properties *)
val actlit_p0_of_prop_set : prop_set -> Term.t

(** Return the activation literal for the positive primed conjunction
    of properties *)
val actlit_p1_of_prop_set : prop_set -> Term.t
  
(** Return the (singleton list of) activation literals for the negated
    conjunction of properties *)
val actlits_n0_of_prop_set : prop_set -> Term.t list
  
(** Return the (singleton list of) activation literals for the negated
    primed conjunction of properties *)
val actlits_n1_of_prop_set : prop_set -> Term.t list
  
(** {1 Frames} *)

(** Create or return an activation literal for the given frame *)
val actlit_of_frame : int -> Term.t
  
(** Create or return the uninterpreted functoin symbol for the
    activation literal for the given frame *)
val actlit_symbol_of_frame : int -> UfSymbol.t
  
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
