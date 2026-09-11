(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(** SMT-level definitions of recursive functions

    A recursive function is compiled by unrolling its definition once and
    abstracting its recursive calls by its contract, with the outputs of every
    instance tied to a functional symbol [f.out.__function_of_inputs] (see
    {!LustreTransSys}). This module gives that symbol a definition, as an
    SMT-LIB [define-funs-rec] block, when the function has no contract to
    abstract its calls with (no guarantee and no mode, neither explicit nor
    through a refinement type of an output; an assumption is an obligation of
    the callers and does not count) or is declared transparent, so that a
    solver can reason about the function by unfolding its definition rather
    than through a contract.

    The definition of a function is built from the equations of its body. A
    call to a function of the same recursive group applies the symbol of the
    callee under the guard of the termination checks of the call, and yields
    an arbitrary value ([f.out.__undefined_call]) otherwise: the definitions
    are then well-founded whether or not the measure of the function actually
    decreases, so they always have a model and cannot make the transition
    system inconsistent. The termination checks themselves remain properties of
    the transition system. A call to a recursive function of another group
    applies the functional symbol of the callee, which either has a definition
    of its own or is uninterpreted; a call to an imported function applies its
    functional symbol; and a call to any other function is inlined.

    Every function of a recursive group is defined, or none is. A group is
    defined only if each of its functions is eligible and definable: its
    body is a total function of its inputs, without assertions, oracles,
    array-typed variables or calls to nodes, and the same holds for the
    functions it inlines. Definitions are only produced for the solvers that
    support them (Z3 and cvc5) and when no logic is set with [--smt_logic],
    and can be turned off with [--define_fun_rec false].

    A defined function's contract, if it has one, is never assumed in place
    of its body: see [LustreTransSys]. *)

(** A function definition: the symbol, its formal parameters and its body *)
type def = UfSymbol.t * Var.t list * Term.t

(** A block of mutually recursive definitions, defined together *)
type block = def list

(** The definitions of the recursive functions of a set of nodes *)
type t

(** No definitions *)
val empty : t

(** [true] iff recursive functions are to be defined at the SMT level: the
    option is on, the SMT solver supports recursive function definitions,
    and the logic is inferred from the system rather than set explicitly. *)
val enabled : unit -> bool

(** Compute the definitions of the recursive functions of the given nodes.
    [adt_junk_ufs] are the symbols giving selectors their value outside of
    their constructor, which a definition may apply. *)
val compute : adt_junk_ufs:UfSymbol.t list -> LustreNode.t list -> t

(** [true] iff the functional symbols of the given function are defined *)
val is_defined : t -> NodeId.t -> bool

(** The blocks of definitions the given function's own depends on, followed
    by its own, in dependency order; empty if the function is not defined *)
val blocks_of_node : t -> NodeId.t -> block list

(** The uninterpreted symbols applied by the blocks of the given function,
    to be declared before them; empty if the function is not defined *)
val ufs_of_node : t -> NodeId.t -> UfSymbol.t list

(** [bounded_below ms] states that every component of the measure [ms] is
    non-negative *)
val bounded_below : Term.t list -> Term.t

(** [lex_lt callee caller] states that the measure [callee] is strictly
    smaller than the measure [caller] in the lexicographic order over their
    common prefix *)
val lex_lt : Term.t list -> Term.t list -> Term.t
