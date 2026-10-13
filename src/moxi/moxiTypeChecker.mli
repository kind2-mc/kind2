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

(** Sort checker for MoXI scripts

    Checks a parsed script against the MoXI language definition before it is
    translated into transition systems: the sorts of the variables are
    well-formed and belong to the declared logic; every term is well-sorted
    under the SMT-LIB theories of Core, Ints, Reals, Reals_Ints,
    FixedSizeBitVectors and ArraysEx, and only uses the symbols of the
    declared logic (including its linearity restriction); the [:init] and
    [:inv] conditions are one-state formulas and the [:trans] condition is a
    two-state formula; every subsystem instance refers to a defined system
    and binds its inputs and outputs to variables of the right sorts and
    kinds; and every [check-system] renames the variables of its system
    consistently, primes only inputs in its assumptions, and names declared
    conditions in its queries.

    The checker stops at the first error. *)

(** A MoXI sort *)
type sort =
  | Bool
  | Int
  | Real
  | BitVec of int
  | Array of sort * sort (** Index sort, element sort *)

(** Print a sort in SMT-LIB syntax *)
val pp_print_sort : Format.formatter -> sort -> unit

(** What went wrong *)
type error_kind =
  | UnknownLogic of string
  | LogicAlreadySet
  | LogicAfterDefinition
  | UnknownSort of string
  | MalformedSort of string * string
  | SortNotInLogic of sort * string
  | NumeralNotInLogic of string
  | DecimalNotInLogic of string
  | BitvectorNotInLogic of string
  | BitvectorOutOfRange of string * int
  | SymbolNotInLogic of string * string
  | NonlinearTerm of string * string
  | UnboundVariable of string
  | UnknownFunction of string
  | UnknownIndexedIdentifier of string
  | PrimedLetVariable of string
  | PrimedNonVariable of string
  | PrimeNotAllowed of string * string
  | PrimedNonInput of string * string
  | Arity of string * string * int
  | ArgumentSort of string * int * sort * string
  | ExpectedBool of string * sort
  | AscriptionMismatch of sort * sort
  | ConstArrayWithoutSort
  | ConstArrayNotArraySort of sort
  | DuplicateLetBinding of string
  | SystemRedefined of string
  | UnknownSystem of string
  | SelfInstantiation of string
  | DuplicateInstance of string
  | DuplicateVariable of string
  | SubsystemArity of string * string * int * int
  | SubsystemArgumentSort of string * string * sort * string * sort
  | SubsystemOutputToInput of string * string * string
  | RenamingArity of string * string * int * int
  | RenamingSort of string * sort * string * sort
  | DuplicateFormula of string
  | DuplicateQuery of string
  | UnknownFormula of string * string

(** An error and where it was found *)
type error = Lib.position * error_kind

(** A message describing an error *)
val error_message : error_kind -> string

(** Check a script, returning the first error found, if any *)
val check_script : MoxiAst.script -> (unit, error) result

(** {1 For the translation} *)

(** An identifier with its indices as written, [(_ f i j)], or the bare
    symbol when it has none *)
val string_of_indexed_id : string -> MoxiAst.index list -> string

(** The value and width of a bit-vector literal [(_ bvN m)], given the
    symbol and indices of an indexed identifier, if it is one. The checker
    has verified that the value fits the width of every literal of a
    checked script. *)
val bv_literal : string -> MoxiAst.index list -> (Numeral.t * Numeral.t) option

(** Whether numerals denote reals in the logic of the given name: it has
    reals and no integers *)
val numerals_are_real : string -> bool
