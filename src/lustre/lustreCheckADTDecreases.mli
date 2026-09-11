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

(** Static termination check for recursive functions with ADT decreases clauses.

    For each recursive call [f(args)] inside such a function, verifies that
    [t_callee\[callee_formals := args\]] is a strict syntactic subterm of the
    caller's decreases expression [t]: exactly a variable bound, at some
    depth >= 1, by an enclosing match's constructor pattern, matched
    (transitively) against [t] itself. 

    @author Rob Lorch *)

type error_kind =
  | NotAStructuralSubterm of LustreAst.expr * LustreAst.expr
  (** [(callee_measure_after_substitution, caller_measure)]: the recursive
      call's substituted measure is not a strict subterm of the caller's. *)
  | MixedDecreasesKindsInScc of LustreAst.ident list
  (** The named functions are mutually recursive but do not all use the same
      kind of decreases measure (integer vs. algebraic data type). *)
  | RecursiveCallInContract of LustreAst.ident
  (** A recursive function's own contract calls the named function, which
      belongs to the same recursive group. *)

val error_message : error_kind -> string

type error = [`LustreCheckADTDecreasesError of Lib.position * error_kind]

(** Check all recursive [FuncDecl]s in [decls] whose [decreases] clause has a
    recursive ADT type. *)
val check :
  TypeCheckerContext.tc_context ->
  LustreDesugarADTs.adt_map ->
  int HString.HStringMap.t ->
  LustreAst.t ->
  (LustreAst.t, [> error]) result
