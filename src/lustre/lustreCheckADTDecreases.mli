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
    caller's decreases expression [t]. A strict syntactic subterm means the
    substituted expression is a chain of one or more field projections whose
    base is exactly [t].

    @author Rob Lorch *)

type error_kind =
  | NotAStructuralSubterm of LustreAst.expr * LustreAst.expr
  (** [(callee_measure_after_substitution, caller_measure)]: the recursive
      call's substituted measure is not a strict subterm of the caller's. *)

val error_message : error_kind -> string

type error = [`LustreCheckADTDecreasesError of Lib.position * error_kind]

(** Check all recursive [FuncDecl]s in [decls] whose [decreases] clause has a
    recursive ADT type.  Returns the declarations unchanged on success, or an
    error if any recursive call fails the structural subterm check. *)
val check :
  TypeCheckerContext.tc_context ->
  LustreDesugarADTs.adt_map ->
  int HString.HStringMap.t ->
  LustreAst.t ->
  (LustreAst.t, [> error]) result
