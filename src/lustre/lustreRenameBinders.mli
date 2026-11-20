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

(** Alpha-renaming of the local binders of a program, before type checking.

    Every quantified variable, [any]/[choose] binder, array-comprehension
    index, match-arm pattern variable and refinement-type binder is renamed,
    with the identifiers it binds, to a fresh name
    {!LustreAstHelpers.fresh_bound_ident} that no source identifier can have.
    No later pass can then move a user-written name into the scope of a binder
    and have it captured. {!LustreAst.original_name} recovers the name the user
    wrote, for display.

    A variable pattern named after a datatype constructor is a constructor
    pattern, not a binder, and keeps its name. *)

val rename_binders : LustreAst.t -> LustreAst.t
