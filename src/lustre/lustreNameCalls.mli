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

(** Assign fresh local variables to the results of call statements.

    A call statement such as [double(n-1);] is parsed into an equation with an
    empty left-hand side. This pass introduces, for each returned value, a fresh
    local variable to hold the (otherwise discarded) result, so that distinct
    call statements never share a left-hand side. It must run after type
    checking but before if/when blocks are desugared. *)
val name_calls :
  TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  (LustreAst.declaration list, [> LustreTypeChecker.error]) result
