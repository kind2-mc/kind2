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

(** Checks match expressions for useless (redundant) arms and for
    non-exhaustive pattern coverage.

    Both anomalies are instances of the useful clause problem, decided by the
    recursive function [Urec] of Luc Maranget, "Warnings for pattern matching",
    {i Journal of Functional Programming} 17(3):387-421, 2007, Section 3.1.
    Lustre patterns (currently) have no or-patterns, so the corresponding cases of the
    algorithm are omitted. Match scrutinees are always fully evaluated values,
    so the strict semantics of Section 3 applies; the algorithm is in any case
    the same one Maranget proves correct for lazy semantics in Section 4.

    @author Rob Lorch 
*)

type error_kind =
  | RedundantPattern of LustreAst.pattern
  | IncompletePatternMatch

val error_message : error_kind -> string

type error = [
  | `LustreCheckMatchExpressionsError of Lib.position * error_kind
]

(** Reports redundant match arms and cases where match arms are not exhaustive. 
    Returns the declarations unchanged. *)
val check_match_expressions :
  TypeCheckerContext.tc_context -> LustreAst.t -> (LustreAst.t, [> error]) result
