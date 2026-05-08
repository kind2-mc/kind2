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

(* Check match expressions for redundant/unreachable patterns and incomplete
    pattern coverage. *)

module A = LustreAst
module Ctx = TypeCheckerContext

type error_kind =
  | RedundantPattern of A.pattern
  | IncompletePatternMatch 

type error = [ `LustreCheckMatchExpressionsError of Lib.position * error_kind ]

let error_message = function
  | RedundantPattern (patt) ->
    Format.asprintf "Redundant pattern: %a" 
      A.pp_print_pattern patt
  | IncompletePatternMatch ->
    "Incomplete pattern match: cases are not exhaustive"

let check_redundancy _ = assert false

let check_exhaustiveness _ = assert false 

let check_match_expressions (_ctx : Ctx.tc_context) (ast : A.t) : (A.t, [> error]) result =
  (* TODO: implement redundant/unreachable pattern detection and incomplete pattern coverage checking *)
  Ok ast
