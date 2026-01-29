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


(**
    "Desugar" free constants to functions without arguments. 
    With new additions to the input language (namely, set binary operations), 
    global constants can now have associated generated identifiers. 
    There is no existing infrastructure to give these generated identifiers 
    (with set types) global definitions. 
    So, we convert the constants to functions without args to use existing infrastructure 
    for generated identifiers of functions/nodes.

    If a global constant does not have associated generated identifiers, 
    we refrain from converting it to a function for efficiency purposes. 

    We cannot handle the case where a constant `C` becomes a function, but `C` is part of 
    some array length (e.g. `int^C`). This is because we cannot currently handle 
    function calls in array lengths (e.g., `int^C()`).

    @author Rob Lorch
*)

module A = LustreAst
module Ctx = TypeCheckerContext

type error_kind = GenCallInArrayLength of HString.t

val error_message : error_kind -> string

type error =
    [ `LustreConstantsToFunctionsError of Lib.position * error_kind ]

(** Across all decls, convert identifiers present in `new_func_ids` to calls with no args *)
val constants_to_calls :
  HString.t list ->
  A.declaration list ->
  (A.declaration list,
   [> `LustreConstantsToFunctionsError of Lib.position * error_kind ])
  result

(** Convert free constants to imported functions without args if there are (will be) associated 
    generated identifiers *)
val gen_functions :
  Ctx.tc_context ->
  A.declaration list -> A.declaration list * A.ident list * Ctx.tc_context
