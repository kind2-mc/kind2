(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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
(** Functions for type checking surface syntax [LustreAst]
    
    @author Apoorv Ingle *)

type tcResult = Ok | NotOk of Lib.position * string

type tcContext

val emptyContext: tcContext
  
(* Type check with an empty context *)
val typeCheck: LustreAst.expr -> tcResult

(* typecheck with a user supplied context *)
val typeCheck': tcContext -> LustreAst.expr -> tcResult                 

(* Perform type analysis on the AST *)
val typeAnalize: LustreAst.t -> tcResult
