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

(* @author Apoorv Ingle *)

type tcResult = Ok | NotOk of Lib.position * string

module OrdIdent = struct
  type t = LustreAst.ident
  let compare i1 i2 = Pervasives.compare i1 i2
end
                            
module IdentMap = Map.Make(OrdIdent)
                
type tcContext = LustreAst.lustre_type IdentMap.t
                            
let emptyContext = IdentMap.empty

let typeCheck': LustreAst.expr -> tcContext -> tcResult
  = fun expr tcContext -> Ok
                 
let typeCheck:  LustreAst.expr -> tcResult
  = fun e -> typeCheck' e emptyContext

let typingContextof: LustreAst.t -> tcContext
  = fun _ -> emptyContext

let typeAnalize: LustreAst.t -> tcResult =
  fun decls ->
  let _ = typingContextof decls in
  match decls with
  | _ -> Ok 
  
                       
