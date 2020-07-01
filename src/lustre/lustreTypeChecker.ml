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

module LA = LustreAst
module LC = LustreContext

          
type tcResult = Ok | NotOk of Lib.position * string

module OrdIdent = struct
  type t = LA.ident
  let compare i1 i2 = Pervasives.compare i1 i2
end
                            
module IdentMap = Map.Make(OrdIdent)
                
type tcContext = LA.lustre_type IdentMap.t
                            
let emptyContext = IdentMap.empty

let typeCheckExpr: tcContext -> LA.expr -> tcResult
  = fun _ e -> Ok 

let scc: LA.t -> LA.t list
  = fun decls -> [decls]
           
(* TODO: Find strongly connected components, put them in a group, then typecheck the group *)
let typingContextOf: LA.t -> tcContext
  = fun decls -> 
  let typingContextOf': tcContext -> LA.declaration -> tcContext
    = fun ctx decl ->
    match decl with
      | LA.TypeDecl  (_, tyDecl) -> emptyContext
      | LA.ConstDecl (_, tyDecl) -> emptyContext
      | LA.NodeDecl  (_, nodeDecl) -> emptyContext
      | LA.FuncDecl  (_, nodeDecl) -> emptyContext
      | LA.ContractNodeDecl (_, cnrtNodeDecl) -> emptyContext
      | LA.NodeParamInst (_, nodeParamLst) -> emptyContext
    in List.fold_left typingContextOf' emptyContext decls 

let typeCheckGroup: (tcContext * LA.t) list -> tcResult list =
  fun ctxGrpPair -> List.map (fun _ -> Ok) ctxGrpPair 

let staticTypeAnalize: LustreAst.t -> tcResult list =
  fun decls ->
  (* Setup type checking contexts by first breaking the program 
   * into typing groups (strongly connected components) *)
  let typingGroups = scc decls in
  (* compute the base typing contexts of each typing group *)
  let tyGrpsCtxs = List.map typingContextOf typingGroups in
  let ctxAndDeclPair = List.combine tyGrpsCtxs typingGroups in
  typeCheckGroup ctxAndDeclPair  

(* Get the top most error at a time *)
let reportAnalysisResult: tcResult list -> tcResult = function
  | []
  | Ok :: _ -> Ok
  | NotOk (pos,err) :: _ -> LC.fail_at_position pos err  


let typeCheckProgram: LA.t -> tcResult = fun prg ->
  prg |> staticTypeAnalize |> reportAnalysisResult 
    
