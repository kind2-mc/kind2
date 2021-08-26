(* This file is part of the Kind 2 model checker.

   Copyright (c) 2021 by the Board of Trustees of the University of Iowa

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
(** Check various syntactic properties that do not depend on type information
  
  @author Andrew Marmaduke *)

module LA = LustreAst

type 'a sc_result = ('a, Lib.position * string) result

(* let (>>=) = Res.(>>=) *)
let (>>) = Res.(>>)

let syntax_error pos msg = Error (pos, msg)
    
let rec syntax_check (ast:LustreAst.t) =
  Res.seq (List.map check_declaration ast)

and check_declaration = function
  | TypeDecl (span, decl) -> Ok (LA.TypeDecl (span, decl))
  | ConstDecl (span, decl) -> Ok (LA.ConstDecl (span, decl))
  | NodeDecl (span, decl) -> check_node_decl span decl
  | FuncDecl (span, decl) -> check_func_decl span decl
  | ContractNodeDecl (span, decl) -> Ok (LA.ContractNodeDecl (span, decl))
  | NodeParamInst (span, inst) -> Ok (LA.NodeParamInst (span, inst))

and check_node_decl span (id, ext, params, inputs, outputs, locals, items, contracts) =
  let decl = LA.NodeDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contracts))
  in
  (locals_must_have_definitions locals items) >> (Ok decl)

and check_func_decl span (id, ext, params, inputs, outputs, locals, items, contracts) =
  let decl = LA.FuncDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contracts))
  in
  Ok decl

and locals_must_have_definitions locals items =
  let find_local_def_lhs id test = function
    | LA.SingleIdent (_, id') -> test || id = id'
    | _ -> test
  in
  let find_local_def id = function
    | LA.Body eqn -> (match eqn with
      | LA.Assert _ -> false
      | LA.Equation (_, lhs, _) -> (match lhs with
        | LA.StructDef (_, vars)
          -> List.fold_left (find_local_def_lhs id) false vars)
      | LA.Automaton _ -> false)
    | LA.AnnotMain _ -> false
    | LA.AnnotProperty _ -> false
  in
  let over_locals = function
    | LA.NodeConstDecl _ -> Ok ()
    | LA.NodeVarDecl (_, (pos, id, _, _)) ->
      let test = List.find_opt (fun item -> find_local_def id item) items in
      match test with
      | Some _ -> Ok ()
      | None -> syntax_error pos
        (Format.asprintf "Local variable %s has no definition." id)
  in
  Res.seq (List.map over_locals locals)
