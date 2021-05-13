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

module Ast = LustreAst

let lsp_type_decl_json { Ast.start_pos = spos; Ast.end_pos = epos } = function
  | LustreAst.AliasType (_, id, _) | LustreAst.FreeType (_, id) ->
      let file, slnum, scnum = Lib.file_row_col_of_pos spos in
      let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
      Format.fprintf !Lib.log_ppf
        ",@.{@[<v 1>@,\
         \"objectType\" : \"lsp\",@,\
         \"source\" : \"lsp\",@,\
         \"kind\" : \"typeDecl\",@,\
         \"name\" : \"%s\",@,\
         \"file\" : \"%s\",@,\
         \"startLine\" : %d,@,\
         \"startColumn\" : %d,@,\
         \"endLine\" : %d,@,\
         \"endColumn\" : %d@]@.}@." id file slnum scnum elnum ecnum

let lsp_const_decl_json { Ast.start_pos = spos; Ast.end_pos = epos } = function
  | LustreAst.FreeConst (_, id, _)
  | LustreAst.UntypedConst (_, id, _)
  | LustreAst.TypedConst (_, id, _, _) ->
      let file, slnum, scnum = Lib.file_row_col_of_pos spos in
      let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
      Format.fprintf !Lib.log_ppf
        ",@.{@[<v 1>@,\
         \"objectType\" : \"lsp\",@,\
         \"source\" : \"lsp\",@,\
         \"kind\" : \"constDecl\",@,\
         \"name\" : \"%s\",@,\
         \"file\" : \"%s\",@,\
         \"startLine\" : %d,@,\
         \"startColumn\" : %d,@,\
         \"endLine\" : %d,@,\
         \"endColumn\" : %d@]@.}@." id file slnum scnum elnum ecnum

let lsp_node_json { Ast.start_pos = spos; Ast.end_pos = epos }
    (id, imported, _, _, _, _, _, _) =
  let file, slnum, scnum = Lib.file_row_col_of_pos spos in
  let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
  Format.fprintf !Lib.log_ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"kind\" : \"node\",@,\
     \"name\" : \"%s\",@,\
     \"imported\" : \"%b\",@,\
     \"file\" : \"%s\",@,\
     \"startLine\" : %d,@,\
     \"startColumn\" : %d,@,\
     \"endLine\" : %d,@,\
     \"endColumn\" : %d@]@.}@." id imported file slnum scnum elnum ecnum

let lsp_function_json { Ast.start_pos = spos; Ast.end_pos = epos }
    (id, imported, _, _, _, _, _, _) =
  let file, slnum, scnum = Lib.file_row_col_of_pos spos in
  let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
  Format.fprintf !Lib.log_ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"kind\" : \"function\",@,\
     \"name\" : \"%s\",@,\
     \"imported\" : \"%b\",@,\
     \"file\" : \"%s\",@,\
     \"startLine\" : %d,@,\
     \"startColumn\" : %d,@,\
     \"endLine\" : %d,@,\
     \"endColumn\" : %d@]@.}@." id imported file slnum scnum elnum ecnum

let lsp_contract_json { Ast.start_pos = spos; Ast.end_pos = epos }
    (id, _, _, _, _) =
  let file, slnum, scnum = Lib.file_row_col_of_pos spos in
  let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
  Format.fprintf !Lib.log_ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"kind\" : \"contract\",@,\
     \"name\" : \"%s\",@,\
     \"file\" : \"%s\",@,\
     \"startLine\" : %d,@,\
     \"startColumn\" : %d,@,\
     \"endLine\" : %d,@,\
     \"endColumn\" : %d@]@.}@." id file slnum scnum elnum ecnum

let print_ast_info declarations =
  List.iter
    (fun decl ->
      match decl with
      | LustreAst.TypeDecl (span, type_decl) ->
          lsp_type_decl_json span type_decl
      | LustreAst.ConstDecl (span, const_decl) ->
          lsp_const_decl_json span const_decl
      | LustreAst.NodeDecl (span, node) -> lsp_node_json span node
      | LustreAst.FuncDecl (span, func) -> lsp_function_json span func
      | LustreAst.ContractNodeDecl (span, contract) ->
          lsp_contract_json span contract
      | _ -> ())
    declarations
