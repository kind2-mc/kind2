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

let pp_print_fname_json ppf fname =
  if fname = "" then () else Format.fprintf ppf "\"file\" : \"%s\",@," fname

let lsp_type_decl_json ppf ctx { Ast.start_pos = spos; Ast.end_pos = epos } tyd =
  let print p id ps =
    let file, slnum, scnum = Lib.file_row_col_of_pos spos in
    let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
    let ty_args = List.map (fun id -> LustreAst.AbstractType (p, id)) ps in
    let ty = TypeCheckerContext.expand_type_syn ctx (LustreAst.UserType (p, ty_args, id)) in
    let contains_ref = TypeCheckerContext.type_contains_ref ctx ty in
    Format.fprintf ppf
      ",@.{@[<v 1>@,\
        \"objectType\" : \"lsp\",@,\
        \"source\" : \"lsp\",@,\
        \"kind\" : \"typeDecl\",@,\
        \"name\" : \"%a\",@,\
        \"containsRefinementType\" : \"%b\",@,\
        %a\"startLine\" : %d,@,\
        \"startColumn\" : %d,@,\
        \"endLine\" : %d,@,\
        \"endColumn\" : %d@]@.}@."
      HString.pp_print_hstring id
      contains_ref
      pp_print_fname_json file
      slnum scnum
      elnum ecnum
  in
  match tyd with
  | LustreAst.AliasType (p, id, ps, _) -> print p id ps
  | LustreAst.FreeType (p, id) -> print p id []


let lsp_const_decl_json ppf { Ast.start_pos = spos; Ast.end_pos = epos } =
  function
  | LustreAst.FreeConst (_, id, _)
  | LustreAst.UntypedConst (_, id, _)
  | LustreAst.TypedConst (_, id, _, _) ->
      let file, slnum, scnum = Lib.file_row_col_of_pos spos in
      let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
      Format.fprintf ppf
        ",@.{@[<v 1>@,\
         \"objectType\" : \"lsp\",@,\
         \"source\" : \"lsp\",@,\
         \"kind\" : \"constDecl\",@,\
         \"name\" : \"%a\",@,\
         %a\"startLine\" : %d,@,\
         \"startColumn\" : %d,@,\
         \"endLine\" : %d,@,\
         \"endColumn\" : %d@]@.}@."
        HString.pp_print_hstring id
        pp_print_fname_json file
        slnum scnum
        elnum ecnum

let lsp_node_json ppf { Ast.start_pos = spos; Ast.end_pos = epos }
    (id, imported, _, _, _, _, _, _, contract) =
  let file, slnum, scnum = Lib.file_row_col_of_pos spos in
  let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
  match contract with 
  | Some (cpos, _) ->
    let _, celnum, cecnum = Lib.file_row_col_of_pos cpos in
    Format.fprintf ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"kind\" : \"node\",@,\
     \"name\" : \"%a\",@,\
     \"imported\" : \"%b\",@,\
     %a\"startLine\" : %d,@,\
     \"startColumn\" : %d,@,\
     \"endLine\" : %d,@,\
     \"endColumn\" : %d,@,\
     \"contractStartLine\" : %d,@,\ 
     \"contractStartColumn\" : %d@]@.}@."
    HString.pp_print_hstring id
    imported pp_print_fname_json file slnum scnum
    elnum ecnum
    celnum cecnum
  | None -> 
    Format.fprintf ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"kind\" : \"node\",@,\
     \"name\" : \"%a\",@,\
     \"imported\" : \"%b\",@,\
     %a\"startLine\" : %d,@,\
     \"startColumn\" : %d,@,\
     \"endLine\" : %d,@,\
     \"endColumn\" : %d@]@.}@."
    HString.pp_print_hstring id
    imported pp_print_fname_json file slnum scnum
    elnum ecnum

let lsp_function_json ppf { Ast.start_pos = spos; Ast.end_pos = epos }
    (id, imported, _, _, _, _, _, _, _) =
  let file, slnum, scnum = Lib.file_row_col_of_pos spos in
  let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
  Format.fprintf ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"kind\" : \"function\",@,\
     \"name\" : \"%a\",@,\
     \"imported\" : \"%b\",@,\
     %a\"startLine\" : %d,@,\
     \"startColumn\" : %d,@,\
     \"endLine\" : %d,@,\
     \"endColumn\" : %d@]@.}@."
    HString.pp_print_hstring id
    imported pp_print_fname_json file slnum scnum
    elnum ecnum

let lsp_contract_json ppf { Ast.start_pos = spos; Ast.end_pos = epos }
    (id, _, _, _, _) =
  let file, slnum, scnum = Lib.file_row_col_of_pos spos in
  let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
  Format.fprintf ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"kind\" : \"contract\",@,\
     \"name\" : \"%a\",@,\
     %a\"startLine\" : %d,@,\
     \"startColumn\" : %d,@,\
     \"endLine\" : %d,@,\
     \"endColumn\" : %d@]@.}@."
    HString.pp_print_hstring id
    pp_print_fname_json file slnum scnum elnum
    ecnum

let print_ast_info ctx declarations =
  List.iter
    (fun decl ->
      match decl with
      | LustreAst.TypeDecl (span, type_decl) ->
          lsp_type_decl_json !Lib.log_ppf ctx span type_decl
      | LustreAst.ConstDecl (span, const_decl) ->
          lsp_const_decl_json !Lib.log_ppf span const_decl
      | LustreAst.NodeDecl (span, node) -> lsp_node_json !Lib.log_ppf span node
      | LustreAst.FuncDecl (span, func) ->
          lsp_function_json !Lib.log_ppf span func
      | LustreAst.ContractNodeDecl (span, contract) ->
          lsp_contract_json !Lib.log_ppf span contract
      | _ -> ())
    declarations
