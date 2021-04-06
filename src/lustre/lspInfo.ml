module Ast = LustreAst

let lsp_component_json { Ast.start_pos = spos; Ast.end_pos = epos } id =
  let file, slnum, scnum = Lib.file_row_col_of_pos spos in
  let _, elnum, ecnum = Lib.file_row_col_of_pos epos in
  Format.fprintf !Lib.log_ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
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
      | LustreAst.NodeDecl (span, (id, false, _, _, _, _, _, _)) ->
          lsp_component_json span id
      | LustreAst.FuncDecl (span, (id, false, _, _, _, _, _, _)) ->
          lsp_component_json span id
      | _ -> ())
    declarations
