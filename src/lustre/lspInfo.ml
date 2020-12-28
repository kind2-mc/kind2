let lsp_component_json pos id =
  let file, lnum, cnum = Lib.file_row_col_of_pos pos in
  Format.fprintf !Lib.log_ppf
    ",@.{@[<v 1>@,\
     \"objectType\" : \"lsp\",@,\
     \"source\" : \"lsp\",@,\
     \"name\" : \"%s\",@,\
     \"file\" : \"%s\",@,\
     \"line\" : %d,@,\
     \"column\" : %d\
    }"
    id file lnum cnum

let print_ast_info declarations =
  List.iter
    (fun decl ->
      match decl with
      | LustreAst.NodeDecl (pos, (id, false, _, _, _, _, _, _)) ->
          lsp_component_json pos id
      | LustreAst.FuncDecl (pos, (id, false, _, _, _, _, _, _)) ->
          lsp_component_json pos id
      | _ -> ())
    declarations
