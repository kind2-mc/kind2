type token =
  | STRING of (HString.t)
  | LPAREN
  | RPAREN
  | SEXP_COMMENT
  | EOF

val sexp :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> HStringSExpr.t
val sexp_opt :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> HStringSExpr.t option
val sexps :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> HStringSExpr.t list
val rev_sexps :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> HStringSExpr.t list
