type token =
  | TYPE
  | SEMICOLON
  | EQUALS
  | LSQBRACKET
  | RSQBRACKET
  | FUNCTION
  | RETURNS
  | LPAREN
  | RPAREN
  | COLON
  | COMMA
  | INT
  | REAL
  | BOOL
  | NODE
  | LET
  | TEL
  | MINUS
  | UMINUS
  | PLUS
  | MULT
  | DIV
  | INTDIV
  | MOD
  | TRUE
  | FALSE
  | NOT
  | AND
  | OR
  | XOR
  | IMPL
  | LT
  | GT
  | LTE
  | GTE
  | NEQ
  | IF
  | THEN
  | ELSE
  | WHEN
  | CURRENT
  | PRE
  | FBY
  | CONDACT
  | ARROW
  | PROPERTY
  | SUBRANGE
  | OF
  | ASSERT
  | METAPROPERTY of (string)
  | MAIN_NODE
  | VAR
  | CONST
  | DOT
  | TO_TOK
  | CONVERT_TO of (string)
  | CONVERT_FROM of (string)
  | NUM of (string)
  | FLOAT of (string)
  | SYM of (string)
  | EOF_TOK

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Types.il_formula * Types.typed_stream * Types.typed_stream list * Types.node_id_t
