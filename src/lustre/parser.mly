(* This file is part of the Kind verifier

 * Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
 * here after designated as the Copyright Holder.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the University of Iowa, nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

%{

(* String representation of a token *)
let string_of_token = function
  | INCLUDE -> "INCLUDE"
  | STRING p -> Format.sprintf "STRING %s" p
  | SEMICOLON -> "SEMICOLON"  
  | EQUALS -> "EQUALS"  
  | COLON -> "COLON"  
  | COMMA -> "COMMA"  
  | LSQBRACKET -> "LSQBRACKET"  
  | RSQBRACKET -> "RSQBRACKET"  
  | LPAREN -> "LPAREN"  
  | RPAREN -> "RPAREN"  
  | DOT -> "DOT" 
  | DECIMAL p -> Format.sprintf "DECIMAL %s" p
  | NUMERAL p -> Format.sprintf "NUMERAL %s" p
  | SYM p -> Format.sprintf "SYM %s" p
  | TYPE -> "TYPE" 
  | INT -> "INT" 
  | REAL -> "REAL" 
  | BOOL -> "BOOL" 
  | SUBRANGE -> "SUBRANGE" 
  | OF -> "OF" 
  | ARRAY -> "ARRAY" 
  | CARET -> "CARET" 
  | LCURLYBRACKET -> "LCURLYBRACKET"  
  | RCURLYBRACKET -> "RCURLYBRACKET"  
  | LARRAYBRACKET -> "LARRAYBRACKET"  
  | RARRAYBRACKET -> "RARRAYBRACKET"  
  | PIPE -> "PIPE"
  | CONST -> "CONST" 
  | NODE -> "NODE" 
  | FUNCTION -> "FUNCTION" 
  | RETURNS -> "RETURNS" 
  | VAR -> "VAR" 
  | LET -> "LET" 
  | TEL -> "TEL" 
  | PROPERTY -> "PROPERTY" 
  | MAIN -> "MAIN" 
  | REQUIRES -> "REQUIRES" 
  | ENSURES -> "ENSURES" 
  | ASSERT -> "ASSERT" 
  | TRUE -> "TRUE" 
  | FALSE -> "FALSE" 
  | NOT -> "NOT" 
  | AND -> "AND" 
  | XOR -> "XOR" 
  | OR -> "OR" 
  | IF -> "IF" 
  | THEN -> "THEN" 
  | ELSE -> "ELSE" 
  | IMPL -> "IMPL" 
  | LTE -> "LTE" 
  | GTE -> "GTE" 
  | LT -> "LT" 
  | GT -> "GT" 
  | NEQ -> "NEQ" 
  | MINUS -> "MINUS" 
  | PLUS -> "PLUS" 
  | DIV -> "DIV" 
  | MULT -> "MULT" 
  | INTDIV -> "INTDIV" 
  | MOD -> "MOD" 
  | WHEN -> "WHEN" 
  | CURRENT -> "CURRENT" 
  | CONDACT -> "CONDACT" 
  | PRE -> "PRE" 
  | FBY -> "FBY" 
  | ARROW -> "ARROW" 
  | EOF -> "EOF" 

(* Pretty-print a token *)
let pp_print_token ppf t = 
  Format.fprintf ppf "%s" (string_of_token t)

(* Pretty-print a position *)
let pp_print_position 
    ppf 
    { Lexing.pos_lnum; Lexing.pos_bol; Lexing.pos_cnum } =

  Format.fprintf 
    ppf
    "(%d,%d)"
    pos_lnum
    (pos_cnum - pos_bol)
    
%}

(* Include directive *)
%token INCLUDE
%token <string>STRING

(* Special characters *)
%token SEMICOLON 
%token EQUALS 
%token COLON 
%token COMMA 
%token LSQBRACKET 
%token RSQBRACKET 
%token LPAREN 
%token RPAREN 

(* Records *)
%token DOT
%token LCURLYBRACKET 
%token RCURLYBRACKET 

(* Decimal or numeral *)
%token <string>DECIMAL
%token <string>NUMERAL
      
(* Identifier *)
%token <string>SYM 
      
(* Type *)
%token TYPE
%token INT
%token REAL
%token BOOL
%token SUBRANGE
%token OF
    
(* Array *)
%token ARRAY
%token CARET
%token LARRAYBRACKET 
%token RARRAYBRACKET 
%token PIPE

(* Constant declaration *)
%token CONST
    
(* Node declaration *)
%token NODE
%token FUNCTION
%token RETURNS
%token VAR
%token LET
%token TEL
    
(* Annotation *)
%token PROPERTY
%token MAIN
%token REQUIRES
%token ENSURES

(* Assertion *)
%token ASSERT
    
(* Boolean operator *)
%token TRUE
%token FALSE
%token NOT
%token AND
%token XOR
%token OR
%token IF
%token THEN
%token ELSE
%token IMPL
    
(* Relation *)
%token LTE
%token GTE
%token LT
%token GT
%token NEQ
    
(* Arithmetic operators *)
%token MINUS
%token PLUS
%token DIV
%token MULT
%token INTDIV
%token MOD
    
(* Clock operators *)
%token WHEN
%token CURRENT
%token CONDACT
    
(* Temporal operators *)
%token PRE
%token FBY
%token ARROW
    
(* End of file marker *)
%token EOF
    

%right ARROW
%right IMPL
%left OR XOR
%left AND
%nonassoc EQUALS LT GT LTE GTE NEQ
%left MINUS PLUS
%left MULT DIV INTDIV MOD
%left UMINUS NOT
%left PRE FBY


/* %start <Program.t> main */

%start <Program.expr> expr_main 

%%


expr_main:
  expr EOF { $1 }

expr: 

  (* Symbol *)
  | s = SYM { Program.Id s } 

  (* Parenthesized expression *)
  | LPAREN; e = expr; RPAREN { e } 

  (* Propositional constants *)
  | TRUE { Program.True }
  | FALSE { Program.False }

  (* Integer numeral and floating-point decimal constants *)
  | s = NUMERAL { Program.Num s } 
  | s = DECIMAL { Program.Dec s } 

  (* Arithmetic operators *)
  | e1 = expr; MINUS; e2 = expr { Program.Minus (e1, e2) }
  | MINUS; e = expr { Program.Uminus e } 
  | e1 = expr; PLUS; e2 = expr { Program.Plus (e1, e2) }
  | e1 = expr; MULT; e2 = expr { Program.Times (e1, e2) }
  | e1 = expr; DIV; e2 = expr { Program.Div (e1, e2) }
  | e1 = expr; INTDIV; e2 = expr { Program.Intdiv (e1, e2) }
  | e1 = expr; MOD; e2 = expr { Program.Mod (e1, e2) }

  (* Boolean operators *)
  | NOT; e = expr { Program.Not e } 
  | e1 = expr; AND; e2 = expr { Program.And (e1, e2) }
  | e1 = expr; OR; e2 = expr { Program.Or (e1, e2) }
  | e1 = expr; XOR; e2 = expr { Program.Xor (e1, e2) }
  | e1 = expr; IMPL; e2 = expr { Program.Impl (e1, e2) }

  (* Relations *)
  | e1 = expr; LT; e2 = expr { Program.Lt (e1, e2) }
  | e1 = expr; GT; e2 = expr { Program.Gt (e1, e2) }
  | e1 = expr; LTE; e2 = expr { Program.Lte (e1, e2) }
  | e1 = expr; GTE; e2 = expr { Program.Gte (e1, e2) }
  | e1 = expr; EQUALS; e2 = expr { Program.Eq (e1, e2) } 
  | e1 = expr; NEQ; e2 = expr { Program.Neq (e1, e2) } 

  (* If operator *)
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { Program.Ite (e1, e2, e3) }

  (* Clock operators *)
  | e1 = expr; WHEN; e2 = expr { Program.When (e1, e2) }
  | CURRENT; e = expr { Program.Current e }
  | CONDACT LPAREN; e1 = expr COMMA; e2 = expr COMMA; e3 = expr RPAREN
    { Program.Condact (e1, e2, e3) } 

  (* Temporal operators *)
  | PRE; e = expr { Program.Pre e }
  | FBY LPAREN; e1 = expr COMMA; s = NUMERAL; COMMA; e2 = expr RPAREN
    { Program.Fby (e2, (int_of_string s), e2) } 
  | e1 = expr; ARROW; e2 = expr { Program.Arrow (e1, e2) }

  (* Node call *)
  | s = SYM ; LPAREN; a = separated_list(COMMA, expr); RPAREN 
    { Program.Call (s, a) }

  (* Record field projection *)
  | s = SYM; DOT; t = SYM 
    { Program.RecordProject (s, t) }

  (* Tuple projection *)
  | s = SYM; LSQBRACKET; t = NUMERAL; RSQBRACKET
    { Program.TupleProject (s, (int_of_string t)) }

