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

(* Enums *)
%token ENUM

(* Records *)
%token STRUCT
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
%token LPARAMBRACKET
%token RPARAMBRACKET
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
    

%nonassoc /* IF THEN */ ELSE
%right ARROW
%right IMPL
%left OR XOR
%left AND
%nonassoc EQUALS LT GT LTE GTE NEQ
%left MINUS PLUS
%left MULT DIV INTDIV MOD
%left /* UMINUS */ NOT
%nonassoc CURRENT WHEN
%left PRE /* FBY */


%start <Program.declaration list> main
(* %start <Program.expr> expr_main *)

%%


(* A Lustre program is a list of declarations *)
main: p = list(decl) EOF { List.flatten p }


(* A declaration is a type, a constant, a node or a function declaration *)
decl:
  | CONST; d = const_decl { List.map (function e -> Program.ConstDecl e) d }
  | d = type_decl { List.map (function e -> Program.TypeDecl e) d }
  | d = node_decl { [Program.NodeDecl d] }
  | d = func_decl { [Program.FuncDecl d] }


(* ********************************************************************** *)


(* Constant declaration *)
const_decl: 

  (* Imported (free) constant *)
  | l = ident_list; COLON; t = lustre_type; SEMICOLON 
    { List.map (function e -> Program.FreeConst (e, t)) l } 

  (* Defined constant without a type *)
  | s = ident; EQUALS; e = expr; SEMICOLON 
    { [Program.UntypedConst (s, e)] }

  (* Defined constant with a type *)
  | c = typed_ident; EQUALS; e = expr; SEMICOLON 
    { let (s, t) = c in [Program.TypedConst (s, e, t)] }


typed_ident: s = ident; COLON; t = lustre_type { (s, t) }


(* ********************************************************************** *)


(* Type declaration *) 
type_decl: 

  (* Type definition (alias) *)
  | TYPE; l = ident_list; EQUALS; t = lustre_type; SEMICOLON
     { List.map (function e -> (e, t)) l }

(* A type *)
lustre_type:

  (* Predefined types *)
  | BOOL { Program.Bool }
  | INT { Program.Int }
  | REAL { Program.Real }

  (* User-defined type *)
  | s = ident { Program.UserType s }

  (* Tuple type *)
  | t = tuple_type { Program.TupleType t } 

  (* Record type *)
  | t = record_type { Program.RecordType t } 

  (* Array type *)
  | t = array_type { Program.ArrayType t }

  (* Enum type *)
  | t = enum_type { Program.EnumType t }


(* Tuple type *)
tuple_type:

  (* Tuples are between square brackets *)
  | LSQBRACKET; l = lustre_type_list; RSQBRACKET { l } 


(* A record type (V6) *)
record_type:

  (* Keyword "struct" is optional *)
  | STRUCT LCURLYBRACKET; f = typed_idents_list; SEMICOLON?; RCURLYBRACKET 
  | LCURLYBRACKET; f = typed_idents_list; SEMICOLON?; RCURLYBRACKET
    { f }


(* Array type *)
array_type:
  | t = lustre_type; CARET; s = expr { t, s }


(* Enum type (V6) *)
enum_type:
  | ENUM LCURLYBRACKET; l = ident_list; RCURLYBRACKET { l } 











(* An identifier *)
ident: s = SYM { s }

(* A comma-separated list of identifiers *)
ident_list:
  | l = separated_nonempty_list(COMMA, ident) { l }

(* A comma-separated list of types *)
lustre_type_list:
  | l = separated_nonempty_list(COMMA, lustre_type) { l }
  
(* A list of lists of typed identifiers *)
typed_idents_list: 
  | a = separated_list(SEMICOLON, typed_idents) { List.flatten a }

(* A list of comma-separated identifiers with a type *)
typed_idents: 
  | l = separated_nonempty_list(COMMA, ident); COLON; t = lustre_type 

    (* Pair each identifier with its type *)
    { List.map (function e -> (e, t)) l }
  




(* Node declaration *)
node_decl:
  | NODE; 
    n = ident; 
    p = option(static_params); 
    LPAREN;
    i = typed_idents_list; 
    RPAREN;
    RETURNS; 
    LPAREN;
    o = typed_idents_list; 
    RPAREN;
    SEMICOLON;
    l = list(node_local_decl);
    LET;
    e = list(node_equation);
    TEL
    option(node_sep) 

    { (n, 
       (match p with None -> [] | Some l -> l), 
       i, 
       o, 
       (List.flatten l), 
       e)  }


(* Static parameters of a node *)
static_params:
  | LPARAMBRACKET; l = separated_nonempty_list(SEMICOLON, static_param); RPARAMBRACKET { l } 


(* Support type and constant parameters *)
static_param:
  | TYPE; t = ident { Program.TypeParam t }
  | CONST; c = ident; COLON; t = lustre_type { Program.ConstParam (c, t) }


(* Local declarations of constants or variables *)
node_local_decl:
  | c = const_decl { List.map (function e -> Program.NodeConstDecl e) c }
  | v = var_decls { List.map (function e -> Program.NodeVarDecl e) v }


(* A variable declaration section of a node *)
var_decls: 
  | VAR; l = nonempty_list(var_decl); SEMICOLON { List.flatten l }


(* A declaration of variables *)
var_decl:

  (* A clock-less variable *)
  | l = typed_idents 
    { List.map (function (s, t) -> (s, t, None)) l }

  (* A variable with a clock *)
  | l = typed_idents; WHEN; c = clock_expr
    { List.map (function (s, t) -> (s, t, Some c)) l }

  (* A list of variables with a clock *)
  | LPAREN; l = typed_idents_list; RPAREN; c = clock_expr
    { List.map (function (s, t) -> (s, t, Some c)) l }


(* Equations of a node *)
node_equation:

  (* An assertion *)
  | ASSERT; e = expr; SEMICOLON
    { Program.Assert e }

  (* An equation *)
  | l = ident_list; EQUALS; e = expr; SEMICOLON
    { Program.Equation (l, e) }


(* Nodes are separated by a period or a semicolon *)
node_sep: DOT | SEMICOLON { } 

func_decl:
  | FUNCTION; 
    n = ident; 
    LPAREN;
    i = typed_idents_list; 
    RPAREN;
    RETURNS; 
    LPAREN;
    o = typed_idents_list; 
    RPAREN;
    SEMICOLON;

    { (n, i, o)  }

(*
expr_main:
  expr EOF { $1 }
*)

expr: 

  (* Symbol *)
  | s = SYM { Program.Id ($startpos, s) } 

  (* Parenthesized expression *)
  | LPAREN; e = expr; RPAREN { e } 

  (* Propositional constants *)
  | TRUE { Program.True $startpos }
  | FALSE { Program.False $startpos }

  (* Integer numeral and floating-point decimal constants *)
  | s = NUMERAL { Program.Num ($startpos, s) } 
  | s = DECIMAL { Program.Dec ($startpos, s) } 

  (* Arithmetic operators *)
  | e1 = expr; MINUS; e2 = expr { Program.Minus ($startpos, e1, e2) }
  | MINUS; e = expr { Program.Uminus ($startpos, e) } 
  | e1 = expr; PLUS; e2 = expr { Program.Plus ($startpos, e1, e2) }
  | e1 = expr; MULT; e2 = expr { Program.Times ($startpos, e1, e2) }
  | e1 = expr; DIV; e2 = expr { Program.Div ($startpos, e1, e2) }
  | e1 = expr; INTDIV; e2 = expr { Program.Intdiv ($startpos, e1, e2) }
  | e1 = expr; MOD; e2 = expr { Program.Mod ($startpos, e1, e2) }

  (* Boolean operators *)
  | NOT; e = expr { Program.Not ($startpos, e) } 
  | e1 = expr; AND; e2 = expr { Program.And ($startpos, e1, e2) }
  | e1 = expr; OR; e2 = expr { Program.Or ($startpos, e1, e2) }
  | e1 = expr; XOR; e2 = expr { Program.Xor ($startpos, e1, e2) }
  | e1 = expr; IMPL; e2 = expr { Program.Impl ($startpos, e1, e2) }

  (* Relations *)
  | e1 = expr; LT; e2 = expr { Program.Lt ($startpos, e1, e2) }
  | e1 = expr; GT; e2 = expr { Program.Gt ($startpos, e1, e2) }
  | e1 = expr; LTE; e2 = expr { Program.Lte ($startpos, e1, e2) }
  | e1 = expr; GTE; e2 = expr { Program.Gte ($startpos, e1, e2) }
  | e1 = expr; EQUALS; e2 = expr { Program.Eq ($startpos, e1, e2) } 
  | e1 = expr; NEQ; e2 = expr { Program.Neq ($startpos, e1, e2) } 

  (* If operator *)
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr 
    { Program.Ite ($startpos, e1, e2, e3) }

  (* Clock operators *)
  | e1 = expr; WHEN; e2 = expr { Program.When ($startpos, e1, e2) }
  | CURRENT; e = expr { Program.Current ($startpos, e) }
  | CONDACT LPAREN; e1 = expr COMMA; e2 = expr COMMA; e3 = expr RPAREN
    { Program.Condact ($startpos, e1, e2, e3) } 

  (* Temporal operators *)
  | PRE; e = expr { Program.Pre ($startpos, e) }
  | FBY LPAREN; e1 = expr COMMA; s = NUMERAL; COMMA; e2 = expr RPAREN
    { Program.Fby ($startpos, e2, (int_of_string s), e2) } 
  | e1 = expr; ARROW; e2 = expr { Program.Arrow ($startpos, e1, e2) }

  (* Node call *)
  | s = SYM ; LPAREN; a = separated_list(COMMA, expr); RPAREN 
    { Program.Call ($startpos, s, a) }

  (* Record field projection *)
  | s = SYM; DOT; t = SYM 
    { Program.RecordProject ($startpos, s, t) }

  (* Tuple projection *)
  | s = SYM; LSQBRACKET; t = NUMERAL; RSQBRACKET
    { Program.TupleProject ($startpos, s, (int_of_string t)) }


clock_expr:
  | c = ident { Program.ClockPos c } 
  | NOT; c = ident { Program.ClockNeg c } 
  | NOT; LPAREN; c = ident; RPAREN { Program.ClockNeg c } 



(* 
   Local Variables:
   compile-command: "ocmlabuild -use-menhir -tag debug -tag annot test.native"
   indent-tabs-mode: nil
   End: 
*)
  
