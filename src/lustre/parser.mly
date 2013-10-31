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

(*
(* Include directive, unfolded by the lexer *)
%token INCLUDE
%token <string>STRING
*)

(* Special characters *)
%token SEMICOLON 
%token EQUALS 
%token COLON 
%token COMMA 
%token LSQBRACKET 
%token RSQBRACKET 
%token LPAREN 
%token RPAREN 

(* Tokens for enumerated types *)
%token ENUM

(* Tokens for records *)
%token STRUCT
%token DOT
%token LCURLYBRACKET 
%token RCURLYBRACKET 

(* Tokens for decimals and numerals *)
%token <string>DECIMAL
%token <string>NUMERAL
      
(* Identifier token *)
%token <string>SYM 
      
(* Tokens for types *)
%token TYPE
%token INT
%token REAL
%token BOOL
%token SUBRANGE
%token OF
    
(* Tokens for arrays *)
(* %token ARRAY *)
%token CARET
%token DOTDOT
(* %token LARRAYBRACKET *)
(* %token RARRAYBRACKET *)
%token PIPE

(* Token for constant declarations *)
%token CONST
    
(* Tokens for node declarations *)
%token NODE
%token LPARAMBRACKET
%token RPARAMBRACKET
%token FUNCTION
%token RETURNS
%token VAR
%token LET
%token TEL
    
(* Tokens for annotations *)
%token PROPERTY
%token MAIN
%token REQUIRES
%token ENSURES

(* Token for assertions *)
%token ASSERT
    
(* Tokens for Boolean operations *)
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
%token HASH
    
(* Tokens for relations *)
%token LTE
%token GTE
%token LT
%token GT
%token NEQ
    
(* Tokens for arithmetic operators *)
%token MINUS
%token PLUS
%token DIV
%token MULT
%token INTDIV
%token MOD
    
(* Tokens for clocks *)
%token WHEN
%token CURRENT
%token CONDACT
    
(* Tokens for temporal operators *)
%token PRE
%token FBY
%token ARROW
    
(* Token for end of file marker *)
%token EOF
    
(* Priorities and associativity of operators, lowest first *)
%left CARET PIPE
%nonassoc IF THEN ELSE
%right ARROW
%right IMPL
%left OR XOR
%left AND
%left LT LTE EQUALS NEQ GTE GT
%left PLUS MINUS
%left MULT INTDIV MOD DIV
%nonassoc WHEN
%nonassoc NOT 
%nonassoc CURRENT 
%nonassoc PRE 
%nonassoc INT REAL 
%nonassoc LSQBRACKET

(* Start token *)
%start <Program.declaration list> main

%%


(* A Lustre program is a list of declarations *)
main: p = list(decl) EOF { List.flatten p }


(* A declaration is a type, a constant, a node or a function declaration *)
decl:
  | d = const_decl { List.map (function e -> Program.ConstDecl e) d }
  | d = type_decl { List.map (function e -> Program.TypeDecl e) d }
  | d = node_decl { [Program.NodeDecl d] }
  | d = func_decl { [Program.FuncDecl d] }


(* ********************************************************************** *)


(* A constant declaration *)
const_decl: CONST; l = nonempty_list(const_decl_body) { List.flatten l }

(* The body of a constant declaration *)
const_decl_body:

  (* Imported (free) constant 

     Separate rule for singleton list to avoid shift/reduce conflict *)
  | h = ident; COLON; t = lustre_type; SEMICOLON 
    { [Program.FreeConst (h, t)] } 

  (* Imported (free) constant *)
  | h = ident; COMMA; l = ident_list; COLON; t = lustre_type; SEMICOLON 
    { List.map (function e -> Program.FreeConst (e, t)) (h :: l) } 

  (* Defined constant without a type *)
  | s = ident; EQUALS; e = expr; SEMICOLON 
    { [Program.UntypedConst (s, e)] }

  (* Defined constant with a type *)
  | c = typed_ident; EQUALS; e = expr; SEMICOLON 
    { let (s, t) = c in [Program.TypedConst (s, e, t)] }


(* ********************************************************************** *)


(* A type declaration *) 
type_decl: 

  | TYPE; l = ident_list; SEMICOLON 
     { List.map (function e -> Program.FreeType e) l }

  (* Type definition (alias) *)
  | TYPE; l = ident_list; EQUALS; t = lustre_type; SEMICOLON
     { List.map (function e -> Program.AliasType (e, t)) l }


(* A type *)
lustre_type:

  (* Predefined types *)
  | BOOL { Program.Bool }
  | INT { Program.Int }
  | REAL { Program.Real }

  | SUBRANGE;
    LSQBRACKET;
    l = expr; 
    COMMA; 
    u = expr; 
    RSQBRACKET 
    OF
    INT 
    { Program.IntRange (l, u)}

  (* User-defined type *)
  | s = ident { Program.UserType s }

  (* Tuple type *)
  | t = tuple_type { Program.TupleType t } 

  (* Record type (V6) *)
  | t = record_type { Program.RecordType t } 

  (* Array type (V6) *)
  | t = array_type { Program.ArrayType t }

  (* Enum type (V6) *)
  | t = enum_type { Program.EnumType t }


(* A tuple type *)
tuple_type:

  (* Tuples are between square brackets *)
  | LSQBRACKET; l = lustre_type_list; RSQBRACKET { l } 


(* A record type (V6) *)
record_type:

  (* Keyword "struct" is optional *)
  | option(STRUCT); LCURLYBRACKET; f = typed_idents_list; RCURLYBRACKET { f }


(* An array type (V6) *)
array_type: t = lustre_type; CARET; s = expr { t, s }


(* An enum type (V6) *)
enum_type: ENUM LCURLYBRACKET; l = ident_list; RCURLYBRACKET { l } 


(* ********************************************************************** *)


(* An uninterpreted function declaration *)
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


(* A node declaration *)
node_decl:
  | r = contract;
    NODE; 
    n = ident; 
    p = option(static_params); 
    LPAREN;
    i = const_clocked_typed_idents_list; 
    RPAREN;
    RETURNS; 
    LPAREN;
    o = clocked_typed_idents_list; 
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
       e,
       r)  }


(* A node declaration is optionally terminated by a period or a semicolon *)
node_sep: DOT | SEMICOLON { } 

(* A list of contract clauses *)
contract:
  | l = list(contract_clause) { l }

(* A requires or ensures annotation *)
contract_clause:
  | REQUIRES; e = expr; SEMICOLON { Program.Requires e }
  | ENSURES; e = expr; SEMICOLON { Program.Ensures e }


(* The static parameters of a node *)
static_params:
  | LPARAMBRACKET; 
    l = separated_nonempty_list(SEMICOLON, static_param); 
    RPARAMBRACKET 

    { l } 


(* A static parameter is a type or a constant *)
static_param:
  | TYPE; t = ident { Program.TypeParam t }
  | CONST; c = ident; COLON; t = lustre_type { Program.ConstParam (c, t) }


(* A node-local declaration of constants or variables *)
node_local_decl:
  | c = const_decl { List.map (function e -> Program.NodeConstDecl e) c }
  | v = var_decls { List.map (function e -> Program.NodeVarDecl e) v }


(* A variable declaration section of a node *)
var_decls: 
  | VAR; l = nonempty_list(var_decl) { List.flatten l }


(* A declaration of variables *)
var_decl:
  | l = clocked_typed_idents; SEMICOLON { l }


(* An equations of a node *)
node_equation:

  (* An assertion *)
  | ASSERT; e = expr; SEMICOLON
    { Program.Assert e }

  (* An equation, multiple (optionally parenthesized) identifiers on 
     the left-hand side, an expression on the right *)
  | l = left_side; EQUALS; e = expr; SEMICOLON
    { Program.Equation (l, e) }

  (* Node annotation *)
  | MAIN { Program.AnnotMain }

  (* Property annotation *)
  | PROPERTY; e = expr; SEMICOLON { Program.AnnotProperty e }


left_side:

  (* List without parentheses *)
  | l = struct_item_list { l }

  (* Parenthesized list *)
  | LPAREN; l = struct_item_list; RPAREN { l }


(* Item in a structured equation *)
struct_item:

  (* Single identifier *)
  | s = ident { Program.SingleIdent s }

  (* Filter array values *)
  | LSQBRACKET; l = struct_item_list; RSQBRACKET 
    { Program.TupleStructItem l }

  (* Select from tuple *)
  | e = ident; LSQBRACKET; i = expr; RSQBRACKET 
    { Program.TupleSelection (e, i) }

  (* Select from record *)
  | e = ident; DOT; i = ident 
    { Program.FieldSelection (e, i) }
 
(* List of structured items *)
struct_item_list:
 | l = separated_nonempty_list(COMMA, struct_item) { l }


(* ********************************************************************** *)

(* An expression *)
expr: 
  
  (* An identifier *)
  | s = ident { Program.Ident ($startpos, s) } 

  (* A propositional constant *)
  | TRUE { Program.True $startpos }
  | FALSE { Program.False $startpos }

  (* An integer numeral or a floating-point decimal constant *)
  | s = NUMERAL { Program.Num ($startpos, s) } 
  | s = DECIMAL { Program.Dec ($startpos, s) } 

  (* Conversions *)
  | INT; e = expr { Program.ToInt ($startpos, e) }
  | REAL; e = expr { Program.ToReal ($startpos, e) }

  (* A parenthesized single expression *)
  | LPAREN; e = expr; RPAREN { e } 

  (* An expression list 

     Singleton list is in production above *)
  | LPAREN; h = expr; COMMA; l = expr_list; RPAREN 
    { Program.ExprList ($startpos, h :: l) } 

  (* A tuple expression *)
  | LSQBRACKET; l = expr_list; RSQBRACKET { Program.TupleExpr ($startpos, l) }

  (* An array constructor *)
  | e1 = expr; CARET; e2 = expr { Program.ArrayConstr ($startpos, e1, e2) }

  (* A tuple projection *)
  | e = expr; LSQBRACKET; i = expr ; RSQBRACKET
    { Program.TupleProject ($startpos, e, i) }

  (* A multidimensional array slice *)
  | e = expr; LSQBRACKET; l = array_slice_list; RSQBRACKET
    { Program.ArraySlice ($startpos, e, l) }

  (* A record field projection *)
  | s = ident; DOT; t = ident 
    { Program.RecordProject ($startpos, s, t) }

  (* An array concatenation *)
  | e1 = expr; PIPE; e2 = expr { Program.ArrayConcat ($startpos, e1, e2) } 

  (* An arithmetic operation *)
  | e1 = expr; MINUS; e2 = expr { Program.Minus ($startpos, e1, e2) }
  | MINUS; e = expr { Program.Uminus ($startpos, e) } 
  | e1 = expr; PLUS; e2 = expr { Program.Plus ($startpos, e1, e2) }
  | e1 = expr; MULT; e2 = expr { Program.Times ($startpos, e1, e2) }
  | e1 = expr; DIV; e2 = expr { Program.Div ($startpos, e1, e2) }
  | e1 = expr; INTDIV; e2 = expr { Program.Intdiv ($startpos, e1, e2) }
  | e1 = expr; MOD; e2 = expr { Program.Mod ($startpos, e1, e2) }

  (* A Boolean operation *)
  | NOT; e = expr { Program.Not ($startpos, e) } 
  | e1 = expr; AND; e2 = expr { Program.And ($startpos, e1, e2) }
  | e1 = expr; OR; e2 = expr { Program.Or ($startpos, e1, e2) }
  | e1 = expr; XOR; e2 = expr { Program.Xor ($startpos, e1, e2) }
  | e1 = expr; IMPL; e2 = expr { Program.Impl ($startpos, e1, e2) }
  | HASH; LPAREN; e = expr_list; RPAREN { Program.OneHot ($startpos, e) }

  (* A relation *)
  | e1 = expr; LT; e2 = expr { Program.Lt ($startpos, e1, e2) }
  | e1 = expr; GT; e2 = expr { Program.Gt ($startpos, e1, e2) }
  | e1 = expr; LTE; e2 = expr { Program.Lte ($startpos, e1, e2) }
  | e1 = expr; GTE; e2 = expr { Program.Gte ($startpos, e1, e2) }
  | e1 = expr; EQUALS; e2 = expr { Program.Eq ($startpos, e1, e2) } 
  | e1 = expr; NEQ; e2 = expr { Program.Neq ($startpos, e1, e2) } 

  (* An if operation *)
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr 
    { Program.Ite ($startpos, e1, e2, e3) }

  (* A clock operation *)
  | e1 = expr; WHEN; e2 = expr { Program.When ($startpos, e1, e2) }
  | CURRENT; e = expr { Program.Current ($startpos, e) }
  | CONDACT 
    LPAREN; 
    e1 = expr; 
    COMMA; 
    e2 = node_call; 
    COMMA; 
    e3 = expr_list 
    RPAREN
    { Program.Condact ($startpos, e1, e2, e3) } 

  (* A temporal operation *)
  | PRE; e = expr { Program.Pre ($startpos, e) }
  | FBY LPAREN; e1 = expr COMMA; s = NUMERAL; COMMA; e2 = expr RPAREN
    { Program.Fby ($startpos, e2, (int_of_string s), e2) } 
  | e1 = expr; ARROW; e2 = expr { Program.Arrow ($startpos, e1, e2) }

  (* A node or function call *)
  | e = node_call { e } 


(* A node or function call *)
node_call:
  | s = SYM ; LPAREN; a = separated_list(COMMA, expr); RPAREN 
    { Program.Call ($startpos, s, a) }


(* A list of expressions *)
expr_list: l = separated_nonempty_list(COMMA, expr) { l }


(* An array slice *)
array_slice: il = expr; DOTDOT; iu = expr { il, iu }

(* A list of array slices *)
array_slice_list: l = separated_nonempty_list(COMMA, array_slice) { l }

(* ********************************************************************** *)


clock_expr:
  | c = ident { Program.ClockPos c } 
  | NOT; c = ident { Program.ClockNeg c } 
  | NOT; LPAREN; c = ident; RPAREN { Program.ClockNeg c } 
  | TRUE { Program.ClockTrue }


(* ********************************************************************** *)


(* An identifier *)
ident: s = SYM { s }


(* An identifier with a type *)
typed_ident: s = ident; COLON; t = lustre_type { (s, t) }


(* A comma-separated list of identifiers *)
ident_list:
  | l = separated_nonempty_list(COMMA, ident) { l }


(* A comma-separated list of types *)
lustre_type_list:
  | l = separated_nonempty_list(COMMA, lustre_type) { l }
  

(* A list of comma-separated identifiers with a type *)
typed_idents: 
  | l = separated_nonempty_list(COMMA, ident); COLON; t = lustre_type 

    (* Pair each identifier with the type *)
    { List.map (function e -> (e, t)) l }


(* A list of lists of typed identifiers *)
typed_idents_list: 
  | a = separated_list(SEMICOLON, typed_idents) 

    (* Return a flat list *)
    { List.flatten a }


(* Typed identifiers that may be constant *)
const_typed_idents: 
  | o = boption(CONST); l = typed_idents 

    (* Pair each typed identifier with a flag *)
    { List.map (function (e, t) -> (e, t, o)) l }


(* A list of lists of typed identifiers that may be constant *)
const_typed_idents_list: 
  | a = separated_list(SEMICOLON, const_typed_idents) 

    (* Return a flat list *)
    { List.flatten a }


(* A list of comma-separated identifiers with a type *)
clocked_typed_idents: 

  (* Unclocked typed identifiers *)
  | l = typed_idents

    (* Pair each typed identifier with the base clock *)
    { List.map (function (e, t) -> (e, t, Program.ClockTrue)) l }

  (* Clocked typed identifiers *)
  | l = typed_idents; WHEN; c = clock_expr
  | LPAREN; l = typed_idents; RPAREN; WHEN; c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map (function (e, t) -> (e, t, c)) l }

  (* Separate rule for non-singleton list to avaoid shift/reduce conflict *)
  | LPAREN; 
    h = typed_idents; 
    SEMICOLON; 
    l = typed_idents_list; 
    RPAREN; 
    WHEN; 
    c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map (function (e, t) -> (e, t, c)) (h @ l) }



(* A list of lists of typed and clocked identifiers *)
clocked_typed_idents_list: 
  | a = separated_list(SEMICOLON, clocked_typed_idents) 

    (* Return a flat list *)
    { List.flatten a }


(* A list of comma-separated identifiers with a type and a clock that may be constant *)
const_clocked_typed_idents: 

  (* Unclocked typed identifiers *)
  | l = const_typed_idents

    (* Pair each typed identifier with the base clock *)
    { List.map (function (e, t, o) -> (e, t, Program.ClockTrue, o)) l }

  (* Clocked typed identifiers *)
  | l = const_typed_idents; WHEN; c = clock_expr
  | LPAREN; l = const_typed_idents; RPAREN; WHEN; c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map (function (e, t, o) -> (e, t, c, o)) l }

  (* Separate rule for non-singleton list to avaoid shift/reduce conflict *)
  | LPAREN; 
    h = const_typed_idents; 
    SEMICOLON; 
    l = const_typed_idents_list; 
    RPAREN; 
    WHEN; 
    c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map (function (e, t, o) -> (e, t, c, o)) (h @ l) }


(* A list of lists of typed and clocked identifiers that may be constant *)
const_clocked_typed_idents_list: 
  | a = separated_list(SEMICOLON, const_clocked_typed_idents) { List.flatten a }



(* 
   Local Variables:
   compile-command: "ocamlbuild -use-menhir -tag debug -tag annot test.native"
   indent-tabs-mode: nil
   End: 
*)
  
