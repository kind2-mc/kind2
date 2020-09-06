(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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


%{
open Lib

module A = LustreAst

let mk_pos = position_of_lexing 


let rec add_else_branch b belse =
  match b with
  | A.Target _ -> failwith "Cannot add else branch to unconditional target"
  | A.TransIf (p, e, b1, None) -> A.TransIf (p, e, b1, Some belse)
  | A.TransIf (p, e, b1, Some b2) ->
     A.TransIf (p, e, b1, Some (add_else_branch b2 belse))
     
           
let merge_branches transitions =
  List.fold_right (fun (p, b) acc ->
      match acc, b with
      | None, _ -> Some (p, b)
      | Some (_, b2), b1 -> Some (p, add_else_branch b1 b2)
    ) transitions None
  
%}

(* Special characters *)
%token SEMICOLON 
%token EQUALS 
%token COLON 
%token COMMA 
%token LSQBRACKET 
%token RSQBRACKET 
%token LPAREN 
%token RPAREN 
%token DOTPERCENT

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

%token <string>STRING

(* Identifier token *)
%token <string>SYM 
%token <string>QUOTSYM 
      
(* Tokens for types *)
%token TYPE
%token INT
%token UINT8;
%token UINT16;
%token UINT32;
%token UINT64;
%token INT8;
%token INT16;
%token INT32;
%token INT64;
%token REAL
%token BOOL
%token SUBRANGE
%token OF
    
(* Tokens for arrays *)
(* %token ARRAY *)
%token CARET
%token DOTDOT
%token PIPE

(* Token for constant declarations *)
%token CONST
    
(* Tokens for node declarations *)
%token IMPORTED
%token NODE
%token LPARAMBRACKET
%token RPARAMBRACKET
%token FUNCTION
%token RETURNS
%token VAR
%token LET
%token TEL
    
(* Tokens for annotations *)

(* Inline annotations. *)
%token MAIN_P_ANNOT
%token MAIN_B_ANNOT
%token PROPERTY_ANNOT
(* Parenthesis star (PS) block annotations. *)
%token MAIN_PSBLOCKSTART
%token PROPERTY_PSBLOCKSTART
%token CONTRACT_PSATBLOCK
%token PSBLOCKEND
(* Slash star (PS) block annotations. *)
%token MAIN_SSBLOCKSTART
%token PROPERTY_SSBLOCKSTART
%token CONTRACT_SSATBLOCK
%token SSBLOCKEND
(* Contract annotations. *)
%token CONTRACT
%token IMPORTCONTRACT
(* %token IMPORTMODE *)
%token ASSUME
%token GUARANTEE
%token MODE
%token REQUIRE
%token ENSURE
%token WEAKLY

(* Token for assertions *)
%token ASSERT
    
(* Token for check *)
%token CHECK

(* Tokens for Boolean operations *)
%token TRUE
%token FALSE
%token NOT
%token AND
%token XOR
%token OR
%token IF
%token WITH
%token THEN
%token ELSE
%token IMPL
%token HASH
%token FORALL
%token EXISTS
    
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
    
(* Tokens for bitvector operators *)
%token BVAND
%token BVOR
%token BVNOT
%token LSH
%token RSH

(* Tokens for clocks *)
%token WHEN
%token CURRENT
%token CONDACT
%token ACTIVATE
%token INITIAL
%token DEFAULT
%token EVERY
%token RESTART
%token MERGE

(* Tokens for automata *)
%token AUTOMATON
%token STATE
%token UNLESS
%token UNTIL
%token RESUME
%token ELSIF
%token END

(* Tokens for temporal operators *)
%token PRE
%token LAST
%token FBY
%token ARROW
    
(* Token for end of file marker *)
%token EOF
    
(* Priorities and associativity of operators, lowest first *)
%nonassoc UINT8 UINT16 UINT32 UINT64 INT8 INT16 INT32 INT64
%nonassoc WHEN CURRENT 
%left PIPE
%nonassoc ELSE
%right ARROW
%nonassoc prec_forall prec_exists
%right IMPL
%left OR XOR
%left AND
%left LT LTE EQUALS NEQ GTE GT
%left PLUS MINUS
%left MULT INTDIV MOD DIV
%left BVAND BVOR
%nonassoc LSH RSH
%nonassoc PRE 
%nonassoc INT REAL 
%nonassoc NOT
%nonassoc BVNOT 
%left CARET 
%left LSQBRACKET DOT DOTPERCENT

(* Start token *)
%start <LustreAst.t> main
%start <LustreAst.expr> one_expr

%%
(** Parser for lustre systems. *)

one_expr: e = expr EOF { e }


(* A Lustre program is a list of declarations *)
main: p = list(decl) EOF { List.flatten p }


(* A declaration is a type, a constant, a node or a function declaration *)
decl:
  | d = const_decl { List.map 
                       (function e -> A.ConstDecl (mk_pos $startpos, e)) 
                       d }
  | d = type_decl { List.map 
                      (function e -> A.TypeDecl (mk_pos $startpos, e)) 
                      d }
  | NODE ; decl = node_decl ; def = node_def {
    let (n, p, i, o, r) = decl in
    let (l, e) = def in
    [A.NodeDecl ( mk_pos $startpos, (n, false, p, i, o, l, e, r) )]
  }
  | FUNCTION ; decl = node_decl ; def = node_def {
    let (n, p, i, o, r) = decl in
    let (l, e) = def in
    [A.FuncDecl (mk_pos $startpos, (n, false, p, i, o, l, e, r))]
  }
  | NODE ; IMPORTED ; decl = node_decl {
    let (n, p, i, o, r) = decl in
    [A.NodeDecl ( mk_pos $startpos, (n, true, p, i, o, [], [], r) )]
  }
  | FUNCTION ; IMPORTED ; decl = node_decl {
    let (n, p, i, o, r) = decl in
    [A.FuncDecl (mk_pos $startpos, (n, true, p, i, o, [], [], r))]
  }
  | d = contract_decl { [A.ContractNodeDecl (mk_pos $startpos, d)] }
  | d = node_param_inst { [A.NodeParamInst (mk_pos $startpos, d)] }


(* ********************************************************************** *)


(* A constant declaration *)
const_decl: CONST; l = nonempty_list(const_decl_body) { List.flatten l }

(* The body of a constant declaration *)
const_decl_body:

  (* Imported (free) constant 

     Separate rule for singleton list to avoid shift/reduce conflict *)
  | h = ident; COLON; t = lustre_type; SEMICOLON 
    { [A.FreeConst (mk_pos $startpos, h, t)] } 

  (* Imported (free) constant *)
  | h = ident; COMMA; l = ident_list; COLON; t = lustre_type; SEMICOLON 
    { List.map (function e -> A.FreeConst (mk_pos $startpos, e, t)) (h :: l) } 

  (* Defined constant without a type *)
  | s = ident; EQUALS; e = expr; SEMICOLON 
    { [A.UntypedConst (mk_pos $startpos, s, e)] }

  (* Defined constant with a type *)
  | c = typed_ident; EQUALS; e = expr; SEMICOLON 
    { let (_, s, t) = c in [A.TypedConst (mk_pos $startpos, s, e, t)] }


(* ********************************************************************** *)


(* A type declaration *) 
type_decl: 

  (* A free type *)
  | TYPE; l = ident_list; SEMICOLON 
     { List.map (fun e -> A.FreeType (mk_pos $startpos, e)) l }

  (* A type alias *)
  | TYPE; l = ident_list; EQUALS; t = lustre_type; SEMICOLON
     { List.map (fun e -> 
                 A.AliasType (mk_pos $startpos, e, t)) l }

  (* Definition of an enum type*)
  | TYPE; l = ident_list; EQUALS; t = enum_type; SEMICOLON
     { List.map (fun e ->
           A.AliasType (mk_pos $startpos, e,
                        A.EnumType (mk_pos $startpos, e, t))) l }

  (* A record type, can only be defined as alias *)
  | TYPE; l = ident_list; EQUALS; t = record_type; SEMICOLON
     { List.map 
         (function e -> 
           A.AliasType (mk_pos $startpos, 
                        e, 
                        A.RecordType (mk_pos $startpos, t))) 
         l }


(* A type *)
lustre_type:

  (* Predefined types *)
  | BOOL { A.Bool (mk_pos $startpos) }
  | INT { A.Int (mk_pos $startpos)}
  | REAL { A.Real (mk_pos $startpos)}
  | UINT8 { A.UInt8 (mk_pos $startpos)}
  | UINT16 { A.UInt16 (mk_pos $startpos)}
  | UINT32 { A.UInt32 (mk_pos $startpos)}
  | UINT64 { A.UInt64 (mk_pos $startpos)}
  | INT8 { A.Int8 (mk_pos $startpos)}
  | INT16 { A.Int16 (mk_pos $startpos)}
  | INT32 { A.Int32 (mk_pos $startpos)}
  | INT64 { A.Int64 (mk_pos $startpos)}
  | SUBRANGE;
    LSQBRACKET;
    l = expr; 
    COMMA; 
    u = expr; 
    RSQBRACKET 
    OF
    INT 
    { A.IntRange (mk_pos $startpos, l, u)}

  (* User-defined type *)
  | s = ident { A.UserType (mk_pos $startpos, s) }

  (* Tuple type *)
  | t = tuple_type { A.TupleType (mk_pos $startpos, t) } 

(* Record types can only be defined as aliases 
  (* Record type (V6) *)
  | t = record_type { A.RecordType t } 
*)

  (* Array type (V6) *)
  | t = array_type { A.ArrayType (mk_pos $startpos, t) }

(* A tuple type *)
tuple_type:

  (* Tuples are between square brackets *)
  | LSQBRACKET; l = lustre_type_list; RSQBRACKET { l } 


(* A record type (V6) *)
record_type:

  (* Keyword "struct" is optional *)
  | option(STRUCT); 
    f = tlist(LCURLYBRACKET, SEMICOLON, RCURLYBRACKET, typed_idents)
  
    { List.flatten f  }


(* An array type (V6) *)
array_type: 
  | t = lustre_type; CARET; s = expr { t, s }

(*
  (* Alternate syntax: array [size] of type *)
  | ARRAY; s = expr; OF; LSQBRACKET; t = lustre_type; RSQBRACKET { t, s }
*)

(* An enum type (V6) *)
enum_type: ENUM LCURLYBRACKET; l = ident_list; RCURLYBRACKET { l } 


(* ********************************************************************** *)


(* A node declaration and contract. *)
node_decl:
| n = ident;
  p = loption(static_params);
  i = tlist(LPAREN, SEMICOLON, RPAREN, const_clocked_typed_idents);
  RETURNS;
  o = tlist(LPAREN, SEMICOLON, RPAREN, clocked_typed_idents);
  option(SEMICOLON);
  r = option(contract_spec)
  {
    (n, p, List.flatten i, List.flatten o, r)
  }

(* A node definition (locals + body). *)
node_def:
  l = list(node_local_decl);
  LET;
  e = list(node_item);
  TEL
  option(node_sep)

  { (List.flatten l, e) }


contract_ghost_var:
  | VAR ;
    i = ident ; COLON ; t = lustre_type; EQUALS ; e = qexpr ;
    SEMICOLON 
    { A.GhostVar (A.TypedConst (mk_pos $startpos, i, e, t)) }
(*  | VAR ; i = ident ; EQUALS ; e = expr ; SEMICOLON 
    { A.GhostVar (A.UntypedConst (mk_pos $startpos, i, e)) } *)

contract_ghost_const:
  | CONST; i = ident; COLON; t = lustre_type; EQUALS; e = qexpr; SEMICOLON 
    { A.GhostConst (A.TypedConst (mk_pos $startpos, i, e, t)) }
  | CONST; i = ident; EQUALS; e = qexpr; SEMICOLON 
    { A.GhostConst (A.UntypedConst (mk_pos $startpos, i, e)) }

contract_assume:
  | ASSUME; name = option(STRING); e = qexpr; SEMICOLON
  { A.Assume (mk_pos $startpos, name, false, e) }
  | WEAKLY; ASSUME; name = option(STRING); e = qexpr; SEMICOLON
  { A.Assume (mk_pos $startpos, name, true, e) }

contract_guarantee:
  GUARANTEE; name = option(STRING); e = qexpr; SEMICOLON
  { A.Guarantee (mk_pos $startpos, name, false, e) }
  | WEAKLY; GUARANTEE; name = option(STRING); e = qexpr; SEMICOLON
  { A.Guarantee (mk_pos $startpos, name, true, e) }

contract_require:
  REQUIRE; name = option(STRING); e = qexpr; SEMICOLON
  { mk_pos $startpos, name, e }

contract_ensure:
  ENSURE; name = option(STRING); e = qexpr; SEMICOLON
  { mk_pos $startpos, name, e }

mode_equation:
  MODE; n = ident; LPAREN;
  reqs = list(contract_require);
  enss = list(contract_ensure);
  RPAREN; SEMICOLON {
    A.Mode (mk_pos $startpos, n, reqs, enss)
  }

contract_import:
  IMPORTCONTRACT ; n = ident ;
  LPAREN ; in_params = separated_list(COMMA, qexpr) ; RPAREN ; RETURNS ;
  LPAREN ; out_params = separated_list(COMMA, qexpr) ; RPAREN ; SEMICOLON ; {
    A.ContractCall (mk_pos $startpos, n, in_params, out_params)
  }


contract_item:
  | v = contract_ghost_var { v } 
  | c = contract_ghost_const { c }
  | a = contract_assume { a }
  | g = contract_guarantee { g }
  | m = mode_equation { m }
  | i = contract_import { i }

contract_in_block:
  | c = nonempty_list(contract_item) { c }


(* A contract node declaration. *)
contract_decl:
  | CONTRACT;
    n = ident; 
    p = loption(static_params);
    i = tlist(LPAREN, SEMICOLON, RPAREN, const_clocked_typed_idents); 
    RETURNS; 
    o = tlist(LPAREN, SEMICOLON, RPAREN, clocked_typed_idents); 
    SEMICOLON;
    LET;
      e = contract_in_block;
    TEL
    option(node_sep) 

    { (n,
       p,
       List.flatten i,
       List.flatten o,
       e) }


contract_spec:
  (* Block contract, parenthesis star (PS). *)
  | CONTRACT_PSATBLOCK ;
    eqs = contract_in_block
    PSBLOCKEND
    { eqs }
  (* Block contract, slash star (SS). *)
  | CONTRACT_SSATBLOCK ;
    eqs = contract_in_block
    SSBLOCKEND
    { eqs }


(* A node declaration as an instance of a paramterized node *)
node_param_inst: 
  | NODE; 
    n = ident; 
    EQUALS;
    s = ident; 
    p = tlist 
         (LPARAMBRACKET, SEMICOLON, RPARAMBRACKET, node_call_static_param); 
    SEMICOLON
        
    { (n, s, p) } 


(* A node declaration is optionally terminated by a period or a semicolon *)
node_sep: DOT | SEMICOLON { }


(* A static parameter is a type *)
static_param:
  | TYPE; t = ident { A.TypeParam t }


(* The static parameters of a node *)
static_params:
  | l = tlist (LPARAMBRACKET, SEMICOLON, RPARAMBRACKET, static_param)
    
    { l }  


(* A node-local declaration of constants or variables *)
node_local_decl:
  | c = const_decl { List.map 
                       (function e -> A.NodeConstDecl (mk_pos $startpos, e))
                       c }
  | v = var_decls { List.map 
                      (function e -> A.NodeVarDecl (mk_pos $startpos, e)) 
                      v }


(* A variable declaration section of a node *)
var_decls: 
  | VAR; l = nonempty_list(var_decl) { List.flatten l }


(* A declaration of variables *)
var_decl:
  | l = clocked_typed_idents; SEMICOLON { l }


boolean:
  | TRUE { true }
  | FALSE { false }

    
main_annot:
  | MAIN_P_ANNOT ; SEMICOLON { A.AnnotMain true }
  | MAIN_PSBLOCKSTART ; option (SEMICOLON) ; PSBLOCKEND { A.AnnotMain true }
  | MAIN_SSBLOCKSTART ; option (SEMICOLON) ; SSBLOCKEND { A.AnnotMain true }
  | MAIN_B_ANNOT ; COLON ; b = boolean ; SEMICOLON { A.AnnotMain b }
  | MAIN_PSBLOCKSTART ; COLON ; b = boolean ; option (SEMICOLON) ; PSBLOCKEND {
    A.AnnotMain b
  }
  | MAIN_SSBLOCKSTART ; COLON ; b = boolean ; option (SEMICOLON) ; SSBLOCKEND {
    A.AnnotMain b
  }

property:
  | PROPERTY_ANNOT ; name = option(STRING) ; e = qexpr ; SEMICOLON
    { A.AnnotProperty (mk_pos $startpos, name, e) }
  | PROPERTY_PSBLOCKSTART ; name = option(STRING);
    e = qexpr; SEMICOLON ; PSBLOCKEND
    { A.AnnotProperty (mk_pos $startpos, name, e) }
  | PROPERTY_PSBLOCKSTART ; name = option(STRING);
    COLON; e = qexpr; SEMICOLON ; PSBLOCKEND
    { A.AnnotProperty (mk_pos $startpos, name, e) }
  | PROPERTY_SSBLOCKSTART ; name = option(STRING);
    e = qexpr ; SEMICOLON; SSBLOCKEND
    { A.AnnotProperty (mk_pos $startpos, name, e) }
  | PROPERTY_SSBLOCKSTART ; name = option(STRING);
    COLON; e = qexpr ; SEMICOLON; SSBLOCKEND
    { A.AnnotProperty (mk_pos $startpos, name, e) }

check:
  | CHECK ; name = option(STRING) ; e = qexpr ; SEMICOLON
    { A.AnnotProperty (mk_pos $startpos, name, e) }

node_item:
  | e = node_equation { A.Body e }
  | a = main_annot { a }
  | p = property { p }
  | p = check { p }


(* An equations of a node *)
node_equation:

  (* An assertion *)
  | ASSERT; e = qexpr; SEMICOLON
    { A.Assert (mk_pos $startpos, e) }

  (* An equation, multiple (optionally parenthesized) identifiers on 
     the left-hand side, an expression on the right *)
  | l = left_side; EQUALS; e = expr; SEMICOLON
    { A.Equation (mk_pos $startpos, l, e) }

  (* An automaton *)
  | AUTOMATON; i = option(ident); s = list(state);
    RETURNS; out = ident_list; SEMICOLON
    { A.Automaton (mk_pos $startpos, i, s, A.Given out) }

  | AUTOMATON; i = option(ident); s = list(state);
    RETURNS DOTDOT SEMICOLON
    { A.Automaton (mk_pos $startpos, i, s, A.Inferred) }

  | AUTOMATON; i = option(ident); s = nonempty_list(state)
    { A.Automaton (mk_pos $startpos, i, s, A.Inferred) }


state_decl:
  | STATE; i = ident { i, false }
  | INITIAL STATE; i = ident { i, true }

state:
  | ii = state_decl; option(COLON)
    us = unless_transitions;
    l = list(node_local_decl);
    LET;
    e = list(node_equation);
    TEL;
    ul = until_transitions
    { let i, init = ii in
      A.State (mk_pos $startpos, i, init, List.flatten l, e,
               merge_branches us, merge_branches ul) }

  | ii = state_decl; option(COLON)
    us = unless_transitions;
    ul = until_transitions
    { let i, init = ii in
      A.State (mk_pos $startpos, i, init, [], [],
               merge_branches us, merge_branches ul) }


unless_transitions:
  | { [] }
  | UNLESS; b = transition_branch; u = unless_transitions
    { (mk_pos $startpos, b) :: u }


until_transitions:
  | { [] }
  | UNTIL; b = transition_branch; u = until_transitions
    { (mk_pos $startpos, b) :: u }


transition_branch:
  | b = branch; option(SEMICOLON)
    { b }
  | e = expr; t = target; option(SEMICOLON)
    { A.TransIf (mk_pos $startpos, e, A.Target t, None) }
  | IF; e = expr; t = target; option(SEMICOLON)
    { A.TransIf (mk_pos $startpos, e, A.Target t, None) }


branch:
  | t = target
    { A.Target t }
  | IF; e = expr; b = branch; END
    { A.TransIf (mk_pos $startpos, e, b, None) }
  | IF; e = expr; b = branch; b2 = elsif_branch; END
    { A.TransIf (mk_pos $startpos, e, b, Some b2) }
    
elsif_branch:
  | ELSE; b = branch
    { b } 
  | ELSIF; e = expr; b = branch
    { A.TransIf (mk_pos $startpos, e, b, None) }
  | ELSIF; e = expr; b = branch; b2 = elsif_branch
    { A.TransIf (mk_pos $startpos, e, b, Some b2) }

target_state:
  | s = ident
    { mk_pos $startpos, s }

target:
  | RESTART; s = target_state
    { A.TransRestart (mk_pos $startpos, s) }

  | RESUME; s = target_state
    { A.TransResume (mk_pos $startpos, s) }

left_side:

  (* List without parentheses *)
  | l = struct_item_list { A.StructDef (mk_pos $startpos, l) }

  (* Parenthesized list *)
  | LPAREN; l = struct_item_list; RPAREN { A.StructDef (mk_pos $startpos, l) }

  (* Empty list *)
  | LPAREN; RPAREN { A.StructDef (mk_pos $startpos, []) }


(* Item in a structured equation *)
struct_item:

  (* Single identifier *)
  | s = ident
      { A.SingleIdent (mk_pos $startpos, s) }
          
  (* Recursive array definition *)
  | s = ident; l = nonempty_list(index_var)
     { A.ArrayDef (mk_pos $startpos, s, l)}

(*
  (* Filter array values *)
  | LSQBRACKET; l = struct_item_list; RSQBRACKET 
    { A.TupleStructItem (mk_pos $startpos, l) }

  (* Select from tuple *)
  | e = ident; LSQBRACKET; i = expr; RSQBRACKET 
    { A.TupleSelection (mk_pos $startpos, e, i) }

  (* Select from record *)
  | e = ident; DOT; i = ident 
    { A.FieldSelection (mk_pos $startpos, e, i) }
 
  | e = ident; LSQBRACKET; s = array_slice_list; RSQBRACKET 
    { A.ArraySliceStructItem (mk_pos $startpos, e, s) }
*)

(* List of structured items *)
struct_item_list:
 | l = separated_nonempty_list(COMMA, struct_item) { l }

(* Running variable for index *)
index_var:
  | LSQBRACKET; s = ident; RSQBRACKET { s }

(* Two colons (for mode reference). *)
two_colons:
  | COLON ; COLON {}

(* ********************************************************************** *)

(* dummy rule for parameter of pexpr to signal we allow quantifiers *)
%inline quantified:
  | { true }

(* dummy rule for parameter of pexpr to signal we do not allow quantifiers *)
%inline nonquantified:
  | { false }
  
(* An possibly quantified expression *)
pexpr(Q): 
  
  (* An identifier *)
  | s = ident { A.Ident (mk_pos $startpos, s) } 

  (* A mode reference. *)
  | two_colons ; mode_ref = separated_nonempty_list(two_colons, ident) {
    A.ModeRef (mk_pos $startpos, mode_ref)
  }

  (* A propositional constant *)
  | TRUE { A.Const (mk_pos $startpos, A.True) }
  | FALSE { A.Const (mk_pos $startpos, A.False) }

  (* An integer numeral or a floating-point decimal constant *)
  | s = NUMERAL { A.Const (mk_pos $startpos, A.Num s) } 
  | s = DECIMAL { A.Const (mk_pos $startpos, A.Dec s) } 

  (* Conversions *)
  | INT; e = expr { A.ConvOp (mk_pos $startpos, A.ToInt, e) }
  | REAL; e = expr { A.ConvOp (mk_pos $startpos, A.ToReal, e) }
  | UINT8; e = expr { A.ConvOp (mk_pos $startpos, A.ToUInt8, e) }
  | UINT16; e = expr { A.ConvOp (mk_pos $startpos, A.ToUInt16, e) }
  | UINT32; e = expr { A.ConvOp (mk_pos $startpos, A.ToUInt32, e) }
  | UINT64; e = expr { A.ConvOp (mk_pos $startpos, A.ToUInt64, e) }
  | INT8; e = expr { A.ConvOp (mk_pos $startpos, A.ToInt8, e) }
  | INT16; e = expr { A.ConvOp (mk_pos $startpos, A.ToInt16, e) }
  | INT32; e = expr { A.ConvOp (mk_pos $startpos, A.ToInt32, e) }
  | INT64; e = expr { A.ConvOp (mk_pos $startpos, A.ToInt64, e) }

  (* A parenthesized single expression *)
  | LPAREN; e = pexpr(Q); RPAREN { e } 

  (* An expression list (not quantified)

     Singleton list is in production above *)
  | LPAREN; h = pexpr(Q); COMMA; l = pexpr_list(Q); RPAREN 
    { A.GroupExpr (mk_pos $startpos, A.ExprList, h :: l) } 

  (* A tuple expression (not quantified) *)
  (* | LSQBRACKET; l = qexpr_list; RSQBRACKET { A.TupleExpr (mk_pos $startpos, l) } *)
  | LCURLYBRACKET; l = pexpr_list(Q); RCURLYBRACKET { A.GroupExpr (mk_pos $startpos, A.TupleExpr, l) }

  (* An array expression (not quantified) *)
  | LSQBRACKET; l = pexpr_list(Q); RSQBRACKET { A.GroupExpr (mk_pos $startpos, A.ArrayExpr, l) }

  (* An array constructor (not quantified) *)
  | e1 = pexpr(Q); CARET; e2 = expr { A.ArrayConstr (mk_pos $startpos, e1, e2) }

  (* Tuple projection (not quantified) *)
  | e = pexpr(Q); DOTPERCENT; i = NUMERAL 
    { A.TupleProject (mk_pos $startpos, e, (int_of_string i)) }

  (* An array slice (not quantified) *)
  | e = pexpr(Q); LSQBRACKET; s = array_slice; RSQBRACKET
    { A.ArraySlice (mk_pos $startpos, e, s) }

  (* An array index (not quantified) *)
  | e = pexpr(Q); LSQBRACKET; i = expr; RSQBRACKET
    { A.ArrayIndex (mk_pos $startpos, e, i) }
    
  (* A record field projection (not quantified) *)
  | s = pexpr(Q); DOT; t = ident 
    { A.RecordProject (mk_pos $startpos, s, t) }

  (* A record (not quantified) *)
  | t = ident; 
    f = tlist(LCURLYBRACKET, SEMICOLON, RCURLYBRACKET, record_field_assign)
    { A.RecordExpr (mk_pos $startpos, t, f) }

  (* An array concatenation *)
  | e1 = pexpr(Q); PIPE; e2 = pexpr(Q) { A.ArrayConcat (mk_pos $startpos, e1, e2) } 

  (* with operator for updating fields of a structure (not quantified) *)
  | LPAREN; 
    e1 = pexpr(Q); 
    WITH; 
    i = nonempty_list(label_or_index); 
    EQUALS; 
    e2 = pexpr(Q); 
    RPAREN

    { A.StructUpdate (mk_pos $startpos, e1, i, e2) } 

  (* An arithmetic operation *)
  | e1 = pexpr(Q); MINUS; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Minus, e1, e2) }
  | MINUS; e = expr { A.UnaryOp (mk_pos $startpos, A.Uminus, e) } 
  | e1 = pexpr(Q); PLUS; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Plus, e1, e2) }
  | e1 = pexpr(Q); MULT; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Times, e1, e2) }
  | e1 = pexpr(Q); DIV; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Div, e1, e2) }
  | e1 = pexpr(Q); INTDIV; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.IntDiv, e1, e2) }
  | e1 = pexpr(Q); MOD; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Mod, e1, e2) }

  (* A Boolean operation *)
  | NOT; e = pexpr(Q) { A.UnaryOp (mk_pos $startpos, A.Not, e) } 
  | e1 = pexpr(Q); AND; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.And, e1, e2) }
  | e1 = pexpr(Q); OR; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Or, e1, e2) }
  | e1 = pexpr(Q); XOR; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Xor, e1, e2) }
  | e1 = pexpr(Q); IMPL; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.Impl, e1, e2) }
  | HASH; LPAREN; e = pexpr_list(Q); RPAREN { A.NArityOp (mk_pos $startpos, A.OneHot, e) }

  (* A Bitvector operator *)
  | BVNOT; e = pexpr(Q) { A.UnaryOp (mk_pos $startpos, A.BVNot, e) }
  | e1 = pexpr(Q); BVAND; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.BVAnd, e1, e2) }
  | e1 = pexpr(Q); BVOR; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.BVOr, e1, e2) }
  | e1 = pexpr(Q); LSH; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.BVShiftL, e1, e2) }
  | e1 = pexpr(Q); RSH; e2 = pexpr(Q) { A.BinaryOp (mk_pos $startpos, A.BVShiftR, e1, e2) }

  (* A quantified expression *)
  | FORALL; q = Q;
    vars = tlist(LPAREN, SEMICOLON, RPAREN, typed_idents); e = pexpr(Q)
    %prec prec_forall
    { let pos = mk_pos $startpos in
      if not q then
        LustreContext.fail_at_position
          pos "Quantifiers not allowed in this position";
      A.Quantifier (pos, A.Forall, List.flatten vars, e) }
  | EXISTS; q = Q;
    vars = tlist(LPAREN, SEMICOLON, RPAREN, typed_idents); e = pexpr(Q)
    %prec prec_exists
    { let pos = mk_pos $startpos in
      if not q then
        LustreContext.fail_at_position
          pos "Quantifiers not allowed in this position";
      A.Quantifier (pos, A.Exists, List.flatten vars, e) }
                                                                       
  (* A relation *)
  | e1 = pexpr(Q); LT; e2 = pexpr(Q) { A.CompOp (mk_pos $startpos, A.Lt, e1, e2) }
  | e1 = pexpr(Q); GT; e2 = pexpr(Q) { A.CompOp (mk_pos $startpos, A.Gt, e1, e2) }
  | e1 = pexpr(Q); LTE; e2 = pexpr(Q) { A.CompOp (mk_pos $startpos, A.Lte, e1, e2) }
  | e1 = pexpr(Q); GTE; e2 = pexpr(Q) { A.CompOp (mk_pos $startpos, A.Gte, e1, e2) }
  | e1 = pexpr(Q); EQUALS; e2 = pexpr(Q) { A.CompOp (mk_pos $startpos, A.Eq, e1, e2) } 
  | e1 = pexpr(Q); NEQ; e2 = pexpr(Q) { A.CompOp (mk_pos $startpos, A.Neq, e1, e2) } 

  (* An if operation *)
  | IF; e1 = pexpr(Q); THEN; e2 = pexpr(Q); ELSE; e3 = pexpr(Q) 
    { A.TernaryOp (mk_pos $startpos, A.Ite, e1, e2, e3) }

  (* Recursive node call *)
  | WITH; e1 = pexpr(Q); THEN; e2 = pexpr(Q); ELSE; e3 = pexpr(Q) 
    { A.TernaryOp (mk_pos $startpos, A.With, e1, e2, e3) }

  (* when operator on qexpression  *)
  | e1 = pexpr(Q); WHEN; e2 = clock_expr { A.When (mk_pos $startpos, e1, e2) }

  (* current operator on qexpression *)
  | CURRENT; e = pexpr(Q) { A.Current (mk_pos $startpos, e) }

  (* condact call with defaults *)
  | CONDACT 
    LPAREN; 
    e1 = pexpr(Q); 
    COMMA; 
    s = ident; LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN; 
    COMMA; 
    d = pexpr_list(Q)
    RPAREN
    { let pos = mk_pos $startpos in
      A.Condact (pos, e1, A.Const (pos, A.False), s, a, d) } 

  (* condact call may have no return values and therefore no defaults *)
  | CONDACT 
    LPAREN; 
    c = pexpr(Q); 
    COMMA; 
    s = ident; LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN; 
    RPAREN

    { let pos = mk_pos $startpos in
      A.Condact (pos, c, A.Const (pos, A.False), s, a, []) } 

  (* condact call with defaults and restart *)
  | CONDACT LPAREN;
    c = pexpr(Q); 
    COMMA;
    LPAREN RESTART; s = ident; EVERY; r = pexpr(Q); RPAREN;
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN; 
    COMMA; 
    d = pexpr_list(Q);
    RPAREN
    { let pos = mk_pos $startpos in
      A.Condact (pos, c, r, s, a, d) } 

  (* condact call with no return values and restart *)
  | CONDACT ; LPAREN;
    c = pexpr(Q); 
    COMMA; 
    LPAREN RESTART; s = ident; EVERY; r = pexpr(Q); RPAREN
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN; 
    RPAREN
    { let pos = mk_pos $startpos in
      A.Condact (pos, c, r, s, a, []) } 

  (* [(activate N every h initial default (d1, ..., dn)) (e1, ..., en)] 
     is an alias for [condact(h, N(e1, ..., en), d1, ,..., dn) ]*)
  | LPAREN; ACTIVATE; s = ident; EVERY; c = pexpr(Q); 
    INITIAL DEFAULT; d = separated_list(COMMA, pexpr(Q)); RPAREN; 
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN

    { let pos = mk_pos $startpos in
      A.Condact (pos, c, A.Const (pos, A.False), s, a, d) }
    
  (* activate operator without initial defaults

     Only supported inside a merge *)
  | LPAREN; ACTIVATE; s = ident; EVERY; c = pexpr(Q); RPAREN; 
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN

    { let pos = mk_pos $startpos in
      A.Activate (pos, s, c, A.Const (pos, A.False), a) }

  (* activate restart *)
  | LPAREN; ACTIVATE;
    LPAREN RESTART; s = ident; EVERY; r = pexpr(Q); RPAREN;
    EVERY; c = pexpr(Q); 
    INITIAL DEFAULT; d = separated_list(COMMA, pexpr(Q)); RPAREN; 
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN

    { let pos = mk_pos $startpos in
      A.Condact (pos, c, r, s, a, d) }
    
  (* alternative syntax for activate restart *)
  | LPAREN; ACTIVATE; s = ident; EVERY; c = pexpr(Q); 
    INITIAL DEFAULT; d = separated_list(COMMA, pexpr(Q));
    RESTART EVERY; r = pexpr(Q); RPAREN;
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN

    { let pos = mk_pos $startpos in
      A.Condact (pos, c, r, s, a, d) }
    
  (* activate operator without initial defaults and restart

     Only supported inside a merge *)
  | LPAREN; ACTIVATE;
    LPAREN RESTART; s = ident; EVERY; r = pexpr(Q); RPAREN;
    EVERY; c = pexpr(Q); RPAREN; 
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN

    { let pos = mk_pos $startpos in
      A.Activate (pos, s, c, r, a) }
    
  (* alternative syntax of previous construct  *)
  | LPAREN; ACTIVATE; s = ident; EVERY; c = pexpr(Q);
    RESTART EVERY; r = pexpr(Q); RPAREN;
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN

    { let pos = mk_pos $startpos in
      A.Activate (pos, s, c, r, a) }

    
  (* restart node call *)
  (*| RESTART; s = ident;
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN;
    EVERY; c = clock_expr

    { A.RestartEvery (mk_pos $startpos, s, a, c) }
   *)
    
  (* alternative syntax for restart node call *)
  | LPAREN; RESTART; s = ident; EVERY; c = pexpr(Q); RPAREN; 
    LPAREN; a = separated_list(COMMA, pexpr(Q)); RPAREN

    { A.RestartEvery (mk_pos $startpos, s, a, c) }
    
        
  (* Binary merge operator *)
  | MERGE; LPAREN;
    c = ident; SEMICOLON;
    pos = pexpr(Q); SEMICOLON;
    neg = pexpr(Q); RPAREN 
    { A.Merge (mk_pos $startpos, c, ["true", pos; "false", neg]) }

  (* N-way merge operator *)
  | MERGE; 
    c = ident;
    l = nonempty_list(merge_case);
    { A.Merge (mk_pos $startpos, c, l) }
    
  (* A temporal operation *)
  | PRE; e = pexpr(Q) { A.Pre (mk_pos $startpos, e) }
  | FBY LPAREN; e1 = pexpr(Q) COMMA; s = NUMERAL; COMMA; e2 = pexpr(Q) RPAREN
    { A.Fby (mk_pos $startpos, e1, (int_of_string s), e2) }

  | e1 = pexpr(Q); ARROW; e2 = pexpr(Q) { A.Arrow (mk_pos $startpos, e1, e2) }

  | LAST; i = ident_or_quotident { A.Last (mk_pos $startpos, i) }
    
  (* A node or function call *)
  | e = node_call { e } 


%inline qexpr:
  | e = pexpr(quantified) { e }

%inline expr:
  | e = pexpr(nonquantified) { e }


(* A list of expressions *)
pexpr_list(Q): l = separated_nonempty_list(COMMA, pexpr(Q)) { l }


(* Static parameters are only types *)
node_call_static_param:
  | t = lustre_type { t }
      

(* A node or function call *)
node_call:

  (* Call a node without static parameters *)
  | s = ident; LPAREN; a = separated_list(COMMA, expr); RPAREN 
    { A.Call (mk_pos $startpos, s, a) }

  (* Call a node with static parameters *)
  | s = ident; 
    p = tlist 
         (LPARAMBRACKET, SEMICOLON, RPARAMBRACKET, node_call_static_param); 
    LPAREN; 
    a = separated_list(COMMA, expr); 
    RPAREN 
    { A.CallParam (mk_pos $startpos, s, p, a) }


(* An array slice *)
array_slice:
  | il = expr; DOTDOT; iu = expr { il, iu }


(* An assignment to a record field *)
record_field_assign: s = ident; EQUALS; e = expr { (s, e) } 


(* ********************************************************************** *)


clock_expr:
  | c = ident { A.ClockPos c } 
  | NOT; c = ident { A.ClockNeg c } 
  | NOT; LPAREN; c = ident; RPAREN { A.ClockNeg c } 
  | cs = ident; LPAREN; c = ident; RPAREN { A.ClockConstr (cs, c) } 
  | TRUE { A.ClockTrue }

merge_case_id:
  | TRUE { "true" }
  | FALSE { "false" }
  | c = ident { c }

merge_case :
  | LPAREN; c = merge_case_id; ARROW; e = expr; RPAREN { c, e }

    
(* ********************************************************************** *)


(* An identifier *)
ident:
  (* Contract tokens are not keywords. *)
  | MODE { "mode" }
  | ASSUME { "assume" }
  | GUARANTEE { "guarantee" }
  | REQUIRE { "require" }
  | ENSURE { "ensure" }
  | WEAKLY { "weakly" }
  | s = SYM { s }

ident_or_quotident:
  | id = ident { id }
  | s = QUOTSYM { s }

(* An identifier with a type *)
typed_ident: s = ident; COLON; t = lustre_type { (mk_pos $startpos, s, t) }


(* A comma-separated list of identifiers *)
ident_list:
  | l = separated_nonempty_list(COMMA, ident) { l }


(* A comma-separated list of types *)
lustre_type_list:
  | l = separated_nonempty_list(COMMA, lustre_type) { l }
  

(* A comma-separated list of identifiers with position information *)
ident_list_pos :
  | i = ident { [mk_pos $startpos, i] }
  | i = ident; COMMA; l = ident_list_pos
    { (mk_pos $startpos, i) :: l }


(* A list of comma-separated identifiers with a type *)
typed_idents: 
  | l = ident_list_pos; COLON; t = lustre_type 
    (* Pair each identifier with the type *)
    { List.map (function (pos, e) -> (pos, e, t)) l }

(*
(* A list of lists of typed identifiers *)
typed_idents_list:
  | a = separated_list(SEMICOLON, typed_idents) 

    (* Return a flat list *)
    { List.flatten a }
*)

(* Typed identifiers that may be constant *)
const_typed_idents: 
  | o = boption(CONST); l = typed_idents 

    (* Pair each typed identifier with a flag *)
    { List.map (function (_, e, t) -> (e, t, o)) l }

(*
(* A list of lists of typed identifiers that may be constant *)
const_typed_idents_list: 
  | a = separated_list(SEMICOLON, const_typed_idents)

    (* Return a flat list *)
    { List.flatten a }
*)

(* A list of comma-separated identifiers with a type *)
clocked_typed_idents: 

  (* Unclocked typed identifiers *)
  | l = typed_idents

    (* Pair each typed identifier with the base clock *)
    { List.map (function (pos, e, t) -> (pos, e, t, A.ClockTrue)) l }

  (* Clocked typed identifiers *)
  | l = typed_idents; WHEN; c = clock_expr
  | LPAREN; l = typed_idents; RPAREN; WHEN; c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map (function (pos, e, t) -> (pos, e, t, c)) l }

  (* Separate rule for non-singleton list to avoid shift/reduce conflict *)
  | LPAREN; 
    h = typed_idents; 
    SEMICOLON; 
    l = tlist_tail(SEMICOLON, RPAREN, typed_idents); 
    WHEN; 
    c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map
        (function (pos, e, t) -> (pos, e, t, c)) 
        (h @ (List.flatten l)) }


(*
(* A list of lists of typed and clocked identifiers *)
clocked_typed_idents_list: 
  | a = separated_list(SEMICOLON, clocked_typed_idents)

    (* Return a flat list *)
    { List.flatten a }
*)

(* A list of comma-separated identifiers with a type and a clock that may be constant *)
const_clocked_typed_idents: 

  (* Unclocked typed identifiers *)
  | l = const_typed_idents

    (* Pair each typed identifier with the base clock *)
    { List.map
        (function (e, t, o) -> (mk_pos $startpos, e, t, A.ClockTrue, o)) 
        l }

  (* Clocked typed identifiers *)
  | l = const_typed_idents; WHEN; c = clock_expr
  | LPAREN; l = const_typed_idents; RPAREN; WHEN; c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map
        (function (e, t, o) -> (mk_pos $startpos, e, t, c, o)) 
        l }

  (* Separate rule for non-singleton list to avaoid shift/reduce conflict *)
  | LPAREN; 
    h = const_typed_idents; 
    SEMICOLON; 
    l = tlist_tail(SEMICOLON, RPAREN, const_typed_idents); 
    WHEN; 
    c = clock_expr

    (* Pair each types identifier the given clock *)
    { List.map (function (e, t, o) -> (mk_pos $startpos, e, t, c, o)) (h @ (List.flatten l)) }

(*
(* A list of lists of typed and clocked identifiers that may be constant *)
const_clocked_typed_idents_list: 
  | a = separated_list(SEMICOLON, const_clocked_typed_idents)

      { List.flatten a }
*)

(* The tail of a list of X *)
tlist_tail(separator, closing, X):
  | x = X; option(separator); closing { [ x ] }
  | x = X; separator; xs = tlist_tail(separator, closing, X)
    { x :: xs }

(* A list of elements between opening and closing, separated by separator, 
   the separator may occur at the end of the list *)
tlist(opening, separator, closing, X):
  | opening; l = tlist_tail(separator, closing, X) { l }
  | opening; closing { [ ] }

(* ********************************************************************** *)


(* An index *)
label_or_index: 

  (* An index into a record *)
  | DOT; i = ident
     { A.Label (mk_pos $startpos, i) } 

  (* An index into an array with a variable or constant *)
  | LSQBRACKET; e = expr; RSQBRACKET
     { A.Index (mk_pos $startpos, e) }

  (* An index into a tuple with a variable or constant *)
  | DOTPERCENT; e = expr; 
     { A.Index (mk_pos $startpos, e) }



(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
