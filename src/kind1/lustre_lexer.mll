{
(*
This file is part of the Kind verifier

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

open Lustre_parser
let linenum = Lus_convert.linenum
let linepos = Lus_convert.linepos
}
rule token = parse
  | "--%PROPERTY" {PROPERTY}
  | "--%METAPROPERTY" [^';']* {METAPROPERTY(
      let s = Lexing.lexeme lexbuf in
      String.sub s 16 ((String.length s) - 16)
     )}
  | "--%MAIN" [^'\n']* {MAIN_NODE}
  | "--" ['\n'] {token lexbuf}
  | "--" [^'%' '\n'] [^'\n']* {token lexbuf}
  |  "/*" ([^'*']* ('*' [^'/'])?)* "*/" {
      String.iter (fun x -> if x = '\n' then incr linenum) (Lexing.lexeme lexbuf);
      token lexbuf}
  | "_TO_" ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* {CONVERT_TO(Lexing.lexeme lexbuf)}
  | "_FROM_" ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* {CONVERT_FROM(Lexing.lexeme lexbuf)}
  | "type" {TYPE}
  | ';' {SEMICOLON}
  | '=' {EQUALS}
  | '[' {LSQBRACKET}
  | ']' {RSQBRACKET}
  | "function" {FUNCTION}
  | "returns" {RETURNS}
  | '(' {LPAREN}
  | ')' {RPAREN}
  | ':' {COLON}
  | ',' {COMMA}
  | "int" {INT}
  | "real" {REAL}
  | "bool" {BOOL}
  | "node" {NODE}
  | "let" {LET}
  | "tel" {TEL}
  | '-' {MINUS}
  | '+' {PLUS}
  | '/' {DIV}
  | '*' {MULT}
  | "div" {INTDIV}
  | "mod" {MOD}
  | "true" {TRUE}
  | "false" {FALSE}
  | "not" {NOT}
  | "and" {AND}
  | "xor" {XOR}
  | "or" {OR}
  | "if" {IF}
  | "then" {THEN}
  | "else" {ELSE}
  | "when" {WHEN}
  | "const" {CONST}
  | "current" {CURRENT}
  | "condact" {CONDACT}
  | "condact_reset" {CONDACT}
  | "assert" {ASSERT}
  | "pre" {PRE}
  | "fby" {FBY}
  | "var" {VAR}
  | "->" {ARROW}
  | "=>" {IMPL}
  | "<=" {LTE}
  | ">=" {GTE}
  | '<' {LT}
  | '>' {GT}
  | "<>" {NEQ}
  | "subrange" {SUBRANGE}
  | "of" {OF}
  | ['0'-'9']+ '.' ['0'-'9']+ {FLOAT(Lexing.lexeme lexbuf)}
  | ['0'-'9']+ '.' ['0'-'9']+ 'E' ('+'|'-') ['0'-'9'] ['0'-'9'] {FLOAT(Lexing.lexeme lexbuf)}
  | ['0'-'9']+ {NUM(Lexing.lexeme lexbuf)}
  | '.' {DOT}
  | ['a'-'z' 'A'-'Z' '_' '~']['a'-'z' 'A'-'Z' '_' '~' '0'-'9']* {SYM(Lexing.lexeme lexbuf)}
  | eof {EOF_TOK}
  | '\n' {incr linenum; linepos := Lexing.lexeme_start lexbuf; token lexbuf}
  | _ {token lexbuf}
