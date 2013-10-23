{
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

(* Recoginized tokens *)
type token =

  (* Include directive *)
  | INCLUDE
  | STRING of string

  (* Special characters *)
  | SEMICOLON 
  | EQUALS 
  | COLON 
  | COMMA 
  | LSQBRACKET 
  | RSQBRACKET 
  | LPAREN 
  | RPAREN 
  | DOT

  (* Decimal or numeral *)
  | DECIMAL of string
  | NUMERAL of string 
      
  (* Identifier *)
  | SYM of string 
      
  (* Type *)
  | TYPE
  | INT
  | REAL
  | BOOL
  | SUBRANGE
  | OF
    
  (* Arrays *)
  | ARRAY
  | CARET
  | LARRAYBRACKET 
  | RARRAYBRACKET 
  | PIPE

  (* Constant declaration *)
  | CONST
    
  (* Node declaration *)
  | NODE
  | FUNCTION
  | RETURNS
  | VAR
  | LET
  | TEL
    
  (* Annotations *)
  | PROPERTY
  | MAIN
    
  (* Assertion *)
  | ASSERT
    
  (* Boolean operators *)
  | TRUE
  | FALSE
  | NOT
  | AND
  | XOR
  | OR
  | IF
  | THEN
  | ELSE
  | IMPL
    
  (* Relations *)
  | LTE
  | GTE
  | LT
  | GT
  | NEQ
    
  (* Arithmetic operators *)
  | MINUS
  | PLUS
  | DIV
  | MULT
  | INTDIV
  | MOD
    
  (* Clock operators *)
  | WHEN
  | CURRENT
  | CONDACT
    
  (* Temporal operators *)
  | PRE
  | FBY
  | ARROW
    
  (* End of file marker *)
  | EOF
    

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
    
(* Create and populate a hashtable *)
let mk_hashtbl size init =
  let tbl = Hashtbl.create size in
  List.iter
    (function (k, v) -> Hashtbl.add tbl k v)
    init;
  tbl
  
(* Use hash tables instead of rule matches to keep numer of transition
   of lexer small *)

(* Hashtable of keywords *)
let keyword_table = 
  mk_hashtbl 
    43
    [

      (* Include directive *)
      ("include", INCLUDE);

      (* Types *)
      ("type", TYPE);
      ("int", INT);
      ("real", REAL);
      ("bool", BOOL);
      ("subrange", SUBRANGE);
      ("of", OF);
      ("array", ARRAY);

      (* Constant declaration *)
      ("const", CONST);
      
      (* Node declaration *)
      ("node", NODE);
      ("function", FUNCTION);
      ("returns", RETURNS);
      ("var", VAR);
      ("let", LET);
      ("tel", TEL);
      
      (* Assertion *)
      ("assert", ASSERT);
      
      (* Boolean operators *)
      ("true", TRUE);
      ("false", FALSE);
      ("not", NOT);
      ("and", AND);
      ("xor", XOR);
      ("or", OR);
      ("if", IF);
      ("then", THEN);
      ("else", ELSE);
      ("=>", IMPL);
      
      (* Relations *)
      ("<=", LTE);
      (">=", GTE);
      ("<", LT);
      (">", GT);
      ("<>", NEQ);
      
      (* Arithmetic operators *)
      ("-", MINUS);
      ("+", PLUS);
      ("/", DIV);
      ("*", MULT);
      ("div", INTDIV);
      ("mod", MOD);
      
      (* Clock operators *)
      ("when", WHEN);
      ("current", CURRENT);
      ("condact", CONDACT);
      
      (* Temporal operators *)
      ("pre", PRE);
      ("fby", FBY);
      ("->",  ARROW)
      
    ]
    
}


(* Identifier *)
let id = ['a'-'z' 'A'-'Z' '_' '~'] ['a'-'z' 'A'-'Z' '_' '~' '0'-'9']*
  
(* Keep these separated from alphabetic characters, otherwise a->b would be one token *)
let printable = ['+' '-' '*' '/' '>' '<' '=' ]+

(* Floating point decimal *)
let decimal = ['0'-'9']+ '.' ['0'-'9']+ ('E' ('+'|'-')? ['0'-'9']+)?

(* Integer numeral *)
let numeral = ['0'-'9']+

(* Whitespace *)
let whitespace = [' ' '\t']

(* Newline *)
let newline = '\r'* '\n'

(* Toplevel function *)
rule token = parse
(*
  (* Annotation *)
  | "--%" (id as p) 
      { try Hashtbl.find annotation_table p with 
	| Not_found -> 
	  (Format.printf "Warninng: unknown annotation %s skipped@." p; 
	   skip_to_eol lexbuf ) }

  (* Comment until end of line *)
  | "--" [^'\n'] * newline { Lexing.new_line lexbuf; token lexbuf }
*)

  (* Comment until end of line *)
  | "--" '-'* { comment lexbuf }

  (* Multi-line comment *)
  |  "/*" { skip_commented lexbuf }

  (* String *)
  | '\"' ([^'\"']* as p) '\"' { STRING p }

  (* Delimiters *)
  | ';' { SEMICOLON }
  | '=' { EQUALS }
  | ':' { COLON }
  | ',' { COMMA }
  | '[' { LSQBRACKET }
  | ']' { RSQBRACKET }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '.' { DOT }
  | '^' { CARET }
  | "[|" { LARRAYBRACKET }
  | "|]" { RARRAYBRACKET }
  | '|' { PIPE }

  (* Decimal or numeral *)
  | decimal as p { DECIMAL p }
  | numeral as p { NUMERAL p } 

  (* Keyword *)
  | id as p 
      { try Hashtbl.find keyword_table p with 
	| Not_found -> (SYM p) }

  (* Symbol that is not a delimiter *)
  | printable+ as p 
      { try Hashtbl.find keyword_table p with 
	| Not_found -> failwith (Format.sprintf "Unknown operator %s" p) }

  (* Whitespace *)
  | whitespace { token lexbuf }

  (* Newline *)
  | newline { Lexing.new_line lexbuf; token lexbuf }

  (* End of file *)
  | eof 
      { EOF }

  (* Unrecognized character *)
  | _ as c 
      { failwith 
          (Format.sprintf "Unrecognized token %c (%X)" c (Char.code c)) }

(* Parse until end of comment, count newlines and otherwise discard
   characters *)
and skip_commented = parse 

  (* End of comment *)
  | "*/" { token lexbuf } 

  (* Count new line *)
  | newline { Lexing.new_line lexbuf; skip_commented lexbuf } 

  | eof 
      { failwith (Format.sprintf "Unterminated comment") }

  (* Ignore characters in comments *)
  | _ { skip_commented lexbuf }


(* Parse until end of line and otherwise discard characters *)
and comment = parse 

  (* Annotation *)
  | "%" (id as p) 
      { match p with 

        (* Ignore rest of line and return token *)
        | "MAIN" -> return_at_eol MAIN lexbuf

        (* Return token, continue with rest of line *)
        | "PROPERTY" -> PROPERTY

        (* Warn and ignore rest of line *)
        | _ -> (Format.printf "Warninng: unknown annotation %s skipped@." p; 
	        skip_to_eol lexbuf ) }

  (* Count new line and resume *)
  | newline { Lexing.new_line lexbuf; token lexbuf } 

  (* Ignore characters *)
  | _ { skip_to_eol lexbuf }

and skip_to_eol = parse

  (* Count new line and resume *)
  | newline { Lexing.new_line lexbuf; token lexbuf } 

  (* Line ends at end of file *)
  | eof { EOF }

  (* Ignore characters *)
  | _ { skip_to_eol lexbuf }


and return_at_eol t = parse

  (* Count new line and resume *)
  | newline { Lexing.new_line lexbuf; t } 

  (* Line ends at end of file *)
  | eof { t }

  (* Ignore characters *)
  | _ { return_at_eol t lexbuf }


{

  let main = 
    

    let rec aux ppf lexbuf =

      let token = token lexbuf in

      Format.fprintf 
        ppf 
        "%a %a" 
        pp_print_position lexbuf.Lexing.lex_start_p
        pp_print_token token;

      if token = EOF then () else
        
        (Format.fprintf ppf "@,";
         aux ppf lexbuf)
         
    in
      
    let in_ch = 
      
      if Array.length Sys.argv > 1 then 
        
        open_in Sys.argv.(1)

      else

        stdin

    in

    let lexbuf = Lexing.from_channel in_ch in

    Format.printf "@[<v>%t@]@." (function ppf -> aux ppf lexbuf)

}
