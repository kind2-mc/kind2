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

  (* Recoginized tokens *)
  type token =

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


  (* Pretty-print a position *)
  let pp_print_position ppf { Lexing.pos_fname; Lexing.pos_lnum; Lexing.pos_bol; Lexing.pos_cnum } =
    Format.fprintf 
      ppf
      "line %d, column %d"
      pos_lnum
      (pos_cnum - pos_bol)

  (* Create and populate a hashtable *)
  let mk_hashtbl size init =
    let tbl = Hashtbl.create size in
    List.iter
      (function (k, v) -> Hashtbl.add tbl k v)
      init;
    tbl
     
  (* Use hash tables instead of rule matches to keep numer of transition of lexer small *)

  (* Hashtable of annotations *)
  let annotation_table = 
    mk_hashtbl 
      3
      [("PROPERTY", PROPERTY);
       ("MAIN", MAIN)]
    
    
  (* Hashtable of keywords *)
  let keyword_table = 
    mk_hashtbl 
      43
      [
	
	(* Types *)
	("type", TYPE);
	("int", INT);
	("real", REAL);
	("bool", BOOL);
	("subrange", SUBRANGE);
	("of", OF);

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

    (* Hashtable of annotations *)
    let annotation_table = 
      mk_hashtbl 
	3
	[("PROPERTY", PROPERTY);
	 ("MAIN", MAIN)]

      
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

(* Toplevel function *)
rule token = parse

  (* Annotation *)
  | "--%" (id as p) 
      { try Hashtbl.find annotation_table p with 
	| Not_found -> 
	  (Format.printf "Warninng: unknown annotation %s skipped@." p; 
	   skip_to_eol lexbuf ) }

  (* Comment until end of line *)
  | "--" { skip_to_eol lexbuf }

  (* Multi-line comment *)
  |  "/*" { skip_commented lexbuf }

  (* Terminal symbol *)
  | ';' { SEMICOLON }
  | '=' { EQUALS }
  | ':' { COLON }
  | ',' { COMMA }
  | '[' { LSQBRACKET }
  | ']' { RSQBRACKET }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '.' { DOT }

  (* Decimal or numeral *)
  | decimal as p { DECIMAL p }
  | numeral as p { NUMERAL p } 

  (* Symbol or keyword *)
  | id as p 
      { try Hashtbl.find keyword_table p with 
	| Not_found -> (SYM p) }

  | printable+ as p 
      { try Hashtbl.find keyword_table p with 
	| Not_found -> failwith (Format.sprintf "Unknown operator %s" p) }

  (* Whitespace *)
  | whitespace { token lexbuf }

  (* Newline *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }

  (* End of file *)
  | eof { Format.printf "End of file %a" pp_print_position lexbuf.Lexing.lex_curr_p; EOF }



(* Parse until end of comment, count newlines and otherwise discard characters *)
and skip_commented = parse 

  (* End of comment *)
  | "*/" { token lexbuf } 

  (* Count new line *)
  | '\n' { Lexing.new_line lexbuf; skip_commented lexbuf } 

  | eof 
      { failwith (Format.sprintf "Unterminated comment") }

  (* Ignore characters in comments *)
  | _ { skip_commented lexbuf }


(* Parse until end of line and otherwise discard characters *)
and skip_to_eol = parse 

  (* Count new line and resume *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf } 

  (* Line ends at end of file *)
  | eof { EOF }

  (* Ignore characters *)
  | _ { skip_to_eol lexbuf }

