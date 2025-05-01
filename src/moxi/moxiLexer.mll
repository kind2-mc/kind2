(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

{
  module P = MoxiParser

  exception Unexpected_Char of char

  exception Unexpected_EOF

  let buffer = Buffer.create 1024

  (* Create and populate a reserved word hashtable *)
  let mk_hashtbl words =
    let tbl =
      Hashtbl.create (List.length words)
    in
    words |> List.iter (fun (k, v) -> Hashtbl.add tbl k v) ;
    tbl

  let reserved_word_table = mk_hashtbl [
    "_", P.UNDERSCORE ;
    "as", P.AS ;
    "define-system", P.DEFINE_SYSTEM ;
    "check-system", P.CHECK_SYSTEM ;
    "set-logic", P.SET_LOGIC ;
    "true", P.TRUE ;
    "false", P.FALSE ;
    "let", P.LET ;
  ]
}

let whitespace = ['\t' ' ']

let newline = '\r' | '\n' | "\r\n"

let white_space_char = ['\t' '\r' '\n' ' ']

let printable_char = [' '-'~'] | ['\x80'-'\xFF']

let digit = ['0'-'9']

let letter = ['A'-'Z' 'a'-'z']

let numeral = '0' | ['1'-'9']['0'-'9']*

let decimal = numeral '.' '0'* numeral

let hexadecimal = "#x" (digit | ['A'-'F' 'a'-'f'])+

let binary = "#b" ['0'-'1']+

let symbol_char =
  ['~' '!' '@' '$' '%' '^' '&' '*' '_' '-' '+' '=' '<' '>' '.' '?' '/']

let simple_symbol = (letter | symbol_char) (letter | digit | symbol_char)*

rule token = parse
  (* Comment *)
  | ';' { skip_to_eol lexbuf }

  (* Numeric literals *)
  | numeral as n { P.NUMERAL_LIT (Numeral.of_string n) }

  | decimal as d { P.DECIMAL_LIT (Decimal.of_string d) }

  | hexadecimal as h { P.BITVECTOR_LIT (Bitvector.bitvector_of_string h) }

  | binary as b { P.BITVECTOR_LIT (Bitvector.bitvector_of_string b) }

  (* Keywords *)
  | ":input"        { P.INPUT_KW }
  | ":output"       { P.OUTPUT_KW }
  | ":local"        { P.LOCAL_KW }

  | ":init"         { P.INIT_KW }
  | ":trans"        { P.TRANS_KW }
  | ":inv"          { P.INV_KW }

  | ":subsys"       { P.SUBSYS_KW }

  | ":assumption"   { P.ASSUMPTION_KW }
  | ":reachable"    { P.REACHABLE_KW }
  | ":query"        { P.QUERY_KW }

  (* Quoted symbol *)
  | '|'              { 
    Buffer.clear buffer;
    let sym = quoted_symbol lexbuf in
    P.QUOTED_SYMBOL (HString.mk_hstring sym)
  }

  | simple_symbol as s
  {
    try
      Hashtbl.find reserved_word_table s
    with Not_found ->
      P.SIMPLE_SYMBOL (HString.mk_hstring s)
  }

  | '('            { P.LPAREN }
  | ')'            { P.RPAREN }
  | '\''           { P.APOSTROPHE }
  | whitespace     { token lexbuf }
  | newline        { Lexing.new_line lexbuf ; token lexbuf }
  | eof            { P.EOF }
  | _ as c         { raise (Unexpected_Char c) }

and skip_to_eol = parse

  (* Count new line and resume *)
  | newline { Lexing.new_line lexbuf; token lexbuf } 

  (* Line ends at end of file *)
  | eof { token lexbuf }

  (* Ignore characters *)
  | _ { skip_to_eol lexbuf }

and quoted_symbol = parse
  | '\\' as c {
    raise (Unexpected_Char c) (* Refine error *)
  }
  | '|' 
  { 
    Buffer.contents buffer
  }
  | (white_space_char | printable_char)* as chars 
  { 
    Buffer.add_string buffer chars; quoted_symbol lexbuf
  }
  | _ as c { 
    raise (Unexpected_Char c) (* Refine error *)
  }