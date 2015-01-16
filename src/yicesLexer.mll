(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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
  open Printf
  open Lexing
  open YicesParser

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "id", ID;
	"unsat", UNSAT;
	"sat", SAT;
	"unknown", UNKNOWN;
	"core", CORE;
        "ids:", IDS;
	(* "unsatisfied", UNSATISFIED; *)
        (* "assertion", ASSERTION; *)
        "Error", ERROR;
        "error", ERROR;
        YicesResponse.success, SUCCESS;
        YicesResponse.custom, CUSTOM;
      ]

  let string_buf = Buffer.create 1024
	       
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
}


let lf = '\010'
let lf_cr = ['\010' '\013']
let dos_newline = "\013\010"
let blank = [' ' '\009' '\012']
let newline = '\n'
let space = [' ' '\t' '\r' '\009' '\012']
let digit = ['0' - '9']
let integer = ('-')? digit+
let ident = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '@' '$' '#' '%' '!' '.' '^' '~' '\\' '['  ']' '-' ':' ]+
let line = [^ '\n']*
let ratio = integer+ '/' integer+
                
rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | integer as i
      { INT (int_of_string i) }
  | ratio as r
      { DECIMAL (Decimal.of_num (Num.num_of_string r)) }
  | ident as id
      { try
          let k = Hashtbl.find keywords id in
          match k with
          | CUSTOM -> Buffer.clear string_buf; custom lexbuf
          | _ -> k
	with Not_found -> IDENT id
      }
  
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | ":"
      { COLON }
  | "="
      { EQ }
  | "-" | "+" | "*" | "/" as op
      { IDENT (String.make 1 op) }
  | eof
      { EOF }
  (* | line as l *)
  (*     { LINE l } *)
  | _ as c
      { failwith ("YicesLexer: illegal character: " ^ String.make 1 c) }


and error_msg = parse
 | newline 
     { newline lexbuf; Buffer.add_char string_buf '\n'; error_msg lexbuf }
 | eof
     { ERROR_MSG (Buffer.contents string_buf) }
 | _ as c
     { Buffer.add_char string_buf c; error_msg lexbuf }


and custom = parse
 | ident as id
     { if id = YicesResponse.success then CUSTOM_RESP (Buffer.contents string_buf)
       else (Buffer.add_string string_buf id; custom lexbuf) }
 | newline 
     { newline lexbuf; Buffer.add_char string_buf '\n'; custom lexbuf }
 | eof
     { EOF }
 | _ as c
     { Buffer.add_char string_buf c; custom lexbuf }
