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
  open SExprParser

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "id", ID;
	"unsat", UNSAT;
	"sat", SAT;
	"unknown", UNKNOWN;
	"core", CORE;
        "ids", IDS;
	"unsatisfied", UNSATISFIED;
        "assertion", ASSERTION;
      ]
	       
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
}

let newline = '\n'
let space = [' ' '\t' '\r']
let digit = ['0' - '9']
let integer = digit+
let ident = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '@' '$' '#' '%' '!' '.' '^' '~' '\' '[' '\' ']']

rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | integer as i
      { INT (int_of_string i) }
  | ident as id
      {
        try Hashtbl.find keywords other
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
  | eof 
      { EOF }
  | _ as c
      { raise (Lexical_error ("illegal character: " ^ String.make 1 c)) }
