%{
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

(* Parser for S-expressions
   
   Code lightly adapted from the OCaml sexplib, which is part of the
   ocaml-core alternative standard library for OCaml.

   Most of the sexplib in the ocaml-core library was written by:
   
   Markus Mottl          <markus.mottl@gmail.com>
   
   This work in turn is derived from the library "Tywith", version
   0.45.  The library "Tywith" was written and is distributed by:
   
   Martin Sandin         <msandin@hotmail.com>

*)

  (** Parser: Grammar Specification for Parsing S-expressions *)

  open Lexing

  let parse_failure what =
    let pos = symbol_start_pos () in
    let msg =
      Printf.sprintf "Sexplib.Parser: failed to parse line %d char %d: %s"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol) what in
    failwith msg
%}

%token <HString.t> STRING
%token LPAREN RPAREN SEXP_COMMENT EOF

%start sexp
%type <HStringSExpr.t> sexp

%start sexp_opt
%type <HStringSExpr.t option> sexp_opt

%start sexps
%type <HStringSExpr.t list> sexps

%start rev_sexps
%type <HStringSExpr.t list> rev_sexps

%%

sexp
  : STRING { HStringSExpr.Atom $1 }
  | LPAREN RPAREN { HStringSExpr.List [] }
  | LPAREN rev_sexps_aux RPAREN { HStringSExpr.List (List.rev $2) }
  | EOF { parse_failure "Read EOF, empty sexpr token" }
  | error { parse_failure "sexp" }

sexp_comment
  : SEXP_COMMENT sexp { () }
  | SEXP_COMMENT sexp_comments sexp { () }

sexp_comments
  : sexp_comment { () }
  | sexp_comments sexp_comment { () }

sexp_opt
  : sexp { Some $1 }
  | sexp_comments sexp { Some $2 }
  | EOF { None }

rev_sexps_aux
  : sexp { [$1] }
  | sexp_comment { [] }
  | rev_sexps_aux sexp { $2 :: $1 }
  | rev_sexps_aux sexp_comment { $1 }

rev_sexps
  : rev_sexps_aux { $1 }
  | EOF { [] }

sexps
  : rev_sexps_aux { List.rev $1 }
  | EOF { [] }

%%

(* 
   Local Variables:
   indent-tabs-mode: nil
   End: 
*)

