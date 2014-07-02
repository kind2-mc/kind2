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

  let parse_failure pos what =
    (* Removed for menhir *)
    (* let pos = symbol_start_pos () in *)
    let msg =
      Printf.sprintf "SExprParser: failed to parse line %d char %d: %s"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol) what in
    failwith msg
%}

%token <HString.t> STRING
%token LPAREN RPAREN HASH_SEMI EOF

%start sexp
%type <HStringSExpr.t> sexp

%start sexp_opt
%type <HStringSExpr.t option> sexp_opt

%start sexps
%type <HStringSExpr.t list> sexps

%start rev_sexps
%type <HStringSExpr.t list> rev_sexps

%%

sexp:
| sexp_comments sexp_but_no_comment { $2 }
| sexp_but_no_comment { $1 }

sexp_but_no_comment
  : STRING { HStringSExpr.Atom $1 }
  | LPAREN RPAREN { HStringSExpr.List [] }
  | LPAREN rev_sexps_aux RPAREN { HStringSExpr.List (List.rev $2) }
  | error { parse_failure $startpos "sexp" }

sexp_comment
  : HASH_SEMI sexp_but_no_comment { () }
  | HASH_SEMI sexp_comments sexp_but_no_comment { () }

sexp_comments
  : sexp_comment { () }
  | sexp_comments sexp_comment { () }

sexp_opt
  : sexp_but_no_comment { Some $1 }
  | sexp_comments sexp_but_no_comment { Some $2 }
  | EOF { None }
  | sexp_comments EOF { None }

rev_sexps_aux
  : sexp_but_no_comment { [$1] }
  | sexp_comment { [] }
  | rev_sexps_aux sexp_but_no_comment { $2 :: $1 }
  | rev_sexps_aux sexp_comment { $1 }

rev_sexps
  : rev_sexps_aux EOF { $1 }
  | EOF { [] }

sexps
  : rev_sexps_aux EOF { List.rev $1 }
  | EOF { [] }

(* 
   Local Variables:
   indent-tabs-mode: nil
   End: 
*)

