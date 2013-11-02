%{
(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
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
  | EOF { parse_failure $startpos "Read EOF, empty sexpr token" }
  | error { parse_failure $startpos "sexp" }

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

