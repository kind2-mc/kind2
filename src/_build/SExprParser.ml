type token =
  | STRING of (HString.t)
  | LPAREN
  | RPAREN
  | SEXP_COMMENT
  | EOF

open Parsing;;
let _ = parse_error;;
# 2 "SExprParser.mly"
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

  let parse_failure what =
    let pos = symbol_start_pos () in
    let msg =
      Printf.sprintf "Sexplib.Parser: failed to parse line %d char %d: %s"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol) what in
    failwith msg
# 68 "SExprParser.ml"
let yytransl_const = [|
  258 (* LPAREN *);
  259 (* RPAREN *);
  260 (* SEXP_COMMENT *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* STRING *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\006\000\006\000\007\000\
\007\000\002\000\002\000\002\000\005\000\005\000\005\000\005\000\
\004\000\004\000\003\000\003\000\000\000\000\000\000\000\000\000"

let yylen = "\002\000\
\001\000\002\000\003\000\001\000\001\000\002\000\003\000\001\000\
\002\000\001\000\002\000\001\000\001\000\001\000\002\000\002\000\
\001\000\001\000\001\000\001\000\002\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\005\000\001\000\000\000\
\004\000\021\000\000\000\004\000\010\000\022\000\008\000\000\000\
\004\000\013\000\023\000\000\000\014\000\004\000\024\000\000\000\
\002\000\000\000\006\000\000\000\011\000\009\000\015\000\016\000\
\003\000\007\000"

let yydgoto = "\005\000\
\018\000\014\000\019\000\023\000\020\000\021\000\016\000"

let yysindex = "\038\000\
\031\000\011\000\016\000\021\000\000\000\000\000\000\000\001\000\
\000\000\000\000\026\000\000\000\000\000\000\000\000\000\026\000\
\000\000\000\000\000\000\026\000\000\000\000\000\000\000\026\000\
\000\000\006\000\000\000\026\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\002\000\000\000\000\000\000\000\003\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\008\000\000\000\000\000\000\000\252\255\027\000\250\255"

let yytablesize = 289
let yytable = "\024\000\
\009\000\019\000\017\000\026\000\028\000\009\000\000\000\000\000\
\010\000\013\000\012\000\000\000\000\000\000\000\000\000\017\000\
\000\000\000\000\027\000\000\000\022\000\000\000\000\000\029\000\
\000\000\009\000\000\000\031\000\015\000\000\000\009\000\031\000\
\000\000\031\000\000\000\034\000\000\000\015\000\001\000\002\000\
\003\000\004\000\030\000\000\000\000\000\000\000\032\000\000\000\
\000\000\000\000\032\000\000\000\032\000\000\000\030\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\006\000\007\000\008\000\025\000\011\000\006\000\007\000\008\000\
\033\000\011\000\006\000\007\000\008\000\000\000\011\000\006\000\
\007\000\008\000\000\000\011\000\006\000\007\000\008\000\000\000\
\011\000\006\000\007\000\008\000\000\000\011\000\006\000\007\000\
\008\000"

let yycheck = "\004\000\
\000\000\000\000\000\000\008\000\011\000\000\000\255\255\255\255\
\001\000\002\000\000\000\255\255\255\255\255\255\255\255\000\000\
\255\255\255\255\011\000\255\255\000\000\255\255\255\255\016\000\
\255\255\000\000\255\255\020\000\002\000\255\255\000\000\024\000\
\255\255\026\000\255\255\028\000\255\255\011\000\001\000\002\000\
\003\000\004\000\016\000\255\255\255\255\255\255\020\000\255\255\
\255\255\255\255\024\000\255\255\026\000\255\255\028\000\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\000\001\001\001\002\001\003\001\004\001\000\001\001\001\002\001\
\003\001\004\001\000\001\001\001\002\001\255\255\004\001\000\001\
\001\001\002\001\255\255\004\001\000\001\001\001\002\001\255\255\
\004\001\000\001\001\001\002\001\255\255\004\001\000\001\001\001\
\002\001"

let yynames_const = "\
  LPAREN\000\
  RPAREN\000\
  SEXP_COMMENT\000\
  EOF\000\
  "

let yynames_block = "\
  STRING\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : HString.t) in
    Obj.repr(
# 78 "SExprParser.mly"
           ( HStringSExpr.Atom _1 )
# 214 "SExprParser.ml"
               : HStringSExpr.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "SExprParser.mly"
                  ( HStringSExpr.List [] )
# 220 "SExprParser.ml"
               : HStringSExpr.t))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'rev_sexps_aux) in
    Obj.repr(
# 80 "SExprParser.mly"
                                ( HStringSExpr.List (List.rev _2) )
# 227 "SExprParser.ml"
               : HStringSExpr.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "SExprParser.mly"
        ( parse_failure "Read EOF, empty sexpr token" )
# 233 "SExprParser.ml"
               : HStringSExpr.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "SExprParser.mly"
          ( parse_failure "sexp" )
# 239 "SExprParser.ml"
               : HStringSExpr.t))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : HStringSExpr.t) in
    Obj.repr(
# 85 "SExprParser.mly"
                      ( () )
# 246 "SExprParser.ml"
               : 'sexp_comment))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'sexp_comments) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : HStringSExpr.t) in
    Obj.repr(
# 86 "SExprParser.mly"
                                    ( () )
# 254 "SExprParser.ml"
               : 'sexp_comment))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sexp_comment) in
    Obj.repr(
# 89 "SExprParser.mly"
                 ( () )
# 261 "SExprParser.ml"
               : 'sexp_comments))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sexp_comments) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'sexp_comment) in
    Obj.repr(
# 90 "SExprParser.mly"
                               ( () )
# 269 "SExprParser.ml"
               : 'sexp_comments))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : HStringSExpr.t) in
    Obj.repr(
# 93 "SExprParser.mly"
         ( Some _1 )
# 276 "SExprParser.ml"
               : HStringSExpr.t option))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sexp_comments) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : HStringSExpr.t) in
    Obj.repr(
# 94 "SExprParser.mly"
                       ( Some _2 )
# 284 "SExprParser.ml"
               : HStringSExpr.t option))
; (fun __caml_parser_env ->
    Obj.repr(
# 95 "SExprParser.mly"
        ( None )
# 290 "SExprParser.ml"
               : HStringSExpr.t option))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : HStringSExpr.t) in
    Obj.repr(
# 98 "SExprParser.mly"
         ( [_1] )
# 297 "SExprParser.ml"
               : 'rev_sexps_aux))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sexp_comment) in
    Obj.repr(
# 99 "SExprParser.mly"
                 ( [] )
# 304 "SExprParser.ml"
               : 'rev_sexps_aux))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'rev_sexps_aux) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : HStringSExpr.t) in
    Obj.repr(
# 100 "SExprParser.mly"
                       ( _2 :: _1 )
# 312 "SExprParser.ml"
               : 'rev_sexps_aux))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'rev_sexps_aux) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'sexp_comment) in
    Obj.repr(
# 101 "SExprParser.mly"
                               ( _1 )
# 320 "SExprParser.ml"
               : 'rev_sexps_aux))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'rev_sexps_aux) in
    Obj.repr(
# 104 "SExprParser.mly"
                  ( _1 )
# 327 "SExprParser.ml"
               : HStringSExpr.t list))
; (fun __caml_parser_env ->
    Obj.repr(
# 105 "SExprParser.mly"
        ( [] )
# 333 "SExprParser.ml"
               : HStringSExpr.t list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'rev_sexps_aux) in
    Obj.repr(
# 108 "SExprParser.mly"
                  ( List.rev _1 )
# 340 "SExprParser.ml"
               : HStringSExpr.t list))
; (fun __caml_parser_env ->
    Obj.repr(
# 109 "SExprParser.mly"
        ( [] )
# 346 "SExprParser.ml"
               : HStringSExpr.t list))
(* Entry sexp *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry sexp_opt *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry sexps *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry rev_sexps *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let sexp (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : HStringSExpr.t)
let sexp_opt (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : HStringSExpr.t option)
let sexps (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 3 lexfun lexbuf : HStringSExpr.t list)
let rev_sexps (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 4 lexfun lexbuf : HStringSExpr.t list)
;;
# 112 "SExprParser.mly"

(* 
   Local Variables:
   indent-tabs-mode: nil
   End: 
*)

# 391 "SExprParser.ml"
