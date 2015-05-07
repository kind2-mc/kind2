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

open Lib

module HH = HString.HStringHashtbl
module HS = HStringSExpr
module D = GenericSMTLIBDriver
(* module TS = TransSys *)
module SVMap = StateVar.StateVarMap
module SVH = StateVar.StateVarHashtbl

module Conv = SMTExpr.Converter(D)
let conv = D.smtlib_string_sexpr_conv
let conv_type_of_sexpr = conv.D.type_of_sexpr
let conv_term_of_sexpr = conv.D.expr_of_string_sexpr conv

(************************)
(* Useful hconsed names *)
(************************)

let s_assert = HString.mk_hstring "assert"
let s_leq = HString.mk_hstring "<="

(* LFSC symbols *)

let s_and = HString.mk_hstring "and"
let s_or = HString.mk_hstring "or"
let s_not = HString.mk_hstring "not"
let s_impl = HString.mk_hstring "impl"
let s_iff = HString.mk_hstring "iff"
let s_ifte = HString.mk_hstring "ifte"
let s_xor = HString.mk_hstring "xor"
let s_true = HString.mk_hstring "true"
let s_false = HString.mk_hstring "false"

let s_formula = HString.mk_hstring "formula"
let s_th_holds = HString.mk_hstring "th_holds"
let s_holds = HString.mk_hstring "holds"

let s_sort = HString.mk_hstring "sort"
let s_term = HString.mk_hstring "term"
let s_let = HString.mk_hstring "let"
let s_flet = HString.mk_hstring "flet"
let s_eq = HString.mk_hstring "="

let s_Bool = HString.mk_hstring "Bool"
let s_p_app = HString.mk_hstring "p_app"
let s_cln = HString.mk_hstring "cln"

let s_check = HString.mk_hstring "check"
let s_proof = HString.mk_hstring ":"
let s_PI = HString.mk_hstring "!"
let s_lambda = HString.mk_hstring "%"
(* let s_lambda = HString.mk_hstring "\\" *)



let smt2_of_lfsc t =
  try
    (match t with
     | _ when t == s_iff -> "="
     | _ when t == s_ifte -> "ite"
     | _ when t == s_flet -> "let"
     | _ when t == s_impl -> "=>"
     | _ -> raise Exit)
    |> HString.mk_hstring
  with Exit -> t


let rec parse_term = function
  
  | HS.Atom t -> HS.Atom (smt2_of_lfsc t)

  (* predicate application *)
  | HS.List (HS.Atom p_app :: l) when p_app == s_p_app ->
    HS.List (List.map parse_term l)

  (* other *)
  | HS.List l -> HS.List (List.map parse_term l)


type pty = Decl of HS.t | Assu of HS.t
    
let parse_type = function

  | HS.Atom _ as ty -> Decl ty
  | HS.List [HS.Atom t; HS.Atom _ as ty] when t == s_term -> Decl ty

  | HS.List [HS.Atom h; t] when h == s_th_holds || h == s_holds ->

    Assu (parse_term t)

  | _ -> assert false



let rec parse_proof (symbols, assump) = function

  (* Only look at declarations *)
  | HS.List [HS.Atom l; HS.Atom s; ty; r] when l == s_lambda ->

    begin match parse_type ty with
      | Decl t -> parse_proof ((s,t) :: symbols, assump) r
      | Assu p -> parse_proof (symbols, p :: assump) r
    end
    
  (* Stop at actual proof term of empty clause *)
  | HS.List [HS.Atom p; HS.List [HS.Atom holds; HS.Atom cln] ; _]
    when p == s_proof && holds == s_holds && cln == s_cln ->

    symbols, assump
    
  | _ -> assert false



(* Parse a list of s-expressions and extract symbol definitions and
   assumptions *)
let rec parse_file acc = function

  (* Only look at check *)
  | HS.List [HS.Atom ch; proof] :: r when ch == s_check ->

    parse_file (parse_proof ([], []) proof :: acc) r
    
  (* Ignore others *)
  | _ :: r -> parse_file acc r

  | [] -> acc


let extract in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  List.iter (fun (_, assumptions) ->

      let formula = HS.List (HS.Atom s_and :: assumptions) in

      Format.printf "%a@." HS.pp_print_sexpr formula

    ) (parse_file [] sexps)



let () =

  (* open file given as argument or read from stdin *)
  let in_ch = try open_in Sys.argv.(1) with Invalid_argument _ -> stdin in

  extract in_ch;

  (* Close channel *)
  close_in in_ch

  
(* 
   Local Variables:
   compile-command: "make -C .. lfsc-extractor"
   indent-tabs-mode: nil
   End: 
*)
