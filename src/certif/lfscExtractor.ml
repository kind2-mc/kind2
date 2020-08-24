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
let s_apply = HString.mk_hstring "apply"
let s_cln = HString.mk_hstring "cln"

let s_check = HString.mk_hstring "check"
let s_proof = HString.mk_hstring ":"
let s_PI = HString.mk_hstring "!"
let s_lambda = HString.mk_hstring "%"
(* let s_lambda = HString.mk_hstring "\\" *)


(* SMTLIB2 symbols *)

let s_assert = HString.mk_hstring "assert"
let s_push = HString.mk_hstring "push"
let s_pop = HString.mk_hstring "pop"
let s_setinfo = HString.mk_hstring "set-info"
let s_checksat = HString.mk_hstring "check-sat"
let s_exit = HString.mk_hstring "exit"
let s_leq = HString.mk_hstring "<="


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


let rec uncurry = function
  | HS.List (HS.List f :: args) ->
    HS.List (List.map uncurry (f @ args))
  | e -> e


let rec parse_term = function
  
  | HS.Atom t -> HS.Atom (smt2_of_lfsc t)

  (* remove type argument of equality *)
  | HS.List (HS.Atom eq :: _ :: l) when eq == s_eq ->
    HS.List (HS.Atom eq :: List.map parse_term l)
  
  (* predicate application *)
  | HS.List (HS.Atom p_app :: l) when p_app == s_p_app ->
    begin match l with
      | [t] -> parse_term t
      | _ -> HS.List (List.map parse_term l)
    end
    |> uncurry

  (* function application *)
  | HS.List (HS.Atom apply :: _ :: _ :: l) when apply == s_apply ->
    begin match l with
      | [t] -> parse_term t
      | _ -> HS.List (List.map parse_term l)
    end
    |> uncurry
    
  (* other *)
  | HS.List l -> HS.List (List.map parse_term l)


type pty = Decl of HS.t | Assu of HS.t
    
let parse_type = function

  | HS.Atom _ as ty -> Decl ty
  | HS.List (HS.Atom t :: ty) when t == s_term ->
    begin match ty with
      | [HS.Atom _ as ty] -> Decl ty
      | _ -> Decl (HS.List ty)
    end

  | HS.List [HS.Atom h; t] when h == s_th_holds || h == s_holds ->

    Assu (parse_term t)

  | e ->
    Format.eprintf "Failed on %a@." HS.pp_print_sexpr e;
    assert false



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

    List.rev symbols, List.rev assump
    
  | _ -> assert false



(* Parse a list of s-expressions and extract symbol definitions and
   assumptions *)
let rec parse_file acc = function

  (* Only look at check *)
  | HS.List [HS.Atom ch; proof] :: r when ch == s_check ->

    parse_file (parse_proof ([], []) proof :: acc) r
    
  (* Ignore others *)
  | _ :: r -> parse_file acc r

  (* stop on end of file *)
  | [] -> List.rev acc


let extract_from_proof in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  List.map (fun (_, assumptions) ->

      match assumptions with
        | [] -> HS.Atom s_true
        | [a] -> a
        | _ -> HS.List (HS.Atom s_and :: assumptions)

    ) (parse_file [] sexps)



let rec parse_smt2 acc (others, asserts) = function

  (* Fail on push / pop *)
  | HS.List (HS.Atom p :: _) :: _
    when p == s_push || p == s_pop  ->
    failwith ((HString.string_of_hstring p)^" not supported for cvc4 proofs")

  (* stop on exit or end of file *)
  | [] ->
    List.rev others, List.rev acc

  | HS.List (HS.Atom p :: _) :: _ when p == s_exit  ->
    List.rev others, List.rev acc

  (* ignore meta-information *)
  | HS.List (HS.Atom i :: _) :: r when i == s_setinfo ->
    parse_smt2 acc (others, asserts) r
      
  (* save assertion stack on check-sat *)
  | HS.List (HS.Atom c :: _) :: r when c == s_checksat ->
    parse_smt2 (List.rev asserts :: acc) (others, asserts) r

  (* identify asserts ... *)
  | HS.List [HS.Atom a; f] :: r when a == s_assert ->
    parse_smt2 acc (others, f :: asserts) r
    
  (* ... from the rest *)
  | se :: r ->
    parse_smt2 acc (se :: others, asserts) r


let extract_from_smt2 in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  let others, assert_st = parse_smt2 [] ([],[]) sexps in

  let formulas =
    List.map (fun asserts ->

      match asserts with
        | [] -> HS.Atom s_true
        | [a] -> a
        | _ -> HS.List (HS.Atom s_and :: asserts)

      ) assert_st in

  others, formulas

  
  

let () =

  (* open file given as argument or read from stdin *)
  let in_ch_smt2 = try open_in Sys.argv.(1) with Invalid_argument _ ->
    Format.eprintf "Usage: %s file.smt2 proof.lfsc@." Sys.argv.(0);
    failwith "Give the original smt2 file as first argument"
  in

  (* open file given as argument or read from stdin *)
  let in_ch_lfsc = try open_in Sys.argv.(2) with Invalid_argument _ -> stdin in

  (* Set line width *)
  Format.pp_set_margin Format.std_formatter max_int;

  let context, formulas = extract_from_smt2 in_ch_smt2 in
  let proofs = extract_from_proof in_ch_lfsc in

  (* Output context *)
  List.iter (Format.printf "%a\n" HS.pp_print_sexpr) context;
  Format.printf "@.";

  (* Output equivalences *)
  begin try
      List.iter2 (fun formula proven ->
          let equiv = HS.List [HS.Atom s_not;
                               HS.List [HS.Atom s_eq; formula; proven]] in
          Format.printf "(assert %a)\n\n" HS.pp_print_sexpr equiv;
          Format.printf "(check-sat)\n@.";
        ) formulas proofs;

      Format.printf "(exit)@.";
      
    with Invalid_argument _ ->
      failwith "Not the same number of proofs as check-sats."
  end;
  
  (* Close channels *)
  close_in in_ch_smt2;
  close_in in_ch_lfsc

  
(* 
   Local Variables:
   compile-command: "make -C .. lfsc-extractor"
   indent-tabs-mode: nil
   End: 
*)
