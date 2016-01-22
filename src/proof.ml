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
open Format


module HH = HString.HStringHashtbl
module HS = HStringSExpr
module H = HString

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
let s_ascr = HString.mk_hstring ":"
let s_PI = HString.mk_hstring "!"
let s_LAMBDA = HString.mk_hstring "%"
let s_lambda = HString.mk_hstring "\\"
let s_at = HString.mk_hstring "@"

let s_unsat = HString.mk_hstring "unsat"
let s_sat = HString.mk_hstring "sat"
let s_unknown = HString.mk_hstring "unknown"


type lfsc_type = HS.t
type lfsc_term = HS.t

let ty_formula = HS.Atom s_formula
let ty_term ty = HS.(List [Atom s_term; ty])

type lfsc_decl = {
  decl_symb : H.t;
  decl_type : lfsc_type;
}

type lfsc_def = {
  def_symb : H.t;
  def_args : (H.t * lfsc_type) list;
  def_ty : lfsc_type;
  def_body : lfsc_term;
}

type cvc4_proof_context = {
  lfsc_decls : lfsc_decl list;
  lfsc_defs : lfsc_def list;
  fun_defs_args : (H.t * lfsc_type) list HH.t;
}

let mk_empty_proof_context () = {
  lfsc_decls = [];
  lfsc_defs = [];
  fun_defs_args = HH.create 17;
}

type cvc4_proof = {
  proof_context : cvc4_proof_context;
  proof_hyps : lfsc_decl list; 
  proof_type : lfsc_type;
  proof_term : lfsc_type;
}

let mk_empty_proof ctx = {
  proof_context = ctx;
  proof_hyps = [];
  proof_type = HS.List [];
  proof_term = HS.List [];
}

type lambda_kind =
  | Lambda_decl of lfsc_decl
  | Lambda_hyp of lfsc_decl
  | Lambda_def of lfsc_def
  | Lambda_ignore



(**********************************)
(* Printing LFSC terms and proofs *)
(**********************************)

let print_type = HS.pp_print_sexpr_indent 0


let print_term = HS.pp_print_sexpr_indent 0


let print_decl fmt { decl_symb; decl_type } =
  fprintf fmt "@[<hov 1>(declare@ %a@ %a)@]"
    H.pp_print_hstring decl_symb print_type decl_type


let rec print_def_type ty fmt args =
  match args with
  | [] -> print_type fmt ty
  | (_, ty_a) :: rargs ->
    fprintf fmt "@[<hov 0>(! _ %a@ %a)@]" print_type ty_a (print_def_type ty) rargs


let rec print_def_lambdas term fmt args =
  match args with
  | [] -> print_term fmt term
  | (a, _) :: rargs ->
    fprintf fmt "@[<hov 0>(\\ %a@ %a)@]"
      H.pp_print_hstring a (print_def_lambdas term) rargs


let print_def fmt { def_symb; def_args; def_ty; def_body } =
  fprintf fmt "@[<hov 1>(define@ %a@ @[<hov 1>(: @[<hov 0>%a@]@\n%a)@])@]"
    H.pp_print_hstring def_symb
    (print_def_type def_ty) def_args
    (print_def_lambdas def_body) def_args


let print_context fmt { lfsc_decls; lfsc_defs } =
  List.iter (fprintf fmt "%a@." print_decl) (List.rev lfsc_decls);
  fprintf fmt "@.";
  List.iter (fprintf fmt "%a\n@." print_def) (List.rev lfsc_defs);
  fprintf fmt "@."


let rec print_hyps_type ty fmt = function
  | [] -> print_type fmt ty
  | { decl_symb; decl_type } :: rhyps ->
    fprintf fmt "@[<hov 0>(! %a %a@ %a)@]"
      H.pp_print_hstring decl_symb
      print_type decl_type
      (print_hyps_type ty) rhyps


let rec print_proof_term term fmt = function
  | [] -> print_term fmt term
  | { decl_symb } :: rhyps ->
    fprintf fmt "@[<hov 0>(\\ %a@ %a)@]"
      H.pp_print_hstring decl_symb
      (print_proof_term term) rhyps


let print_proof name fmt { proof_context; proof_hyps; proof_type; proof_term } =
  print_context fmt proof_context;
  let hyps = List.rev proof_hyps in
  fprintf fmt "@[<hov 1>(define %s@ @[<hov 1>(: @[<hov 0>%a@]@\n%a)@])@]"
    name
    (print_hyps_type proof_type) hyps
    (print_proof_term proof_term) hyps



(*********************************)
(* Parsing LFSC proofs from CVC4 *)
(*********************************)

let lex_comp h1 h2 =
  String.compare (H.string_of_hstring h1) (H.string_of_hstring h2)

let lex_comp_b (h1, _) (h2, _) = lex_comp h1 h2


let fun_symbol_of_dummy_arg ctx b ty =
  let s = H.string_of_hstring b in
  try
    Scanf.sscanf s "%s@%%%_d" (fun f ->
      let hf = H.mk_hstring f in
      let args = try HH.find ctx.fun_defs_args hf with Not_found -> [] in
      let nargs = (b, ty) :: args |> List.fast_sort lex_comp_b in
      HH.replace ctx.fun_defs_args hf nargs
      );
    true
  with End_of_file | Scanf.Scan_failure _ -> false

let fun_symbol_of_def b =
  let s = H.string_of_hstring b in
  try
    Scanf.sscanf s "%s@%%def" (fun f -> Some (H.mk_hstring f))
  with End_of_file | Scanf.Scan_failure _ -> None


let is_hyp b ty =
  let s = H.string_of_hstring b in
  try Scanf.sscanf s "A%_d" true
  with End_of_file | Scanf.Scan_failure _ -> false

let is_hyp_true = let open HS in function
  | List [Atom th_holds; Atom tt]
    when th_holds == s_th_holds && tt == s_true -> true
  | _ -> false

let rec definition_artifact_rec ctx = let open HS in function
  | List [Atom at; b; t; s] when at == s_at ->
    begin match definition_artifact_rec ctx s with
      | None -> None
      | Some def ->
        (* FIXME some ugly allocations *)
        Some { def with def_body = List [Atom at; b; t; def.def_body ]}
    end

  | List [Atom iff; List [Atom p_app; Atom fdef]; term]
    when iff == s_iff && p_app == s_p_app -> 
    begin match fun_symbol_of_def fdef with
      | None -> None
      | Some f ->
        let targs = try HH.find ctx.fun_defs_args f with Not_found -> [] in
        Some { def_symb = f;
               def_args = targs;
               def_body = term;
               def_ty = ty_formula } 
    end
  | List [Atom eq; ty; Atom fdef; term] when eq == s_eq -> 
    begin match fun_symbol_of_def fdef with
      | None -> None
      | Some f ->
        let targs = try HH.find ctx.fun_defs_args f with Not_found -> [] in
        Some { def_symb = f;
               def_args = targs;
               def_body = term;
               def_ty = ty_term ty } 
    end
  | _ -> None


let definition_artifact ctx = let open HS in function
    | List [Atom th_holds; d] when th_holds == s_th_holds ->
      definition_artifact_rec ctx d
    | _ -> None


let parse_Lambda_binding ctx b ty =
  if is_hyp b ty then
    if is_hyp_true ty then Lambda_ignore
    else match definition_artifact ctx ty with
      | Some def -> Lambda_def def
      | None -> Lambda_hyp { decl_symb = b; decl_type = ty }
  else if fun_symbol_of_dummy_arg ctx b ty || fun_symbol_of_def b <> None then
    Lambda_ignore
  else Lambda_decl { decl_symb = b; decl_type = ty }


(***********************)
(* Parsing proof terms *)
(***********************)

let rec parse_proof acc = let open HS in function

  | List [Atom lam; Atom b; ty; r] when lam == s_LAMBDA ->

    let acc = match parse_Lambda_binding acc.proof_context b ty with
      | Lambda_decl _ | Lambda_def _ | Lambda_ignore -> acc
      | Lambda_hyp h -> { acc with proof_hyps = h :: acc.proof_hyps }
    in
    parse_proof acc r

  | List [Atom ascr; ty; pterm] when ascr = s_ascr ->

    { acc with proof_type = ty; proof_term = pterm }

  | _ -> assert false


let parse_proof_check ctx = let open HS in function
  | List [Atom check; proof] when check == s_check ->
    parse_proof (mk_empty_proof ctx) proof
  | _ -> assert false


(******************************************)
(* Parsing context from dummy lfsc proofs *)
(******************************************)

let rec parse_context ctx = let open HS in function

  | List [Atom lam; Atom b; ty; r] when lam == s_LAMBDA ->

    let ctx = match parse_Lambda_binding ctx b ty with
      | Lambda_decl d -> { ctx with lfsc_decls = d :: ctx.lfsc_decls }
      | Lambda_def d -> { ctx with lfsc_defs = d :: ctx.lfsc_defs }
      | Lambda_hyp _ | Lambda_ignore -> ctx
    in
    parse_context ctx r

  | List [Atom ascr; _; _] when ascr = s_ascr -> ctx

  | _ -> assert false


let parse_context_dummy = let open HS in function
  | List [Atom check; dummy] when check == s_check ->
    parse_context (mk_empty_proof_context ()) dummy
  | _ -> assert false



let context_from_chan in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in
  let open HS in
  
  match sexps with
  
    | [Atom a] when a == s_sat || a == s_unknown ->
      failwith (sprintf "Certificate cannot be checked by smt solver (%s)@."
                  (H.string_of_hstring a))

    | [Atom a] ->
      failwith (sprintf "No proofs, instead got:\n%s@." (H.string_of_hstring a))

    | [Atom u; dummy_proof] when u == s_unsat ->

      parse_context_dummy dummy_proof
      
    | _ -> assert false


let proof_from_chan ctx in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in
  let open HS in
  
  match sexps with
  
    | [Atom a] when a == s_sat || a == s_unknown ->
      failwith (sprintf "Certificate cannot be checked by smt solver (%s)@."
                  (H.string_of_hstring a))

    | [Atom a] ->
      failwith (sprintf "No proofs, instead got:\n%s@." (H.string_of_hstring a))

    | [Atom u; proof] when u == s_unsat ->

      parse_proof_check ctx proof
      
    | _ -> assert false






type smtlib2_certif = {
  dummy_trace_file: string;
  base: string;
  induction: string;
  implication: string;
}





let cvc4_proof_cmd = "ssh kind \"~/CVC4_proofs/builds/x86_64-unknown-linux-gnu/production-proof/bin/cvc4 --lang smt2 --dump-proof\" <"



(* TODO this is just for testing *)
let test () =

  (* pp_set_margin std_formatter max_int; *)

  let cmd = cvc4_proof_cmd ^ " production_cell.lus_certificates/lfsc_defs.smt2" in
  let ic, oc = Unix.open_process cmd in
  let ctx = context_from_chan ic in
  printf "Parsed context:\n%a@." print_context ctx;
  ignore(Unix.close_process (ic, oc));

  let cmd = cvc4_proof_cmd ^ " production_cell.lus_certificates/induction.smt2" in
  let ic, oc = Unix.open_process cmd in
  let proof = proof_from_chan ctx ic in
  printf "Parsed proof:\n%a@." (print_proof "induction") proof;
  ignore(Unix.close_process (ic, oc));

  
  exit 0



let _ = test ()
