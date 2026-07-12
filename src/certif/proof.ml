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

module Ids = ReservedIds
module JP = JkindParser
module HS = HStringSExpr

(* Hard coded options *)
let global_logic = ref `None
let set_proof_logic l = global_logic := l

(* disable the preprocessor and tell cvc5 to dump proofs *)
let cvc5_proof_args () =
  let args =
    [
      "--lang=smt2";
      "--simplification=none";
      (* Resort to full effort quantifier instantiation techniques instead of
         answering unknown; without it, certificates with quantified
         constraints (e.g. from Lustre maps and sets) are not provable *)
      "--full-saturate-quant";
      "--dump-proofs";
      "--proof-format-mode=cpc";
    ]
  in
  List.rev args

let cvc5_proof_cmd () =
  String.concat " " (Flags.Smt.cvc5_bin () :: cvc5_proof_args ())

let safety_proofname_cpc = "safety_proof.cpc"
let kind_2_proofname_cpc = "kind_2_proof.cpc"
let base_proofname_cpc = "base.cpc"
let induction_proofname_cpc = "induction.cpc"
let implication_proofname_cpc = "implication.cpc"
let frontend_proofname_cpc = "frontend_proof.cpc"
let frontend_base_proofname_cpc = "frontend_base.cpc"
let frontend_induction_proofname_cpc = "frontend_induction.cpc"
let frontend_implication_proofname_cpc = "frontend_implication.cpc"

type cpc_step = HS.t

let pp_cpc_proof fmt pf =
  List.iter (fun s -> HS.pp_print_sexpr fmt s; Format.fprintf fmt "@.") pf

let parse_cpc_from_lexbuf lexbuf =
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in
  let commands =
    match sexps with
    | [HS.List xs] -> xs
    | xs -> xs 
  in
  commands

let cpc_proof_from_chan prefix in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let first_line = input_line in_ch in
  if String.trim first_line <> "unsat"
  then failwith "Expected 'unsat' at beginning of CPC proof";

  let sexps = parse_cpc_from_lexbuf lexbuf in
  let oc = open_out prefix in
  let fmt = Format.formatter_of_out_channel oc in
  List.iter (fun s -> Format.fprintf fmt "%a@." HS.pp_print_sexpr s) sexps;
  close_out oc;
  (* Format.printf "Outputted file: %s@." prefix; *)
  sexps


let s_define = HString.mk_hstring "define"
let s_declare_const = HString.mk_hstring "declare-const"
let s_assume = HString.mk_hstring "assume"
let s_assume_push = HString.mk_hstring "assume-push"
let s_step = HString.mk_hstring "step"

let is_global_name (s : HString.t) : bool =
  let name = HString.string_of_hstring s in
  not (String.length name > 0 && name.[0] = '@')

let is_global_def = function
  | HS.List (HS.Atom kw :: HS.Atom name :: _) ->
      (HString.equal kw (s_define)
      && is_global_name name) 
      || HString.equal kw (s_declare_const)
  | _ -> false


let is_local_def = function
  | HS.List (HS.Atom kw :: HS.Atom name :: _) ->
      HString.equal kw (HString.mk_hstring "define")
      && not (is_global_name name)
  | _ -> false

let normalize_step = function
  | HS.List (HS.Atom kw :: tl)
      when HString.equal kw s_assume ->
        HS.List (HS.Atom s_assume_push :: tl)
  | sexpr -> sexpr


let get_proof_defs (proof : cpc_step list) =
  let rec aux (acc_global_defs, acc_steps) = function
    | sexpr :: tl when is_global_def sexpr ->
        aux (sexpr :: acc_global_defs, acc_steps) tl
    | sexpr :: tl when is_local_def sexpr ->
        aux (acc_global_defs, sexpr :: acc_steps) tl
     | sexpr :: tl ->
        let sexpr = normalize_step sexpr in
        aux (acc_global_defs, sexpr :: acc_steps) tl
    | [] ->
        (List.rev acc_global_defs, List.rev acc_steps)
  in
  aux ([], []) proof


let is_jkind_name (s : HString.t) =
  let n = HString.string_of_hstring s in
  String.starts_with ~prefix: JP.jkind_id n
  || String.starts_with ~prefix:"%f" n

let is_jkind_decl = function
  | HS.List [HS.Atom kw; HS.Atom name; _]
    when HString.equal kw (HString.mk_hstring "declare-const") ->
      is_jkind_name name
  | _ -> false


let factor_jkind_defs (proof : cpc_step list) =
  let rec aux (acc_k2_global_defs) = function
    | sexpr :: tl when sexpr |> is_jkind_decl->
       (acc_k2_global_defs, sexpr :: tl)
    | sexpr :: tl ->
        aux (sexpr :: acc_k2_global_defs) tl
    | [] ->
        (acc_k2_global_defs, [])
  in
  aux ([]) proof

  let is_kind_2_def_name (s : HString.t) =
    let open ReservedIds in
  
    let n = HString.string_of_hstring s in
    let result =
    ((String.starts_with ~prefix: init_uf_string n) && 
    (not (String.starts_with ~prefix: (Ids.init_uf_string ^ "_" ^ JP.jkind_id) n)))
    ||
    ((String.starts_with ~prefix: trans_uf_string n) && 
    (not (String.starts_with ~prefix: (Ids.trans_uf_string ^ "_" ^ JP.jkind_id) n)))

    in

    (* Format.printf "%B :: %s" result n; *)
    result
  let is_kind_2_def = function 
  
  | HS.List (HS.Atom kw :: HS.Atom name :: _)
     when HString.equal kw (HString.mk_hstring "define") ->
      (* Format.printf "CHecking if its a kind 2 def (true-ish) (kw = %a): %a\n"  HString.pp_print_hstring kw HS.pp_print_sexpr step; *)
      is_kind_2_def_name name
  | _ -> 
      (* Format.printf "CHecking if its a kind 2 def (false by struct): %a\n"  HS.pp_print_sexpr step; *)
      false

  let remove_kind_2_defs (proof : cpc_step list) =
  let rec aux (acc) = function
    | sexpr :: tl when sexpr |> is_kind_2_def->
       aux acc tl
    | sexpr :: tl ->
        aux (sexpr :: acc) tl
    | [] ->
        List.rev acc
  in
  aux ([]) proof
let get_first_assm steps= 

 let rec aux = function
    | [] ->
        failwith "Couldn't find the first assume-push"

    | (HS.List (HS.Atom kw :: HS.Atom _ :: assm :: _)):: _    
        when HString.equal kw (s_assume_push) ->
        assm
    | _ :: rest ->
      aux rest
    in
    aux steps
      
      (* failwith (Format.asprintf "Unexpected format of assume-push:  %a"  HS.pp_print_sexpr s)  *)

   
    

let get_last_step_name steps =
  let rec find_last = function
    | [] ->
        failwith "Empty proof: no steps"

    | [HS.List (HS.Atom kw :: HS.Atom id :: _)]
      when HString.equal kw (s_step) ->
        id

    | [sexpr] ->
        failwith ("Last SExpr is not a step: " ^
                  (Format.asprintf "%a" HS.pp_print_sexpr sexpr))

    | _ :: tl ->
        find_last tl
  in
  find_last steps


let generate_cpc_proof dirname smt_file =
  let cmd =
    Printf.sprintf "%s %s" (cvc5_proof_cmd ()) smt_file
  in
  let (in_ch, _, _) =
    Unix.open_process_full cmd (Unix.environment ())
  in
  cpc_proof_from_chan dirname in_ch

  let mk_k_ind_proof_step_kind_2 k = 
    
    let str = "(step k_ind_proof_kind_2 (Invariant I1 T1 PHI1) :rule k-induction 
       :premises (base_proof_kind_2 induction_proof_kind_2) :args (I1 T1 PHI1 " ^ (string_of_int k) ^ "))" in
    HS.List (Lexing.from_string (str) |> parse_cpc_from_lexbuf )


  let mk_k_ind_proof_step_jkind k = 
    let str = "(step k_ind_proof_jkind (Invariant IO TO PHIO) :rule k-induction
       :premises (base_proof_jkind induction_proof_jkind) :args (IO TO PHIO " ^ (string_of_int k) ^ "))" in
    HS.List (Lexing.from_string (str) |> parse_cpc_from_lexbuf )


  let hardcoded_steps = [
    (
      "proof_inv", 
      "(step proof_inv (Invariant I1 T1 P1) :rule invariant-implies
       :premises (k_ind_proof_kind_2 implication_proof_kind_2) :args (I1 T1 PHI1 P1))"
    );
    (
      "proof_obs",
      "(step proof_obs (Invariant IO TO PO) :rule invariant-implies
       :premises (k_ind_proof_jkind implication_proof_jkind) :args (IO TO PHIO PO))"
    );
    (
      "proof_obs_eq",
      "(step proof_obs_eq (Weak_Obs_Eq I1 T1 P1 I2 T2 P2) :rule weak-obs-eq
       :premises (proof_obs) :args (I1 T1 P1 I2 T2 P2 same_inputs))"
    );
    (
      "proof_safe",
      "(step proof_safe (Safe I1 T1 P1) :rule inv-and-obs
       :premises (proof_inv proof_obs_eq) :args (I1 T1 P1 I2 T2 P2))"
    );
  ]
let rec hardoced_lookup step_name = function
  | (step, formula) :: rest -> if (String.equal step step_name) then formula else (hardoced_lookup step_name rest)
  | [] -> "" 

let mk_hardcoded_step step_name = 
  HS.List (Lexing.from_string (hardoced_lookup step_name hardcoded_steps) |> parse_cpc_from_lexbuf )


let mk_step_pop_dyn name last_step_id assm =
  HS.List [
    HS.Atom (HString.mk_hstring "step-pop");
    HS.Atom (HString.mk_hstring name);
    HS.List [
      HS.Atom (HString.mk_hstring "=>");
      assm;
      HS.Atom (HString.mk_hstring "false");
    ];
    HS.Atom (HString.mk_hstring ":rule");
    HS.Atom (HString.mk_hstring "scope");
    HS.Atom (HString.mk_hstring ":premises");
    HS.List [ HS.Atom last_step_id ];
  ]
let pp_print_safety_proof fmt defs base_steps induction_steps implication_steps k =
    Format.fprintf fmt "%a" pp_cpc_proof defs;
    Format.fprintf fmt ";; Base proof\n";
    Format.fprintf fmt "%a" pp_cpc_proof base_steps;
    Format.fprintf fmt ";; base_proof_k2\n";
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_step_pop_dyn "base_proof_kind_2" (get_last_step_name base_steps) (get_first_assm base_steps))] ;
    Format.fprintf fmt ";; Induction proof \n";
    Format.fprintf fmt "%a" pp_cpc_proof induction_steps;
    Format.fprintf fmt ";; induction_proof_k2 \n";
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_step_pop_dyn "induction_proof_kind_2" (get_last_step_name induction_steps) (get_first_assm induction_steps))] ;
    Format.fprintf fmt ";; k_ind_proof\n";
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_k_ind_proof_step_kind_2 k )];
    Format.fprintf fmt ";; implication_proof\n";
    Format.fprintf fmt "%a" pp_cpc_proof implication_steps;
    Format.fprintf fmt ";; impl_rule \n" ;
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_step_pop_dyn "implication_proof_kind_2" (get_last_step_name implication_steps) (get_first_assm implication_steps))]; 
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_hardcoded_step "proof_inv")]


let pp_print_frontend_proof fmt defs base_steps induction_steps implication_steps k =
    Format.fprintf fmt "%a" pp_cpc_proof defs;
    Format.fprintf fmt ";; Base proof (Observer)\n";
    Format.fprintf fmt "%a" pp_cpc_proof base_steps;
    Format.fprintf fmt ";; base_proof_jkind\n";
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_step_pop_dyn "base_proof_jkind" (get_last_step_name base_steps) (get_first_assm base_steps))] ;
    Format.fprintf fmt ";; Induction proof (Observer) \n";
    Format.fprintf fmt "%a" pp_cpc_proof induction_steps;
    Format.fprintf fmt ";; induction_proof_jkind \n";
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_step_pop_dyn "induction_proof_jkind" (get_last_step_name induction_steps) (get_first_assm induction_steps))] ;
    Format.fprintf fmt ";; k_ind_proof\n";
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_k_ind_proof_step_jkind k )];
    Format.fprintf fmt ";; implication_proof (Observer)\n";
    Format.fprintf fmt "%a" pp_cpc_proof implication_steps;
    Format.fprintf fmt ";; impl_rule \n" ;
    Format.fprintf fmt "%a" pp_cpc_proof [(mk_step_pop_dyn "implication_proof_jkind" (get_last_step_name implication_steps) (get_first_assm implication_steps))]


let construct_kind_2_proof dirname base induction implication k = 

  let base_k2 = generate_cpc_proof (Filename.concat dirname base_proofname_cpc) base in
  let induction_k2 = generate_cpc_proof (Filename.concat dirname induction_proofname_cpc) induction in
  let implication_k2 =generate_cpc_proof (Filename.concat dirname implication_proofname_cpc) implication in


  let (defs, base_steps) = get_proof_defs base_k2 in
  let (_, induction_steps) = get_proof_defs induction_k2 in
  let (_, implication_steps) = get_proof_defs implication_k2 in

  let oc = open_out (Filename.concat dirname kind_2_proofname_cpc) in
  let fmt = Format.formatter_of_out_channel oc in
  pp_print_safety_proof fmt defs base_steps induction_steps implication_steps k




let construct_frontend_proof dirname base induction implication k = 

  let base_jkind = generate_cpc_proof (Filename.concat dirname frontend_base_proofname_cpc) base in
  let induction_jkind =generate_cpc_proof (Filename.concat dirname frontend_induction_proofname_cpc) induction in
  let implication_jkind =generate_cpc_proof (Filename.concat dirname frontend_implication_proofname_cpc) implication in

  let (defs, base_steps) = get_proof_defs base_jkind  in
  let (_, induction_steps) = get_proof_defs induction_jkind in
  let (_, implication_steps) = get_proof_defs implication_jkind in
  let induction_steps = remove_kind_2_defs induction_steps in
  let implication_steps = remove_kind_2_defs implication_steps in
  
  let oc = open_out (Filename.concat dirname frontend_proofname_cpc) in
  let fmt = Format.formatter_of_out_channel oc in
  pp_print_frontend_proof fmt defs base_steps induction_steps implication_steps k

let parse_cpc_file (filename : string) : cpc_step list =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  let steps =
    try
      parse_cpc_from_lexbuf lexbuf
    with e ->
      close_in ic;
      raise e
  in
  close_in ic;
  steps


  let construct_safety_proof dirname =
    let kind_2_proof = parse_cpc_file (dirname ^"/" ^ kind_2_proofname_cpc) in
    let frontend_proof = parse_cpc_file (dirname^"/" ^ frontend_proofname_cpc) in

    let (defs, frontend_steps) = get_proof_defs frontend_proof  in
    let (_, jkind_defs) = factor_jkind_defs defs in 
    let trimmed_jkind_defs = remove_kind_2_defs jkind_defs in
    let frontend_proof = trimmed_jkind_defs @ frontend_steps in
      let final_steps = [
          (mk_hardcoded_step "proof_obs");
          (mk_hardcoded_step "proof_obs_eq");
          (mk_hardcoded_step "proof_safe");

    ] in
    
    let final_proof = List.concat [kind_2_proof; frontend_proof; final_steps] in
    let safety_proof_path = Filename.concat dirname safety_proofname_cpc in 
    let oc = open_out safety_proof_path in
    let fmt = Format.formatter_of_out_channel oc in
    Format.fprintf fmt "%a" pp_cpc_proof final_proof;
    Format.printf "Final Safety CPC proof written to %s\n" safety_proof_path