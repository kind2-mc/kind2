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

module TS = TransSys

module SVMap = StateVar.StateVarMap


let print_vars_path sys =
  match TS.get_source sys with
  | TS.Lustre nodes ->

    let model_path = Model.path_of_term_list (List.map (fun sv ->
        let tv = Term.mk_var (Var.mk_state_var_instance sv Numeral.zero) in
        sv, [tv;tv;tv;tv]
      ) (TS.state_vars sys)) in


    let fmt = !log_ppf in    
    Format.fprintf fmt "STATE VARS MAPBACK:@.%a"
      (LustrePath.pp_print_path_pt nodes false) model_path;
    Format.fprintf fmt "@.";
    Format.fprintf fmt "END@.";
    
  | _ -> assert false

let print_vars_path sys =
  match TS.get_source sys with
  | TS.Lustre nodes ->

    let lustre_vars =
      LustrePath.reconstruct_lustre_streams nodes (TS.state_vars sys) in
    
    Format.eprintf "STATE VARS MAPBACK:@.";
    SVMap.iter (fun sv lusv ->
        Format.eprintf "%a ->@." StateVar.pp_print_state_var sv;

        List.iter (fun (svlu, parents) ->
            List.iter (fun (svp, n) ->
                Format.eprintf " %a~%d" (LustreIdent.pp_print_ident true) svp n)
              parents;
            Format.eprintf " . %a@." StateVar.pp_print_state_var svlu
          ) lusv
      ) lustre_vars;
    
    Format.eprintf "@.";
    Format.eprintf "END@.";
    
  | _ -> assert false


let jkind_var_of_lustre kind_sv (li, parents) =
  let base_li = StateVar.name_of_state_var li in
  (* Ignore main top level node for jkind *)
  let parents_wo_main = List.tl parents in
  let strs = List.fold_left (fun acc (ni, n) ->
      let bni = List.hd (LustreIdent.scope_of_ident ni) in
      (bni^"~"^(string_of_int n)) :: acc
    ) [base_li] (List.rev parents_wo_main) in
  let str = Format.sprintf "$%s$" (String.concat "." strs) in
  StateVar.mk_state_var
    ~is_input:(StateVar.is_input kind_sv)
    ~is_const:(StateVar.is_const kind_sv)
    ~for_inv_gen:(StateVar.for_inv_gen kind_sv)
    str [] (StateVar.type_of_state_var kind_sv)


let jkind_vars_of_kind2_statevar lustre_vars sv =
  let lus_vs = SVMap.find sv lustre_vars in
  List.map (jkind_var_of_lustre sv) lus_vs





let state_vars_path sys =
  match TS.get_source sys with
  | TS.Lustre nodes ->

    let lustre_vars =
      LustrePath.reconstruct_lustre_streams nodes (TS.state_vars sys) in

    Format.eprintf "STATE VARS MAPBACK:";
    List.iter (fun sv ->
        Format.eprintf "\n%a -> " StateVar.pp_print_state_var sv;
        try
          List.iter (fun sv_jk ->
            Format.eprintf "%a , " StateVar.pp_print_state_var sv_jk;
            ) (jkind_vars_of_kind2_statevar lustre_vars sv)
        with Not_found -> Format.eprintf "(ignored)"
      ) (TS.state_vars sys);
    
    Format.eprintf "@.";
    Format.eprintf "END@.";
    
  | _ -> assert false


(* let state_vars_path = print_vars_path *)
  







(* let s_prime = HString.mk_hstring "prime" *)

(* module Conv = SMTExpr.Converter(D) *)
(* let conv = { D.smtlib_string_sexpr_conv with *)
(*              D.prime_symbol = Some s_prime } *)
(* let conv_type_of_sexpr = conv.D.type_of_sexpr *)
(* let conv_term_of_sexpr = conv.D.expr_of_string_sexpr conv *)

  
(* let s_define_node = HString.mk_hstring "define-node" *)
(* let s_init = HString.mk_hstring "init" *)
(* let s_trans = HString.mk_hstring "trans" *)
(* let s_callers = HString.mk_hstring "callers" *)
(* let s_lambda = HString.mk_hstring "lambda" *)
(* let s_opt_const = HString.mk_hstring ":const" *)
(* let s_opt_input = HString.mk_hstring ":input" *)
(* let s_opt_for_inv_gen = HString.mk_hstring ":for-inv-gen" *)
(* let s_annot = HString.mk_hstring ":user" *)
(* let s_contract = HString.mk_hstring ":contract" *)
(* let s_gen = HString.mk_hstring ":generated" *)
(* let s_inst = HString.mk_hstring ":subsystem" *)
(* let s_props = HString.mk_hstring "props" *)
(* let s_intrange = HString.mk_hstring "IntRange" *)




(* (\* Parse from input channel *\) *)
(* let of_channel in_ch =  *)

(*   let lexbuf = Lexing.from_channel in_ch in *)
(*   let sexps = SExprParser.sexps SExprLexer.main lexbuf in *)

(*   (\* Parse sexps and register callers *\) *)
(*   let sys_and_calls = *)
(*     List.map (fun sexp -> *)

(*         assert fasle *)
        
(*       ) sexps *)
(*   in *)

(*   assert false *)

(* (\* Open and parse from file *\) *)
(* let of_file filename =  *)

(*     (\* Open the given file for reading *\) *)
(*     let use_file = open_in filename in *)
(*     let in_ch = use_file in *)

(*     of_channel in_ch *)


(* let dump_native sys = assert false *)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
