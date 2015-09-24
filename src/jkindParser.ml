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
module SVH = StateVar.StateVarHashtbl

module Conv = SMTExpr.Converter(D)
let conv = D.smtlib_string_sexpr_conv
let conv_type_of_sexpr = conv.D.type_of_sexpr
let conv_term_of_sexpr = conv.D.expr_of_string_sexpr conv


(************************)
(* Useful hconsed names *)
(************************)

let s_define_fun = HString.mk_hstring "define-fun"
let s_declare_fun = HString.mk_hstring "declare-fun"
let s_set_option = HString.mk_hstring "set-option"
let s_T = HString.mk_hstring "T"
let s_pinit = HString.mk_hstring "%init"
let s_assert = HString.mk_hstring "assert"
let s_leq = HString.mk_hstring "<="
let s_and = HString.mk_hstring "and"


(**************************************)
(* General settings for JKind parsing *)
(**************************************)

(* New scope for the JKind system *)
let jkind_scope = ["JKind"]


(* Options used to run JKind. We make it dump its smt2 files that contain the
   transition relation. Everything is disabled so that JKind only produces one
   file [<file.lus>.bmc.smt2] containing one instance of the transition
   relation and the state variables. *)
let jkind_options = [
  "-scratch";
  "-no_inv_gen";
  "-no_k_induction";
  "-pdr_max 0";
  "-n 0";
  "-scratch";
  "-solver z3" (* We use z3 here but any SMT2lib solver would work *)
]


(* Create command line to call JKind *)
let jkind_command_line file =
  let jkind = Flags.jkind_bin () in
  let file_red =
    if Debug.mode "certif" then [file]
    else [file; ">/dev/null"] in
  String.concat " " (jkind :: jkind_options @ file_red)


(******************************************)
(* JKind state variables from Lustre name *)
(******************************************)

(* Simple heuristic to see if a state variable is an observer (which are named
   differently in JKind when they appear under a condact) *)
let is_observer sv =
  Lib.string_starts_with (StateVar.name_of_state_var sv)
    LustreIdent.observer_ident_string


let is_first_tick sv =
  let b = Lib.string_starts_with (StateVar.name_of_state_var sv)
      LustreIdent.first_tick_ident_string in
  (* Format.eprintf "is_first_tick: %a : %b@." StateVar.pp_print_state_var sv b; *)
  b
  


let rec lookup_fuzzy str scope =
  try StateVar.state_var_of_string (str, scope)
  with Not_found ->
    let pos_us = String.rindex str '_' in
    let str = String.init (String.length str)
        (fun i -> if i = pos_us then '.' else str.[i]) in
    lookup_fuzzy str scope


let build_call_base kind_sv base_li parents =
  
  let strs, _ = List.fold_left (fun (acc, prev_clocked) (ni, n, clock) ->

      let bni = List.hd (LustreIdent.scope_of_ident ni) in

      let jcall_name = match clock, prev_clocked with
        | None, false -> bni ^"~"^ (string_of_int n)
        | None, true -> bni ^"~clocked~"^ (string_of_int n)
        | Some _, _ -> bni ^"~condact~"^ (string_of_int n)
      in

      jcall_name :: acc, (clock <> None)
    ) ([], false) parents
  in

  let strs = List.rev (base_li :: strs) in
  
  let str = Format.sprintf "$%s$" (String.concat "." strs) in
  (* add -1 for constants *)
  let str = if StateVar.is_const kind_sv then str ^"~1" else str in
  
  (* Format.eprintf "kindsv:%a -> jkind? %s@." StateVar.pp_print_state_var kind_sv str; *)
  
  (* get previously constructed jkind variable *)
  lookup_fuzzy str jkind_scope


(* Returns a state variable of JKind form a state variable of Kind 2 and a
   callsite information *)
let jkind_var_of_lustre kind_sv (li, parents) =

  let base_li = match parents, List.rev parents with
    | _, (_, _, Some clock) :: _ when StateVar.equal_state_vars li clock ->
      (* the var is the clock, always named ~clock in JKind *)
      "~clock"

    | _, (_, _, Some clock) :: _ when is_first_tick kind_sv ->
      (* init variable *)
      "~init"

    | (_, _, Some _) :: _, _
      when not (StateVar.is_input li) && is_observer kind_sv ->
      (* clocked property variable *)
      (StateVar.name_of_state_var li) ^"~clocked_property"

    | (_, _, Some _) :: _, _ when not (StateVar.is_input li) ->
      (* other clocked variable *)
      (StateVar.name_of_state_var li) ^"~clocked"

    | _ when is_first_tick kind_sv ->
      (* init variable *)
      "%init"
              
    | _ -> StateVar.name_of_state_var li
  in

  build_call_base kind_sv base_li parents


let match_condact_clock lustre_vars sv =
  let clocks_calls =
    SVMap.fold (fun _ l acc ->
        List.fold_left (fun acc (_, call_chain) ->
            match List.rev call_chain with
            | (_, _, Some clock) :: _ when StateVar.equal_state_vars sv clock ->
              let cl = (sv, "~clock", call_chain) in
              if List.mem cl acc then acc else cl :: acc
            | _ -> acc
          ) acc l
      ) lustre_vars []
  in

  List.map (fun (sv, base_li, parents) -> build_call_base sv base_li parents)
    clocks_calls
  

(* Returns all JKind variables corresponding to a Kind2 variable *)
let jkind_vars_of_kind2_statevar lustre_vars sv =
  let lus_vs = SVMap.find sv lustre_vars in
  List.fold_left (fun acc lv ->
      try jkind_var_of_lustre sv lv :: acc
      with Not_found -> acc
    ) [] lus_vs
  |> List.rev_append (match_condact_clock lustre_vars sv)
       


(*******************************)
(* Parsing of JKind dump files *)
(*******************************)

(* The type of raw systems extracted from JKind dump file. It only contains the
   state variables and a lambda expression for the transition relation. (Note:
   JKind uses the same term for [init] and [trans]. [init] is the partial
   application [jk_trans_lambda true] and [trans] is the partial application
   [jk_trans_lambda false].)*)
type jkind_raw = {
  jk_statevars : StateVar.t list;
  jk_trans_lambda : Term.lambda option;
}


(* An empty raw system to start with*)
let jkind_empty = {
  jk_statevars = [];
  jk_trans_lambda = None;
}

(* Create free variables from an sexp of arguments *)
let rec vars_of_args acc = function
  | [] -> List.rev acc
  | HS.List [HS.Atom v; ty] :: args ->
    let tyv = conv_type_of_sexpr ty in
    let var = Var.mk_free_var v tyv in
    vars_of_args (var :: acc) args
  | _ -> failwith "Not a variable"


(* Get the state varaible name from a JKind name (remove instance info) *)
let state_var_name_of_jkdecl h =
  let s = HString.string_of_hstring h in
  try Scanf.sscanf s "$%s@$~1" (fun x -> "$"^x^"$")
  with End_of_file | Scanf.Scan_failure _ -> s


(* Remove let bindings by propagating the values *)
let unlet_term term = Term.construct (Term.eval_t (fun t _ -> t) term)


(* Parse a list of s-expressions and return a raw JKind system *)
let rec parse acc = function

  (* Ignore set-option *)
  | HS.List (HS.Atom s :: _) :: r when s == s_set_option ->
    parse acc r

  (* Definition of transition relation *)
  | HS.List [HS.Atom s; HS.Atom t; HS.List args;
             HS.Atom _ (* return type *);
             hdef] :: r
    when s == s_define_fun &&
         t == s_T ->

    let argsv = vars_of_args [] args in
    let bvars = List.map (fun v -> Var.hstring_of_free_var v, v) argsv in
    let lamb = Term.mk_lambda argsv (conv_term_of_sexpr bvars hdef) in
    
    parse { acc with jk_trans_lambda = Some lamb } r

  (* Ignore %init state variable *)
  | HS.List (HS.Atom s :: HS.Atom i :: HS.List [] :: ty :: []) :: r
    when s == s_declare_fun &&
         i == s_pinit ->
    parse acc r

  (* Declaration of state variable *)
  | HS.List (HS.Atom s :: HS.Atom sv :: HS.List [] :: ty :: []) :: r
    when s == s_declare_fun ->

    let tysv = conv_type_of_sexpr ty in
    let s = state_var_name_of_jkdecl sv in
    let sv = StateVar.mk_state_var s jkind_scope tysv in

    parse { acc with jk_statevars = sv :: acc.jk_statevars } r

  (* Range constraints from asserts *)
  | HS.List [HS.Atom ass;
             HS.List [HS.Atom conj;
                      HS.List [HS.Atom leq1; HS.Atom l; HS.Atom t1];
                      HS.List [HS.Atom leq2; HS.Atom t2; HS.Atom u]]
            ] :: r
    when ass == s_assert &&
         conj == s_and &&
         leq1 == s_leq &&
         leq2 == s_leq &&
         t1 == t2 ->

    let s = state_var_name_of_jkdecl t1 in
    let sv = StateVar.state_var_of_string (s, jkind_scope) in
    let l = Numeral.of_string (HString.string_of_hstring l) in
    let u = Numeral.of_string (HString.string_of_hstring u) in
    let range_ty = Type.mk_int_range l u in
    (* Change type of variable *)
    StateVar.change_type_of_state_var sv range_ty;

    parse acc r

  (* Finished parsing *)
  | [] ->

    { acc with
      (* Right order for state variables *)
      jk_statevars = List.rev acc.jk_statevars
    }


  (* Unsupported *)
  | _ -> failwith "Unsupported sexp in JKind output"



let minus_one_to_const e =
  let hc = SVH.create 13 in
  let e =
    Term.map (fun _ t ->
        if Term.is_free_var t then
          let v = Term.free_var_of_term t in
          if Var.is_state_var_instance v &&
             Var.offset_of_state_var_instance v |> Numeral.(equal (neg one))
          then
            let sv = Var.state_var_of_state_var_instance v in
            try fst (SVH.find hc sv)
            with Not_found ->
              let svc = StateVar.mk_state_var
                  ~is_const:true
                  ~is_input:true
                  ~for_inv_gen:true
                  ((StateVar.name_of_state_var sv) ^"~1")
                  (StateVar.scope_of_state_var sv)
                  (StateVar.type_of_state_var sv)
              in
              let tc = svc
                       |> Var.mk_const_state_var
                       |> Term.mk_var in
              SVH.add hc sv (tc, svc);
              tc
          else t
        else t
      ) e in
  let new_consts = SVH.fold (fun _ (_, svc) acc -> svc :: acc) hc [] in
  e, new_consts


let simplify_trivial_ites =
  Term.map (fun _ t ->
      let open Term.T in
      match node_of_t t with
      | Node (s_ite, [cond; t_then; t_else])
        when s_ite == Symbol.s_ite ->
        if Term.equal cond Term.t_true then t_then
        else if Term.equal cond Term.t_false then t_else
        else t
      | _ -> t
    )

(* Parse from input channel *)
let of_channel in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  let statevars, jk_trans_lambda =
    match parse jkind_empty sexps with
    | { jk_statevars; jk_trans_lambda = Some jk_trans_lambda } ->
      jk_statevars, jk_trans_lambda
    | _ -> assert false
  in

  (* Get types of state variables*)
  let vars_types = List.map StateVar.type_of_state_var statevars in

  (* Usefull instances of state variables *)
  
  let statevars0 = List.map (fun sv ->
      Var.mk_state_var_instance sv Numeral.zero)
      statevars in

  let statevars1 = List.map (fun sv ->
      Var.mk_state_var_instance sv Numeral.one)
      statevars in

  let statevars_m1 = List.map (fun sv ->
      Var.mk_state_var_instance sv Numeral.(neg one))
      statevars in

  let t_statevars0 = List.map Term.mk_var statevars0 in
  let t_statevars1 = List.map Term.mk_var statevars1 in
  let t_statevars_m1 = List.map Term.mk_var statevars_m1 in
  
  (* Predicate symbol for initial state predicate *)
  let init_uf_symbol = 
    UfSymbol.mk_uf_symbol
      (LustreIdent.init_uf_string ^ "_JKind") 
      vars_types
      Type.t_bool 
  in

  (* Predicate symbol for transition relation predicate *)
  let trans_uf_symbol = 
    UfSymbol.mk_uf_symbol
      (LustreIdent.trans_uf_string ^ "_JKind") 
      (vars_types @ vars_types)
      Type.t_bool 
  in

  (debug certif "JKind Lambda:\n%a" Term.pp_print_lambda jk_trans_lambda
   end);

(* Term for initial states and new constant oracles. We do a simplification
   by removing let bindings originating from the lambda application. *)
  let init_term, consts =
    Term.eval_lambda jk_trans_lambda
      (Term.t_true :: t_statevars_m1 @ t_statevars0)
    |> unlet_term
    |> simplify_trivial_ites
    |> minus_one_to_const 
  in
  
  (* Term for transition relation. We do a simplification by removing let
     bindings originating from the lambda application. *)
  let trans_term =
    Term.eval_lambda jk_trans_lambda
      (Term.t_false :: t_statevars0 @ t_statevars1)
    |> unlet_term
    |> simplify_trivial_ites
  in

  let vconsts = List.map Var.mk_const_state_var consts in
  let init = init_uf_symbol, (vconsts @ statevars0, init_term) in
  let trans = trans_uf_symbol, (vconsts @ statevars1 @ statevars0, trans_term) in

  let allstatevars = consts @ statevars in
  
  (* Creation of transition system *)
  TransSys.mk_trans_sys
    jkind_scope
    allstatevars
    init trans
    (* No subsystems, no properties *)
    [] []
    TransSys.Native


(* Return a transition system extracted from a call to JKind. *)
let get_jkind_transsys file =

  (* Make temporary copy of input file *)
  let base = Filename.basename file in
  let tmp = Filename.temp_file base ".lus" in
  file_copy file tmp;

  (debug certif "Temporary file %s" tmp end);
  
  (* Run JKind on temporary copy *)
  let cmd = jkind_command_line tmp in

  (debug certif "JKind command line: %s" cmd end);

  if Sys.command cmd <> 0 then
    failwith "JKind execution failed";

  (* open dump file and parse *)
  let dump_file = tmp ^ ".bmc.smt2" in

  (debug certif "Parsing from JKind dump file: %s" dump_file end);

  let in_ch = open_in dump_file in
  let sys = of_channel in_ch in

  (* Close file *)
  close_in in_ch;

  sys


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
