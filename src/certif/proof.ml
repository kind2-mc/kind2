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

(* Hard coded options *)
  
let mpz_proofs = true
let compact = true
let set_margin fmt = pp_set_margin fmt 80 (* (if compact then max_int else 80) *)



(* disable the preprocessor and tell cvc4 to dump proofs *)
(* KLUDGE we use a linux version through ssh because of bugs in the mac
   version *)
(* let cvc4_proof_cmd = "ssh kind \"~/CVC4_proofs/builds/x86_64-unknown-linux-gnu/production-proof/bin/cvc4 --lang smt2 --no-simplification --dump-proof\" <" *)

let cvc4_proof_cmd =
  Flags.Smt.cvc4_bin () ^
  " --lang smt2 --no-simplification --fewer-preprocessing-holes --dump-proof"


let get_cvc4_version () =
  let cmd = Flags.Smt.cvc4_bin () ^ " --version" in
  let s = syscall cmd in
  let n = String.index s '\n' in
  let start = 8 in
  String.sub s start (n - start)

(* LFSC symbols *)

let s_and = H.mk_hstring "and"
let s_or = H.mk_hstring "or"
let s_not = H.mk_hstring "not"
let s_impl = H.mk_hstring "impl"
let s_iff = H.mk_hstring "iff"
let s_ifte = H.mk_hstring "ifte"
let s_xor = H.mk_hstring "xor"
let s_true = H.mk_hstring "true"
let s_false = H.mk_hstring "false"

let s_formula = H.mk_hstring "formula"
let s_th_holds = H.mk_hstring "th_holds"
let s_holds = H.mk_hstring "holds"
let s_truth = H.mk_hstring "truth"
let s_trust = H.mk_hstring "trust"
let s_trust_f = H.mk_hstring "trust_f"

let s_sort = H.mk_hstring "sort"
let s_term = H.mk_hstring "term"
let s_let = H.mk_hstring "let"
let s_flet = H.mk_hstring "flet"
let s_eq = H.mk_hstring "="

let s_Bool = H.mk_hstring "Bool"
let s_p_app = H.mk_hstring "p_app"
let s_apply = H.mk_hstring "apply"
let s_cln = H.mk_hstring "cln"

let s_check = H.mk_hstring "check"
let s_ascr = H.mk_hstring ":"
let s_PI = H.mk_hstring "!"
let s_LAMBDA = H.mk_hstring "%"
let s_lambda = H.mk_hstring "\\"
let s_at = H.mk_hstring "@"
let s_hole = H.mk_hstring "_"
let s_define = H.mk_hstring "define"
let s_opaque = H.mk_hstring "opaque"


let s_unsat = H.mk_hstring "unsat"
let s_sat = H.mk_hstring "sat"
let s_unknown = H.mk_hstring "unknown"


let global_logic = ref `None

let set_proof_logic l = global_logic := l

let abstr_ind_of_logic = let open TermLib in
  function
  | `Inferred fs ->
    if FeatureSet.mem RA fs then
      if FeatureSet.mem IA fs then
        failwith "CVC4 cannot generate proofs for systems with both \
                  integer and real variables"
      else true
    else false
  | _ -> false

let abstr_index () =
  Flags.Certif.abstr () || abstr_ind_of_logic !global_logic

let s_index () =
  if abstr_index () then H.mk_hstring "index"
  else H.mk_hstring "Int"

let s_pindex = H.mk_hstring "%index%"
let s_pk = H.mk_hstring "%%k"

(* let s_Int = H.mk_hstring "Int" *)
let s_ind = H.mk_hstring "ind"
let s_mpz = H.mk_hstring "mpz"

let s_invariant = H.mk_hstring "invariant"
let s_kinduction = H.mk_hstring "kinduction"
let s_induction = H.mk_hstring "induction_proof_1"
let s_base = H.mk_hstring "base_proof_1"
let s_implication = H.mk_hstring "implication_proof_1"
let obs_induction = H.mk_hstring "induction_proof_2"
let obs_base = H.mk_hstring "base_proof_2"
let obs_implication = H.mk_hstring "implication_proof_2"
let s_invariant_implies = H.mk_hstring "invariant-implies"
let s_obs_eq = H.mk_hstring "obs_eq"
let s_inv_obs = H.mk_hstring "inv+obs"
let s_weak_obs_eq = H.mk_hstring "weak_obs_eq"
let s_safe = H.mk_hstring "safe"

let proof_inv_name = H.mk_hstring "proof_inv"
let proof_obs_name = H.mk_hstring "proof_obs"
let proof_obs_eq_name = H.mk_hstring "proof_obs_eq"
let proof_safe_name = H.mk_hstring "proof_safe"
  
let proofname = "proof.lfsc"
let frontend_proofname = "frontend_proof.lfsc"


let hstring_of_int i = H.mk_hstring (string_of_int i)


let hole = HS.Atom s_hole

(* LFSC types (sexpressions) *)
type lfsc_type = HS.t

(* LFSC terms (sexpressions) *)
type lfsc_term = HS.t

let ty_formula = HS.Atom s_formula
let ty_term ty = HS.(List [Atom s_term; ty])


(* LFSC [(term index)] *)
let term_index () = HS.(List [Atom s_term; Atom (s_index ())])

(* LFSC type for representing indexes *)
let s_lfsc_index = if mpz_proofs then s_mpz else s_pindex

(* substitution [(term index) -> %index%] *)
let sigma_pindex () = [term_index (), HS.Atom s_pindex]

(* substitution [(term index) -> mpz] *)
let sigma_mpz () = [term_index (), HS.Atom s_mpz;]
                 (* HS.Atom s_index, HS.Atom s_Int] *)

(* substitution from [(term index)] to the selected representation *)
let sigma_tindex () = if mpz_proofs then sigma_mpz () else sigma_pindex ()

(* Returns [true] if the LFSC expression is the type for indexes [(term
   index)] *)
let is_term_index_type = function
  | HS.List [HS.Atom t; HS.Atom i] -> t == s_term && i == s_index ()
  | _ -> false

(* Returns [true] if the argument is ["index"] *)
let is_index_type i = i == (s_index ())



(* Type of LFSC declarations *)
type lfsc_decl = {
  decl_symb : H.t;
  decl_type : lfsc_type;
}

(* Type of LFSC definitions *)
type lfsc_def = {
  def_symb : H.t;
  def_args : (H.t * lfsc_type) list;
  def_ty : lfsc_type;
  def_body : lfsc_term;
}

(* Comparison for equality of declarations *)
let equal_decl d1 d2 =
  H.equal d1.decl_symb d2.decl_symb &&
  HS.equal d1.decl_type d2.decl_type

(* Comparison for equality of definitions *)
let equal_def d1 d2 =
  H.equal d1.def_symb d2.def_symb &&
  HS.equal d1.def_ty d2.def_ty &&
  HS.equal d1.def_body d2.def_body
(* add args if needed *)
  
(* Type of contexts for proofs *)
type cvc4_proof_context = {
  lfsc_decls : lfsc_decl list;
  lfsc_defs : lfsc_def list;
  fun_defs_args : (H.t * int * lfsc_type) list HH.t;
}

(* Empty context *)
let mk_empty_proof_context () = {
  lfsc_decls = [];
  lfsc_defs = [];
  fun_defs_args = HH.create 17;
}

(* The type of a proof returned by CVC4 *)
type cvc4_proof = {
  proof_context : cvc4_proof_context;
  mutable true_hyps : H.t list;
  proof_hyps : lfsc_decl list; 
  proof_type : lfsc_type;
  proof_term : lfsc_type;
}

(* Create an empty proof from a context *)
let mk_empty_proof ctx = {
  proof_context = ctx;
  proof_hyps = [];
  true_hyps = [];
  proof_type = HS.List [];
  proof_term = HS.List [];
}


(* Classifier for lambda abstractions in LFSC *)
type lambda_kind =
  | Lambda_decl of lfsc_decl (* symbol/variables declarations *)
  | Lambda_hyp of lfsc_decl  (* Proof hypothesis % A0 ...*)
  | Lambda_def of lfsc_def   (* definitions % f%def *)
  | Lambda_ignore            (* ignore some extraneous symbols *)
  | Lambda_true



(**********************************)
(* Printing LFSC terms and proofs *)
(**********************************)

(* print an LFSC type *)
let print_type =
  if compact then HS.pp_print_sexpr_indent_compact 0
  else HS.pp_print_sexpr_indent 0

(* print an LFSC term *)
let print_term =
  if compact then HS.pp_print_sexpr_indent_compact 0
  else HS.pp_print_sexpr_indent 0


(* print an LFSC declarations *)
let print_decl fmt { decl_symb; decl_type } =
  fprintf fmt "@[<hov 1>(declare@ %a@ %a)@]"
    H.pp_print_hstring decl_symb print_type decl_type


(* print the type of a symbol for its LFSC definition *)
let rec print_def_type ty fmt args =
  match args with
  | [] -> print_type fmt ty
  | (_, ty_a) :: rargs ->
    fprintf fmt "@[<hov 0>(! _ %a@ %a)@]"
      print_type ty_a
      (print_def_type ty) rargs


(* print the LFSC definition as a lambda abstraction *)
let rec print_def_lambdas term fmt args =
  match args with
  | [] -> print_term fmt term
  | (a, _) :: rargs ->
    fprintf fmt "@[<hov 0>(\\ %a@ %a)@]"
      H.pp_print_hstring a (print_def_lambdas term) rargs


(* Print an LFSC definition with type information *)
let print_def fmt { def_symb; def_args; def_ty; def_body } =
  fprintf fmt "@[<hov 1>(define@ %a@ @[<hov 1>(: @[<hov 0>%a@]@ %a)@])@]"
    H.pp_print_hstring def_symb
    (print_def_type def_ty) def_args
    (print_def_lambdas def_body) def_args


(* Print a proof context *)
let print_context fmt { lfsc_decls; lfsc_defs } =
  List.iter (fprintf fmt "%a@." print_decl) (List.rev lfsc_decls);
  fprintf fmt "@.";
  List.iter (fprintf fmt "%a\n@." print_def) lfsc_defs;
  fprintf fmt "@."

(* Print only definitions of a proof context *)
let print_defs fmt { lfsc_defs } =
  List.iter (fprintf fmt "%a\n@." print_def) lfsc_defs;
  fprintf fmt "@."

(* Print extra declarations/definitions of a context.
   [print_delta_context ctx_old fmt ctx_new] prints the elements of [ctx_new]
   that do not appear in [ctx_old]. *)
let print_delta_context
    { lfsc_decls=old_decls; lfsc_defs=old_defs }
    fmt
    { lfsc_decls; lfsc_defs } =
  List.iter (fun d ->
      if not (List.exists (equal_decl d) old_decls) then
        fprintf fmt "%a@." print_decl d
    ) (List.rev lfsc_decls);
  (* fprintf fmt "@."; *)
  List.iter (fun dl ->
      if not (List.exists (equal_def dl) old_defs) then
        fprintf fmt "%a\n@." print_def dl
    ) lfsc_defs
  (* fprintf fmt "@." *)


(* Print the type of an hypothesis with its name *)
let rec print_hyps_type ty fmt = function
  | [] -> print_type fmt ty
  | { decl_symb; decl_type } :: rhyps ->
    fprintf fmt "@[<hov 0>(! %a %a@ %a)@]"
      H.pp_print_hstring decl_symb
      print_type decl_type
      (print_hyps_type ty) rhyps

(* Print a proof term as lambda abstraction over its hypostheses *)
let rec print_proof_term term fmt = function
  | [] -> print_term fmt term
  | { decl_symb } :: rhyps ->
    fprintf fmt "@[<hov 0>(\\ %a@ %a)@]"
      H.pp_print_hstring decl_symb
      (print_proof_term term) rhyps


(* Print an LFSC proof *)
let print_proof ?(context=false) name fmt
    { proof_context; proof_hyps; proof_type; proof_term } =
  if context then print_context fmt proof_context;
  let hyps = List.rev proof_hyps in
  fprintf fmt "@[<hov 1>(define %s@ @[<hov 1>(: @[<hov 0>%a@]@ %a)@])@]"
    (H.string_of_hstring name)
    (print_hyps_type proof_type) hyps
    (print_proof_term proof_term) hyps



(*********************************)
(* Parsing LFSC proofs from CVC4 *)
(*********************************)

(* Lexicographic comparison of hashconsed strings (used for sorting dummy
   arguments f%1, f%2, f%3, ...) *)
let lex_comp h1 h2 =
  String.compare (H.string_of_hstring h1) (H.string_of_hstring h2)


(* Same on bindings *)
let lex_comp_b (_, i1, _) (_, i2, _) = Pervasives.compare i1 i2


let is_fdummya b =
  let s = H.string_of_hstring b in
  try Scanf.sscanf s "%_s@%%%_d" true
  with End_of_file | Scanf.Scan_failure _ -> false


(* Return the symbol f in dummy symbol f%1 and register it as an argument of
   function f *)
let fun_symbol_of_dummy_arg ctx b ty =
  let s = H.string_of_hstring b in
  try
    Scanf.sscanf s "%s@%%%d" (fun f i ->
      let hf = H.mk_hstring f in
      let args = try HH.find ctx.fun_defs_args hf with Not_found -> [] in
      let nargs = (b, i, ty) :: args |> List.fast_sort lex_comp_b in
      HH.replace ctx.fun_defs_args hf nargs
      );
    true
  with End_of_file | Scanf.Scan_failure _ -> false


(* Return the symbol f in dummy function symbol f%def *)
let fun_symbol_of_def b =
  let s = H.string_of_hstring b in
  try
    Scanf.sscanf s "%s@%%def" (fun f -> Some (H.mk_hstring f))
  with End_of_file | Scanf.Scan_failure _ -> None


let rec fun_symbol_args_of_def acc =
  let open HS in
  function
  | Atom b ->
    (match fun_symbol_of_def b with
     | Some f -> Some (f, acc)
     | None -> None
    )
  | List [Atom a; _; _; f; arg] when a == s_apply ->
    fun_symbol_args_of_def (arg :: acc) f
  | _ -> None

(* Return the symbol f of a function definition dummy hypothesis appearing in
   tracing LFSC proof. Example: [fun_symbol_args_of_def "(apply _ _ (apply _ _
   f f%1) f%2)"] returns ["f"].
*)
let fun_symbol_args_of_def sexp = fun_symbol_args_of_def [] sexp


(* Returns [true] if the bounded symbol is an index constant of the form
   [%%k] or [%%1] *)
let is_index_constant b =
let s = H.string_of_hstring b in
try Scanf.sscanf s "%%%%%_s" true
with End_of_file | Scanf.Scan_failure _ -> false


let concrete_to_mpz ty =
  try List.find (fun (x,y) -> HS.equal ty x) (sigma_tindex ()) |> snd
  with Not_found -> ty


(* Returns [true] if the bounded symbol stands for an hypothesis *)
let is_hyp b ty =
  let s = H.string_of_hstring b in
  try Scanf.sscanf s "A%_d" (true, ty) (* A0, A1, A2, etc. *)
  with End_of_file | Scanf.Scan_failure _ ->
    (* existentially quantified %%k in implication check stays in the
       hypotheses, but replace its index type with mpz *)
    if b == s_pk then (true, concrete_to_mpz ty)
    else if is_index_constant b || is_fdummya b then (false, concrete_to_mpz ty)
    else (false, ty)
                        

(* Returns the integer index of an index constant *)
let mpz_of_index b =
let s = H.string_of_hstring b in
try Scanf.sscanf s "%%%%%d" (fun n -> Some n)
with End_of_file | Scanf.Scan_failure _ -> None


(* Identify useless hypothesis [(th_holds true)] (already in the rules of
   smt.plf) *)
let is_hyp_true = let open HS in function
  | List [Atom th_holds; Atom tt]
    when th_holds == s_th_holds && tt == s_true -> true
  | _ -> false

(* Apply a substitution top to bottom in an LFSC expression *)
let rec apply_subst sigma sexp =
  let open HS in
  try List.find (fun (s,v) -> HS.equal sexp s) sigma |> snd
  with Not_found ->
    match sexp with
    | List l ->
      let l' = List.map (apply_subst sigma) l in
      if List.for_all2 (==) l l' then sexp
      else List l'
    | Atom _ -> sexp

(* Replace the type [(term index)] by the chosen representation *)
(* let repalace_type_index = apply_subst (sigma_tindex ())*)

(* Replacing a constant of type index by an embedding of their chosen
   representation. For example, [%%1] becomes [f (ind 1)] (for mpz embedding)
   and an index variable [i] becomes [(ind i)]. *)
let embed_ind =
  if mpz_proofs then
    fun a -> match a with
    | HS.Atom i ->
      begin match mpz_of_index i with
        | Some n ->
          HS.(List [Atom s_ind; Atom (H.mk_hstring (string_of_int n))])
        | None -> HS.(List [Atom s_ind; a])
      end
    | _ -> HS.(List [Atom s_ind; a])
  else
    fun a -> HS.(List [Atom s_ind; a])

(* Embed indexes by replacing index constants and variables by the chosen
   representation *)
let rec embed_indexes targs sexp =
  let open HS in
  match sexp with
  | Atom i when is_index_constant i -> embed_ind sexp
  | Atom a ->
    (match List.assq a targs with
     | HS.Atom i when i == s_lfsc_index -> embed_ind sexp
     (* | ty when is_term_index_type ty -> embed_ind sexp *)
     | _ -> sexp
     | exception Not_found -> sexp)
  | List l ->
    let l' = List.rev_map (embed_indexes targs) l |> List.rev in
    if List.for_all2 (==) l l' then sexp
    else List l'


let rec definition_artifact_rec ctx = let open HS in function
  | List [Atom at; b; t; s] when at == s_at ->
    begin match definition_artifact_rec ctx s with
      | None -> None
      | Some def ->
        (* FIXME some ugly allocations *)
        Some { def with
               def_body = List [Atom at; b; embed_indexes def.def_args t;
                                def.def_body ]}
    end

  | List [Atom iff; List [Atom p_app; Atom fdef]; term]
    when iff == s_iff && p_app == s_p_app -> 
    begin match fun_symbol_of_def fdef with
      | None -> None
      | Some f ->
        Some { def_symb = f;
               def_args = [];
               def_body = term;
               def_ty = ty_formula } 
    end
    
  | List [Atom eq; ty; Atom fdef; term] when eq == s_eq -> 
    begin match fun_symbol_of_def fdef with
      | None -> None
      | Some f ->
        Some { def_symb = f;
               def_args = [];
               def_body = term;
               def_ty = ty_term ty } 
    end
    
  | List [Atom iff; List [Atom p_app; fd]; term]
    when iff == s_iff && p_app == s_p_app -> 
    begin match fun_symbol_args_of_def fd with
      | None -> None
      | Some (f, _) ->
        let targs = try HH.find ctx.fun_defs_args f with Not_found -> [] in
        let targs =
          List.map (fun (x, _, ty) -> x, (* repalace_type_index *) ty) targs in
        Some { def_symb = f;
               def_args = targs;
               def_body = embed_indexes targs term;
               def_ty = ty_formula } 
    end
    
  | List [Atom eq; ty; fd; term] when eq == s_eq -> 
    begin match fun_symbol_args_of_def fd with
      | None -> None
      | Some (f, _) ->
        let targs = try HH.find ctx.fun_defs_args f with Not_found -> [] in
        let targs =
          List.map (fun (x, _, ty) -> x, (* repalace_type_index *) ty) targs in
        Some { def_symb = f;
               def_args = targs;
               def_body = embed_indexes targs term;
               def_ty = ty_term ty } 
    end
  | _ -> None

(* Identifies definition artifacts introduces to trace inling of CVC4 terms at
   the LFSC level. For example, [(th_holds (@ let38 P1%1(iff (p_app (apply _ _
   P1%def P1%1)) (p_app (apply _ _ top.usr.OK P1%1)))))] is an articfact for
   the definition of pymbol [P1]. *)
let definition_artifact ctx = let open HS in function
    | List [Atom th_holds; d] when th_holds == s_th_holds ->
      definition_artifact_rec ctx d
    | _ -> None

(* Parse lambda binding in proof and classify them. *)
let parse_Lambda_binding ctx b ty =
  let ih, ty = is_hyp b ty in
  if ih then
    if is_hyp_true ty then
      (* ignore useless (th_holds true) *)
      Lambda_true
    else match definition_artifact ctx ty with
      | Some def ->
        (* binding hypothesis for a definition artifact *)
        Lambda_def def
      | None ->
        (* Otherwise its a real hypothesis *)
        Lambda_hyp { decl_symb = b;
                     decl_type = (* repalace_type_index  *)ty |> embed_indexes [] }
  else if fun_symbol_of_dummy_arg ctx b ty || fun_symbol_of_def b <> None then
    (* ignore introduced dummy symbols *)
    Lambda_ignore
  else if is_index_type b then
    (* ignore declaration of abstract type index (already in LFSC rules) *)
    Lambda_ignore
  else if is_index_constant b then
    (* Ignore declaration of index constants *)
    Lambda_ignore
  else
    (* Keep declaration otheriwse *)
    Lambda_decl { decl_symb = b; decl_type = ty }


(* Returns list of admitted holes, i.e. formulas whose validity is trusted *)
let rec extract_trusts acc = let open HS in
  function
  | List [Atom a; f] when a == s_trust_f || a == s_trust -> f :: acc
  | Atom _ -> acc
  | List l -> extract_trusts_list acc l
                
and extract_trusts_list acc = let open HS in
  function
  | [] -> acc
  | x :: r -> extract_trusts_list (extract_trusts acc x) r 


let trusted = ref []

let register_trusts f = trusted := extract_trusts !trusted f

let log_trusted ~frontend () =
  if !trusted <> [] then begin
    Event.log L_warn
      "%s proof contains %d trusted assumptions:@\n@\n@[<v 0>%a@]@."
      (if frontend then "Frontend" else "Invariance")
      (List.length !trusted)
      (fun fmt ->
         List.iter (fprintf fmt "@[%a@]@\n@\n" (HS.pp_print_sexpr_indent 0)))
      !trusted
  end


(***********************)
(* Parsing proof terms *)
(***********************)

(* Parse a proof from CVC4, returns a [!cvc_proof] object *)
let rec parse_proof acc = let open HS in function

  | List [Atom lam; Atom b; ty; r] when lam == s_LAMBDA ->

    let ctx = acc.proof_context in
    let acc = match parse_Lambda_binding ctx b ty with
      | Lambda_decl d ->
        if List.exists (equal_decl d) ctx.lfsc_decls then acc
        else { acc with proof_context =
                          { ctx with lfsc_decls = d :: ctx.lfsc_decls }}
      | Lambda_def d ->
        if List.exists (equal_def d) ctx.lfsc_defs then acc
        else { acc with proof_context =
                          { ctx with lfsc_defs = d :: ctx.lfsc_defs }}
      | Lambda_ignore -> acc
      | Lambda_true -> { acc with true_hyps = b :: acc.true_hyps }
      | Lambda_hyp h -> { acc with proof_hyps = h :: acc.proof_hyps }
    in
    parse_proof acc r

  | List [Atom ascr; ty; pterm] when ascr = s_ascr ->

    let pterm = embed_indexes [] pterm in
    let sigma_truth =
      List.map (fun a -> Atom a, Atom s_truth) acc.true_hyps in
    let pterm =
      if sigma_truth = [] then pterm
      else apply_subst sigma_truth pterm in

    register_trusts pterm;
    (* let trusted = extract_trusts [] pterm in *)
    (* if trusted <> [] then begin *)
    (*   Event.log L_warn *)
    (*     "Proof contains %d trusted assumptions:@\n@\n@[<v 0>%a@]@." *)
    (*     (List.length trusted) *)
    (*     (fun fmt -> *)
    (*        List.iter (fprintf fmt "@[%a@]@\n@\n" (HS.pp_print_sexpr_indent 0))) *)
    (*     trusted *)
    (* end; *)
    
    { acc with proof_type = ty; proof_term = pterm  }

  | s ->
    failwith (asprintf "Unexpected proof:\n%a@." (HS.pp_print_sexpr_indent 0) s)


(* Parse a proof from CVC4 from one that start with [(check ...]. *)
let parse_proof_check ctx = let open HS in function
  | List [Atom check; proof] when check == s_check ->
    parse_proof (mk_empty_proof ctx) proof
  | s ->
    failwith (asprintf "Unexpected proof:\n%a@." (HS.pp_print_sexpr_indent 0) s)



(* Parse a proof from CVC4 from a channel. CVC4 returns the proof after
   displaying [unsat] on the channel. *)
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
      
    | _ ->
      failwith (asprintf "No proofs, instead got:\n%a@."
                  HS.pp_print_sexpr_list sexps)



(* Call CVC4 in proof production mode on an SMT2 file an returns the proof *)
let proof_from_file ctx f =
  let cmd = cvc4_proof_cmd ^ " " ^ f in
  let ic, oc, err = Unix.open_process_full cmd (Unix.environment ()) in
  try
    let proof = proof_from_chan ctx ic in
    ignore(Unix.close_process_full (ic, oc, err));
    proof
  with Failure _ as e ->
    Event.log L_fatal "Could not parse CVC4 proof.";
    (match Unix.close_process_full (ic, oc, err) with
     | Unix.WEXITED 0 -> ()
     | Unix.WSIGNALED i | Unix.WSTOPPED  i | Unix.WEXITED i ->
       Event.log L_fatal "CVC4 crashed with exit code %d." i);
    raise e


(******************************************)
(* Parsing context from dummy lfsc proofs *)
(******************************************)

(* Parse a context from a dummy proof used only for tracing *)
let rec parse_context ctx = let open HS in function

  | List [Atom lam; Atom b; ty; r] when lam == s_LAMBDA ->

    let ctx = match parse_Lambda_binding ctx b ty with
      | Lambda_decl d -> { ctx with lfsc_decls = d :: ctx.lfsc_decls }
      | Lambda_def d -> { ctx with lfsc_defs = d :: ctx.lfsc_defs }
      | Lambda_hyp _ | Lambda_ignore | Lambda_true -> ctx
    in
    parse_context ctx r

  | List [Atom ascr; _; _] when ascr = s_ascr -> ctx

  | s ->
    failwith (asprintf "Unexpected proof:\n%a@." (HS.pp_print_sexpr_indent 0) s)


(* Parse a context from a dummy proof check used only for tracing *)
let parse_context_dummy = let open HS in function
  | List [Atom check; dummy] when check == s_check ->
    parse_context (mk_empty_proof_context ()) dummy

  | s ->
    failwith (asprintf "Unexpected proof:\n%a@." (HS.pp_print_sexpr_indent 0) s)


(* Parse a context from a channel. The goal is trivial because the file
   contains "(assert false)" but we care about the hypotheses to recontruct the
   LFSC definitions inlined by CVC4. *)
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
      
    | _ ->
      failwith (asprintf "No proofs, instead got:\n%a@."
                  HS.pp_print_sexpr_list sexps)



(* Call CVC4 on a file that contains only tracing information and parse the
   dummy proof to extract the context (declarations and definitions). *)
let context_from_file f =
  let cmd = cvc4_proof_cmd ^ " " ^ f in
  let ic, oc, err = Unix.open_process_full cmd (Unix.environment ()) in
  try
    let ctx = context_from_chan ic in
    (* printf "Parsed context:\n%a@." print_context ctx; *)
    ignore(Unix.close_process_full (ic, oc, err));
    ctx
  with Failure _ as e ->
    Event.log L_fatal "Could not parse CVC4 context.";
    (match Unix.close_process_full (ic, oc, err) with
     | Unix.WEXITED 0 -> ()
     | Unix.WSIGNALED i | Unix.WSTOPPED  i | Unix.WEXITED i ->
       Event.log L_fatal "CVC4 crashed with exit code %d." i);
    raise e

(* Merge two contexts *)
let merge_contexts ctx1 ctx2 =
  {
    lfsc_decls = ctx2.lfsc_decls @ ctx1.lfsc_decls;
    lfsc_defs = ctx2.lfsc_defs @ ctx1.lfsc_defs;
    fun_defs_args =
      let h = HH.create 21 in
      HH.iter (HH.add h) ctx1.fun_defs_args;
      HH.iter (HH.add h) ctx2.fun_defs_args;
      h;
  }



let context_from_file f =
  Stat.start_timer Stat.certif_cvc4_time;
  let c = context_from_file f in
  Stat.record_time Stat.certif_cvc4_time;
  c
  
let proof_from_file f =
  Stat.start_timer Stat.certif_cvc4_time;
  let p = proof_from_file f in
  Stat.record_time Stat.certif_cvc4_time;
  p
  


open Certificate


(* Write a proof to the formatter. The proof is given a name [pname] and a
   [type]. The Boolean [check] is used to tell that if LFSC should check this
   proof (its not necessary if the proof is reused in another check). *)
let write_proof_and_check fmt ?(check=true) pname ptype pterm =

  fprintf fmt "@[<hov 1>(define@ %a@ @[<hov 1>(: @[<hov 0>%a@]@ %a)@])@]@.@."
    H.pp_print_hstring pname
    print_type ptype
    print_term pterm;

  if check then
    fprintf fmt "@[<hov 1>(check@ %a@])@]@.@."
      H.pp_print_hstring pname



(* Write a proof of invariance by k-induction using the proof of its subcases
   and a certificate constructed by Kind 2. See [!Certificate.invariant]. *)
let write_inv_proof fmt ?(check=true)
    (s_implication, s_base, s_induction) name_proof c =
  let open HS in

  (* LFSC atoms for formulas *)
  let a_k = Atom (hstring_of_int c.k) in
  let a_init = Atom (H.mk_hstring c.for_system.names.init) in
  let a_trans = Atom (H.mk_hstring c.for_system.names.trans) in
  let a_prop = Atom (H.mk_hstring c.for_system.names.prop) in
  let a_phi = Atom (H.mk_hstring c.for_system.names.phi) in

  (* LFSC commands to construct the proof *)
  let a_invariant = Atom s_invariant in
  let a_invariant_implies = Atom s_invariant_implies in
  let a_kinduction = Atom s_kinduction in

  (* Prior LFSC proofs *)
  let proof_implication = Atom s_implication in
  let proof_base = Atom s_base in
  let proof_induction = Atom s_induction in

  let pterm =
    List [a_invariant_implies; a_init; a_trans; a_phi; a_prop;
          proof_implication;

          List [a_kinduction; a_k; a_init; a_trans; a_phi;
                hole; hole; proof_base; proof_induction ]
         ] in
  let ptype = List [a_invariant; a_init; a_trans; a_prop] in

  write_proof_and_check fmt ~check name_proof ptype pterm

(* Write a proof of weak observational equivalence using the proof ob
   invariance of the observer. *)
let write_obs_eq_proof fmt ?(check=true) proof_obs_name name_proof c =
  
  let open HS in

  (* LFSC atoms for formulas *)
  let a_init_1 = Atom (H.mk_hstring c.kind2_system.names.init) in
  let a_trans_1 = Atom (H.mk_hstring c.kind2_system.names.trans) in
  let a_prop_1 = Atom (H.mk_hstring c.kind2_system.names.prop) in

  let a_init_2 = Atom (H.mk_hstring c.jkind_system.names.init) in
  let a_trans_2 = Atom (H.mk_hstring c.jkind_system.names.trans) in
  let a_prop_2 = Atom (H.mk_hstring c.jkind_system.names.prop) in


  (* LFSC commands to construct the proof *)
  let a_obs_eq = Atom s_obs_eq in
  let a_weak_obs_eq = Atom s_weak_obs_eq in
  let a_same_inputs = Atom (H.mk_hstring "same_inputs") in

  (* named prood of obsercational equivalence *)
  let proof_obs = Atom proof_obs_name in

  let pterm = 
    List [a_obs_eq;
          a_init_1; a_trans_1; a_prop_1;
          a_init_2; a_trans_2; a_prop_2;
          a_same_inputs; proof_obs]
  in

  let ptype =
    List [a_weak_obs_eq;
          a_init_1; a_trans_1; a_prop_1;
          a_init_2; a_trans_2; a_prop_2]
  in

  write_proof_and_check fmt ~check name_proof ptype pterm  


(* Write a proof of safety using the proof of invariance and the proof of weak
   observational equivalence. *)
let write_safe_proof fmt ?(check=true)
    proof_inv proof_obs_eq name_proof kind2_s jkind_s =
  let open HS in

  (* LFSC atoms for formulas *)
  let a_init = Atom (H.mk_hstring kind2_s.names.init) in
  let a_trans = Atom (H.mk_hstring kind2_s.names.trans) in
  let a_prop = Atom (H.mk_hstring kind2_s.names.prop) in

  let a_init' = Atom (H.mk_hstring jkind_s.names.init) in
  let a_trans' = Atom (H.mk_hstring jkind_s.names.trans) in
  let a_prop' = Atom (H.mk_hstring jkind_s.names.prop) in


  (* LFSC commands to construct the proof *)
  let a_inv_obs = Atom s_inv_obs in
  let a_safe = Atom s_safe in

  (* Prior LFSC proofs *)
  let proof_inv = Atom proof_inv in
  let proof_obs_eq = Atom proof_obs_eq in

  let pterm =
    List [a_inv_obs;
          a_init; a_trans; a_prop;
          a_init'; a_trans'; a_prop';
          proof_inv; proof_obs_eq]
  in
  let ptype = List [a_safe; a_init; a_trans; a_prop] in
  
  write_proof_and_check fmt ~check name_proof ptype pterm  
  

(* Generate the LFSC proof of invariance for the original properties and write
   it in the file [!proofname]. *)
let generate_inv_proof inv =

  let proof_file = Filename.concat inv.dirname proofname in
  let proof_chan = open_out proof_file in
  let proof_fmt = formatter_of_out_channel proof_chan in

  set_margin proof_fmt;

  fprintf proof_fmt
    ";;------------------------------------------------------------------\n\
     ;; LFSC proof produced by %s %s and\n\
     ;; %s\n\
     ;; from original problem %s\n\
     ;;------------------------------------------------------------------\n@."
    Version.package_name Version.version
    (get_cvc4_version ())
    (Flags.input_file ());

  
  Debug.certif "Extracting LFSC contexts from CVC4 proofs";
  
  let ctx_k2 = context_from_file inv.for_system.smt2_lfsc_trace_file in
  fprintf proof_fmt ";; System generated by Kind 2\n@.%a\n@."
    print_context ctx_k2;

  let ctx_phi = context_from_file inv.phi_lfsc_trace_file in
  fprintf proof_fmt ";; k-Inductive invariant for Kind 2 system\n@.%a\n@."
    print_defs ctx_phi;

  let ctx = ctx_phi
            |> merge_contexts ctx_k2
  in
  
  Debug.certif "Extracting LFSC proof of base case from CVC4";
  let base_proof = proof_from_file ctx inv.base in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) base_proof.proof_context;
  fprintf proof_fmt ";; Proof of base case\n@.%a\n@."
    (print_proof s_base) base_proof;

  Debug.certif
    "Extracting LFSC proof of inductive case from CVC4";
  let induction_proof = proof_from_file ctx inv.induction in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) induction_proof.proof_context;
  fprintf proof_fmt ";; Proof of inductive case\n@.%a\n@."
    (print_proof s_induction) induction_proof;

  Debug.certif
    "Extracting LFSC proof of implication from CVC4";
  let implication_proof = proof_from_file ctx inv.implication in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) implication_proof.proof_context;
  fprintf proof_fmt ";; Proof of implication\n@.%a\n@."
    (print_proof s_implication) implication_proof;

  fprintf proof_fmt ";; Proof of invariance by %d-induction\n@." inv.k;
  write_inv_proof proof_fmt
    (s_implication, s_base, s_induction) proof_inv_name inv;
  
  close_out proof_chan;
  (* Show which file contains the proof *)
  Debug.certif "LFSC proof written in %s" proof_file;

  log_trusted ~frontend:false ()


(* Generate the LFSC proof of safey by producing an intermediate proofs of
   observational equivalence for the frontend. The proof is written in the file
   [!frontend_proofname]. *)
let generate_frontend_proof inv =

  let proof_file = Filename.concat inv.dirname frontend_proofname in
  let proof_chan = open_out proof_file in
  let proof_fmt = formatter_of_out_channel proof_chan in

  set_margin proof_fmt;

  fprintf proof_fmt
    ";;------------------------------------------------------------------\n\
     ;; LFSC proof produced by %s %s and\n\
     ;; %s\n\
     ;; for frontend observational equivalence and safety\n\
     ;; (depends on proof.lfsc)\n\
     ;;------------------------------------------------------------------\n@."
    Version.package_name Version.version
    (get_cvc4_version ()) ;


  let ctx_jk = context_from_file inv.jkind_system.smt2_lfsc_trace_file in
  fprintf proof_fmt ";; System generated by JKind\n@.%a\n@."
    print_context ctx_jk;

  let ctx_obs = context_from_file inv.obs_system.smt2_lfsc_trace_file in
  fprintf proof_fmt ";; System generated for Observer\n@.%a\n@."
    print_defs ctx_obs;

  let ctx_phi = context_from_file inv.phi_lfsc_trace_file in
  fprintf proof_fmt ";; k-Inductive invariant for observer system\n@.%a\n@."
    print_defs ctx_phi;

  let ctx_k2 = context_from_file inv.kind2_system.smt2_lfsc_trace_file in

  let ctx = ctx_phi
            |> merge_contexts ctx_obs
            |> merge_contexts ctx_jk
            |> merge_contexts ctx_k2
  in
  
  Debug.certif
    "Extracting LFSC frontend proof of base case from CVC4";
  let base_proof = proof_from_file ctx inv.base in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) base_proof.proof_context;
  fprintf proof_fmt ";; Proof of base case\n@.%a\n@."
    (print_proof obs_base) base_proof;

  Debug.certif
    "Extracting LFSC frontend proof of inductive case from CVC4";
  let induction_proof = proof_from_file ctx inv.induction in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) induction_proof.proof_context;
  fprintf proof_fmt ";; Proof of inductive case\n@.%a\n@."
    (print_proof obs_induction) induction_proof;

  Debug.certif
    "Extracting LFSC frontend proof of implication from CVC4";
  let implication_proof = proof_from_file ctx inv.implication in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) implication_proof.proof_context;
  fprintf proof_fmt ";; Proof of implication\n@.%a\n@."
    (print_proof obs_implication) implication_proof;

  fprintf proof_fmt ";; Proof of invariance by %d-induction\n@." inv.k;
  write_inv_proof proof_fmt ~check:false
    (obs_implication, obs_base, obs_induction) proof_obs_name inv;

  fprintf proof_fmt ";; Proof of observational equivalence\n@.";
  write_obs_eq_proof proof_fmt ~check:false
    proof_obs_name proof_obs_eq_name inv;

  fprintf proof_fmt ";; Final proof of safety\n@.";
  write_safe_proof proof_fmt proof_inv_name proof_obs_eq_name
    proof_safe_name inv.kind2_system inv.jkind_system;
  
  close_out proof_chan;
  (* Show which file contains the proof *)
  Debug.certif "LFSC proof written in %s" proof_file;

  log_trusted ~frontend:true ()
