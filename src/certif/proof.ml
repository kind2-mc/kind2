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
module SMT : SolverDriver.S = GenericSMTLIBDriver

(* Hard coded options *)

let debug = List.mem "certif" (Flags.debug ())
let compact = not debug
let set_margin fmt = pp_set_margin fmt (if compact then max_int else 80)

(* disable the preprocessor and tell cvc5 to dump proofs *)
let cvc5_proof_args () =
  let args = ["--lang=smt2"; "--simplification=none"; "--dump-proofs"; "--proof-format=lfsc"] in
  let args =
    if Flags.Certif.smaller_holes () then
      "--proof-granularity=theory-rewrite" :: "--lfsc-expand-trust" :: args
    else
      args
  in
  let args =
    if Flags.Certif.flatten_proof () then
      "--lfsc-flatten" :: args
    else
      args
  in
  List.rev args

let cvc5_proof_cmd () =
  String.concat " " (Flags.Smt.cvc5_bin () :: cvc5_proof_args ())


let get_cvc5_version () =
  let cmd = Flags.Smt.cvc5_bin () ^ " --version" in
  let s = syscall cmd in
  let n = String.index s '\n' in
  let start = 8 in
  String.sub s start (n - start)

(* LFSC symbols *)

let s_declare = H.mk_hstring "declare"
let s_define = H.mk_hstring "define"
let s_lemma = H.mk_hstring "lemma"

let s_holds = H.mk_hstring "holds"

(* let s_iff = H.mk_hstring "iff" *)
(* let s_true = H.mk_hstring "true" *)
let s_false = H.mk_hstring "false"

let s_trust = H.mk_hstring "trust"

(* let s_term = H.mk_hstring "term" *)

(* let s_eq = H.mk_hstring "=" *)

(* let s_apply = H.mk_hstring "apply" *)

let s_check = H.mk_hstring "check"
let s_ascr = H.mk_hstring ":"
(* let s_lambda = H.mk_hstring "#" *)
let s_at = H.mk_hstring "@"
let s_hole = H.mk_hstring "_"


let s_unsat = H.mk_hstring "unsat"
let s_sat = H.mk_hstring "sat"
let s_unknown = H.mk_hstring "unknown"


let global_logic = ref `None

let set_proof_logic l = global_logic := l
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
let trustfname = "trusted.lfsc"


let hstring_of_int i = H.mk_hstring (string_of_int i)


let hole = HS.Atom s_hole

(* LFSC types (sexpressions) *)
type lfsc_type = HS.t

(* LFSC terms (sexpressions) *)
type lfsc_term = HS.t


(* Type of LFSC declarations *)
type lfsc_decl = {
  decl_symb : H.t;
  decl_type : lfsc_type;
}

(* Type of LFSC definitions *)
type lfsc_def = {
  def_symb : H.t;
  def_body : lfsc_term;
}

(* Type of LFSC lemmas *)
type lfsc_lem = {
  lem_symb : H.t;
  lem_ty: lfsc_type;
  lem_body : lfsc_term;
}

(* Comparison for equality of declarations *)
(* let equal_decl d1 d2 =
  H.equal d1.decl_symb d2.decl_symb &&
  HS.equal d1.decl_type d2.decl_type *)

(* Comparison for equality of definitions *)
(* let equal_def d1 d2 =
  let def_ty_eq ot1 ot2 =
    match (ot1, ot2) with Some t1, Some t2 -> HS.equal t1 t2 | _, _ -> true
  in
  H.equal d1.def_symb d2.def_symb
  && def_ty_eq d1.def_ty d2.def_ty
  && HS.equal d1.def_body d2.def_body *)
(* add args if needed *)

(* Type of contexts for proofs *)
type cvc5_proof_context = {
  lfsc_decls : lfsc_decl list;
  lfsc_defs : lfsc_def list;
}

(* Empty context *)
let mk_empty_proof_context () = {
  lfsc_decls = [];
  lfsc_defs = [];
}

(* The type of a proof returned by cvc5 *)
type cvc5_proof = {
  proof_context : cvc5_proof_context;
  proof_temps : lfsc_def list;
  proof_hyps : lfsc_decl list;
  proof_lems : lfsc_lem list;
  proof_type : lfsc_type option;
  proof_term : lfsc_term;
}

(* Create an empty proof from a context *)
let mk_empty_proof ctx = {
  proof_context = ctx;
  proof_temps = [];
  proof_hyps = [];
  proof_lems = [];
  proof_type = None;
  proof_term = HS.List [];
}


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


(* print the optional type of a symbol for its LFSC definition *)
let print_option_def_type fmt = function
  | None -> ()
  | Some ty -> print_type fmt ty


(* Print an LFSC definition with type information *)
let print_def fmt { def_symb; def_body } =
  fprintf fmt "@[<hov 1>(define@ %a@ @[<hov 1>%a@])@]" H.pp_print_hstring
    def_symb
    print_term def_body

(* Print an LFSC lemma with type information *)
(* let print_lem fmt { lem_symb; lem_body } =
  fprintf fmt "@[<hov 1>(lemma@ %a@ @[<hov 1>%a@])@]" H.pp_print_hstring
    lem_symb
    print_term lem_body *)

let print_lem fmt { lem_symb; lem_ty; lem_body } =
  fprintf fmt "@[<hov 1>(check@ @[<hov 1>(: %a %a)@])@]"
    print_type lem_ty
    print_term lem_body;
  fprintf fmt "@.";
  fprintf fmt "@[<hov 1>(declare@ %a@ @[<hov 1>%a@])@]" H.pp_print_hstring
    lem_symb
    print_term lem_ty

(* Print a proof context *)
let print_context fmt { lfsc_decls; lfsc_defs } =
  List.iter (fprintf fmt "%a@." print_decl) (List.rev lfsc_decls);
  fprintf fmt "@.";
  List.iter (fprintf fmt "%a\n@." print_def) lfsc_defs;
  fprintf fmt "@."

(* Print only definitions of a proof context *)
(* let print_defs fmt { lfsc_defs } =
  List.iter (fprintf fmt "%a\n@." print_def) lfsc_defs;
  fprintf fmt "@." *)

(* Print extra declarations/definitions of a context.
   [print_delta_context ctx_old fmt ctx_new] prints the elements of [ctx_new]
   that do not appear in [ctx_old]. *)
let print_delta_context { lfsc_decls = old_decls; lfsc_defs = old_defs } fmt
    { lfsc_decls; lfsc_defs } =
  List.iter
    (fun d ->
      if
        not (List.exists (fun od -> H.equal od.decl_symb d.decl_symb) old_decls)
      then fprintf fmt "%a@." print_decl d)
    (List.rev lfsc_decls);
  List.iter
    (fun dl ->
      if
        not (List.exists (fun odl -> H.equal odl.def_symb dl.def_symb) old_defs)
      then fprintf fmt "%a\n@." print_def dl)
    lfsc_defs


(* Print the type of an hypothesis with its name *)
let rec print_hyps_type ty fmt = function
  | [] -> print_type fmt ty
  | { decl_symb; decl_type } :: rhyps ->
    fprintf fmt "@[<hov 0>(! %a@ %a@ %a)@]"
      H.pp_print_hstring decl_symb
      print_type decl_type
      (print_hyps_type ty) rhyps

(* Print a proof term type with an ascription if it's specified *)
let print_proof_type hyps fmt = function
  | None -> ()
  | Some t -> fprintf fmt ": @[<hov 0>%a@]@ " (print_hyps_type t) hyps

(* Print a proof term as lambda abstraction over its hypostheses *)
let rec print_proof_term term fmt = function
  | [] -> print_term fmt term
  | { decl_symb; _ } :: rhyps ->
    fprintf fmt "@[<hov 0>(\\ %a@ %a)@]"
      H.pp_print_hstring decl_symb
      (print_proof_term term) rhyps


(* Print an LFSC proof *)
let print_proof ?(context = false) name fmt
    { proof_context; proof_temps; proof_hyps; proof_lems; proof_type; proof_term } =
  if context then print_context fmt proof_context;
  fprintf fmt "@.";
  List.iter (fprintf fmt "%a@." print_def) (List.rev proof_temps);
  fprintf fmt "@.";
  List.iter (fprintf fmt "%a@." print_decl) (List.rev proof_hyps);
  fprintf fmt "@.";
  List.iter (fprintf fmt "%a@." print_lem) (List.rev proof_lems);
  fprintf fmt "@.";
  fprintf fmt "@[<hov 1>(define %s@ @[<hov 1>(%a%a)@])@]"
    (H.string_of_hstring name)
    (print_proof_type proof_hyps)
    proof_type
    (print_proof_term proof_term)
    proof_hyps


(*********************************)
(* Parsing LFSC proofs from cvc5 *)
(*********************************)


(* Apply a substitution top to bottom in an LFSC expression *)
let rec apply_subst sigma sexp =
  let open HS in
  try List.find (fun (s,_) -> HS.equal sexp s) sigma |> snd
  with Not_found ->
    match sexp with
    | List l ->
      let l' = List.rev_map (apply_subst sigma) l |> List.rev in
      if List.for_all2 (==) l l' then sexp
      else List l'
    | Atom _ -> sexp

(* Apply to a list of LFSC expressions *)
let rec apply_substs sigma = List.map (apply_subst sigma)


(* Returns list of admitted holes, i.e. formulas whose validity is trusted *)
let rec extract_trusts acc = let open HS in
  function
  | List [Atom a; f] when a == s_trust -> f :: acc
  | Atom _ -> acc
  | List l -> extract_trusts_list acc l
                
and extract_trusts_list acc =
  function
  | [] -> acc
  | x :: r -> extract_trusts_list (extract_trusts acc x) r 


let trusted = ref []

let register_trusts f = trusted := extract_trusts !trusted f

let log_trusted ~frontend dirname =
  if Flags.Certif.log_trust () && !trusted <> [] then begin

    let o_flags =
      if frontend then [Open_wronly; Open_append; Open_text]
      else [Open_wronly; Open_creat; Open_trunc; Open_text]
    in
    let trust_file = Filename.concat dirname trustfname in
    let trust_chan = open_out_gen o_flags 0o666 trust_file in
    let trust_fmt = formatter_of_out_channel trust_chan in
    
    KEvent.log L_warn
      "%s proof contains %d trusted assumptions.@."
      (if frontend then "Frontend" else "Invariance")
      (List.length !trusted);
    fprintf trust_fmt ";; Trusted assumptions in %s proof\n@."
      (if frontend then "frontend" else "invariance");
    List.iter
      (fprintf trust_fmt
         "(check (: @[<hov 2>(th_holds %a)@]@\n  \
          ;; Replace the following by an actual proof@\n  \
          change_me@\n\
          ))@\n@." (HS.pp_print_sexpr_indent 0))
      !trusted;

    close_out trust_chan

  end


exception ProofParseError of string

let extract_proof_type = function
  | HS.List [HS.Atom (ascr); ty; term] when ascr = s_ascr -> ty, term
  | t -> raise (ProofParseError ("Could not extract type of " ^ HS.string_of_sexpr t))


(***********************)
(* Parsing proof terms *)
(***********************)

(* Parse a proof from cvc5, returns a [!cvc_proof] object *)
let rec parse_proof acc prefix =
  let open HS in
  let ctx = acc.proof_context in
  function
  | List [ Atom dec; Atom s; t ] :: r when dec == s_declare && (Lib.string_starts_with (H.string_of_hstring s) "cvc.") ->
      let ctx =
        if List.exists (fun decl -> H.equal decl.decl_symb s) ctx.lfsc_decls
        then ctx
        else
          let decl = { decl_symb = s; decl_type = t } in
          { ctx with lfsc_decls = decl :: ctx.lfsc_decls }
      in
      parse_proof { acc with proof_context = ctx } prefix r
  | List [ Atom dec; Atom s; t ] :: r when dec == s_declare ->
      let s' = (H.mk_hstring (prefix ^ "." ^ (H.string_of_hstring s))) in
      let hyp =
        { decl_symb = s'; decl_type = t }
      in
      parse_proof { acc with proof_hyps = hyp :: acc.proof_hyps; proof_context = ctx } prefix (apply_substs [(Atom s, Atom s')] r)
  | List [ Atom def; Atom s; b ] :: r when def == s_define && (Lib.string_starts_with (H.string_of_hstring s) "cvc.") ->
      let ctx =
        if List.exists (fun def -> H.equal def.def_symb s) ctx.lfsc_defs then
          ctx
        else
          let def =
            { def_symb = s; def_body = b }
          in
          { ctx with lfsc_defs = def :: ctx.lfsc_defs }
      in
      parse_proof { acc with proof_context = ctx } prefix r
  | List [ Atom def; Atom s; b ] :: r when def == s_define ->
      let s' = (H.mk_hstring (prefix ^ "." ^ (H.string_of_hstring s))) in
      let temp =
        { def_symb = s'; def_body = b }
      in
      parse_proof { acc with proof_temps = temp :: acc.proof_temps; proof_context = ctx } prefix (apply_substs [(Atom s, Atom s')] r)
  | List [ Atom check; p ] :: List [_; Atom s; _ ] :: r when check == s_check ->
      let s' = (H.mk_hstring (prefix ^ "." ^ (H.string_of_hstring s))) in
      let ty, p = extract_proof_type p in
      let lem =
        { lem_symb = s'; lem_ty = ty; lem_body = p }
      in
      parse_proof { acc with proof_lems = lem :: acc.proof_lems; proof_context = ctx } prefix (apply_substs [(Atom s, Atom s')] r)
  | [ List (Atom check :: [ pterm ]) ] when check == s_check ->
      let ctx = { ctx with lfsc_defs = List.rev ctx.lfsc_defs } in
      if Flags.Certif.log_trust () then register_trusts pterm;
      let ty, pterm = if Flags.Certif.flatten_proof () then let r = extract_proof_type pterm in Some (fst r), snd r else None, pterm in
      { acc with proof_context = ctx; proof_type = ty; proof_term = pterm }
  | s ->
      failwith
        (asprintf "parse_proof: Unexpected proof:\n%a@." HS.pp_print_sexpr_list
           s)


(* Parse a proof from cvc5 from one that start with [(check ...]. *)
let parse_proof_check ctx prefix = parse_proof (mk_empty_proof ctx) prefix


(* Parse a proof from cvc5 from a channel. cvc5 returns the proof after
   displaying [unsat] on the channel. *)
let proof_from_chan ctx prefix in_ch =

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in
  let open HS in
  
  match sexps with
  
    | [Atom a] when a == s_sat || a == s_unknown ->
      failwith (sprintf "Certificate cannot be checked by smt solver (%s)@."
                  (H.string_of_hstring a))

    | [Atom a] ->
      failwith (sprintf "No proofs, instead got:\n%s@." (H.string_of_hstring a))

    | Atom u :: proof when u == s_unsat ->

      parse_proof_check ctx prefix proof

    | _ ->
      failwith (asprintf "No proofs, instead got:\n%a@."
                  HS.pp_print_sexpr_list sexps)



(* Call cvc5 in proof production mode on an SMT2 file and return the proof *)
let proof_from_file ctx prefix f =
  let cmd = cvc5_proof_cmd () ^ " " ^ f in
  (* Format.eprintf "CMD: %s@." cmd ; *)
  let ic, oc, err = Unix.open_process_full cmd (Unix.environment ()) in
  try
    let proof = proof_from_chan ctx prefix ic in
    ignore(Unix.close_process_full (ic, oc, err));
    proof
  with Failure _ as e ->
    KEvent.log L_fatal "Could not parse cvc5 proof.";
    (match Unix.close_process_full (ic, oc, err) with
     | Unix.WEXITED 0 -> ()
     | Unix.WSIGNALED i | Unix.WSTOPPED  i | Unix.WEXITED i ->
       KEvent.log L_fatal "cvc5 crashed with exit code %d." i);
    raise e


(******************************************)
(* Parsing context from dummy lfsc proofs *)
(******************************************)

(* Parse a context from a dummy proof used only for tracing *)
let rec parse_context ctx =
  let open HS in
  function
  | List [ Atom dec; Atom s; t ] :: r when dec == s_declare ->
      if (Lib.string_starts_with (H.string_of_hstring s) "cvc.") then
        let decl = { decl_symb = s; decl_type = t } in
        parse_context { ctx with lfsc_decls = decl :: ctx.lfsc_decls } r
      else
        parse_context ctx r
  | List [ Atom def; Atom s; b ] :: r when def == s_define ->
      let def = { def_symb = s; def_body = b } in
      parse_context { ctx with lfsc_defs = def :: ctx.lfsc_defs } r
  | [ List (Atom check :: _) ] when check == s_check ->
      { ctx with lfsc_defs = List.rev ctx.lfsc_defs }
  | s ->
      failwith
        (asprintf "parse_context: Unexpected proof:\n%a@."
           HS.pp_print_sexpr_list s)


(* Parse a context from a dummy proof check used only for tracing *)
let parse_context_dummy = parse_context (mk_empty_proof_context ())


(* Parse a context from a channel. The goal is trivial because the file
   contains "(assert false)" but we care about the hypotheses to recontruct the
   LFSC definitions inlined by cvc5. *)
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

    | Atom u :: dummy_proof when u == s_unsat ->

      parse_context_dummy dummy_proof

    | _ ->
      failwith (asprintf "No proofs, instead got:\n%a@."
                  HS.pp_print_sexpr_list sexps)



(* Call cvc5 on a file that contains only tracing information and parse the
   dummy proof to extract the context (declarations and definitions). *)
let context_from_file f =
  let cmd = cvc5_proof_cmd () ^ " " ^ f in
  let ic, oc, err = Unix.open_process_full cmd (Unix.environment ()) in
  try
    let ctx = context_from_chan ic in
    (* printf "Parsed context:\n%a@." print_context ctx; *)
    ignore(Unix.close_process_full (ic, oc, err));
    ctx
  with Failure _ as e ->
    KEvent.log L_fatal "Could not parse cvc5 context.";
    (match Unix.close_process_full (ic, oc, err) with
     | Unix.WEXITED 0 -> ()
     | Unix.WSIGNALED i | Unix.WSTOPPED  i | Unix.WEXITED i ->
       KEvent.log L_fatal "cvc5 crashed with exit code %d." i);
    raise e

(* Merge two contexts. Note: this is a shallow operation that returns `ctx1`
   with `ctx2` decls/defs whose symbol is not in `ctx1` ignoring types/
   bodies. *)
let merge_contexts ctx1 ctx2 =
  let decl_pred acc decl =
    if List.exists (fun decl' -> H.equal decl'.decl_symb decl.decl_symb) acc
    then acc
    else decl :: acc
  in
  let def_pred acc def =
    if List.exists (fun def' -> H.equal def'.def_symb def.def_symb) acc then acc
    else def :: acc
  in
  {
    lfsc_decls =
      List.rev
        (List.fold_left decl_pred (List.rev ctx1.lfsc_decls) ctx2.lfsc_decls);
    lfsc_defs =
      List.rev
        (List.fold_left def_pred (List.rev ctx1.lfsc_defs) ctx2.lfsc_defs);
  }

(* Intersect two contexts. Note: this is a shallow operation that removes decls/
   defs in `ctx1` whose symbol appear in `ctx2` ignoring types/bodies. *)
let intersect_contexts ctx1 ctx2 =
  let decl_pred decl =
    List.exists
      (fun decl' -> H.equal decl'.decl_symb decl.decl_symb)
      ctx2.lfsc_decls
  in
  let def_pred def =
    List.exists (fun def' -> H.equal def'.def_symb def.def_symb) ctx2.lfsc_defs
  in
  {
    lfsc_decls = List.filter decl_pred ctx1.lfsc_decls;
    lfsc_defs = List.filter def_pred ctx1.lfsc_defs;
  }

(* Pretty-print a sort *)
let rec pp_print_sort ppf t =
  let t = SMT.interpr_type t in
  (* Print array types with an abstract sort *)
  match Type.node_of_type t with
  | Type.Array (te, ti) ->
    if Flags.Arrays.smt () then
      Format.fprintf ppf "(Array %a %a)" pp_print_sort ti pp_print_sort te
    else
      Format.fprintf ppf "(cvc.FArray %a %a)" pp_print_sort ti pp_print_sort te
  | Abstr s -> Format.pp_print_string ppf ("cvc." ^ s)
  | UBV i | BV i -> Format.fprintf ppf "(BitVec %d)" i
  | _ -> Type.pp_print_type ppf t

(* Return a string representation of a sort *)
let string_of_sort = string_of_t pp_print_sort

(* Generate a simple context with custom indexing of variables to avoid index
   clashes between proofs generated by cvc5 *)
let context_from_vars vars =
  let to_decl i v =
    let rec sexp_of_sort arg_sorts res_sort =
      match arg_sorts with
      | [] -> HS.Atom (H.mk_hstring (string_of_sort res_sort))
      | arg_sort :: arg_sorts ->
          HS.List
            [
              HS.Atom (H.mk_hstring "arrow");
              HS.Atom (H.mk_hstring (string_of_sort arg_sort));
              sexp_of_sort arg_sorts res_sort;
            ]
    in
    let symb = UfSymbol.name_of_uf_symbol v in
    let arg_sorts = UfSymbol.arg_type_of_uf_symbol v in
    let res_sort = UfSymbol.res_type_of_uf_symbol v in
    let sort =
      HS.List
        [
          HS.Atom (H.mk_hstring "var");
          HS.Atom (H.mk_hstring (string_of_int i));
          sexp_of_sort arg_sorts res_sort;
        ]
    in
    {
      def_symb = H.mk_hstring ("cvc." ^ symb);
      def_body = sort;
    }
  in
  { (mk_empty_proof_context ()) with lfsc_defs = List.mapi to_decl vars }

let context_from_file f =
  Stat.start_timer Stat.certif_cvc5_time;
  let c = context_from_file f in
  Stat.record_time Stat.certif_cvc5_time;
  c
  
let proof_from_file prefix f =
  Stat.start_timer Stat.certif_cvc5_time;
  let p = proof_from_file prefix f in
  Stat.record_time Stat.certif_cvc5_time;
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
  let a_k = List [Atom (H.mk_hstring "int"); Atom (hstring_of_int c.k)] in
  let a_init = Atom (H.mk_hstring ("cvc." ^ c.for_system.names.init)) in
  let a_trans = Atom (H.mk_hstring ("cvc." ^ c.for_system.names.trans)) in
  let a_prop = Atom (H.mk_hstring ("cvc." ^ c.for_system.names.prop)) in
  let a_phi = Atom (H.mk_hstring ("cvc." ^ c.for_system.names.phi)) in

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
let write_obs_eq_proof fmt ?(check=true) proof_obs_name name_proof i a b c d =
  
  let open HS in

  (* LFSC atoms for formulas *)
  let a_init_1 = Atom (H.mk_hstring ("cvc." ^ i.kind2_system.names.init)) in
  let a_trans_1 = Atom (H.mk_hstring ("cvc." ^ i.kind2_system.names.trans)) in
  let a_prop_1 = Atom (H.mk_hstring ("cvc." ^ i.kind2_system.names.prop)) in

  let a_init_2 = Atom (H.mk_hstring ("cvc." ^ i.jkind_system.names.init)) in
  let a_trans_2 = Atom (H.mk_hstring ("cvc." ^ i.jkind_system.names.trans)) in
  let a_prop_2 = Atom (H.mk_hstring ("cvc." ^ i.jkind_system.names.prop)) in


  (* LFSC commands to construct the proof *)
  let a_obs_eq = Atom s_obs_eq in
  let a_weak_obs_eq = Atom s_weak_obs_eq in
  let a_same_inputs = Atom (H.mk_hstring "cvc.same_inputs") in

  (* named prood of obsercational equivalence *)
  let proof_obs = Atom proof_obs_name in

  let pterm = 
    List [a_obs_eq;
          a_init_1; a_trans_1; a_prop_1;
          a_init_2; a_trans_2; a_prop_2;
          a; b; c; d;
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
let write_safe_proof fmt ?(check=true) kind2_s jkind_s =
  let open HS in

  (* LFSC atoms for formulas *)
  let a_init = Atom (H.mk_hstring ("cvc." ^ kind2_s.names.init)) in
  let a_trans = Atom (H.mk_hstring ("cvc." ^ kind2_s.names.trans)) in
  let a_prop = Atom (H.mk_hstring ("cvc." ^ kind2_s.names.prop)) in

  let a_init' = Atom (H.mk_hstring ("cvc." ^ jkind_s.names.init)) in
  let a_trans' = Atom (H.mk_hstring ("cvc." ^ jkind_s.names.trans)) in
  let a_prop' = Atom (H.mk_hstring ("cvc." ^ jkind_s.names.prop)) in

  (* LFSC commands to construct the proof *)
  let a_inv_obs = Atom s_inv_obs in
  let a_safe = Atom s_safe in

  (* Prior LFSC proofs *)
  let proof_inv = Atom proof_inv_name in
  let proof_obs_eq = Atom proof_obs_eq_name in

  let pterm =
    List [a_inv_obs;
          a_init; a_trans; a_prop;
          a_init'; a_trans'; a_prop';
          proof_inv; proof_obs_eq]
  in
  let ptype = List [a_safe; a_init; a_trans; a_prop] in
  
  write_proof_and_check fmt ~check proof_safe_name ptype pterm  
  

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
    (get_cvc5_version ())
    (Flags.input_file ());

  Debug.certif "Declaring variables for LFSC contexts";

  let ctx_vars = context_from_vars inv.kind2_system.names.vars in

  Debug.certif "Extracting LFSC contexts from cvc5 proofs";
  
  let ctx_k2 = context_from_file inv.for_system.smt2_lfsc_trace_file in
  fprintf proof_fmt ";; System generated by Kind 2\n@.%a\n@."
  print_context (merge_contexts ctx_vars ctx_k2);

  let ctx_phi = context_from_file inv.phi_lfsc_trace_file in
  fprintf proof_fmt ";; k-Inductive invariant for Kind 2 system\n@.%a\n@."
  (print_delta_context ctx_k2) ctx_phi;

  let ctx = ctx_phi
            |> merge_contexts ctx_k2
            |> merge_contexts ctx_vars
  in
  
  Debug.certif "Extracting LFSC proof of base case from cvc5";
  let base_proof = proof_from_file ctx "inv.base" inv.base in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) base_proof.proof_context;
  fprintf proof_fmt ";; Proof of base case\n@.%a\n@."
    (print_proof s_base) base_proof;

  Debug.certif
    "Extracting LFSC proof of inductive case from cvc5";
  let induction_proof = proof_from_file ctx "inv.ind" inv.induction in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) induction_proof.proof_context;
  fprintf proof_fmt ";; Proof of inductive case\n@.%a\n@."
    (print_proof s_induction) induction_proof;

  Debug.certif
    "Extracting LFSC proof of implication from cvc5";
  let implication_proof = proof_from_file ctx "inv.imp" inv.implication in
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

  log_trusted ~frontend:false inv.dirname;

  let decl_syms = List.map (fun decl -> decl.decl_symb) ctx.lfsc_decls in
  let def_syms = List.map (fun def -> def.def_symb) ctx.lfsc_defs in
  decl_syms @ def_syms


let get_itp_binders ctx =
  let is_sym sym lfsc_def =
    match lfsc_def.def_symb with
    | sym' when H.equal sym' (H.mk_hstring sym) -> true
    | _ -> false
  in
  let i = List.find (is_sym "cvc.IO") ctx.lfsc_defs in
  let t = List.find (is_sym "cvc.TO") ctx.lfsc_defs in
  let p = List.find (is_sym "cvc.PO") ctx.lfsc_defs in
  let s_lambda = H.mk_hstring "lambda" in
  let rec find_lambda_binders n =
    let open HS in
    function
    | List (Atom at :: _ :: _ :: [ r ]) when at == s_at ->
        find_lambda_binders n r
    | List (List [ Atom lam; i; _ ] :: [ r ]) when lam == s_lambda ->
        i :: (if n == 1 then [] else find_lambda_binders (n - 1) r)
    | _ -> []
  in
  let error f =
    raise
      (ProofParseError
         ("Could not parse " ^ f ^ " definition in the proof generated by cvc5"))
  in
  let a =
    match find_lambda_binders 1 i.def_body with
    | [ a ] -> a
    | _ -> error "cvc.IO"
  in
  let b, c =
    match find_lambda_binders 2 t.def_body with
    | [ b; c ] -> (b, c)
    | _ -> error "cvc.TO"
  in
  let d =
    match find_lambda_binders 1 p.def_body with
    | [ d ] -> d
    | _ -> error "cvc.PO"
  in
  (a, b, c, d)


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
    (get_cvc5_version ()) ;

  let ctx_vars =
    context_from_vars (inv.kind2_system.names.vars @ inv.jkind_system.names.vars)
  in

  let ctx_jk = context_from_file inv.jkind_system.smt2_lfsc_trace_file in
  let ctx_obs = context_from_file inv.obs_system.smt2_lfsc_trace_file in

  fprintf proof_fmt ";; System generated by JKind\n@.%a\n@."
  print_context (intersect_contexts (merge_contexts ctx_vars ctx_obs) ctx_jk);

  fprintf proof_fmt ";; System generated for Observer\n@.%a\n@."
  (print_delta_context (merge_contexts ctx_vars ctx_jk)) ctx_obs;

  let ctx_phi = context_from_file inv.phi_lfsc_trace_file in
  fprintf proof_fmt ";; k-Inductive invariant for observer system\n@.%a\n@."
  (print_delta_context (merge_contexts ctx_jk ctx_obs)) ctx_phi;

  let ctx_k2 = context_from_file inv.kind2_system.smt2_lfsc_trace_file in

  let ctx = ctx_phi
            |> merge_contexts ctx_obs
            |> merge_contexts ctx_jk
            |> merge_contexts ctx_k2
            |> merge_contexts ctx_vars
  in
  
  Debug.certif
    "Extracting LFSC frontend proof of base case from cvc5";
  let base_proof = proof_from_file ctx "front.base" inv.base in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) base_proof.proof_context;
  fprintf proof_fmt ";; Proof of base case\n@.%a\n@."
    (print_proof obs_base) base_proof;

  Debug.certif
    "Extracting LFSC frontend proof of inductive case from cvc5";
  let induction_proof = proof_from_file ctx "front.ind" inv.induction in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) induction_proof.proof_context;
  fprintf proof_fmt ";; Proof of inductive case\n@.%a\n@."
    (print_proof obs_induction) induction_proof;

  Debug.certif
    "Extracting LFSC frontend proof of implication from cvc5";
  let implication_proof = proof_from_file ctx "front.imp" inv.implication in
  fprintf proof_fmt ";; Additional symbols@.%a@."
    (print_delta_context ctx) implication_proof.proof_context;
  fprintf proof_fmt ";; Proof of implication\n@.%a\n@."
    (print_proof obs_implication) implication_proof;

  fprintf proof_fmt ";; Proof of invariance by %d-induction\n@." inv.k;
  write_inv_proof proof_fmt ~check:false
    (obs_implication, obs_base, obs_induction) proof_obs_name inv;

  fprintf proof_fmt ";; Proof of observational equivalence\n@.";
  let a, b, c, d = get_itp_binders ctx in
  write_obs_eq_proof proof_fmt ~check:true proof_obs_name proof_obs_eq_name inv
    a b c d;

  close_out proof_chan;

  (* Show which file contains the proof *)
  Debug.certif "LFSC proof written in %s" proof_file;

  log_trusted ~frontend:true inv.dirname
