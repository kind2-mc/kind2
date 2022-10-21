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

open Format
open Lib
open Actlit
open Certificate

module Ids = Lib.ReservedIds

module TS = TransSys
module TM = Term.TermMap
module TH = Term.TermHashtbl
module SVS = StateVar.StateVarSet
module SVH = StateVar.StateVarHashtbl
module IntM = Map.Make (struct type t = int let compare = compare end)
module SMT  : SolverDriver.S = GenericSMTLIBDriver

let global_jkind_vars = ref []


(*************************************************)
(* Hard coded options for certificate generation *)
(*************************************************)
let file_width = 120
let quant_free = true
let monolithic_base = true
let simple_base = false
let clean_tmp = false
let call_frontend = true


let names_bare = {
  vars = [];
  init = "I";
  prop = "P";
  trans = "T";
  phi = "PHI"
}

let names_kind2 vars = {
  vars = vars;
  init = "I1";
  prop = "P1";
  trans = "T1";
  phi = "PHI1"
}

let names_jkind vars = {
  vars = vars;
  init = "I2";
  prop = "P2";
  trans = "T2";
  phi = "PHI2"
}

let names_obs = {
  vars = [];
  init = "IO";
  prop = "PO";
  trans = "TO";
  phi = "PHIO"
}

let obs_defs_f = "observer.smt2"
let obs_defs_lfsc_f = "observer_lfsc_trace.smt2"
let obs_phi_f = "obs_phi.smt2"
let obs_phi_lfsc_f = "obs_phi_lfsc_trace.smt2"

let kind2_defs_f = "kind2_sys.smt2"
let kind2_defs_lfsc_f = "kind2_sys_lfsc_trace.smt2"
let kind2_phi_f = "kind2_phi.smt2"
let kind2_phi_lfsc_f = "kind2_phi_lfsc_trace.smt2"

let jkind_defs_f = "jkind_sys.smt2"
let jkind_defs_lfsc_f = "jkind_sys_lfsc_trace.smt2"

let base_f = "base.smt2"
let induction_f = "induction.smt2"
let implication_f = "implication.smt2"

let frontend_base_f = "frontend_base.smt2"
let frontend_induction_f = "frontend_induction.smt2"
let frontend_implication_f = "frontend_implication.smt2"


let kind2_cert_sys vars dirname = {
  names = names_kind2 vars;
  smt2_file = Filename.concat dirname kind2_defs_f;
  smt2_lfsc_trace_file = Filename.concat dirname kind2_defs_lfsc_f;
}

let jkind_cert_sys vars dirname = {
  names = names_jkind vars;
  smt2_file = Filename.concat dirname jkind_defs_f;
  smt2_lfsc_trace_file = Filename.concat dirname jkind_defs_lfsc_f;
}

let obs_cert_sys dirname = {
  names = names_obs;
  smt2_file = Filename.concat dirname obs_defs_f;
  smt2_lfsc_trace_file = Filename.concat dirname obs_defs_lfsc_f;
}

exception CouldNotProve of (Format.formatter -> unit)


(****************************)
(* Global hconsed constants *)
(****************************)
(*let s_and = Symbol.mk_symbol `AND
let s_or = Symbol.mk_symbol `OR
let s_not = Symbol.mk_symbol `NOT*)


let ty_index () = Type.t_int

let index_sym_of_int i = string_of_int i
    
let index_of_int i = Term.mk_num_of_int i

let t0 = Term.mk_num_of_int 0 (* index_of_int 0 *)
let t1 = Term.mk_num_of_int 1 (* index_of_int 1 *)


(*********************)
(* Utility functions *)
(*********************)

(* Hashtable from activation literal to term *)
(* let hactlits = TH.create 2001 *)

let solver_actlits = Hashtbl.create 2


(* Create an activation literal only if it does not currently exists. In this
   case declare it in the solver and assert its definition. If it exists simply
   get the activatition literal corresponding to the term. In all cases, the
   activation literal is returned at the end. *)
let actlitify ?(imp=false) solver t =
  let solver_id = SMTSolver.id_of_instance solver in
  let hactlits =
    try Hashtbl.find solver_actlits solver_id
    with Not_found ->
      let h = TH.create 2001 in
      Hashtbl.add solver_actlits solver_id h;
      h
  in
  try TH.find hactlits t
  with Not_found ->
    let a = fresh_actlit () in (* was generate actlit before *)
    let ta = term_of_actlit a in
    (* if not (TH.mem hactlits ta) then begin *)
    TH.add hactlits t ta;
    SMTSolver.declare_fun solver a;
    (if imp then Term.mk_implies else Term.mk_eq)
      [ta; t] |> SMTSolver.assert_term solver;
    (* end; *)
    ta

let is_two_state inv =
  match Term.var_offsets_of_term inv with
  | Some lo, Some hi when Numeral.(equal lo hi |> not) -> true
  | _ -> false

let guard_two_state_term_list t v_at_0 =

  let guard_two_state_term t =
    if is_two_state t then
      Term.mk_implies
        [Term.mk_eq [v_at_0; index_of_int 0] |> Term.mk_not; t]
    else t
  in

  match Term.node_of_term t with
  | Term.T.Node (s, l) when Symbol.node_of_symbol s == `AND -> (
    Term.mk_and (List.map guard_two_state_term l)
  )
  | _ -> guard_two_state_term t


(* Transform unrolled state variables back to functions (that take an integer
   as argument) *)
let roll sigma t =

  Term.map (fun _ term ->

    if Term.is_free_var term then

      let v = Term.free_var_of_term term in
      if Var.is_state_var_instance v then

        let sv = Var.state_var_of_state_var_instance v in
        let off = Var.offset_of_state_var_instance v in

        let vf = StateVar.uf_symbol_of_state_var sv in
        let i = Term.mk_num off in
        let arg =
          try TM.find i sigma
          with Not_found ->
            (* find variable v to replace for 0 *)
            let v_at_0 = TM.find t0 sigma in
            (* and return v+i *)
            Term.mk_plus [v_at_0; i]
        in
        Term.mk_uf vf [arg]
      else
      if Var.is_const_state_var v then
        let sv = Var.state_var_of_state_var_instance v in
        let vf = StateVar.uf_symbol_of_state_var sv in
        Term.mk_uf vf []
    else term
    else term

  ) t


(* Create a directory if it does not already exists. *)
let create_dir dir =
  try
    if not (Sys.is_directory dir) then failwith (dir^" is not a directory");
    (* TODO remove directory *)
  with Sys_error _ -> Unix.mkdir dir 0o755


(*************************************************************************)
(* Printing functions for the certificate.                               *)
(* We use the generic SMTLIB pretty printer for that because we want to  *)
(* create SMTLIB2 compliant certificates.                                *)
(*************************************************************************)

let rec split_cmp acc cmp = function
  | [] | [_] -> List.rev acc |> Term.mk_and
  | a :: (b :: _ as l) ->
    let ci = Term.mk_app cmp [a; b] in
    split_cmp (ci :: acc) cmp l

(* Preprocessing of terms for proof producing version of cvc5 *)
let preproc term =
  Term.map (fun _ t -> match Term.node_of_term t with
      | Term.T.Node (cmp, (_::_::_::_ as l)) ->
        begin match Symbol.node_of_symbol cmp with
          | `LEQ | `LT | `GEQ | `GT ->
            split_cmp [] cmp l
          | _ -> t
        end
      | _ -> t
    ) term

(* Assert the expression *)
let assert_expr fmt expr =
  fprintf fmt
    "@[<hv 1>(assert@ @[<hov>%a@])@]@." 
    SMT.pp_print_expr (preproc expr)


(* Declare a new function symbol *)
let declare_fun fmt fun_symbol arg_sorts res_sort =
  fprintf fmt
    "@[<hv 1>(declare-fun@ %s@ @[<hv 1>%s@]@ %a)@]@." 
    fun_symbol
    (paren_string_of_string_list (List.map SMT.string_of_sort arg_sorts))
    SMT.pp_print_sort res_sort


(* Declare a new constant symbol from a uf *)
let declare_const fmt uf =
  let fun_symbol = UfSymbol.name_of_uf_symbol uf in
  let arg_sorts = UfSymbol.arg_type_of_uf_symbol uf in
  let res_sort = UfSymbol.res_type_of_uf_symbol uf in
  declare_fun fmt fun_symbol arg_sorts res_sort


(* Declare a new state variable from a uf *)
let declare_state_var fmt uf =
  let fun_symbol = UfSymbol.name_of_uf_symbol uf in
  assert (UfSymbol.arg_type_of_uf_symbol uf = []);
  let arg_sorts = [(ty_index ())] in
  let res_sort = UfSymbol.res_type_of_uf_symbol uf in
  declare_fun fmt fun_symbol arg_sorts res_sort


(* Declare select functions *)
let declare_selects fmt =
  if not (Flags.Arrays.smt ()) then
    List.iter (declare_const fmt) (StateVar.get_select_ufs ())


(* Define a new function symbol as an abbreviation for an expression *)
let define_fun ?(trace_lfsc_defs=false) fmt fun_symbol arg_vars res_sort defn = 

  fprintf fmt
    "@[<hov 1>(define-fun@ %s@ @[<hv 1>(%a)@]@ %s@ %a)@]\n@." 
    (UfSymbol.string_of_uf_symbol fun_symbol)
    (pp_print_list
       (fun ppf var -> 
          Format.fprintf ppf "(%s %s)" 
            (Var.string_of_var var)
            (SMT.string_of_sort (Var.type_of_var var)))
       "@ ")
    arg_vars
    (SMT.string_of_sort res_sort)
    SMT.pp_print_expr (preproc defn);

  if trace_lfsc_defs then begin

    (* fprintf fmt ";; Tracing artifact for cvc5 and LFSC proofs\n";
    
    let fs = UfSymbol.string_of_uf_symbol fun_symbol in
    let fun_def_sy = fs ^ "%def" in
    fprintf fmt "(declare-fun %s %s %s)\n"
      fun_def_sy
      (paren_string_of_string_list
         (List.map (fun v -> SMT.string_of_sort (Var.type_of_var v)) arg_vars))
      (SMT.string_of_sort res_sort);

    let cpt = ref 0 in
    let fun_def_args = List.map (fun v ->
        incr cpt;
        let ty_v = Var.type_of_var v in
        let vfs = fs ^ "%" ^ string_of_int !cpt in
        fprintf fmt "(declare-fun %s () %s)\n"
          vfs (SMT.string_of_sort ty_v);
        vfs
      ) arg_vars in

    fprintf fmt "@[<hov 1>(assert@ @[<hov 1>(=@ @[<hv 1>(%s@ %a)@]@ @[<hv 1>(%s@ %a)@])@])@]\n@."
      fun_def_sy (pp_print_list pp_print_string "@ ") fun_def_args
      fs (pp_print_list pp_print_string "@ ") fun_def_args *)
    
  end
  

  

(* Solver stack for certificate checker *)
  
let push fmt = fprintf fmt "\n(push 1)@." 

let pop fmt = fprintf fmt "(pop 1)\n@." 

(* Satisfiability checking for the certificate checker *)
let check_sat fmt = fprintf fmt "(check-sat)@." 

let sexit fmt = fprintf fmt "(exit)@." 




(***************************)
(* Certificates extraction *)
(***************************)

let extract_props_terms sys =
  List.fold_left (fun p_acc -> function
      | { Property.prop_term = p } -> p :: p_acc
    ) [] (TS.get_real_properties sys)
  |> List.rev |> Term.mk_and


(* Extract properties and invariants together with their certificates from a
   system. *)
let extract_props_certs sys =

  (* We add certificates of the invariants first,
    because certificates of properties may depend on invariants *)
  let certs, invs = List.fold_left (fun (c_acc, i_acc) (i, c) ->
    (* let (k, p') = c in
    KEvent.log_uncond "[INV] %a -----> %i:%a" Term.pp_print_term i k Term.pp_print_term p' ; *)
    (c :: c_acc, i :: i_acc)
  ) ([], []) (TS.get_invariants sys |> Invs.flatten) in

  let certs, props = List.fold_left (fun ((c_acc, p_acc) as acc) -> function
      | { Property.prop_source = Property.Candidate _ } -> acc
      | { Property.prop_status = Property.PropInvariant c; prop_term = p } ->
        (* let (k,p') = c in
        KEvent.log_uncond "[PROP] %a -----> %i:%a" Term.pp_print_term p k Term.pp_print_term p' ; *)
        (if List.exists (Term.equal p) invs then c_acc else c :: c_acc), p :: p_acc
      | { Property.prop_name } ->
        KEvent.log L_info "Skipping unproved property %s" prop_name;
        acc
    ) (certs, []) (TS.get_real_properties sys) in

  let certs =  List.fold_left (fun certs -> function
      | { Property.prop_status = Property.PropInvariant c;
          prop_source = Property.Candidate _ } -> c :: certs
      | { Property.prop_name } ->
        KEvent.log L_info "Skipping unproved candidate %s" prop_name;
        certs
    ) certs (TS.get_candidate_properties sys) in

  List.rev props, certs



let global_certificate sys =
  let props, certs = extract_props_certs sys in
  Term.mk_and props, Certificate.merge certs




(**************************************************************************)
(* Minimization / simplification of certificates.                         *)
(*                                                                        *)
(* We use an SMT solver to replay the inductive step in order to identify *)
(* what is the minimal bound for k-induction and the smallest set of      *)
(* invariants necessary.                                                  *)
(**************************************************************************)


let create_acts solver k inv =
  let l = ref [inv] in
  for i = 1 to k - 1 do
    l := Term.bump_state (Numeral.of_int i) inv :: !l;
  done;
  let t = Term.mk_and (List.rev !l) in
  let pred_act = actlitify ~imp:true solver t in
  let not_act_k = Term.bump_state (Numeral.of_int k) inv
                  |> Term.mk_not |> actlitify solver in
  (inv, pred_act, not_act_k)


let at_most_one_false solver acts =
  let acts_cptl = List.map (fun t ->
      Term.mk_ite t (Term.mk_num_of_int 0) (Term.mk_num_of_int 1)) acts in
  let acts_sum = Term.mk_plus acts_cptl in
  let c = Term.mk_leq [acts_sum; Term.mk_num_of_int 1] in
  SMTSolver.assert_term solver c


let rec find_must solver must acts q =
  try
    let not_a = Queue.pop q in
    (* eprintf "find_must %d : %a@." (Queue.length q) Term.pp_print_term not_a; *)
    SMTSolver.check_sat_assuming_and_get_term_values solver
      (fun _ term_values -> (* Sat *)
         try
           let inv, ai, not_ai' = List.find (fun (_, ai, _) ->
               let v = List.assq ai term_values in
               Term.equal v (Term.mk_false ())
             ) acts in
           SMTSolver.assert_term solver ai;
           Queue.push not_ai' q;
           find_must solver (inv :: must) acts q
         with Not_found -> find_must solver must acts q
      )
      (fun _ -> (* Unsat *)
         find_must solver must acts q
      )
      [not_a] (List.map (fun (_, ai, _) -> ai) acts)
  with Queue.Empty -> must


let under_approx sys k invs prop =

  let open TermLib in
  let logic = match TransSys.get_logic sys with
    | `None | `SMTLogic _ -> `None
    | `Inferred l -> `Inferred (FeatureSet.add IA l)
  in
  
  let solver =
    SMTSolver.create_instance ~produce_assignments:true
      logic (Flags.Smt.solver ())
  in

  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.(~- one) (Numeral.of_int (k+1));

  (* Declaring path compression function if needed. *)
  if Flags.BmcKind.compress () then
    Compress.init (SMTSolver.declare_fun solver) sys ;

  (* Asserting transition relation up to k *)
  for i = 1 to k do
    TransSys.trans_of_bound
      (Some (SMTSolver.declare_fun solver))
      sys (Numeral.of_int i)
    |> SMTSolver.assert_term solver;
  done;

  (* create activation literals *)
  let acts = List.map (create_acts solver k) invs in

  (* at most one false constraints *)
  List.map (fun (_, ai, _) -> ai) acts |> at_most_one_false solver;

  let _, _, not_p' = create_acts solver k prop in
  let q = Queue.create () in
  Queue.push not_p' q;
  
  let must = find_must solver [] acts q in
  SMTSolver.delete_instance solver;

  must


(* Exception raised to interrupt the computation. A continuation is given to
   resume this computation. *)
exception Reduce_cont of (unit -> Term.t list * Term.t list)


(* Iterative fixpoint to identify which invariants are usefull. Returns the
   subset of invs_acts which preserves inductiveness. The parameter
   just_check_ind controls if we want to only check the induction step without
   minimizing the set of invariants.

   - Raises Exit if the invariants with the property are not inductive.

   - Raises Reduce_cont with a continuation (which miminizes the set of
     invariants) if it was called with ~just_check_ind:true.

   - Returns a subset of invs_acts which preserves inductiveness otherwise.
*)
let rec trim
  solver uinvs_acc invs_acts prev_props_act prop'act neg_prop'act trans_acts =

  let if_sat _ =
    (* this should not happen because we've already performed the inductive
       check *)
    Debug.certif "[Fixpoint] fail (impossible)";
    raise Exit
  in

  let if_unsat _ =
    (* Activation literals in unsat core, extracted right away in case we
       modify the solver state before calling the continuation *)
    let uc = SMTSolver.get_unsat_core_lits solver in

    (* Identify the useful invariants with the unsat core *)
    let uinvs_acts, invs_acts =
      List.partition (fun (a, _) -> List.exists (Term.equal a) uc) invs_acts
    in

    Debug.certif "[Fixpoint] extracted %d useful invariants"
      (List.length uinvs_acts);

    let uinvs, uinvs' = List.split uinvs_acts in

    (* Create activation literals for inductive check *)
    let new_prop = Term.mk_and (prev_props_act :: uinvs) in
    let new_prop_act = actlitify solver new_prop in
    let new_prop_acts = prev_props_act :: uinvs in

    let new_prop' = Term.mk_and (prop'act :: uinvs') in
    let new_prop'act = actlitify solver new_prop' in
    
    let neg_new_prop' = Term.mk_not new_prop' in
    let neg_new_prop'act = actlitify solver neg_new_prop' in

    let uinvs_acc = uinvs' @ uinvs_acc in

    (* Check preservation of invariants by k-steps *)
    SMTSolver.check_sat_assuming solver
      
      (fun _ ->
         (* SAT try to find what invariants are missing *)
         Debug.certif
           "[Fixpoint] could not verify inductiveness";

         trim solver uinvs_acc invs_acts
           new_prop_act new_prop'act neg_new_prop'act trans_acts)
      
      (fun _ ->
         (* UNSAT: return accumulated invariants *)
         Debug.certif "[Fixpoint] OK" ;
         (* (pp_print_list Term.pp_print_term "@ ") acc *)

         (* Return useful invariants (identified by their activation
            literals) *)
         uinvs_acc)

      (trans_acts @ new_prop_acts @ [neg_new_prop'act])
  in
  
  (* Get invariants at k - 1 *)
  let invs = List.map fst invs_acts in

  SMTSolver.trace_comment solver "fixpoint cs;";

  (* Check if the property is preserved by k-steps when assuming the
     invariants *)
  SMTSolver.check_sat_assuming solver if_sat if_unsat
    (trans_acts @ (neg_prop'act :: prev_props_act :: invs))





let rec check_ind_and_trim ~just_check_ind sys k prop invs_terms
    solver invs_acts prev_props_act prop'act neg_prop'act trans_acts =

  (* Get invariants at k - 1 *)
  let invs, invs' = List.split invs_acts in

  let neg_invs'prop'act = prop'act :: invs'
                          |> Term.mk_and |> Term.mk_not |> actlitify solver in
  
  SMTSolver.trace_comment solver "check inductiveness at k;";

  (* Check k-inductiveness of whole set first *)
  SMTSolver.check_sat_assuming solver
    (fun _ -> (* SAT *)

       (* Maybe we need path compression to reprove the invariants *)
       if Flags.BmcKind.compress () then
         let svi = TransSys.get_state_var_bounds sys in
         let model = SMTSolver.get_var_values solver svi
             (TransSys.vars_of_bounds sys Numeral.zero (Numeral.of_int k)) in
         let path = Model.path_from_model (TransSys.state_vars sys) model
             (Numeral.of_int k) in
         match Compress.check_and_block
                 (SMTSolver.declare_fun solver) sys path with
         | [] -> Debug.certif "[Fixpoint] no compression, failure"; raise Exit
         | compressor ->
           let compr_act = actlitify solver (Term.mk_and compressor) in
           (* try again *)
           check_ind_and_trim ~just_check_ind sys k prop invs_terms
             solver invs_acts prev_props_act prop'act neg_prop'act
             (compr_act :: trans_acts)
       else begin
         Debug.certif "[Fixpoint] failure of whole inductive check";
         raise Exit
       end)
    
    (fun _ -> (* UNSAT *)

     (* First cleaning *)    
     let uc = SMTSolver.get_unsat_core_lits solver in
     let invs_acts =
       List.filter (fun (a, _) -> List.exists (Term.equal a) uc) invs_acts in

     let do_under = false in
     
     let must, prev_props_act, prop'act, neg_prop'act =
       if not do_under || invs_terms = [] then
         [], prev_props_act, prop'act, neg_prop'act
       else
         let must = under_approx sys k invs_terms prop in
         Debug.certif
           "Under approximation identified %d necessary invariants out of %d"
           (List.length must)
           (List.length invs_terms);
         let prop = Term.mk_and (prop :: must) in
         (* Construct properties from 1 to k-1 *)
         let prev_props_l = ref [prop] in
         for i = 1 to k - 1 do
           prev_props_l := Term.bump_state (Numeral.of_int i) prop :: !prev_props_l;
         done;
         (* Activation literals for properties from 1 to k-1 *)
         let prev_props_act =
           actlitify solver (Term.mk_and (List.rev !prev_props_l)) in
         (* Construct property at k *)
         let prop' = Term.bump_state (Numeral.of_int k) prop in
         let prop'act = actlitify solver prop' in
         (* Construct negation of property at k *)
         let neg_prop' = Term.mk_not prop' in
         let neg_prop'act = actlitify solver neg_prop' in
         must, prev_props_act, prop'act, neg_prop'act
     in
     
     (* Continuation: execute fixpoint *)
     let cont () =
       match Flags.Certif.mininvs () with
       | `HardOnly | `MediumOnly ->
         (* Only do the first inductive check if we want only hard
            minimization *)
         List.map snd invs_acts, must
       | _ ->
         (* Otherwise complete the fixpoint in the continuation *)
         trim solver
           [] invs_acts prev_props_act prop'act neg_prop'act trans_acts, must
     in

     if just_check_ind then raise (Reduce_cont cont)
     else cont ())

    (trans_acts @ (neg_invs'prop'act :: prev_props_act :: invs))



(* Second phase of minimization, a lot more costly. This is also a fixpoint
   computation but this time we add invariants instead of removing them.
   We start with the k-inductive check:
     P /\ T |= P'
   and when it is not valid, we look for invariants which evaluate to false in
   the model and add them to P (one-by-one or all at the same time)
*)
let rec cherry_pick solver trans
    needed_invs remaining_invs prev_props_act prop'act neg_prop'act trans_acts =

  let needed_invs_acts, needed_invs'acts = List.split needed_invs in
  
  let neg_invs'prop'act = prop'act :: needed_invs'acts
                          |> Term.mk_and |> Term.mk_not |> actlitify solver in

  SMTSolver.trace_comment solver "Hard minimization";

  SMTSolver.check_sat_assuming solver
    (fun _ -> (* SAT *)
       (* Not enough invariants *)
       
       (* Get the full model *)
       let model = SMTSolver.get_model solver in

       (* Evaluation function. *)
       let eval term =
         Eval.eval_term (TransSys.uf_defs trans) model term
         |> Eval.bool_of_value in

       (* Look for all or the first invariant which evaluate to false *)
       let other_invs, extra_needed, _ =
         (* List.partition (fun (inv, _) -> eval inv) remaining_invs *)
         List.fold_left (fun (other, extra, found) ((inv, _) as ii) ->
             (* Only add the first invariant if we want to do the hardest
                minimization *)
             if (Flags.Certif.mininvs () = `Hard ||
                 Flags.Certif.mininvs () = `HardOnly) &&
                found then
               ii :: other, extra, true
             else if not (eval inv) then other, ii :: extra, true
             else ii :: other, extra, false
           )
           ([], [], false)
           (List.rev remaining_invs)
       in

       (* If we have no more invariants to add, it means the whole set is not
          k-inductive *)
       (* if extra_needed = [] then begin *)
       (*   Debug.certif "[Hard Fixpoint] fail (impossible)"; *)
       (*   raise Exit *)
       (* end; *)

       if extra_needed = [] then needed_invs'acts
       else
       
       (* new list of needed invariants *)
       let needed_invs = List.fold_left (fun acc (inv, inv') ->
           let invact = actlitify solver inv in
           let inv'act = actlitify solver inv' in
           (invact, inv'act) :: acc
         ) needed_invs extra_needed in

       Debug.certif "Hard minimization identified %d"
         (List.length needed_invs);

       (* recursive call to find out if we have found an inductive set or not *)
       cherry_pick solver trans
         needed_invs other_invs prev_props_act prop'act neg_prop'act trans_acts
    )
    (fun _ -> (* UNSAT *)
       (* We found a k-inductive set of invariants *)
       needed_invs'acts
    )

    (trans_acts @ (neg_invs'prop'act :: prev_props_act :: needed_invs_acts))


(* Return type of the following function try_at_bound *)
type return_of_try =
  | Not_inductive
  (* The try failed, it is not inductive*)
  | Inductive_to_reduce of (unit -> Term.t list)
  (* Inductiveness was verified, but we still need to find the useful
     invariants. A continuation is attached for this purpose. *)
  | Inductive of Term.t list
  (* Inductiveness was verified, and we identified the useful invariants which
     are attached *)

(* Verify inductiveness of given property and invariants at k. The argument
   just_check_ind controls whether we want to also identify the useful
   invariants *)
let try_at_bound ?(just_check_ind=false) sys solver k invs prop trans_acts =
  
  Debug.certif "Try bound %d" k ;

  (* Construct properties from 1 to k-1 *)
  let prev_props_l = ref [prop] in
  for i = 1 to k - 1 do
    prev_props_l := Term.bump_state (Numeral.of_int i) prop :: !prev_props_l;
  done;

  (* Activation literals for properties from 1 to k-1 *)
  let prev_props_act =
    actlitify solver (Term.mk_and (List.rev !prev_props_l)) in

  (* Construct invariants (with activation literals) from 1 to k-1 and for k *)
  let invs_acts, invs_infos = List.fold_left (
    fun (invs_acts, invs_infos) inv ->
      let l = ref (if is_two_state inv then [] else [inv]) in
      for i = 1 to k - 1 do
        l := Term.bump_state (Numeral.of_int i) inv :: !l;
      done;
      let prev_invs = Term.mk_and (List.rev !l) in
      let prev_invs_act = actlitify solver prev_invs in
      let p1 = Term.bump_state (Numeral.of_int k) inv in
      let pa1 = actlitify solver p1 in
      (prev_invs_act, pa1) :: invs_acts,
      (inv, prev_invs_act, prev_invs, pa1, p1) :: invs_infos
  ) ([], []) (List.rev invs) in

  (* Construct property at k *)
  let prop' = Term.bump_state (Numeral.of_int k) prop in
  let prop'act = actlitify solver prop' in

  (* Construct negation of property at k *)
  let neg_prop' = Term.mk_not prop' in
  let neg_prop'act = actlitify solver neg_prop' in

  (* This functions maps activation literals (returned by the function
     fixpoint) back to original invariants *)
  let map_back_to_invs must_invs useful_acts =
      List.fold_left (fun acc a ->
        List.fold_left (fun acc (inv, _, _, a', _) ->
            if Term.equal a a' && not (List.exists (Term.equal inv) acc) then
              inv :: acc
            else acc
          ) acc invs_infos
      ) must_invs useful_acts
  in
  
  (* let reconstruct_infos useful_acts = *)
  (*   List.fold_left (fun acc a -> *)
  (*       List.fold_left (fun acc (_, _, prev_inv, a', inv') -> *)
  (*           if Term.equal a a' then (prev_inv, inv') :: acc else acc *)
  (*         ) acc invs_infos *)
  (*     ) [] useful_acts *)
  (* in *)

  let cherry_pick_min (useful_acts, must_invs) =
    (* let useful_infos = reconstruct_infos useful_acts in *)
    let needed, to_consider =
      List.fold_left (fun acc a ->
          List.fold_left (fun (needed, to_consider) (inv, _, prev_inv, a', inv') ->
              if Term.equal a a' then
                if List.exists (Term.equal inv) must_invs then
                  let prev_invact = actlitify solver prev_inv in
                  let inv'act = actlitify solver inv' in
                  (prev_invact, inv'act) :: needed, to_consider
                else
                  needed, (prev_inv, inv') :: to_consider
              else needed, to_consider
            ) acc invs_infos
        ) ([],[]) useful_acts
    in
    cherry_pick solver sys
      (* [] useful_infos *)
      needed to_consider
      prev_props_act prop'act neg_prop'act trans_acts
    |> map_back_to_invs must_invs
  in

  let follow_up =
    match Flags.Certif.mininvs () with
    | `Easy -> fun (ua, must) -> map_back_to_invs must ua
    | `Medium | `MediumOnly | `Hard | `HardOnly ->
      (* Second phase of harder minimization if we decide to not stop at easy *)
      cherry_pick_min
  in
  
  try
    (* Can fail and raise Exit or Reduce_cont *)
    let useful_acts, must_invs  =
      check_ind_and_trim ~just_check_ind sys k prop invs
        solver invs_acts prev_props_act prop'act neg_prop'act trans_acts in
    
    (* If fixpoint returned a list of useful invariants we just return them *)
    Inductive (
      follow_up (useful_acts, must_invs)
      (* map_back_to_invs useful_acts *)
    )
  with
  | Exit ->
    (* The first inductive test of fixpoint failed *)
    Not_inductive
  | Reduce_cont f ->
    (* fixpoint was interrupted, we return the continuation that will resume
       the computation of the useful invariants *)
    Inductive_to_reduce (fun () -> f () |> follow_up)


(* Find the minimum bound by increasing k *)
let rec find_bound sys solver k kmax invs prop =

  if k > kmax then raise (CouldNotProve
    ( fun fmt ->
      Format.fprintf fmt
        "[Certification] simplification of inductive invariant \
        went over bound %d" 
        kmax
    )
  ) ;
  
  (* Asserting transition relation. *)
  TransSys.trans_of_bound
    (Some (SMTSolver.declare_fun solver))
    sys (Numeral.of_int k)
  |> SMTSolver.assert_term solver;

  match try_at_bound sys solver k invs prop [] with
  | Not_inductive ->
    (* Not k-inductive *)
    find_bound sys solver (k+1) kmax invs prop

  | Inductive useful ->
    k, useful

  | Inductive_to_reduce _ ->
    (* Should not happend, we are not asking for continuations when calling 
       try_at_bound *)
    assert false


(* Pre-compute activation literal for unrolling of transtion relation between 1
   and k. We do this because we don't want to assert the whole k unrollings of
   the transition relation as this can overwhelm the solver. *)
let unroll_trans_actlits sys solver kmax =

  let rec fill acc prev = function
    | k when k > kmax -> acc
    | k ->
      let tk = TransSys.trans_of_bound
          (Some (SMTSolver.declare_fun solver))
          sys (Numeral.of_int k) in
      let tuptok = match prev with Some p -> Term.mk_and [p; tk] | _ -> tk in
      let a = actlitify ~imp:true solver tuptok in
      fill (IntM.add k a acc) (Some a) (k + 1)
  in

  (* Start at 1 *)
  fill IntM.empty None 1


(* Find the minimum bound starting from kmax and going backwards *)
let find_bound_back sys solver kmax invs prop =

  (* Creating activation literals for transition unrollings *)
  let trans_acts_map = unroll_trans_actlits sys solver kmax in
  
  let rec loop acc k =

    let res =
      if k = 0 then Not_inductive
      else
        let trans_act = IntM.find k trans_acts_map in
        try_at_bound ~just_check_ind:true sys solver k invs prop [trans_act]
    in

    match res with

    | Not_inductive ->
      (* Check if the previous were inductive *)

      begin match acc with
        (* Not k-inductive *)
        | _, Not_inductive -> raise (CouldNotProve
          (fun fmt ->
            Format.fprintf fmt
              "[Certification] Could not verify %d-inductiveness \
              of invariant" k
          )
        )

        | k, Inductive_to_reduce f ->
          (* The previous step was inductive, evaluate the continuation to
             extract useful invariants *)
          k, f ()

        | k, Inductive useful ->
          (* The previous step was inductive and we already have the useful
             invariants *)
          k, useful
      end

    | Inductive _ | Inductive_to_reduce _ ->
      (* Inductive, we register the result and loop *)
      loop (k, res) (k - 1)

  in

  (* Start at kmax *)
  loop (-1, Not_inductive) kmax



(* Recursive binary search between k_l and k_u *)
let rec loop_dicho sys solver kmax invs prop trans_acts_map acc k_l k_u =

  if k_l > k_u then
    match acc with
    | _, Not_inductive -> raise (
      (* Not k-inductive *)
      CouldNotProve (
        fun fmt ->
          Format.fprintf fmt
            "@[<v>Could not verify inductiveness of invariants@   \
            @[<v>%a@]@   up to %d@]"
            (pp_print_list Term.pp_print_term ",@ ") invs k_u
      )
    )

    | k, Inductive_to_reduce f ->
      (* The previous step was inductive, evaluate the continuation to
         extract useful invariants *)
      k, f ()

    | k, Inductive useful ->
      (* The previous step was inductive and we already have the useful
         invariants *)
      k, useful

  else

    (* Middle point *)
    let k_mid = (k_l + k_u) / 2 in
    (* Activation literals for transition relation from 1 to kmid *)
    let trans_act = IntM.find k_mid trans_acts_map in

    match (
      let res = try_at_bound ~just_check_ind:false
        sys solver k_mid invs prop [trans_act]
      in
      res
    ) with
    | Not_inductive ->
      (* Not inductive, look for inductiveness on the right *)
      loop_dicho sys solver kmax invs prop trans_acts_map
        acc (k_mid + 1) k_u

    | res ->
      (* Inductive, register and Look for non-inductiveness on the left *)
      loop_dicho sys solver kmax invs prop trans_acts_map
        (k_mid, res) k_l (k_mid - 1)


(* Find the minimum bound by dichotomy between 1 and kmax (binary search) *)
let find_bound_dicho sys solver kmax invs prop =
  (* Creating activation literals for transition unrollings *)
  let trans_acts_map = unroll_trans_actlits sys solver kmax in
  (* Start with interval [1; kmax] *)
  loop_dicho sys solver kmax invs prop trans_acts_map (-1, Not_inductive) 1 kmax


(* Find the minimum bound by dichotomy between 1 and kmax (try at kmax frontier
   then binary search) *)
let find_bound_frontier_dicho sys solver kmax invs prop =
  (* Creating activation literals for transition unrollings *)
  let trans_acts_map = unroll_trans_actlits sys solver kmax in

  (* Try boundary kmax / kmax - 1 first *)
  let res_kmax =
      let trans_act = IntM.find kmax trans_acts_map in
      try_at_bound ~just_check_ind:true sys solver kmax invs prop [trans_act]
  in
  let res_kmax_m1 =
    if kmax - 1 = 0 then Not_inductive
    else
      let trans_act = IntM.find (kmax - 1) trans_acts_map in
      try_at_bound ~just_check_ind:true
        sys solver (kmax - 1) invs prop [trans_act]
  in

  match res_kmax, res_kmax_m1 with
  | Not_inductive, _ -> raise (CouldNotProve
    (fun fmt ->
      Format.fprintf fmt
        "[Certification, frontier dicho] Could not verify inductiveness@ \
        of invariant"
    )
  )

  | Inductive useful, Not_inductive -> kmax, useful

  | Inductive_to_reduce f, Not_inductive -> kmax, f ()

  | (Inductive _ | Inductive_to_reduce _),
    (Inductive _ | Inductive_to_reduce _) ->

    (* Binary search in interval [1; kmax-2] *)
    loop_dicho sys solver kmax invs prop trans_acts_map
      (kmax - 1, res_kmax_m1) 1 (kmax - 2)


(* Minimization of certificate: returns the minimum bound for k-induction and a
   list of useful invariants for this preservation step *)
let minimize_invariants sys props invs_predicate =
  (* printf "@{<b>Certificate minimization@}@."; *)

  (* Extract certificates of top level system *)
  let props', certs = extract_props_certs sys in
  let props =
    match props with
    | Some props -> props
    | None -> props'
  in
  let certs =
    match invs_predicate with
    | None -> certs
    | Some filter -> certs |> List.filter (
      fun (_, inv) -> filter inv
    )
  in
  let certs = Certificate.split_certs certs in
  let k, invs =
    List.fold_left (
      fun (m, invs) (k, i) ->
        max m k,
        if List.exists (Term.equal i) props ||
           List.exists (Term.equal i) invs
        then invs
        else i :: invs
    ) (0, []) certs
  in

  (* TODO: Fix the minimize_invariant function when Smt.check_sat_assume is false.
     The issue seems to come from the fact that nested calls to check_sat_assume
     and get_unsat_core_lits are done inside of the continuation given to check_sat_assume. *)
  if Flags.Smt.check_sat_assume ()
  then

    (* For stats *)
    let k_orig, _ (* nb_invs *) = k, List.length invs in
    
    Debug.certif "Trying to simplify up to k = %d\n" k_orig;

    let logic =
      match TransSys.get_logic sys with
      | `Inferred fs when Flags.BmcKind.compress () ->
        `Inferred (TermLib.sup_logics [fs; TermLib.FeatureSet.of_list [IA; LA; UF]])
      | `Inferred l -> `Inferred (TermLib.FeatureSet.add UF l)
      | l -> l
    in

    (* Creating solver that will be used to replay and minimize inductive step *)
    let solver =
      SMTSolver.create_instance ~produce_unsat_assumptions:true ~produce_assignments:true
        logic (Flags.Smt.solver ())
    in
    
    (* Defining uf's and declaring variables. *)
    TransSys.define_and_declare_of_bounds
      sys
      (SMTSolver.define_fun solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero (Numeral.of_int (k+1));

    (* Declaring path compression function if needed. *)
    if Flags.BmcKind.compress () then
      Compress.init (SMTSolver.declare_fun solver) sys ;
    
    (* The property we want to re-verify is the conjunction of all properties *)
    let prop = Term.mk_and props in

    let min_strategy = match Flags.Certif.mink () with
      | `No -> assert false
      | (`Fwd | `Bwd | `Dicho | `FrontierDicho) as s -> s
      | `Auto ->
        (* Heuristic to find best strategy *)
        if k <= 3 then `Fwd
        else if k <= 20 then `Dicho
        else `FrontierDicho
    in

    (* Depending on the minimization strategy, we use different variants to find
      the minimum bound kmin, and the set of useful invariants for the proof of
      prop *)
    let kmin, uinvs = match min_strategy with
      | `Fwd -> find_bound sys solver 1 k invs prop
      | `Bwd -> find_bound_back sys solver 3 invs prop
      | `FrontierDicho -> find_bound_frontier_dicho sys solver k invs prop
      | `Dicho -> find_bound_dicho sys solver k invs prop
    in

    (* We are done with this step of minimization and we don't need the solver
      anylonger *)
    SMTSolver.delete_instance solver;
    
    Debug.certif "Simplification found for k = %d\n" kmin;

    (* printf "Kept %d (out of %d) invariants at bound %d (down from %d)@."
      (List.length uinvs) nb_invs kmin k_orig; *)

    (* Return minimum k found, and the useful invariants *)
    kmin, uinvs

  else
    k, invs

let minimize_certificate sys =
  minimize_invariants sys None None


(***********************************************)
(* Pretty printing sections of the certificate *)
(***********************************************)

let linestr = String.make 79 '-'
let doublelinestr = String.make 79 '='

let print_line fmt str = fprintf fmt ";%s\n" str

let add_section ?(double=false) fmt title =
  fprintf fmt "\n\n";
  if double then print_line fmt doublelinestr else print_line fmt linestr;
  fprintf fmt "; %s :\n" title;
  if double then print_line fmt doublelinestr else print_line fmt linestr;
  fprintf fmt "@."


(* Make the solver display a string on its standard ouptut *)
let echo fmt s = fprintf fmt "(echo \"%s\")@." (String.escaped s)


(******************************************************************************)
(* Information about certificate are reflected in the header of the SMT2 file *)
(******************************************************************************)


(* Returns true if the system is an observer of equivalence, i.e. an FEC *)
let is_fec sys =
  match TransSys.scope_of_trans_sys sys with
  | "OBS" :: _ -> true
  | _ -> false
    

(* Add a set-info header *)
let set_info fmt tag str =
  fprintf fmt
    "@[<hv 1>(set-info@ :%s@ @[<hv>%s@])@]@." 
    tag str

(* System specific header for definitions *)
let add_system_header fmt prefix =

  set_info fmt "system"
    (sprintf "\"Logical transition system generated by %s\""
       prefix);

  (* Original input problem *)
  set_info fmt "input" ("\""^(Flags.input_file ())^"\"");

  fprintf fmt "@."


let add_logic fmt sys = 

  (* Extract the logic of the system and add uninterpreted functions and
     integer arithmetic to it (because of implicit unrolling for state
     variables) *)
  let open TermLib in
  let logic = match TransSys.get_logic sys with
    | `None | `SMTLogic _ -> `None
    | `Inferred l ->
      `Inferred (
        l |> FeatureSet.add UF
        |> FeatureSet.add IA
        |> (if quant_free then Lib.identity else FeatureSet.add Q)
      )
  in
  (* Specify logic to help some solvers check the certificate *)
  fprintf fmt "(set-logic %a)@." SMT.pp_print_logic logic


  
let add_arrays fmt =
  (* Add farray declaration *)
  fprintf fmt "(declare-sort FArray 2)@.";
  (* Add select functions *)
  declare_selects fmt


(* Populate the headers of the certificate *)
let add_header fmt sys k init_n prop_n trans_n phi_n =

  (* Origin of the certificate: Kind 2 version *)
  set_info fmt "origin"
    (sprintf "\"%sCertificate generated by %s %s\""
       (if is_fec sys then "Frontend Certificate " else "")
       Version.package_name Version.version);

  (* Original input problem *)
  set_info fmt "input" ("\""^(Flags.input_file ())^"\"");

  (* The certificate should be unsat if it is correct *)
  set_info fmt "status" "unsat";
  fprintf fmt "@.";

  (* Specify symbols for input system / properties *)
  set_info fmt "init " init_n;
  set_info fmt "trans" trans_n;
  set_info fmt "prop " prop_n;
  fprintf fmt "@.";

  (* Specify symbols that constitute certificate *)
  set_info fmt "certif" (sprintf "\"(%d , %s)\"" k phi_n);
  fprintf fmt "@.";

  add_logic fmt sys;

  add_arrays fmt


(* Populate the headers of the certificate *)
(*let monolithic_header fmt description sys init_n prop_n trans_n phi_n k =

  (* Extract the logic of the system and add uninterpreted functions and
     integer arithmetic to it (because of implicit unrolling for state
     variables) *)
  let open TermLib in
  let logic = match TransSys.get_logic sys with
    | `None | `SMTLogic _ -> `None
    | `Inferred l ->
      `Inferred (
        l |> FeatureSet.add UF
        |> FeatureSet.add IA
        |> (if quant_free then Lib.identity else FeatureSet.add Q)
      )
  in

  (* Origin of the certificate: Kind 2 version *)
  set_info fmt "origin"
    (sprintf "\"Generated by %s %s\"" Version.package_name Version.version);

  (* Original input problem *)
  set_info fmt "input" ("\""^(Flags.input_file ())^"\"");

  (* Specify symbols for input system / properties *)
  set_info fmt "init " init_n;
  set_info fmt "trans" trans_n;
  set_info fmt "prop " prop_n;
  fprintf fmt "@.";

  (* Specify symbols that constitute certificate *)
  set_info fmt "certif" (sprintf "\"(%d , %s)\"" k phi_n);
  fprintf fmt "@.";

  set_info fmt "description" ("\""^description^"\"");
  fprintf fmt "@.";

  (* Specify logic to help some solvers check the certificate *)
  fprintf fmt "(set-logic %a)@." SMT.pp_print_logic logic;

  (* Add farray declaration *)
  fprintf fmt "(declare-sort FArray 2)@.";
  
  (* Add select functions *)
  declare_selects fmt*)


(************************************************)
(* Putting system definitions in separate files *)
(************************************************)

(* let export_system fmt ?(recursive=true) prefix sys prop k = *)
  
(*   (\* Names of predicates *\) *)
(*   let init_n = prefix ^ ".INIT" in *)
(*   let prop_n = prefix ^ ".PROP" in *)
(*   let trans_n = prefix ^ ".TRANS" in *)

(*   (\* add headers for info *\) *)
(*   add_system_header fmt prefix sys init_n prop_n trans_n; *)
  
(*   let consts, svars = List.partition StateVar.is_const (TS.state_vars sys) in *)
  
(*   (\* Declaring constant symbols *\) *)
(*   add_section fmt "Constants"; *)
(*   List.iter (fun sv -> *)
(*       declare_const fmt (StateVar.uf_symbol_of_state_var sv) *)
(*     ) consts; *)
  
(*   (\* Declaring state variables upto k *\) *)
(*   add_section fmt "State variables"; *)
(*   List.iter (fun sv -> *)
(*       declare_state_var ~instantiate_constr:(0, k+1) *)
(*         fmt (StateVar.uf_symbol_of_state_var sv) *)
(*     ) svars; *)
  
(*   (\* Declaring function symbols *\) *)
(*   add_section fmt "Function symbols"; *)
(*   let defs = if recursive then TS.uf_defs sys else List.hd (TS.uf_defs sys) in *)
(*   List.iter (fun (f, (a, d)) -> define_fun fmt f a Type.t_bool d) defs; *)

(*   (\* Variables i and j to be used later *\) *)
(*   let fvi = Var.mk_free_var (HString.mk_hstring "i") Type.t_int in *)
(*   let fvj = Var.mk_free_var (HString.mk_hstring "j") Type.t_int in *)

(*   (\* Substitutions to be used later: *\) *)
(*   (\* [0 -> i] *\) *)
(*   let sigma_0i = TM.singleton t0 (Term.mk_var fvi) in *)
(*   (\* [0 -> i; 1 -> j] *\) *)
(*   let sigma_0i1j = TM.add t1 (Term.mk_var fvj) sigma_0i in *)
  
(*   (\* Declaring initial state (__I__ i) *\) *)
(*   add_section fmt "Initial states"; *)
(*   let init_s = UfSymbol.mk_uf_symbol init_n [Type.t_int] Type.t_bool in *)
(*   let init_def = roll sigma_0i (TS.init_term sys) in *)
(*   define_fun fmt init_s [fvi] Type.t_bool init_def; *)
  
(*   (\* Declaring property (__P__ i) *\) *)
(*   add_section fmt "Original property"; *)
(*   let prop_s = UfSymbol.mk_uf_symbol prop_n [Type.t_int] Type.t_bool in *)
(*   let prop_def = roll sigma_0i prop in *)
(*   define_fun fmt prop_s [fvi] Type.t_bool prop_def; *)

(*   (\* Declaring transition steps (__T__ i j) *\) *)
(*   add_section fmt "Transition_relation";   *)
(*   let trans_s = UfSymbol.mk_uf_symbol trans_n *)
(*       [Type.t_int; Type.t_int] Type.t_bool in *)
(*   let t01 = TransSys.trans_fun_of sys Numeral.zero Numeral.one in *)
(*   let trans_def = roll sigma_0i1j t01 in *)
(*   define_fun fmt trans_s [fvi; fvj] Type.t_bool trans_def *)



let export_system_defs
    fmt ?(recursive=true) ?(trace_lfsc_defs=false) prefix sys =
  
  (* add headers for info *)
  add_system_header fmt prefix ;
  
  (* Declaring function symbols *)
  add_section fmt "Function symbols";
  let defs =
    if recursive then TS.uf_defs sys
    else match TS.uf_defs sys |> List.rev with
      | t::i::_ -> [i;t]
      | _ -> assert false
  in
  List.iter (fun (f, (a, d)) ->
      define_fun ~trace_lfsc_defs fmt f a Type.t_bool d) defs


(**********************************************)
(* Creation of certificate and checker script *)
(**********************************************)


(* Declare predicates (I, T, P, PHI, ...)  with tracing *)
let s_define_pred ?(trace_lfsc_defs=false) fmt fun_symbol args defn = 

  let sindex_sort = ty_index () |> SMT.string_of_sort in
  
  fprintf fmt "(define-fun %s (%a) Bool\n   \
               %s)\n@."
    fun_symbol
    (pp_print_list (fun fmt f -> fprintf fmt "(%s %s)" f sindex_sort) " ") args
    defn;

  if trace_lfsc_defs then begin

    fprintf fmt ";; Tracing artifact for cvc5 and LFSC proofs\n";
    
    let fun_def_sy = fun_symbol ^ "%def" in
    fprintf fmt "(declare-fun %s %s Bool)\n" fun_def_sy
      (paren_string_of_string_list (List.map (fun _ -> sindex_sort) args)) ;

    let cpt = ref 0 in
    let fun_def_args = List.map (fun _ ->
        incr cpt;
        let vfs = fun_symbol ^ "%" ^ string_of_int !cpt in
        fprintf fmt "(declare-fun %s () %s)\n" vfs sindex_sort;
        vfs
      ) args in

    fprintf fmt
      "@[<hov 1>(assert@ @[<hov 1>(=@ @[<hv 1>(%s@ %a)@]@ @[<hv 1>(%s@ %a)@])@])@]\n@."
      fun_def_sy (pp_print_list pp_print_string "@ ") fun_def_args
      fun_symbol (pp_print_list pp_print_string "@ ") fun_def_args
  end
  


let mononames_system fmt ~trace_lfsc_defs sys name_sys prop names =

  let consts, svars = List.partition StateVar.is_const (TS.state_vars sys) in
  
  (* Declaring constant symbols *)
  add_section fmt "Constants";
  List.iter (fun sv ->
      declare_const fmt (StateVar.uf_symbol_of_state_var sv)
    ) consts;
  
  (* Declaring state variables upto k *)
  add_section fmt "State variables";
  List.iter (fun sv ->
      declare_state_var fmt (StateVar.uf_symbol_of_state_var sv)
    ) svars;

  (* Do not export the definitions with tracing information for LFSC *)
  export_system_defs fmt ~recursive:true ~trace_lfsc_defs:false name_sys sys;

  (* Variables i and j to be used later *)
  let fvi = Var.mk_free_var (HString.mk_hstring "i") (ty_index ()) in
  let fvj = Var.mk_free_var (HString.mk_hstring "j") (ty_index ()) in

  (* Substitutions to be used later: *)
  (* [0 -> i] *)
  let sigma_0i = TM.singleton t0 (Term.mk_var fvi) in
  (* [0 -> i; 1 -> j] *)
  let sigma_0i1j = TM.add t1 (Term.mk_var fvj) sigma_0i in
  
  (* Declaring initial state (I i) *)
  add_section fmt "Initial states";
  let init_s = UfSymbol.mk_uf_symbol names.init [(ty_index ())] Type.t_bool in
  let i0 = TransSys.init_fun_of sys Numeral.zero in
  let init_def = roll sigma_0i i0 in
  define_fun ~trace_lfsc_defs fmt init_s [fvi] Type.t_bool init_def;
  
  (* Declaring transition relation (T i j) *)
  add_section fmt "Transition_relation";  
  let trans_s = UfSymbol.mk_uf_symbol names.trans
      [(ty_index ()); (ty_index ())] Type.t_bool in
  let t01 = TransSys.trans_fun_of sys Numeral.zero Numeral.one in
  let trans_def = roll sigma_0i1j t01 in
  define_fun ~trace_lfsc_defs fmt trans_s [fvi; fvj] Type.t_bool trans_def;
  
  (* Declaring property (P i) *)
  add_section fmt "Original property";
  let prop_s = UfSymbol.mk_uf_symbol names.prop [(ty_index ())] Type.t_bool in
  let prop_def = roll sigma_0i prop in
  define_fun ~trace_lfsc_defs fmt prop_s [fvi] Type.t_bool prop_def


let export_system ~trace_lfsc_defs
    dirname file names sys name_sys =

  let filename = Filename.concat dirname file in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;

  (* Conjunction of properties *)
  let prop = extract_props_terms sys in

  if trace_lfsc_defs then begin
    add_logic fmt sys;
    add_arrays fmt
  end;
  
  (* declare state variables, write I, T and P *)
  mononames_system fmt ~trace_lfsc_defs sys name_sys prop names;  

  (* dummy goal if we only want to do tracing *)
  if trace_lfsc_defs then begin
    assert_expr fmt Term.t_false;
    check_sat fmt;
    sexit fmt;
  end;
  close_out oc


let export_phi ~trace_lfsc_defs dirname file definitions_files names sys phi =

  let filename = Filename.concat dirname file in
  let oc =
    if trace_lfsc_defs then
      files_cat_open
        ~add_prefix:(fun fmt ->
            if trace_lfsc_defs then begin
              add_logic fmt sys;
              add_arrays fmt;
            end else ())
        definitions_files filename |> Unix.out_channel_of_descr
    else open_out filename in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;

  let fvi = Var.mk_free_var (HString.mk_hstring "i") (ty_index ()) in
  (* Substitutions to be used later: *)
  (* [0 -> i] *)
  let t_fvi = Term.mk_var fvi in
  let sigma_0i = TM.singleton t0 t_fvi in
  
  (* Declaring k-inductive invariant (PHI i) *)
  add_section fmt "k-Inductive invariant";
  let phi_s = UfSymbol.mk_uf_symbol names.phi [(ty_index ())] Type.t_bool in
  let phi_def = roll sigma_0i (guard_two_state_term_list phi t_fvi) in
  define_fun ~trace_lfsc_defs fmt phi_s [fvi] Type.t_bool phi_def;

  (* dummy goal if we only want to do tracing *)
  if trace_lfsc_defs then begin
    assert_expr fmt Term.t_false;
    check_sat fmt;
    sexit fmt;
  end;
  close_out oc




let smk s l =
  asprintf "@[<hov 1>(%s@ %a)@]" s
    (pp_print_list pp_print_string "@ ") l


(* Build disjunction from the right as this is how the LFSC signature contructs
   them *)
let rec smk_or = function
  | [] -> "false"
  | [cj] -> cj
  | cj :: (_::_ as r) -> smk "or" [smk_or r; cj]

let smk_or l = smk_or (List.rev l)

(* Build conjunctions from the right as this is how the LFSC signature
   contructs them *)
let rec smk_and = function
  | [] -> "true"
  | [cj] -> cj
  | cj :: (_::_ as r) -> smk "and" [smk_and r; cj]

let smk_and l = smk_and (List.rev l)

let s_assert fmt s = fprintf fmt "@[<hov 1>(assert@ %s)@]\n@." s
  

let mononames_base_check sys dirname file definitions_files k names =

  let filename = Filename.concat dirname file in
  
  let od = files_cat_open
      ~add_prefix:(fun fmt ->
          add_logic fmt sys;
          add_arrays fmt)
      definitions_files filename in
  let oc = Unix.out_channel_of_descr od in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;
  
  add_section fmt "Base case";

  let dnf = ref [] in

  for i = k - 1 downto 0 do

    let l = ref [] in
    for j = i - 1 downto 0 do
      l := smk names.trans [index_sym_of_int j; index_sym_of_int (j+1)] :: !l;
    done;

    let conj =
      smk_and [smk_and (smk names.init [index_sym_of_int 0] :: !l);
               smk "not" [smk names.phi [index_sym_of_int i]]] in

    dnf := conj :: !dnf

  done;
  
  s_assert fmt (smk_or !dnf);
  (* s_assert fmt (smk "or" !dnf); *)
  check_sat fmt;

  sexit fmt;
  close_out oc;
  filename

let mononames_induction_check sys dirname file definitions_files k names =

  let filename = Filename.concat dirname file in

  let od = files_cat_open
      ~add_prefix:(fun fmt ->
          add_logic fmt sys;
          add_arrays fmt)
      definitions_files filename in
  let oc = Unix.out_channel_of_descr od in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;
    
  (* Checking k-inductive case *)
  add_section fmt (sprintf "%d-Inductiveness" k);    

  (* unroll k times*)
  let l = ref [] in
  for i = k - 1 downto 0 do
    l := smk_and [smk names.phi [index_sym_of_int i];
                  smk names.trans [index_sym_of_int i;
                                   index_sym_of_int (i+1)]] :: !l
  done;

  let g = smk_and [smk_and !l;
                   smk "not" [smk names.phi [index_sym_of_int k]]] in

  s_assert fmt g;
  check_sat fmt;
  
  sexit fmt;
  close_out oc;
  filename


let mononames_implication_check sys dirname file definitions_files names =

  let filename = Filename.concat dirname file in

  let od = files_cat_open
      ~add_prefix:(fun fmt ->
          add_logic fmt sys;
          add_arrays fmt)
      definitions_files filename in
  let oc = Unix.out_channel_of_descr od in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;
  
  (* Checking implication of indutive invariant to original properties *)
  add_section fmt "Property implication";
    

  let v = "0" in
  let f = smk "=>" [smk names.phi [v];
                    smk names.prop [v]] in
  
  s_assert fmt (smk "not" [f]);

  check_sat fmt;
  
  sexit fmt;
  close_out oc;
  filename






let generate_split_certificates sys dirname =

  KEvent.set_module `Certif;

  (* Extract the global raw certificate of the system *)
  let prop, (k, phi) = global_certificate sys in

  Stat.start_timer Stat.certif_min_time;
  Stat.set k Stat.certif_old_k;
  Stat.set (Certificate.size (k, phi)) Stat.certif_old_size;

  (* Performed minimization of certificate *)
  let k, phi = match Flags.Certif.mink () with
    | `No -> k, phi
    | _ ->
      (* Simplify certificate *)
      let k, uinvs = minimize_certificate sys in
      k, Term.mk_and (prop :: uinvs)
  in
  
  (* Record statistics for minimization *)
  Stat.record_time Stat.certif_min_time;  
  Stat.set k Stat.certif_k;
  Stat.set (Certificate.size (k, phi)) Stat.certif_size;

  let svars =
    List.filter_map
      (fun v ->
        if StateVar.is_const v then None
        else Some (StateVar.uf_symbol_of_state_var v))
      (TS.state_vars sys)
  in

  let names_kind2 = names_kind2 svars in

  (* Export system in SMT-LIB2 format *)
  export_system ~trace_lfsc_defs:false
    (* "System constructed by Kind 2" *)
    dirname kind2_defs_f names_kind2 sys "Kind2";

  export_system ~trace_lfsc_defs:true
    (* "System constructed by Kind 2 (tracing info for cvc5/LFSC)" *)
    dirname kind2_defs_lfsc_f names_kind2 sys "Kind2";

  let kind2_defs_path = Filename.concat dirname kind2_defs_f in

  (* Export k-inductive invariant phi in SMT-LIB2 format *)
  export_phi ~trace_lfsc_defs:false
    dirname kind2_phi_f [kind2_defs_path] names_kind2 sys phi;

  export_phi ~trace_lfsc_defs:true
    dirname kind2_phi_lfsc_f [kind2_defs_path] names_kind2 sys phi;

  let kind2_phi_path = Filename.concat dirname kind2_phi_f in
  let kind2_phi_lfsc_path = Filename.concat dirname kind2_phi_lfsc_f in
  
  (* definitions to use for the checks *)
  let smt2_definitions = [kind2_defs_path; kind2_phi_path] in
  
  (* write certificates checks in smtlib2 scripts *)
  let base =
    mononames_base_check sys dirname base_f smt2_definitions k names_kind2 in

  let induction =
    mononames_induction_check sys
      dirname induction_f smt2_definitions k names_kind2 in

  let implication = 
    mononames_implication_check sys
      dirname implication_f smt2_definitions names_kind2 in

  let kind2_sys = kind2_cert_sys svars dirname in
  
  let inv = {
    k;
    name = names_kind2.phi;
    dirname;
    phi_file = kind2_phi_path;
    phi_lfsc_trace_file = kind2_phi_lfsc_path;
    base;
    induction;
    implication;
    for_system = kind2_sys;
    kind2_system = kind2_sys;
    jkind_system = jkind_cert_sys [] dirname;
    obs_system = obs_cert_sys dirname;
  } in

  (* Time statistics *)
  Stat.record_time Stat.certif_gen_time;

  (* Show which file contains the certificate *)
  Debug.certif
     "SMT-LIB2 intermediate certificates were written in %s" dirname;

  inv

  

(* Generate a certificate from a (possibly) proven system sys. It is written in
   the file <input_file>.certificate.smt2 placed in the current directory by
   default *)
let generate_certificate sys dirname =

  KEvent.set_module `Certif;

  (* Time statistics *)
  Stat.start_timer Stat.certif_gen_time;

  let certificate_filename = Filename.concat dirname
      (if is_fec sys then "FECC.smt2" else "certificate.smt2") in

  let header_filename = Filename.concat dirname
      (if is_fec sys then "FECC_prelude.smt2" else "certificate_prelude.smt2")
  in


  let certif_oc = open_out certificate_filename in
  let header_oc = open_out header_filename in

  let fmt = formatter_of_out_channel certif_oc in
  let fmt_header = formatter_of_out_channel header_oc in

  (* Set line width *)
  Format.pp_set_margin fmt file_width;

  (* Extract the global raw certificate of the system *)
  let prop, (k, phi) = global_certificate sys in

  Stat.start_timer Stat.certif_min_time;
  Stat.set k Stat.certif_old_k;
  Stat.set (Certificate.size (k, phi)) Stat.certif_old_size;

  (* Performed minimization of certificate *)
  let k , phi = match Flags.Certif.mink () with
    | `No -> k, phi
    | _ ->
      (* Simplify certificate *)
      let k, uinvs = minimize_certificate sys in
      k, Term.mk_and (prop :: uinvs)

  in

  (* Record statistics for minimization *)
  Stat.record_time Stat.certif_min_time;  
  Stat.set k Stat.certif_k;
  Stat.set (Certificate.size (k, phi)) Stat.certif_size;

  (* add headers for info *)
  add_header fmt_header sys k
    names_bare.init names_bare.prop names_bare.trans names_bare.phi;

  if is_fec sys then begin

    let obs_sys = sys in

    (*let jkind_sys =
      TransSys.find_subsystem_of_scope sys JkindParser.jkind_scope in

    let jkdef_filename = Filename.concat dirname jkind_defs_f in
    let jkdef_oc = open_out jkdef_filename in
    let fmt_jkdef = formatter_of_out_channel jkdef_oc in
    export_system_defs fmt_jkdef "JKind" jkind_sys;
    close_out jkdef_oc;*)

    let obsdef_filename = Filename.concat dirname "observer_sys.smt2" in
    let obsdef_oc = open_out obsdef_filename in
    let fmt_obsdef = formatter_of_out_channel obsdef_oc in
    export_system_defs fmt_obsdef ~recursive:true "Obs" obs_sys;
    close_out obsdef_oc;

  end
  else begin

    let def_filename = Filename.concat dirname kind2_defs_f in
    let def_oc = open_out def_filename in
    let fmt_def = formatter_of_out_channel def_oc in

    export_system_defs fmt_def "Kind2" sys;

    close_out def_oc;

  end;



  let consts, svars = List.partition StateVar.is_const (TS.state_vars sys) in

  (* Declaring constant symbols *)
  add_section fmt "Constants";
  List.iter (fun sv ->
      declare_const fmt (StateVar.uf_symbol_of_state_var sv)
    ) consts;

  (* Declaring state variables upto k *)
  add_section fmt "State variables";
  List.iter (fun sv ->
      declare_state_var fmt (StateVar.uf_symbol_of_state_var sv)
    ) svars;


  (* Variables i and j to be used later *)
  let fvi = Var.mk_free_var (HString.mk_hstring "i") (ty_index ()) in
  let fvj = Var.mk_free_var (HString.mk_hstring "j") (ty_index ()) in

  (* Substitutions to be used later: *)
  (* [0 -> i] *)
  let t_fvi = Term.mk_var fvi in
  let sigma_0i = TM.singleton t0 t_fvi in
  (* [0 -> i; 1 -> j] *)
  let sigma_0i1j = TM.add t1 (Term.mk_var fvj) sigma_0i in

  
  (* Declaring initial state (I i) *)
  add_section fmt "Initial states";
  let init_s =
    UfSymbol.mk_uf_symbol names_bare.init [(ty_index ())] Type.t_bool in
  let i0 = TransSys.init_fun_of sys Numeral.zero in
  let init_def = roll sigma_0i i0 in
  define_fun fmt init_s [fvi] Type.t_bool init_def;
  let init_t0 = Term.mk_uf init_s [index_of_int 0] in
  
  (* Declaring transition relation (T i j) *)
  add_section fmt "Transition_relation";  
  let trans_s = UfSymbol.mk_uf_symbol names_bare.trans
      [(ty_index ()); (ty_index ())] Type.t_bool in
  let t01 = TransSys.trans_fun_of sys Numeral.zero Numeral.one in
  let trans_def = roll sigma_0i1j t01 in
  define_fun fmt trans_s [fvi; fvj] Type.t_bool trans_def;
  let trans_t i j = Term.mk_uf trans_s [index_of_int i; index_of_int j] in
  
  (* Declaring property (P i) *)
  add_section fmt "Original property";
  let prop_s =
    UfSymbol.mk_uf_symbol names_bare.prop [(ty_index ())] Type.t_bool in
  let prop_def = roll sigma_0i prop in
  define_fun fmt prop_s [fvi] Type.t_bool prop_def;
  (* let prop_t i = Term.mk_uf prop_s [Term.mk_num_of_int i] in *)
  let prop_v v = Term.mk_uf prop_s [Term.mk_var v] in
  let prop_u u l = Term.mk_uf prop_s [Term.mk_uf u l] in


  (* Declaring k-inductive invariant (PHI i) *)
  add_section fmt (sprintf "%d-Inductive invariant" k);
  let phi_s =
    UfSymbol.mk_uf_symbol names_bare.phi [(ty_index ())] Type.t_bool in
  let phi_def = roll sigma_0i (guard_two_state_term_list phi t_fvi) in
  define_fun fmt phi_s [fvi] Type.t_bool phi_def;
  let phi_t i = Term.mk_uf phi_s [index_of_int i] in
  let phi_v v = Term.mk_uf phi_s [Term.mk_var v] in
  let phi_u u l = Term.mk_uf phi_s [Term.mk_uf u l] in


  add_section ~double:true fmt "CERTIFICATE CHECKER";

  (* Checking base case *)
  add_section fmt "Base case";
  echo fmt "Checking base case";
  push fmt;

  if monolithic_base then
    if simple_base then
      (* Incorrect base case checking *)

      let l = ref [] in

      KEvent.log L_warn "Using potentially incorrect check for base case";

      for i = k - 2 downto 0 do
        l := trans_t i (i+1) :: !l;
      done;

      let conj = Term.mk_and (init_t0 :: !l) in
      assert_expr fmt conj;

      let g = ref [] in
      for i = k - 1 downto 0 do
        g := phi_t i :: !g;
      done;
      let goal = Term.mk_and !g in
      assert_expr fmt (Term.mk_not goal);
      check_sat fmt;

    else
      (* Monolithic base case *)

      let dnf = ref [] in

      for i = k - 1 downto 0 do

        let l = ref [Term.mk_not (phi_t i)] in
        for j = i - 1 downto 0 do
          l := trans_t j (j+1) :: !l;
        done;

        let conj = Term.mk_and (init_t0 :: !l) in
        dnf := conj :: !dnf

      done;

      assert_expr fmt (Term.mk_or !dnf);
      check_sat fmt;

  else begin
    (* Incremental base case *)

    assert_expr fmt init_t0;

    for i = 0 to k - 1 do
      echo fmt (string_of_int i);

      if i > 0 then assert_expr fmt (trans_t (i-1) i);

      push fmt;
      assert_expr fmt (Term.mk_not (phi_t i));
      check_sat fmt;
      pop fmt;

      assert_expr fmt (phi_t i);

    done;

  end;
  pop fmt;



  (* Checking k-inductive case *)
  add_section fmt (sprintf "%d-Inductiveness" k);
  echo fmt (sprintf "Checking %d-inductive case" k);
  push fmt;

  (* unroll k times*)
  let l = ref [] in
  for i = k - 1 downto 0 do
    l := (phi_t i) :: (trans_t i (i+1)) :: !l
  done;

  assert_expr fmt (Term.mk_and !l);
  assert_expr fmt (Term.mk_not (phi_t k));
  check_sat fmt;
  pop fmt;


  (* Checking implication of indutive invariant to original properties *)
  add_section fmt "Property subsumption";
  echo fmt "Checking property subsumption";
  push fmt;
  begin
    if quant_free then
      let v = UfSymbol.mk_fresh_uf_symbol [] (ty_index ()) in
      declare_const fmt v;
      let f = Term.mk_implies [phi_u v []; prop_u v []] in
      assert_expr fmt (Term.mk_not f)
    else
      let v = Var.mk_fresh_var (ty_index ()) in
      let f = Term.mk_forall [v] (Term.mk_implies [phi_v v; prop_v v]) in
      assert_expr fmt (Term.mk_not f);
  end;

  check_sat fmt;
  pop fmt;
  sexit fmt;


  (* Close files *)
  close_out certif_oc;
  close_out header_oc;

  (* Time statistics *)
  Stat.record_time Stat.certif_gen_time;

  (* Show which file contains the certificate *)
  KEvent.log L_note
    "Certificate checker was written in @{<b>%s@}"
    certificate_filename

(*****************************************)
(* Certificates for frontend translation *)
(*****************************************)

(* Name of the system observing the jKind and Kind2 systems and comparing
   values of their states *)
let obs_name = "OBS"

(* Add an additional scope to a state variable *)
let add_scope_state_var scope sv =
  (* if StateVar.equal_state_vars (TransSys.init_flag_state_var sys) sv then sv *)
  (* else *)
  (* TODO we use to not scope init_flags, still the case? *)
    StateVar.mk_state_var
      ~is_input:(StateVar.is_input sv)
      ~is_const:(StateVar.is_const sv)
      ~for_inv_gen:(StateVar.for_inv_gen sv)
      (StateVar.name_of_state_var sv)
      (scope @ StateVar.scope_of_state_var sv)
      (StateVar.type_of_state_var sv)

(* Remove top scope of a state variable *)
let unscope_state_var sv =
  (* if StateVar.equal_state_vars TransSys.init_flag_svar sv then sv *)
  (* else *)
  (* TODO we use to not scope init_flags, still the case? *)
    StateVar.mk_state_var
      ~is_input:(StateVar.is_input sv)
      ~is_const:(StateVar.is_const sv)
      ~for_inv_gen:(StateVar.for_inv_gen sv)
      (StateVar.name_of_state_var sv)
      (StateVar.scope_of_state_var sv |> List.tl)
      (StateVar.type_of_state_var sv)

(* Add an additional scope to a variable *)
let add_scope_var scope v =
  if Var.is_state_var_instance v then
    Var.mk_state_var_instance
      (Var.state_var_of_state_var_instance v |> add_scope_state_var scope)
      (Var.offset_of_state_var_instance v)
  else 
  if Var.is_const_state_var v then
    Var.mk_const_state_var
      (Var.state_var_of_state_var_instance v |> add_scope_state_var scope)
  else
    v

(* Remove top scope of a variable *)
let unscope_var v =
  if Var.is_state_var_instance v then
    Var.mk_state_var_instance
      (Var.state_var_of_state_var_instance v |> unscope_state_var)
      (Var.offset_of_state_var_instance v)
  else 
  if Var.is_const_state_var v then
    Var.mk_const_state_var
      (Var.state_var_of_state_var_instance v |> unscope_state_var)
  else
    v


let unscope_term t =
  Term.map (fun _ t -> match Term.node_of_term t with
      | Term.T.FreeVar v -> Term.mk_var (unscope_var v)
      | _ -> t
    ) t


(* Helper function for creating an initial term with scoping information *)
let mk_init_term init_flag scope sys =
  let vinit = Var.mk_state_var_instance
      (TransSys.init_flag_state_var sys) TransSys.init_base in
  let viflag = Var.mk_state_var_instance init_flag TransSys.init_base in
  Term.mk_uf (TS.init_uf_symbol sys)
    (List.map (fun v ->
         if Var.equal_vars v vinit then
           Term.mk_var viflag
         else Term.mk_var (add_scope_var scope v))
       (TS.init_formals sys))


(* Helper function for creating a transition term with scoping information *)
let mk_trans_term init_flag scope sys =
  let vinit = Var.mk_state_var_instance
      (TransSys.init_flag_state_var sys) Numeral.(TransSys.trans_base - one) in
  let viflag = Var.mk_state_var_instance
      init_flag Numeral.(TransSys.trans_base - one) in
  let vinit' = Var.mk_state_var_instance
      (TransSys.init_flag_state_var sys) TransSys.trans_base in
  let viflag' = Var.mk_state_var_instance init_flag TransSys.trans_base in

  Term.mk_uf (TS.trans_uf_symbol sys)
    (List.map (fun v ->
         if Var.equal_vars v vinit' then
           Term.mk_var viflag'
         else if Var.equal_vars v vinit then
           Term.mk_var viflag
         else Term.mk_var (add_scope_var scope v))
        (TS.trans_formals sys))


(* Helper function for creating terms of state variables at offset 0 with an
   extra scope *)
let term_state_var0 scope sv =
  Var.mk_state_var_instance (add_scope_state_var scope sv) Numeral.zero
  |> Term.mk_var


(* Helper function for creating terms of state variables at offset 1 with an
   extra scope *)
let term_state_var1 scope sv =
  Var.mk_state_var_instance (add_scope_state_var scope sv) Numeral.one
  |> Term.mk_var




let mk_obs_eqs kind2_sys ?(prime=false) ?(prop=false) lustre_vars orig_kind2_vars =

  let term_state_var =
    if prime then term_state_var1 [obs_name]
    else term_state_var0 [obs_name] in

  List.fold_left (fun acc sv ->

      let jkind_vars =
        JkindParser.jkind_vars_of_kind2_statevar kind2_sys lustre_vars sv in

      Debug.fec "(Kind2->JKind): %a -> [ %a ]"
         StateVar.pp_print_state_var sv
         (pp_print_list StateVar.pp_print_state_var ", ") jkind_vars;

      (* Fail if variables of properties do not have a jKind equivalent *)
      if jkind_vars = [] then begin
  
      KEvent.log L_info
        "Could not find a match for the%s variable %a."
        (if StateVar.is_input sv then " INPUT" else "")
        StateVar.pp_print_state_var sv;
      
        if prop (* && jkind_vars = [] *) then begin

          KEvent.log L_fatal "Frontend certificate was not generated.";
          
          raise (CouldNotProve
            (fun fmt ->
              Format.fprintf fmt
                "Could not find a match for the property variable %a."
                StateVar.pp_print_state_var sv
            )
          )
        end;
      end;


      List.fold_left (fun acc jv ->
          global_jkind_vars := List.filter (fun sv -> not (StateVar.equal_state_vars sv jv)) !global_jkind_vars;
          Term.mk_eq [term_state_var sv; term_state_var jv] :: acc
        ) acc jkind_vars

    ) [] orig_kind2_vars
  |> List.rev


(* Create a term for the observational equivalence of the original state
   variables of Kind2 ([orig_kind2_vars]) and their computed jKind
   counterparts. The optional parameter [prime] controls if the resulting
   eqaulities should be on primed varaibles. *)
(*let mk_prop_obs ~only_out lustre_vars kind2_sys =
  
  let orig_kind2_vars = TS.state_vars kind2_sys in

  let vars =
    if only_out then
      List.filter (fun x -> not (StateVar.is_input x)) orig_kind2_vars
    else orig_kind2_vars in      
  let eqs = mk_obs_eqs kind2_sys ~prime:false lustre_vars vars in
  
  (* Conjunction of equalities between state varaibles *)
  ["Observational_Equivalence",
   Property.Generated (None, []),
   Term.mk_and eqs]*)


let mk_multiprop_obs ~only_out lustre_vars kind2_sys =
 
  let orig_kind2_vars = TS.state_vars kind2_sys in
  
  let prop_vs =
    List.fold_left (fun acc p ->
        Term.state_vars_of_term p.Property.prop_term |> SVS.union acc
      ) SVS.empty (TS.get_real_properties kind2_sys)
  in
  
  let other_vars =
    List.filter (fun sv -> not (SVS.mem sv prop_vs) &&
                           (not only_out || not (StateVar.is_input sv))
                ) orig_kind2_vars in

  let prop_vars = SVS.elements prop_vs in
  
  let props_eqs =
    mk_obs_eqs kind2_sys ~prime:false ~prop:true lustre_vars prop_vars in
  let others_eqs =
    mk_obs_eqs kind2_sys  ~prime:false ~prop:false lustre_vars other_vars in

  let cpt = ref 0 in
  let props_obs =
    List.map (fun eq ->
        incr cpt;
        { Property.prop_name =
            "PROPERTY_Observational_Equivalence_" ^(string_of_int !cpt);
          prop_source = Property.Generated (None, []);
          prop_term = eq;
          prop_status = Property.PropUnknown; }
      ) props_eqs in

  let others_obs =
    List.map (fun eq ->
        incr cpt;
        { Property.prop_name =
            "OTHER_Observational_Equivalence_" ^(string_of_int !cpt);
          prop_source = Property.Candidate None ;
          prop_term = eq;
          prop_status = Property.PropUnknown; }
        ) others_eqs in

  props_obs @ others_obs
  


let is_nondet sv =
  let nondetst, _ = (LustreIdent.oracle_ident :> string * int list) in
  let name = StateVar.name_of_state_var sv in
  try Scanf.sscanf name "%s@_%s" (fun s _ -> s = nondetst)
  with Scanf.Scan_failure _ -> false
  

(* Create additional constraints that force the input state varaibles to be the
   same in Kind2 and jKind. *)
let same_inputs kind2_sys ?(prime=false) lustre_vars orig_kind2_vars =
  mk_obs_eqs kind2_sys ~prime
    lustre_vars
    (List.filter (fun sv -> StateVar.is_input sv || is_nondet sv)
       orig_kind2_vars)
  |> Term.mk_and



let mk_inst init_flag sys formal_vars =
  let map_down, map_up =
    List.fold_left (fun (map_down, map_up) vf ->
        let v =
          if StateVar.equal_state_vars vf (TransSys.init_flag_state_var sys)
          then init_flag
          else add_scope_state_var [obs_name] vf
        in
        StateVar.StateVarMap.add v vf map_down,
        StateVar.StateVarMap.add vf v map_up
      ) StateVar.StateVarMap.(empty, empty) formal_vars
  in
  sys,
  [ { TransSys.pos = Lib.dummy_pos;
      map_down;
      map_up;
      guard_clock = (fun _ t -> t);
      assumes = None } ]


let add_scope_and_register_bounds scope orig_tbl dest_tbl sv =
  let sv' = add_scope_state_var scope sv in
  begin
    try SVH.add dest_tbl sv' (SVH.find orig_tbl sv)
    with Not_found -> ()
  end;
  sv'
  

(* Create a system that calls the Kind2 system [kind2_sys] and the jKind system
   [jkind_sys] in parallel synchronous composition and observes the values of
   their state variables. All variables are put under a new scope. *)
let merge_systems lustre_vars kind2_sys jkind_sys =

  let kind2_bounds = TransSys.get_state_var_bounds kind2_sys in
  let jkind_bounds = TransSys.get_state_var_bounds jkind_sys in
  let bounds = SVH.copy kind2_bounds in
  SVH.iter (SVH.add bounds) jkind_bounds;
  
  (* Remember the original state variables*)
  let orig_kind2_vars = TS.state_vars kind2_sys in
  let orig_jkind_vars = TS.state_vars jkind_sys in

  (* let init_flag = StateVar.mk_init_flag [obs_name] in *)
  let init_flag = TS.init_flag_state_var kind2_sys
                  |> add_scope_state_var [obs_name] in

  (* Create versions of variables with the new scope *)
  let kind2_vars =
    List.map (add_scope_and_register_bounds [obs_name] kind2_bounds bounds)
      orig_kind2_vars in
  let jkind_vars =
    List.map (add_scope_and_register_bounds [obs_name] jkind_bounds bounds)
      orig_jkind_vars in
  let state_vars =
    (* init_flag :: *)
    kind2_vars @ jkind_vars |>
    List.filter (fun sv ->
        not (StateVar.equal_state_vars
               sv (TransSys.init_flag_state_var kind2_sys)))
  in
  let vars_types = List.map StateVar.type_of_state_var state_vars in
  
  let state_vars0 = List.map (fun sv ->
      Var.mk_state_var_instance sv Numeral.zero)
      state_vars in

  let state_vars1 = List.map (fun sv ->
      Var.mk_state_var_instance sv Numeral.one)
      state_vars in

  let unconstrained_inputs =
     StateVar.StateVarSet.union
       (TS.unconstrained_inputs kind2_sys)
       (TS.unconstrained_inputs jkind_sys)
  in

  (* Symbol for initial predicate of new system *)
  let init_uf =
    UfSymbol.mk_uf_symbol
      (Ids.init_uf_string ^"_"^ obs_name) 
      vars_types
      Type.t_bool 
  in

  (* Symbol for transition relation of new system *)
  let trans_uf =
    UfSymbol.mk_uf_symbol
      (Ids.trans_uf_string ^"_"^ obs_name) 
      (vars_types @ vars_types)
      Type.t_bool 
  in

  (* Term describing the initial states: [inputs1 = inputs2 /\ I1(X1) /\
     I2(X2)]. Here [inputs1] is the subset of [X1] which are input
     varaibles. *)
  let init_term =
    Term.mk_and [
      (* init flag *)
      Var.mk_state_var_instance init_flag TransSys.init_base |> Term.mk_var;
      same_inputs kind2_sys lustre_vars orig_kind2_vars;
      mk_init_term init_flag [obs_name] kind2_sys;
      mk_init_term init_flag [obs_name] jkind_sys] in

  (* Term describing the transition relation: [inputs1' = inputs2' /\
     T1(X1,X1') /\ T2(X2,X2')]. Here [inputs1'] is the subset of [X1'] which
     are input varaibles. *)
  let trans_term =
    Term.mk_and [
      (* init flag *)
      Var.mk_state_var_instance init_flag TransSys.trans_base
      |> Term.mk_var |> Term.mk_not;
      same_inputs ~prime:true kind2_sys lustre_vars orig_kind2_vars;
      mk_trans_term init_flag [obs_name] kind2_sys;
      mk_trans_term init_flag [obs_name] jkind_sys] in

  let init_args = state_vars0 in
  let trans_args = state_vars1 @ state_vars0 in

  global_jkind_vars := orig_jkind_vars; 
  
  (* Create properties *)
  let props = mk_multiprop_obs ~only_out:false lustre_vars kind2_sys in

  Debug.fec 
     "@[<hv 4>Unmatched JKind vars:@,%a@]@."
     (pp_print_list StateVar.pp_print_state_var "@,") !global_jkind_vars;


  let kind2_subsys_inst = mk_inst init_flag kind2_sys orig_kind2_vars in
  let jkind_subsys_inst = mk_inst init_flag jkind_sys orig_jkind_vars in
  
  (* Create observer system *)
  let obs_sys, _ =
    TS.mk_trans_sys
      [obs_name]
      None
      init_flag
      (* [] *)
      state_vars
      unconstrained_inputs
      bounds
      []
      []
      init_uf
      init_args
      init_term
      trans_uf
      trans_args
      trans_term
      [kind2_subsys_inst; jkind_subsys_inst]
      props
      (None, []) (Invs.empty ()) in

  (* (\* Add caller info to subnodes *\) *)
  (* TS.add_caller kind2_sys *)
  (*   obs_sys ((List.combine orig_kind2_vars kind2_vars), (fun t -> t)); *)

  (* TS.add_caller jkind_sys *)
  (*   obs_sys ((List.combine orig_jkind_vars jkind_vars), (fun t -> t)); *)

  (* Return the observer system *)
  obs_sys



let export_obs_system ~trace_lfsc_defs
    dirname file definitions_files
    names_obs names_kind2 names_jkind kind2_sys same_inputs_term =

  let filename = Filename.concat dirname file in

  let oc =
    if trace_lfsc_defs then
      files_cat_open
        ~add_prefix:(fun fmt ->
            if trace_lfsc_defs then begin
              add_logic fmt kind2_sys;
              add_arrays fmt
            end else ())
        definitions_files filename |> Unix.out_channel_of_descr
    else open_out filename in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;

  let same_inputs_pred = "same_inputs" in
  
  (* Variables i and j to be used later *)
  let fvi = Var.mk_free_var (HString.mk_hstring "i") (ty_index ()) in
  let sigma_0i = TM.singleton t0 (Term.mk_var fvi) in

  (* Declaring constraint to make inputs the same (I i) *)
  add_section fmt "Same inputs for both subsystems";
  let sip_s =
    UfSymbol.mk_uf_symbol same_inputs_pred
      [(ty_index ())] Type.t_bool in
  let sip_def = roll sigma_0i (unscope_term same_inputs_term) in
  define_fun ~trace_lfsc_defs fmt sip_s [fvi] Type.t_bool sip_def;

  add_section fmt "Initial states for observer";

  s_define_pred ~trace_lfsc_defs fmt names_obs.init ["i"]
    (sprintf "(and (%s i) (and (%s i) (%s i)))"
       same_inputs_pred names_kind2.init names_jkind.init);

  add_section fmt "Transition relation for observer";

  s_define_pred ~trace_lfsc_defs fmt names_obs.trans ["i"; "j"]
    (sprintf "(and (%s j) (and (%s i j) (%s i j)))"
       same_inputs_pred names_kind2.trans names_jkind.trans);

  add_section fmt "Weak observational equivalence";

  s_define_pred ~trace_lfsc_defs fmt names_obs.prop ["i"]
    (sprintf "(= (%s i) (%s i))" names_kind2.prop names_jkind.prop);

  (* dummy goal if we only want to do tracing *)
  if trace_lfsc_defs then begin
    assert_expr fmt Term.t_false;
    check_sat fmt;
    sexit fmt;
  end;
  close_out oc



(* Generate a certificate for the frontend translation / simplification phases
   as a system in native input. To be verified, this certificate is expected to
   be fed back to Kind 2. *)
let generate_frontend_obs node kind2_sys dirname =

  (* Time statistics *)
  Stat.start_timer Stat.certif_frontend_time;

  KEvent.log L_note "Generating frontend eq-observer with jKind...";

  (* Call jKind and get back its internal transition system for the same
     file *)
  let jkind_sys = JkindParser.get_jkind_transsys (Flags.input_file ()) in

  (* Find original Lustre names (with callsite info) for the state variables
     in the Kind2 system. *)
  let lustre_vars =
    InputSystem.reconstruct_lustre_streams node (TS.state_vars kind2_sys) in

    Debug.fec "Lustre vars:@,%a"
     (fun fmt ->
        StateVar.StateVarMap.iter (fun sv l ->
            List.iter (fun (sv', l') ->
                Format.fprintf fmt "%a -> %a : %a@,"
                  StateVar.pp_print_state_var sv
                  StateVar.pp_print_state_var sv'
                  (pp_print_list
                     (fun fmt (lid, n, cond) ->
                        Format.fprintf fmt "%a [%d] %a"
                          (LustreIdent.pp_print_ident true) lid n
                          (pp_print_list (fun fmt -> function
                           | LustreNode.CActivate c ->
                             Format.fprintf fmt "ACTIVATE ON %s"
                               (StateVar.string_of_state_var c)
                           | LustreNode.CRestart c ->
                             Format.fprintf fmt "RESTART ON %s"
                               (StateVar.string_of_state_var c))
                              ", ") cond
                     )
                     " , ") l'
              ) l
          ))
     lustre_vars;


  (* Add jkind properties *)
  let jkind_props = List.fold_left (fun acc p ->
    let open Property in
    match p.prop_term
          |> Term.free_var_of_term
          |> Var.state_var_of_state_var_instance
          |> JkindParser.jkind_vars_of_kind2_statevar kind2_sys lustre_vars
    with
    | [] -> acc
    | jksvs ->
      let jkp =
        List.map (fun jksv ->
            Var.mk_state_var_instance jksv TS.prop_base
            |> Term.mk_var
          ) jksvs
        |> Term.mk_and
      in
      { p with prop_status = PropUnknown; prop_term = jkp } :: acc
    | exception _ -> acc
  ) [] (TransSys.get_properties kind2_sys) in

  let jkind_sys = TS.add_properties jkind_sys jkind_props in

  (* Create the observer system with the property of observational
     equivalence. *)
  let obs_sys = merge_systems lustre_vars kind2_sys jkind_sys in

  let filename = Filename.concat dirname "FEC.kind2" in

  (* Output certificate in native format *)
  NativeInput.dump_native_to obs_sys filename;

  let names_kind2 = names_kind2 [] in
  let names_jkind = names_jkind [] in

  (* Export JKind system in SMT-LIB2 format *)
  export_system ~trace_lfsc_defs:false
    (* "System constructed by JKind" *)
    dirname jkind_defs_f names_jkind jkind_sys "JKind";

  export_system ~trace_lfsc_defs:true
    (* "System constructed by JKind (tracing info for cvc5/LFSC)" *)
    dirname jkind_defs_lfsc_f names_jkind jkind_sys "JKind";

  let jkind_defs_path = Filename.concat dirname jkind_defs_f in
  let jkind_defs_lfsc_path = Filename.concat dirname jkind_defs_lfsc_f in

  let kind2_defs_path = Filename.concat dirname kind2_defs_f in

  let observer_deps = [kind2_defs_path; jkind_defs_path] in

  let same_inputs_term =
    same_inputs kind2_sys lustre_vars (TS.state_vars kind2_sys) in
  
  (* Export Observer system in SMT-LIB2 format for use in proof *)
  export_obs_system ~trace_lfsc_defs:false
    dirname obs_defs_f observer_deps
    names_obs names_kind2 names_jkind kind2_sys same_inputs_term;

  export_obs_system ~trace_lfsc_defs:true
    dirname obs_defs_lfsc_f observer_deps
    names_obs names_kind2 names_jkind kind2_sys same_inputs_term;

  let obs_defs_path = Filename.concat dirname obs_defs_f in
  let obs_defs_lfsc_path = Filename.concat dirname obs_defs_lfsc_f in

  let jkind_cert_sys = {
    names = names_jkind;
    smt2_file = jkind_defs_path;
    smt2_lfsc_trace_file = jkind_defs_lfsc_path;
  } in

  let obs_cert_sys = {
    names = names_obs;
    smt2_file = obs_defs_path;
    smt2_lfsc_trace_file = obs_defs_lfsc_path;
  } in

  
  (* Time statistics *)
  Stat.record_time Stat.certif_frontend_time;

  (* Show which file contains the certificate *)
    Debug.fec 
      "Frontend eq-observer was written in %s, \
       run Kind 2 on it" filename;

  jkind_cert_sys, obs_cert_sys




let generate_frontend_certificates sys dirname =

  assert(is_fec sys);

  KEvent.set_module `Certif;

  (* Extract the global raw certificate of the system *)
  let prop, (k, phi) = global_certificate sys in

  Stat.start_timer Stat.certif_min_time;
  Stat.set k Stat.certif_old_k;
  Stat.set (Certificate.size (k, phi)) Stat.certif_old_size;

  (* Perform minimization of certificate *)
  let k, phi = match Flags.Certif.mink () with
    | `No -> k, phi
    | _ ->
      (* Simplify certificate *)
      let k, uinvs = minimize_certificate sys in
      k, Term.mk_and (prop :: uinvs)

  in

  (* Remove the OBS scope *)
  let phi = unscope_term phi in
  
  (* Record statistics for minimization *)
  Stat.record_time Stat.certif_min_time;  
  Stat.set k Stat.certif_k;
  Stat.set (Certificate.size (k, phi)) Stat.certif_size;

  let deps = [kind2_defs_f; jkind_defs_f; obs_defs_f]
           |> List.map (Filename.concat dirname) in
  
  (* Export k-inductive invariant phi in SMT-LIB2 format *)
  export_phi ~trace_lfsc_defs:false dirname obs_phi_f deps names_obs sys phi;

  export_phi ~trace_lfsc_defs:true dirname obs_phi_lfsc_f
    deps names_obs sys phi;

  let obs_phi_path = Filename.concat dirname obs_phi_f in
  let obs_phi_lfsc_path = Filename.concat dirname obs_phi_lfsc_f in
  
  (* definitions to use for the checks *)
  let smt2_definitions =
    [kind2_defs_f; jkind_defs_f; obs_defs_f; obs_phi_f]
    |> List.map (Filename.concat dirname) in

  let base =
    mononames_base_check sys
      dirname frontend_base_f smt2_definitions k names_obs in

  let induction =
    mononames_induction_check sys
      dirname frontend_induction_f smt2_definitions k names_obs in

  let implication = 
    mononames_implication_check sys
      dirname frontend_implication_f smt2_definitions names_obs in

  (* Time statistics *)
  Stat.record_time Stat.certif_gen_time;

  let pred v =
    if StateVar.is_const v then None
    else Some (StateVar.uf_symbol_of_state_var v)
  in

  let kind2_sys = List.nth (TS.get_subsystems sys) 1 in
  let kind2_svars = List.filter_map pred (TS.state_vars kind2_sys) in

  let jkind_sys = List.nth (TS.get_subsystems sys) 0 in
  let jkind_svars = List.filter_map pred (TS.state_vars jkind_sys) in

  let obs_sys = obs_cert_sys dirname in

  let inv = {
    k;
    name = names_obs.phi;
    dirname;
    phi_file = obs_phi_path;
    phi_lfsc_trace_file = obs_phi_lfsc_path;
    base;
    induction;
    implication;
    for_system = obs_sys;
    kind2_system = kind2_cert_sys kind2_svars dirname;
    jkind_system = jkind_cert_sys jkind_svars dirname;
    obs_system = obs_sys;
  } in
  
  
  (* Time statistics *)
  Stat.record_time Stat.certif_gen_time;

  (* Show which file contains the certificate *)
  Debug.certif 
     "SMT-LIB2 frontend certificates were written in %s" dirname;

  inv




(****************************)
(* Checker scripts for glue *)
(****************************)


let z3_cmd = "z3 -smt2 -in"
let cvc5_cmd = "cvc5 --incremental --lang=smt2"
let yices2_cmd = "yices-smt2 --incremental"

let goto_cert_dir="cd $(dirname \"$(which \"$0\")\")\n"

let select_solver_script =
  Format.sprintf
  "case $1 in
    z3)
        solver=\"%s\"
        ;;
    cvc5)
        solver=\"%s\"
        ;;
    yices2)
        solver=\"%s\"
        ;;
    *)
        solver=\"$1\"
        ;;
    esac\n"
  z3_cmd cvc5_cmd yices2_cmd

let certificate_checker_script =
  "#!/bin/sh\n" ^
  "set -e\n" ^
  select_solver_script ^
  goto_cert_dir ^
  "cat certificate_prelude.smt2 kind2_sys.smt2 certificate.smt2 | $solver"

let fecc_checker_script =
  "#!/bin/sh\n" ^
  "set -e\n" ^
  select_solver_script ^
  goto_cert_dir ^
  (* "cat FECC_prelude.smt2 kind2_sys.smt2 jkind_sys.smt2 observer_sys.smt2 FECC.smt2 | $solver" *)
  "cat FECC_prelude.smt2 observer_sys.smt2 FECC.smt2 | $solver"


(*****************************************)
(* Creation of intermediate certificates *)
(*****************************************)


(* Generate all certificates in the directory given by {!Flags.output_dir}. *)
let generate_smt2_certificates input sys =

  Proof.set_proof_logic (TS.get_logic sys);
  
  Hashtbl.clear solver_actlits;

  let dirname =
    (* Create directories if they don't exist. *)
    Flags.output_dir () |> mk_dir;
    let dir = Filename.concat (Flags.output_dir ()) "certif" in
    mk_dir dir ;
    dir
  in
  create_dir dirname;

  (try generate_certificate sys dirname
   with e ->
     (* Send statistics *)
     KEvent.stat Stat.[certif_stats_title, certif_stats];
     raise e);

  (* Only generate frontend observational equivalence system for Lustre *)
  let gen_frontend =
    if InputSystem.is_lustre_input input then
      try
        generate_frontend_obs input sys dirname |> ignore;
        true
      with Failure s ->
        KEvent.log L_warn "%s@.(No frontend observer)" s;
        false
    else begin
      KEvent.log L_warn "No certificate for frontend";
      false
    end
  in
  
  let open Unix in

  let certif_script_name =
    Filename.concat dirname
      (if is_fec sys then "FECC_checker" else "certificate_checker") in
  let csoc = openfile certif_script_name [O_WRONLY; O_CREAT; O_TRUNC] 0o755
             |> out_channel_of_descr in
  let fmt_cs = formatter_of_out_channel csoc in
  Format.pp_print_string fmt_cs
    (if is_fec sys then fecc_checker_script else certificate_checker_script);
  close_out csoc;

  (* Send statistics *)
  KEvent.stat Stat.[certif_stats_title, certif_stats];

  (* Recursive call *)
  if not (is_fec sys) && call_frontend && gen_frontend then begin

    KEvent.log L_note "@{<b>Generating frontend certificate@}";
    let cmd_l =
      Array.to_list Sys.argv
      |> List.filter (fun s -> s <> (Flags.input_file ()))
    in

    let cmd =
      asprintf "%a %s"
        (pp_print_list pp_print_string " ") cmd_l
        (Filename.concat dirname "FEC.kind2")
    in
    (* Format.printf "cmd: %s@.@." cmd ; *)
    Debug.certif "Second run with: %s" cmd;

    match Sys.command cmd with
    | 0 | 20 -> ()
    | c ->
      KEvent.log L_warn
        "Failed to generate frontend certificate (return code %d)" c
  end  


(********************************)
(* Creation of LFSC proofs      *)
(********************************)

(* Remove temporary files for certificates and intermediate certificates *)
let remove dirname =
  let temps = Sys.readdir dirname in
  Array.iter (fun f -> Sys.remove (Filename.concat dirname f)) temps;
  Unix.rmdir dirname


(* Temporary fix for proofs that contain dummy A0 input *)
(*let fix_A0 final_lfsc =
  Sys.command ("sed -i '' 's/A0/truth/' " ^ final_lfsc)
  |> ignore*)


(* Generate all certificates in the directory given by {!Flags.output_dir}. *)
let generate_all_proofs uid input sys =

  Proof.set_proof_logic (TS.get_logic sys);

  Hashtbl.clear solver_actlits;
  
  let dirname =
    if is_fec sys then Filename.dirname (Flags.input_file ())
    else begin
      Flags.output_dir () |> mk_dir ;
      Filename.concat (Flags.output_dir ())
        ("certificates." ^ string_of_int uid)
    end
  in
  create_dir dirname;

  if not (is_fec sys) then begin
    let cert_inv, syms =
      try
        let cert_inv = generate_split_certificates sys dirname in
        (cert_inv, Proof.generate_inv_proof cert_inv)
      with e ->
        (* Send statistics *)
        KEvent.stat Stat.[ (certif_stats_title, certif_stats) ];
        raise e
    in
    let inv_lfsc = Filename.concat dirname Proof.proofname in
    let front_lfsc = Filename.concat dirname Proof.frontend_proofname in
    let trust_lfsc = Filename.concat dirname Proof.trustfname in
    Flags.output_dir () |> mk_dir ;
    let final_lfsc =
      Filename.concat (Flags.output_dir ())
        (String.concat "."
           [Filename.basename (Flags.input_file ());
            string_of_int uid; "lfsc"]) in
    let final_trust =
      Filename.concat (Flags.output_dir ())
        (String.concat "."
           [Filename.basename (Flags.input_file ());
            string_of_int uid; "trusted_aux"; "lfsc"]) in

    (* Copy first LFSC proof in case *)
    file_copy inv_lfsc final_lfsc;
    if Sys.file_exists trust_lfsc then file_copy trust_lfsc final_trust;
    
    (* Only generate frontend observational equivalence system for Lustre *)
    let gen_frontend =
      if InputSystem.is_lustre_input input then
        try
          generate_frontend_obs input sys dirname |> ignore;
          true
        with Failure s ->
          KEvent.log L_warn "%s@ No frontend observer." s;
          false
      else begin
        Debug.certif "No certificate for frontend";
        false
      end
    in

    (* Send statistics *)
    KEvent.stat Stat.[certif_stats_title, certif_stats];

    if call_frontend then begin

      if gen_frontend then begin

        KEvent.log L_note "@{<b>Generating frontend proof@}";
        let cmd_l =
          Array.to_list Sys.argv
          |> List.filter (fun s -> s <> (Flags.input_file ()))
        in

        let cmd =
          asprintf "%a %s"
            (pp_print_list pp_print_string " ") cmd_l
            (Filename.concat dirname "FEC.kind2")
        in
        Debug.certif "Second run with: %s" cmd;

        begin match Sys.command cmd with
          | 0 | 20 ->
            let filter_and_copy_lines ic oc keep =
              let rec read_line () =
                try
                  let line = input_line ic in
                  if keep line then Printf.fprintf oc "%s\n" line ;
                  read_line ()
                with End_of_file -> ()
              in
              read_line ()
            in
            let sym_defs =
              List.map
                (fun sym -> "(define " ^ HString.string_of_hstring sym)
                syms
            in
            let pred l =
              List.exists (fun sym -> Lib.string_starts_with l sym) sym_defs
              |> not
            in
            let oc =
              open_out_gen [ Open_append; Open_creat ] 0o666 final_lfsc
            in
            filter_and_copy_lines (open_in front_lfsc) oc pred ;
            fprintf (formatter_of_out_channel oc) ";; Final proof of safety\n@.";
            Proof.write_safe_proof
              (formatter_of_out_channel oc)
              cert_inv.kind2_system cert_inv.jkind_system;
            close_out oc;
            if Sys.file_exists trust_lfsc then file_copy trust_lfsc final_trust;

          | c ->
            KEvent.log L_warn
              "Failed to generate frontend proof (return code %d)" c;
            file_copy inv_lfsc final_lfsc;
            if Sys.file_exists trust_lfsc then file_copy trust_lfsc final_trust;

        end;
      end;

      if clean_tmp then begin
        Debug.certif "Cleaning temporary files";
        remove dirname;
      end;

      (* fix_A0 final_lfsc; *) (* temporary *)
      KEvent.log L_note "Final @{<green>LFSC proof@} written to @{<b>%s@}" final_lfsc;
      if Sys.file_exists final_trust then 
        KEvent.log L_warn "Some trusted assumptions remain to be proven in @{<b>%s@}"
          final_trust;
    end;
  end
  else begin

    let frontend_inv = generate_frontend_certificates sys dirname in

    (try
      Proof.generate_frontend_proof frontend_inv;
     with e ->
       (* Send statistics *)
       KEvent.stat Stat.[certif_stats_title, certif_stats];
       raise e);

    (* Send statistics *)
    KEvent.stat Stat.[certif_stats_title, certif_stats];

  end
