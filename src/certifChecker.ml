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

module TS = TransSys
module TM = Term.TermMap
module TH = Term.TermHashtbl
module SVS = StateVar.StateVarSet
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
let abstr_index = true 


(****************************)
(* Global hconsed constants *)
(****************************)
let s_and = Symbol.mk_symbol `AND
let s_or = Symbol.mk_symbol `OR
let s_not = Symbol.mk_symbol `NOT


let ty_index_name = "index"
let ty_index = if abstr_index then Type.mk_abstr ty_index_name else Type.t_int 

let index_sym_of_int i = "%%" ^ string_of_int i
let index_of_int =
  if not abstr_index then Term.mk_num_of_int
  else fun i ->
    Term.mk_uf
      (UfSymbol.mk_uf_symbol (index_sym_of_int i) [] ty_index)
      []

let t0 = Term.mk_num_of_int 0 (* index_of_int 0 *)
let t1 = Term.mk_num_of_int 1 (* index_of_int 1 *)


(*********************)
(* Utility functions *)
(*********************)

(* Hashtable from activation literal to term *)
let hactlits = TH.create 2001


(* Create an activation literal only if it does not currently exists. In this
   case declare it in the solver and assert its definition. If it exists simply
   get the activatition literal corresponding to the term. In all cases, the
   activation literal is returned at the end. *)
let actlitify ?(imp=false) solver t =
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
  try if not (Sys.is_directory dir) then failwith (dir^" is not a directory")
  with Sys_error _ -> Unix.mkdir dir 0o755


(*************************************************************************)
(* Printing functions for the certificate.                               *)
(* We use the generic SMTLIB pretty printer for that because we want to  *)
(* create SMTLIB2 compliant certificates.                                *)
(*************************************************************************)
        
(* Assert the expression *)
let assert_expr fmt expr =
  fprintf fmt
    "@[<hv 1>(assert@ @[<hov>%a@])@]@." 
    SMT.pp_print_expr expr


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
  let arg_sorts = [ty_index] in
  let res_sort = UfSymbol.res_type_of_uf_symbol uf in
  declare_fun fmt fun_symbol arg_sorts res_sort


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
    SMT.pp_print_expr defn;

  if trace_lfsc_defs then begin

    fprintf fmt ";; Tracing artifact for CVC4 and LFSC proofs\n";
    
    let fs = UfSymbol.string_of_uf_symbol fun_symbol in
    let fun_def_sy = fs ^ "%def" in
    fprintf fmt "(declare-fun %s () %s)\n"
      fun_def_sy (SMT.string_of_sort res_sort);

    let cpt = ref 0 in
    let fun_def_args = List.map (fun v ->
        incr cpt;
        let ty_v = Var.type_of_var v in
        let vfs = fs ^ "%" ^ string_of_int !cpt in
        fprintf fmt "(declare-fun %s () %s)\n"
          vfs (SMT.string_of_sort ty_v);
        vfs
      ) arg_vars in

    fprintf fmt "@[<hov 1>(assert@ @[<hov 1>(=@ %s@ @[<hv 1>(%s@ %a)@])@])@]\n@."
      fun_def_sy fs (pp_print_list pp_print_string "@ ") fun_def_args
    
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

(* Extract properties and invariants together with their certificates from a
   system. *)
let extract_props_certs sys =
  let certs, props = List.fold_left (fun ((c_acc, p_acc) as acc) -> function
      | { Property.prop_source = Property.Candidate } ->
        (* Put valid candidates in invariants *)
        acc
      | { Property.prop_status = Property.PropInvariant c; prop_term = p } ->
        c :: c_acc, p :: p_acc
      | { Property.prop_name } ->
        Event.log L_info "Skipping unproved property %s" prop_name;
        acc
    ) ([], []) (TS.get_real_properties sys) in

  let certs = List.fold_left (fun c_acc (i, c) ->
      if List.exists (Term.equal i) props then c_acc
      else c :: c_acc
    ) certs (TS.get_invariants sys) in

  let certs =  List.fold_left (fun certs -> function
      | { Property.prop_status = Property.PropInvariant c;
          prop_source = Property.Candidate; prop_term = p } -> c :: certs
      | { Property.prop_name } ->
        Event.log L_info "Skipping unproved candidate %s" prop_name;
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

(* Exception raised to interrupt the computation. A continuation is given to
   resume this computation. *)
exception Reduce_cont of (unit -> Term.t list)


(* Iterative fixpoint to identify which invariants are usefull. Returns the
   subset of invs_acts which preserves inductiveness. The paramteer
   just_check_ind controls if we want to only check the induction step without
   minimizing the set of invariants.

   - Raises Exit if the invariants with the property are not inductive.

   - Raises Reduce_cont with a continuation (which miminizes the set of
     invariants) if it was called with ~just_check_ind:true.

   - Returns a subset of invs_acts which preserves inductiveness otherwise.
*)
let rec fixpoint
    solver invs_acts prev_props_act prop'act neg_prop'act trans_acts =

  let if_sat _ =
    (* this should not happen because we've already performed the inductive
       check *)
    (debug certif "[Fixpoint] fail (impossible)" end);
    raise Exit
  in

  let if_unsat _ =
    (* Activation literals in unsat core, extracted right away in case we
       modify the solver state before calling the continuation *)
    let uc = SMTSolver.get_unsat_core_lits solver in

    (* Identify the useful invariants with the unsat core *)    
    let uinvs_acts =
      List.filter (fun (a, _) -> List.exists (Term.equal a) uc) invs_acts in

    (debug certif "[Fixpoint] extracted %d useful invariants"
      (List.length uinvs_acts) end);

    let uinvs, uinvs' = List.split uinvs_acts in

    (* Create activation literals for inductive check *)
    let new_prop = Term.mk_and (prev_props_act :: uinvs) in
    let new_prop_act = actlitify solver new_prop in
    let new_prop_acts = prev_props_act :: uinvs in

    let new_prop' = Term.mk_and (prop'act :: uinvs') in
    let new_prop'act = actlitify solver new_prop' in
    
    let neg_new_prop' = Term.mk_not new_prop' in
    let neg_new_prop'act = actlitify solver neg_new_prop' in

    (* let acc = uinvs' @ acc in *)

    (* Check preservation of invariants by k-steps *)
    SMTSolver.check_sat_assuming solver
      
      (fun _ ->
         (* SAT try to find what invariants are missing *)
         (debug certif "[Fixpoint] could not verify inductiveness" end);

         fixpoint solver
           invs_acts new_prop_act new_prop'act neg_new_prop'act trans_acts)
      
      (fun _ ->
         (* UNSAT: return accumulated invariants *)
         (debug certif "[Fixpoint] OK"
           (* (pp_print_list Term.pp_print_term "@ ") acc *) end);

         (* Return useful invariants (identified by their activation
            literals) *)
         uinvs')

      (trans_acts @ new_prop_acts @ [neg_new_prop'act])
  in
  
  (* Get invariants at k - 1 *)
  let invs = List.map fst invs_acts in

  SMTSolver.trace_comment solver "fixpoint cs;";

  (* Check if the property is preserved by k-steps when assuming the
     invariants *)
  SMTSolver.check_sat_assuming solver if_sat if_unsat
    (trans_acts @ (neg_prop'act :: prev_props_act :: invs))





let check_ind_and_fixpoint ~just_check_ind
    solver invs_acts prev_props_act prop'act neg_prop'act trans_acts =

  (* Get invariants at k - 1 *)
  let invs, invs' = List.split invs_acts in

  let neg_invs'prop'act = prop'act :: invs'
                          |> Term.mk_and |> Term.mk_not |> actlitify solver in
  
  SMTSolver.trace_comment solver "check inductiveness at k;";

  (* Check k-inductiveness of whole set first *)
  SMTSolver.check_sat_assuming solver
    (fun _ -> (* SAT *)
        (debug certif "[Fixpoint] failure of whole inductive check" end);
        raise Exit)
    (fun _ -> (* UNSAT *)

     (* First cleaning *)    
     let uc = SMTSolver.get_unsat_core_lits solver in
     let invs_acts =
       List.filter (fun (a, _) -> List.exists (Term.equal a) uc) invs_acts in

     (* Continuation: execute fixpoint *)
     let cont () =
       match Flags.certif_mininvs () with
       | `HardOnly | `MediumOnly ->
         (* Only do the first inductive check if we want only hard
            minimization *)
         List.map snd invs_acts
       | _ ->
         (* Otherwise complete the fixpoint in the continuation *)
         fixpoint solver
           invs_acts prev_props_act prop'act neg_prop'act trans_acts
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
let rec minimize_hard solver trans
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
             if (Flags.certif_mininvs () = `Hard ||
                 Flags.certif_mininvs () = `HardOnly) &&
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
       if extra_needed = [] then begin
         (debug certif "[Hard Fixpoint] fail (impossible)" end);
         raise Exit
       end;
       
       (* new list of needed invariants *)
       let needed_invs = List.fold_left (fun acc (inv, inv') ->
           let invact = actlitify solver inv in
           let inv'act = actlitify solver inv' in
           (invact, inv'act) :: acc
         ) needed_invs extra_needed in

       (debug certif "Hard minimization identified %d"
          (List.length needed_invs) end);

       (* recursive call to find out if we have found an inductive set or not *)
       minimize_hard solver trans
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
  
  (debug certif "Try bound %d" k end);

  (* Construct properties from 1 to k-1 *)
  let prev_props_l = ref [prop] in
  for i = 1 to k - 1 do
    prev_props_l := Term.bump_state (Numeral.of_int i) prop :: !prev_props_l;
  done;

  (* Activation literals for properties from 1 to k-1 *)
  let prev_props_act =
    actlitify solver (Term.mk_and (List.rev !prev_props_l)) in

  (* Construct invariants (with activation literals) from 1 to k-1 and for k *)
  let invs_acts, invs_infos = List.fold_left (fun (invs_acts, invs_infos) inv ->
      let l = ref [inv] in
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
  let map_back_to_invs useful_acts =
    List.fold_left (fun acc a ->
        List.fold_left (fun acc (inv, _, _, a', _) ->
            if Term.equal a a' then inv :: acc else acc
          ) acc invs_infos
      ) [] useful_acts
  in

  let reconstruct_infos useful_acts =
    List.fold_left (fun acc a ->
        List.fold_left (fun acc (_, _, prev_inv, a', inv') ->
            if Term.equal a a' then (prev_inv, inv') :: acc else acc
          ) acc invs_infos
      ) [] useful_acts
  in

  let min_hard useful_acts =
    let useful_infos = reconstruct_infos useful_acts in
    minimize_hard solver sys
      [] useful_infos prev_props_act prop'act neg_prop'act trans_acts
    |> map_back_to_invs
  in

  let follow_up =
    match Flags.certif_mininvs () with
    | `Easy -> map_back_to_invs
    | `Medium | `MediumOnly | `Hard | `HardOnly ->
      (* Second phase of harder minimization if we decide to not stop at easy *)
      min_hard
  in
  
  try
    (* Can fail and raise Exit or Reduce_cont *)
    let useful_acts =
      check_ind_and_fixpoint ~just_check_ind
        solver invs_acts prev_props_act prop'act neg_prop'act trans_acts in
    
    (* If fixpoint returned a list of useful invariants we just return them *)
    Inductive (
      follow_up useful_acts
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

  if k > kmax then failwith
      (sprintf "[Certification] simplification of inductive invariant \
                went over bound %d" kmax);
  
  (* Asserting transition relation. *)
  TransSys.trans_of_bound sys (Numeral.of_int k)
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
   the the transition relation as this can overwhelm the solver. *)
let unroll_trans_actlits sys solver kmax =

  let rec fill acc prev = function
    | k when k > kmax -> acc
    | k ->
      let tk = TransSys.trans_of_bound sys (Numeral.of_int k) in
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
        | _, Not_inductive ->
          (* Not k-inductive *)
          failwith
            (sprintf
               "[Certification] Could not verify %d-inductiveness \
                of invariant" k);

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
    | _, Not_inductive ->
      (* Not k-inductive *)
      failwith "[Certification] Could not verify inductiveness of invariant"

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

    match try_at_bound ~just_check_ind:true
            sys solver k_mid invs prop [trans_act]
    with
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
  | Not_inductive, _ ->
    failwith "[Certification] Could not verify inductiveness of invariant"

  | Inductive useful, Not_inductive -> kmax, useful

  | Inductive_to_reduce f, Not_inductive -> kmax, f ()

  | (Inductive _ | Inductive_to_reduce _),
    (Inductive _ | Inductive_to_reduce _) ->

    (* Binary search in interval [1; kmax-2] *)
    loop_dicho sys solver kmax invs prop trans_acts_map
      (kmax - 1, res_kmax_m1) 1 (kmax - 2)


(* Minimization of certificate: returns the minimum bound for k-induction and a
   list of useful invariants for this preservation step *)
let minimize_certificate sys =
  printf "Certificate minimization@.";

  (* Extract certificates of top level system *)
  let props, certs = extract_props_certs sys in
  let certs = Certificate.split_certs certs in
  let k, invs = List.fold_left (fun (m, invs) (k, i) ->
      max m k,
      if List.exists (Term.equal i) props ||
         List.exists (Term.equal i) invs
      then invs
      else i :: invs) (0, []) certs in

  (* For stats *)
  let k_orig, nb_invs = k, List.length invs in
  
  (debug certif "Trying to simplify up to k = %d\n" k_orig end);
  
  (* Creating solver that will be used to replay and minimize inductive step *)
  let solver =
    SMTSolver.create_instance ~produce_cores:true
      (TransSys.get_logic sys) (Flags.smtsolver ())
  in
  
  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.(~- one) (Numeral.of_int (k+1));

  (* The property we want to re-verify the conjunction of all the properties *)
  let prop = Term.mk_and props in

  let min_strategy = match Flags.certif_min () with
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
    | `Bwd -> find_bound_back sys solver k invs prop
    | `FrontierDicho -> find_bound_frontier_dicho sys solver k invs prop
    | `Dicho -> find_bound_dicho sys solver k invs prop
  in

  (* We are done with this step of minimization and we don't neet the solver
     anylonger *)
  SMTSolver.delete_instance solver;
  
  (debug certif "Simplification found for k = %d\n" kmin end);

  printf "Kept %d (out of %d) invariants at bound %d (down from %d)@."
    (List.length uinvs) nb_invs kmin k_orig;

  (* Return minimum k found, and the useful invariants *)
  kmin, uinvs
  


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
let add_system_header fmt prefix sys =

  set_info fmt "system"
    (sprintf "\"Logical transition system generated by %s\""
       prefix);

  (* Original input problem *)
  set_info fmt "input" ("\""^(Flags.input_file ())^"\"");

  fprintf fmt "@."


(* Populate the headers of the certificate *)
let add_header fmt sys k init_n prop_n trans_n phi_n =

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

  (* Specify logic to help some solvers check the certificate *)
  match logic with
  | `None -> ()
  | _ -> fprintf fmt "(set-logic %a)@." SMT.pp_print_logic logic 


(* Populate the headers of the certificate *)
let monolithic_header fmt description sys init_n prop_n trans_n phi_n k =

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
  match logic with
  | `None -> ()
  | _ -> fprintf fmt "(set-logic %a)@." SMT.pp_print_logic logic 


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



let export_system fmt ?(recursive=true) ?(trace_lfsc_defs=false) prefix sys =
  
  (* add headers for info *)
  add_system_header fmt prefix sys;
  
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

(* Names of predicates *)
let init_n = "I"
let prop_n = "P"
let trans_n = "T"
let phi_n = "PHI"

let monolithic_definitions fmt ~trace_lfsc_defs description sys prop (k, phi) =
  (* add headers for info *)
  (* add_header fmt_header sys k init_n prop_n trans_n phi_n; *)

  (* add headers for info *)
  monolithic_header fmt description sys init_n prop_n trans_n phi_n k;

  if abstr_index then begin
    add_section fmt "Indexes for k-induction";
    fprintf fmt "(declare-sort %s 0)\n@." ty_index_name;
    for i = 0 to k do
      fprintf fmt "(declare-fun %s () %s)@." (index_sym_of_int i) ty_index_name;
    done
  end;
 
  let name_sys = if is_fec sys then "Kind2" else "Obs" in

  (* Do not export the definitions with tracing information for LFSC *)
  export_system fmt ~recursive:true ~trace_lfsc_defs:false name_sys sys;
  
  
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
  let fvi = Var.mk_free_var (HString.mk_hstring "i") ty_index in
  let fvj = Var.mk_free_var (HString.mk_hstring "j") ty_index in

  (* Substitutions to be used later: *)
  (* [0 -> i] *)
  let sigma_0i = TM.singleton t0 (Term.mk_var fvi) in
  (* [0 -> i; 1 -> j] *)
  let sigma_0i1j = TM.add t1 (Term.mk_var fvj) sigma_0i in
  
  (* Declaring initial state (__I__ i) *)
  add_section fmt "Initial states";
  let init_s = UfSymbol.mk_uf_symbol init_n [ty_index] Type.t_bool in
  let i0 = TransSys.init_fun_of sys Numeral.zero in
  let init_def = roll sigma_0i i0 in
  define_fun ~trace_lfsc_defs fmt init_s [fvi] Type.t_bool init_def;
  let init_t0 = Term.mk_uf init_s [index_of_int 0] in
  
  (* Declaring property (__P__ i) *)
  add_section fmt "Original property";
  let prop_s = UfSymbol.mk_uf_symbol prop_n [ty_index] Type.t_bool in
  let prop_def = roll sigma_0i prop in
  define_fun ~trace_lfsc_defs fmt prop_s [fvi] Type.t_bool prop_def;
  (* let prop_t i = Term.mk_uf prop_s [Term.mk_num_of_int i] in *)
  let prop_v v = Term.mk_uf prop_s [Term.mk_var v] in
  let prop_u u l = Term.mk_uf prop_s [Term.mk_uf u l] in

  
  (* Declaring transition steps (__T__ i j) *)
  add_section fmt "Transition_relation";  
  let trans_s = UfSymbol.mk_uf_symbol trans_n
      [ty_index; ty_index] Type.t_bool in
  let t01 = TransSys.trans_fun_of sys Numeral.zero Numeral.one in
  let trans_def = roll sigma_0i1j t01 in
  define_fun ~trace_lfsc_defs fmt trans_s [fvi; fvj] Type.t_bool trans_def;
  let trans_t i j = Term.mk_uf trans_s
      [index_of_int i; index_of_int j] in


  (* Declaring k-inductive invariant (__PHI__ i) *)
  add_section fmt (sprintf "%d-Inductive invariant" k);
  let phi_s = UfSymbol.mk_uf_symbol phi_n [ty_index] Type.t_bool in
  let phi_def = roll sigma_0i phi in
  define_fun ~trace_lfsc_defs fmt phi_s [fvi] Type.t_bool phi_def;
  let phi_t i = Term.mk_uf phi_s [index_of_int i] in
  let phi_v v = Term.mk_uf phi_s [Term.mk_var v] in
  let phi_u u l = Term.mk_uf phi_s [Term.mk_uf u l] in

  init_t0, prop_v, prop_u, trans_t, phi_t, phi_v, phi_u



let generate_lfsc_tracing sys dirname prop certif =

  let prefix = if is_fec sys then "frontend_" else "" in
  let filename = Filename.concat dirname (prefix ^ "lfsc_defs.smt2") in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;

  monolithic_definitions fmt ~trace_lfsc_defs:true
    "Dummy file for tracing LFSC definitions"
    sys prop certif
  |> ignore;

  assert_expr fmt Term.t_false;
  check_sat fmt;
  sexit fmt;
  close_out oc;
  filename


let mono_base_check sys dirname prop certif =

  let prefix = if is_fec sys then "frontend_" else "" in
  let filename = Filename.concat dirname (prefix ^ "base.smt2") in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;
  
  add_section fmt "Base case";

  let init_t0, _, _, trans_t, phi_t, _, _ =
    monolithic_definitions fmt ~trace_lfsc_defs:false
      "Base case"
      sys prop certif
  in

  let k = fst certif in
  
  if monolithic_base then
    if simple_base then
      (* Incorrect base case checking *)
      
      let l = ref [] in

      Event.log L_warn "Using potentially incorrect check for base case";

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

        let l = ref [] in
        for j = i - 1 downto 0 do
          l := trans_t j (j+1) :: !l;
        done;

        let conj =
          Term.mk_and [Term.mk_and (init_t0 :: !l);
                       Term.mk_not (phi_t i)] in
        
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
  
  sexit fmt;
  close_out oc;
  filename
    
  
  
let mono_induction_check sys dirname prop certif =

  let prefix = if is_fec sys then "frontend_" else "" in
  let filename = Filename.concat dirname (prefix ^ "induction.smt2") in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;
  
  add_section fmt "Base case";

  let _, _, _, trans_t, phi_t, _, _ =
    monolithic_definitions fmt ~trace_lfsc_defs:false
      "k-Inductive case"
      sys prop certif
  in

  let k = fst certif in

  (* Checking k-inductive case *)
  add_section fmt (sprintf "%d-Inductiveness" k);

  (* unroll k times*)
  let l = ref [] in
  for i = k - 1 downto 0 do
    l := Term.mk_and [phi_t i; trans_t i (i+1)] :: !l
  done;

  let g = Term.mk_and [Term.mk_and !l;
                       Term.mk_not (phi_t k)] in
  
  assert_expr fmt g;
  check_sat fmt;
  
  sexit fmt;
  close_out oc;
  filename



let mono_implication_check sys dirname prop certif =

  let prefix = if is_fec sys then "frontend_" else "" in
  
  let filename = Filename.concat dirname (prefix ^ "implication.smt2") in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  Format.pp_set_margin fmt file_width;
  
  add_section fmt "Property implication";

  let _, prop_v, prop_u, _, _, phi_v, phi_u =
    monolithic_definitions fmt ~trace_lfsc_defs:false
      "Property implication case"
      sys prop certif
  in

  (* Checking implication of indutive invariant to original properties *)
  add_section fmt "Property implication";

  begin
    if quant_free then
      let v = UfSymbol.mk_fresh_uf_symbol [] ty_index in
      declare_const fmt v;
      let f = Term.mk_implies [phi_u v []; prop_u v []] in
      assert_expr fmt (Term.mk_not f)
    else
      let v = Var.mk_fresh_var ty_index in
      let f = Term.mk_forall [v] (Term.mk_implies [phi_v v; prop_v v]) in
      assert_expr fmt (Term.mk_not f);
  end;

  check_sat fmt;
  
  sexit fmt;
  close_out oc;
  filename


let generate_mono_certificates sys dirname =

  Event.set_module `Certif;

  (* Extract the global raw certificate of the system *)
  let prop, (k, phi) = global_certificate sys in

  Stat.start_timer Stat.certif_min_time;

  (* Performed minimization of certificate *)
  let k, phi = match Flags.certif_min () with
    | `No -> k, phi
    | _ ->
      (* Simplify certificate *)
      let k, uinvs = minimize_certificate sys in
      k, Term.mk_and (prop :: uinvs)

  in

  let certif = k, phi in
  
  (* Record statistics for minimization *)
  Stat.record_time Stat.certif_min_time;  
  Stat.set k Stat.certif_k;
  Stat.set (Certificate.size (k, phi)) Stat.certif_size;

  (* write certificates in smtlib2 scripts *)
  let out = Certificate.{
      k;
      phi = phi_n;
      init = init_n;
      prop = prop_n;
      trans = trans_n;
      dirname = dirname;
      proofname = if is_fec sys then "frontend_proof" else "proof";
      dummy_trace = generate_lfsc_tracing sys dirname prop certif;
      base = mono_base_check sys dirname prop certif;
      induction = mono_induction_check sys dirname prop certif;
      implication = mono_implication_check sys dirname prop certif;
    } in

  (* Time statistics *)
  Stat.record_time Stat.certif_gen_time;

  (* Show which file contains the certificate *)
  printf "SMT-LIB2 certificates were written in %s@." dirname;

  out

  

(* Generate a certificate from a (possibly) proven system sys. It is written in
   the file <input_file>.certificate.smt2 placed in the current directory by
   default *)
let generate_certificate sys dirname =

  Event.set_module `Certif;

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

  (* Performed minimization of certificate *)
  let k , phi = match Flags.certif_min () with
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
  add_header fmt_header sys k init_n prop_n trans_n phi_n;

  if is_fec sys then begin

    let obs_sys = sys in

    let jkind_sys =
      TransSys.find_subsystem_of_scope sys JkindParser.jkind_scope in
  
    let jkdef_filename = Filename.concat dirname "jkind_defs.smt2" in
    let jkdef_oc = open_out jkdef_filename in
    let fmt_jkdef = formatter_of_out_channel jkdef_oc in
    export_system fmt_jkdef "JKind" jkind_sys;
    close_out jkdef_oc;

    let obsdef_filename = Filename.concat dirname "observer_defs.smt2" in
    let obsdef_oc = open_out obsdef_filename in
    let fmt_obsdef = formatter_of_out_channel obsdef_oc in
    export_system fmt_obsdef ~recursive:false "Obs" obs_sys;
    close_out obsdef_oc;
    
  end
  else begin
    
    let def_filename = Filename.concat dirname "kind2_defs.smt2" in
    let def_oc = open_out def_filename in
    let fmt_def = formatter_of_out_channel def_oc in
    
    export_system fmt_def "Kind2" sys;

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
  let fvi = Var.mk_free_var (HString.mk_hstring "i") Type.t_int in
  let fvj = Var.mk_free_var (HString.mk_hstring "j") Type.t_int in

  (* Substitutions to be used later: *)
  (* [0 -> i] *)
  let sigma_0i = TM.singleton t0 (Term.mk_var fvi) in
  (* [0 -> i; 1 -> j] *)
  let sigma_0i1j = TM.add t1 (Term.mk_var fvj) sigma_0i in
  
  (* Declaring initial state (__I__ i) *)
  add_section fmt "Initial states";
  let init_s = UfSymbol.mk_uf_symbol init_n [Type.t_int] Type.t_bool in
  let i0 = TransSys.init_fun_of sys Numeral.zero in
  let init_def = roll sigma_0i i0 in
  define_fun fmt init_s [fvi] Type.t_bool init_def;
  let init_t0 = Term.mk_uf init_s [t0] in
  
  (* Declaring property (__P__ i) *)
  add_section fmt "Original property";
  let prop_s = UfSymbol.mk_uf_symbol prop_n [Type.t_int] Type.t_bool in
  let prop_def = roll sigma_0i prop in
  define_fun fmt prop_s [fvi] Type.t_bool prop_def;
  (* let prop_t i = Term.mk_uf prop_s [Term.mk_num_of_int i] in *)
  let prop_v v = Term.mk_uf prop_s [Term.mk_var v] in
  let prop_u u l = Term.mk_uf prop_s [Term.mk_uf u l] in

  
  (* Declaring transition steps (__T__ i j) *)
  add_section fmt "Transition_relation";  
  let trans_s = UfSymbol.mk_uf_symbol trans_n
      [Type.t_int; Type.t_int] Type.t_bool in
  let t01 = TransSys.trans_fun_of sys Numeral.zero Numeral.one in
  let trans_def = roll sigma_0i1j t01 in
  define_fun fmt trans_s [fvi; fvj] Type.t_bool trans_def;
  let trans_t i j = Term.mk_uf trans_s
      [Term.mk_num_of_int i; Term.mk_num_of_int j] in


  (* Declaring k-inductive invariant (__PHI__ i) *)
  add_section fmt (sprintf "%d-Inductive invariant" k);
  let phi_s = UfSymbol.mk_uf_symbol phi_n [Type.t_int] Type.t_bool in
  let phi_def = roll sigma_0i phi in
  define_fun fmt phi_s [fvi] Type.t_bool phi_def;
  let phi_t i = Term.mk_uf phi_s [Term.mk_num_of_int i] in
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

      Event.log L_warn "Using potentially incorrect check for base case";

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
      let v = UfSymbol.mk_fresh_uf_symbol [] Type.t_int in
      declare_const fmt v;
      let f = Term.mk_implies [phi_u v []; prop_u v []] in
      assert_expr fmt (Term.mk_not f)
    else
      let v = Var.mk_fresh_var Type.t_int in
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
  printf "Certificate checker was written in %s@." certificate_filename



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
let unscope_state_var scope sv =
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
let unscope_var scope v =
  if Var.is_state_var_instance v then
    Var.mk_state_var_instance
      (Var.state_var_of_state_var_instance v |> unscope_state_var scope)
      (Var.offset_of_state_var_instance v)
  else 
  if Var.is_const_state_var v then
    Var.mk_const_state_var
      (Var.state_var_of_state_var_instance v |> unscope_state_var scope)
  else
    v


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

      (debug fec "(Kind2->JKind): %a -> [ %a ]"
         StateVar.pp_print_state_var sv
         (pp_print_list StateVar.pp_print_state_var ", ") jkind_vars
      end);

      (* Fail if variables of properties do not have a jKind equivalent *)
      if jkind_vars = [] then begin
  
      Event.log L_info
        "Could not find a match for the%s variable %a."
        (if StateVar.is_input sv then " INPUT" else "")
        StateVar.pp_print_state_var sv;
      
        if prop (* && jkind_vars = [] *) then begin

          Event.log L_fatal "Frontend certificate was not generated.";
          
          failwith (
            Format.asprintf
              "Could not find a match for the property variable %a."
              StateVar.pp_print_state_var sv);
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
let mk_prop_obs ~only_out lustre_vars kind2_sys =
  
  let orig_kind2_vars = TS.state_vars kind2_sys in

  let vars =
    if only_out then
      List.filter (fun x -> not (StateVar.is_input x)) orig_kind2_vars
    else orig_kind2_vars in      
  let eqs = mk_obs_eqs kind2_sys ~prime:false lustre_vars vars in
  
  (* Conjunction of equalities between state varaibles *)
  ["Observational_Equivalence",
   Property.Generated [],
   Term.mk_and eqs]


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
          prop_source = Property.Generated [];
          prop_term = eq;
          prop_status = Property.PropUnknown; }
      ) props_eqs in

  let others_obs =
    List.map (fun eq ->
        incr cpt;
        { Property.prop_name =
            "OTHER_Observational_Equivalence_" ^(string_of_int !cpt);
          prop_source = Property.Candidate;
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
      guard_clock = fun _ t -> t } ]

(* Create a system that calls the Kind2 system [kind2_sys] and the jKind system
   [jkind_sys] in parallel and observes the values of their state
   variables. All variables are put under a new scope. *)
let merge_systems lustre_vars kind2_sys jkind_sys =

  (* Remember the original state variables*)
  let orig_kind2_vars = TS.state_vars kind2_sys in
  let orig_jkind_vars = TS.state_vars jkind_sys in

  let init_flag = StateVar.mk_init_flag [obs_name] in

  (* Create versions of variables with the new scope *)
  let kind2_vars = List.map (add_scope_state_var [obs_name]) orig_kind2_vars in
  let jkind_vars = List.map (add_scope_state_var [obs_name]) orig_jkind_vars in
  let state_vars =
    init_flag :: kind2_vars @ jkind_vars |>
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

  (* Symbol for initial predicate of new system *)
  let init_uf =
    UfSymbol.mk_uf_symbol
      (LustreIdent.init_uf_string ^"_"^ obs_name) 
      vars_types
      Type.t_bool 
  in

  (* Symbol for transition relation of new system *)
  let trans_uf =
    UfSymbol.mk_uf_symbol
      (LustreIdent.trans_uf_string ^"_"^ obs_name) 
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

  (debug fec
     "@[<hv 4>Unmatched JKind vars:@,%a@]@."
     (pp_print_list StateVar.pp_print_state_var "@,") !global_jkind_vars
   end);


  let kind2_subsys_inst = mk_inst init_flag kind2_sys orig_kind2_vars in
  let jkind_subsys_inst = mk_inst init_flag jkind_sys orig_jkind_vars in
  
  (* Create observer system *)
  let obs_sys, _ =
    TS.mk_trans_sys
      [obs_name]
      None
      init_flag
      []
      state_vars
      []
      init_uf
      init_args
      init_term
      trans_uf
      trans_args
      trans_term
      [kind2_subsys_inst; jkind_subsys_inst]
      props
      [] [] [] in

  (* (\* Add caller info to subnodes *\) *)
  (* TS.add_caller kind2_sys *)
  (*   obs_sys ((List.combine orig_kind2_vars kind2_vars), (fun t -> t)); *)

  (* TS.add_caller jkind_sys *)
  (*   obs_sys ((List.combine orig_jkind_vars jkind_vars), (fun t -> t)); *)

  (* Return the observer system *)
  obs_sys
  

(* Generate a certificate for the frontend translation / simplification phases
   as a system in native input. To be verified, this certificate is expected to
   be fed back to Kind 2. *)
let generate_frontend_certificate node kind2_sys dirname =

  (* Time statistics *)
  Stat.start_timer Stat.certif_frontend_time;

  printf "Generating frontend certificate with jKind ...@.";

  (* Call jKind and get back its internal transition system for the same
     file *)
  let jkind_sys = JkindParser.get_jkind_transsys (Flags.input_file ()) in

  (* Find original Lustre names (with callsite info) for the state variables
     in the Kind2 system. *)
  let lustre_vars =
    InputSystem.reconstruct_lustre_streams node (TS.state_vars kind2_sys) in

  (debug fec "Lustre vars:@,%a"
     (fun fmt ->
        StateVar.StateVarMap.iter (fun sv l ->
            List.iter (fun (sv', l') ->
                Format.fprintf fmt "%a -> %a : %a@,"
                  StateVar.pp_print_state_var sv
                  StateVar.pp_print_state_var sv'
                  (pp_print_list
                     (fun fmt (lid, n, clock) ->
                        Format.fprintf fmt "%a [%d] %s"
                          (LustreIdent.pp_print_ident true) lid n
                          (match clock with
                           | None -> ""
                           | Some c -> "ON "^ (StateVar.string_of_state_var c))
                     )
                     " , ") l'
              ) l
          ))
     lustre_vars
  end);
    
  (* Create the observer system with the property of observational
     equivalence. *)
  let obs_sys = merge_systems lustre_vars kind2_sys jkind_sys in

  let filename = Filename.concat dirname "FEC.kind2" in

  (* Output certificate in native format *)
  NativeInput.dump_native_to obs_sys filename;

  (* Time statistics *)
  Stat.record_time Stat.certif_frontend_time;

  (* Show which file contains the certificate *)
  printf "Frontend certificate was written in %s, run Kind 2 on it with option --certif@." filename



(****************************)
(* Checker scripts for glue *)
(****************************)


let z3_cmd = "z3 -smt2 -in"
let cvc4_cmd = "cvc4 --incremental --lang smt2"
let yices2_cmd = "yices-smt2 --incremental"

let goto_cert_dir="cd $(dirname \"$(which \"$0\")\")\n"

let select_solver_script =
  Format.sprintf
  "case $1 in
    z3)
        solver=\"%s\"
        ;;
    cvc4)
        solver=\"%s\"
        ;;
    yices2)
        solver=\"%s\"
        ;;
    *)
        solver=\"$1\"
        ;;
    esac\n"
  z3_cmd cvc4_cmd yices2_cmd

let certificate_checker_script =
  "#!/bin/sh\n" ^
  "set -e\n" ^
  select_solver_script ^
  goto_cert_dir ^
  "cat certificate_prelude.smt2 kind2_defs.smt2 certificate.smt2 | $solver"

let fecc_checker_script =
  "#!/bin/sh\n" ^
  "set -e\n" ^
  select_solver_script ^
  goto_cert_dir ^
  "cat FECC_prelude.smt2 kind2_defs.smt2 jkind_defs.smt2 observer_defs.smt2 FECC.smt2 | $solver"


(********************************)
(* Creation of all certificates *)
(********************************)

(* Generate all certificates in the directory given by {!Flags.certif_dir}. *)
let generate_all_certificates input sys =

  TH.clear hactlits;
  
  let dirname =
    if is_fec sys then Filename.dirname (Flags.input_file ())
    else Filename.concat (Flags.certif_dir ())
         (Filename.basename (Flags.input_file ()) ^ "_certificates")
  in
  create_dir dirname;

  let cert_out = generate_mono_certificates sys dirname in

  Proof.generate_proof cert_out;
  

  (* Only generate frontend certificates for Lustre *)
  if InputSystem.is_lustre_input input then
    generate_frontend_certificate input sys dirname
  else
    printf "No certificate for frontend@.";

  
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
  Event.stat Stat.[certif_stats_title, certif_stats];

  (* Show which file contains the certificate *)
  printf "Certificates were produced in %s@." dirname


(* FIXME this is just to force the compilation of proof.ml *)
open Proof
