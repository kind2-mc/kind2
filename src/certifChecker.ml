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
module IntM = Map.Make (struct type t = int let compare = compare end)
module SMT  : SolverDriver.S = GenericSMTLIBDriver


(*************************************************)
(* Hard coded options for certificate generation *)
(*************************************************)
let file_width = 220
let quant_free = true
let monolithic_base = true
let simple_base = false



(****************************)
(* Global hconsed constants *)
(****************************)
let s_and = Symbol.mk_symbol `AND
let s_or = Symbol.mk_symbol `OR
let s_not = Symbol.mk_symbol `NOT


let t0 = Term.mk_num_of_int 0
let t1 = Term.mk_num_of_int 1


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
  let a = generate_actlit t in
  let ta = term_of_actlit a in
  if not (TH.mem hactlits ta) then begin
    TH.add hactlits ta ();
    SMTSolver.declare_fun solver a;
    (if imp then Term.mk_implies else Term.mk_eq)
      [ta; t] |> SMTSolver.assert_term solver;
  end;
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
(* create SMT2LIB compliant certificates.                                *)
(*************************************************************************)
        
(* Assert the expression *)
let assert_expr fmt expr =
  fprintf fmt
    "@[<hv 1>(assert@ @[<hov>%a@])@]@." 
    SMT.pp_print_expr expr

(* Returns a typing constraint that reflects types that are not natively
   supported (only subranges for now). *)
let create_typing_constraint ?instantiate_constr uf arg_sorts res_sort =

  if Type.is_int_range res_sort then
    (* Add typing constraints for subranges *)

    (* Get lower and upper bounds *)
    let l, u = Type.bounds_of_int_range res_sort in

    let args = List.map Var.mk_fresh_var arg_sorts in
    let ufa = Term.mk_uf uf (List.map Term.mk_var args) in

    (* create constraint *)
    let constr = Term.mk_leq [Term.mk_num l; ufa; Term.mk_num u] in

    (* quantify over arguments *)
    match args, instantiate_constr with
    | [], _ -> constr
    | _, None -> Term.mk_forall args constr
    | [_], Some (a, b) ->
      let rec inst acc i =
        if i < a then acc
        else
          let ufa = Term.mk_uf uf [Term.mk_num_of_int i] in
          let acc = Term.mk_leq [Term.mk_num l; ufa; Term.mk_num u] :: acc in
          inst acc (i-1)
      in
      let l = inst [] b in
      Term.mk_and l
    | _ -> assert false
      
  else Term.t_true

  
(* Create typing constraint for uf symbol *)
let typing_constr svuf =
  create_typing_constraint
    svuf
    (UfSymbol.arg_type_of_uf_symbol svuf)
    (UfSymbol.res_type_of_uf_symbol svuf)


(* Create a typing constraint from a declaration and add it to the
   certificate *)
let add_typing_constraint ?instantiate_constr fmt uf arg_sorts res_sort =
  let qconstr =
    create_typing_constraint ?instantiate_constr uf arg_sorts res_sort in
  (* assert constraint *)
  if not (Term.equal qconstr Term.t_true) then assert_expr fmt qconstr



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
  declare_fun fmt fun_symbol arg_sorts res_sort;
  add_typing_constraint fmt uf arg_sorts res_sort


(* Declare a new state variable from a uf *)
let declare_state_var ?instantiate_constr fmt uf =
  let fun_symbol = UfSymbol.name_of_uf_symbol uf in
  assert (UfSymbol.arg_type_of_uf_symbol uf = []);
  let arg_sorts = [Type.t_int] in
  let res_sort = UfSymbol.res_type_of_uf_symbol uf in
  declare_fun fmt fun_symbol arg_sorts res_sort;
  add_typing_constraint ?instantiate_constr fmt uf arg_sorts res_sort



(* Define a new function symbol as an abbreviation for an expression *)
let define_fun fmt fun_symbol arg_vars res_sort defn = 
  fprintf fmt
  "@[<hv 1>(define-fun@ %s@ @[<hv 1>(%a)@]@ %s@ %a)@]\n@." 
  (UfSymbol.string_of_uf_symbol fun_symbol)
  (pp_print_list
     (fun ppf var -> 
        Format.fprintf ppf "(%s %s)" 
          (Var.string_of_var var)
          (SMT.string_of_sort (Var.type_of_var var)))
     "@ ")
  arg_vars
  (SMT.string_of_sort res_sort)
  SMT.pp_print_expr defn

(* Solver stack for certificate checker *)
  
let push fmt = fprintf fmt "@[<hv 1>\n(push 1)@]@." 

let pop fmt = fprintf fmt "@[<hv 1>(pop 1)@]\n@." 

(* Satisfiability checking for the certificate checker *)
let check_sat fmt = fprintf fmt "@[<hv 1>(check-sat)@]@." 

let sexit fmt = fprintf fmt "@[<hv 1>(exit)@]@." 




(***************************)
(* Certificates extraction *)
(***************************)

(* Extract properties and invariants together with their certificates from a
   system. *)
let extract_props_certs sys =
  let certs, props = List.fold_left (fun ((c_acc, p_acc) as acc) -> function
      | _, _, p, TS.PropInvariant c -> c :: c_acc, p :: p_acc
      | p_name, _, _, _ ->
        Event.log L_fatal "[Warning] Skipping unproved property %s" p_name;
        acc
    ) ([], []) (TS.get_properties sys) in

  let certs = List.fold_left (fun c_acc (i, c) ->
      if List.exists (Term.equal i) props then c_acc
      else c :: c_acc
    ) certs (TS.get_invariants sys) in

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
let rec fixpoint ~just_check_ind
    acc solver invs_acts prev_props_act prop'act neg_prop'act trans_acts =

  let if_sat () =
    (debug certif "[Fixpoint] fail@." in ());
    raise Exit
    
  in

  let reduce uc =

    (* Identify the useful invariants with the unsat core *)    
    let uinvs_acts =
      List.filter (fun (a, _) -> List.exists (Term.equal a) uc) invs_acts in

    (debug certif "[Fixpoint] extracted %d useful invariants@."
      (List.length uinvs_acts)in ());

    let uinvs, uinvs' = List.split uinvs_acts in

    (* Create activation literals for inductive check *)
    let new_prop = Term.mk_and (prev_props_act :: uinvs) in
    let new_prop_act = actlitify solver new_prop in
    let new_prop_acts = prev_props_act :: uinvs in

    let new_prop' = Term.mk_and (prop'act :: uinvs') in
    let new_prop'act = actlitify solver new_prop' in
    
    let neg_new_prop' = Term.mk_not new_prop' in
    let neg_new_prop'act = actlitify solver neg_new_prop' in

    (* Accumulate useful invariants (identified by their activation
       literals) *)
    let acc = (uinvs' @ acc) in

    (* Check preservation of invariants by k-steps *)
    SMTSolver.check_sat_assuming solver
      
      (fun () ->
         (* SAT try to find what invariants are missing *)
         (debug certif "[Fixpoint] could not verify inductiveness@." in ());

         fixpoint ~just_check_ind:false acc solver
           invs_acts new_prop_act new_prop'act neg_new_prop'act trans_acts)
      
      (fun () ->
         (* UNSAT: return accumulated invariants *)
         (debug certif "[Fixpoint] OK@."
           (* (pp_print_list Term.pp_print_term "@ ") acc *) in ());
  
         acc)

      (trans_acts @ new_prop_acts @ [neg_new_prop'act])
    
  in

  
  let if_unsat () =
    
    (* Activation literals in unsat core, extracted right away in case we
       modify the solver state before calling the continuation *)
    let uc = SMTSolver.get_unsat_core_lits solver in

    (* return a continuation to minimize the set of invariants *)
    fun () -> reduce uc
  in

  (* Get invariants at k - 1 *)
  let invs = List.map fst invs_acts in

  SMTSolver.trace_comment solver "fixpoint cs;";

  (* Check if the property is preserved by k-steps when assuming the
     invariants *)
  SMTSolver.check_sat_assuming solver
    if_sat
    (fun () ->
       if just_check_ind then raise (Reduce_cont (if_unsat ()))
       else if_unsat () ())
    (trans_acts @ (neg_prop'act :: prev_props_act :: invs))


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
  
  (debug certif "Try bound %d@." k in ());

  (* Construct properties from 1 to k-1 *)
  let prev_props_l = ref [prop] in
  for i = 1 to k - 1 do
    prev_props_l := Term.bump_state (Numeral.of_int i) prop :: !prev_props_l;
  done;

  (* Activation literals for properties from 1 to k-1 *)
  let prev_props_act =
    actlitify solver (Term.mk_and (List.rev !prev_props_l)) in

  (* Construct invariants (with activation literals) from 1 to k-1 and for k *)
  let invs_acts = List.map (fun inv ->
      let l = ref [inv] in
      for i = 1 to k - 1 do
        l := Term.bump_state (Numeral.of_int i) inv :: !l;
      done;
      let prev_invs_act = actlitify solver (Term.mk_and (List.rev !l)) in
      let pa1 = Term.bump_state (Numeral.of_int k) inv |> actlitify solver in
      prev_invs_act, pa1
    ) invs in

  (* Construct property at k *)
  let prop' = Term.bump_state (Numeral.of_int k) prop in
  let prop'act = actlitify solver prop' in

  (* Construct negation of property at k *)
  let neg_prop' = Term.mk_not prop' in
  let neg_prop'act = actlitify solver neg_prop' in

  (* This functions maps activation literals (returned by the function
     fixpoint) back to original invariants *)
  let map_back_to_invs useful_acts =
    List.fold_left (fun acc i ->
        let a = Term.bump_state (Numeral.of_int k) i
                |> generate_actlit |> term_of_actlit in
        if List.exists (Term.equal a) useful_acts &&
           not (List.exists (Term.equal i) acc) then
          i :: acc
        else acc
      ) [] invs
  in
  
  try
    (* Can fail and raise Exit or Reduce_cont *)
    let useful_acts =
      fixpoint ~just_check_ind
        [] solver invs_acts prev_props_act prop'act neg_prop'act trans_acts in

    (* If fixpoint returned a list of useful invariants we just return them *)
    Inductive (
      map_back_to_invs useful_acts
    )
  with
  | Exit ->
    (* The first inductive test of fixpoint failed *)
    Not_inductive
  | Reduce_cont f ->
    (* fixpoint was interrupted, we return the continuation that will resume
       the computation of the useful invariants *)
    Inductive_to_reduce (fun () -> f () |> map_back_to_invs)


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


(* Find the minimum bound by dichotomy between 1 and kmax (binary search) *)
let rec find_bound_dicho sys solver kmax invs prop =
  
  (* Creating activation literals for transition unrollings *)
  let trans_acts_map = unroll_trans_actlits sys solver kmax in

  (* Recursive binary search between k_l and k_u *)
  let rec loop_dicho acc k_l k_u =

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
          loop_dicho acc (k_mid + 1) k_u

        | res ->
          (* Inductive, register and Look for non-inductiveness on the left *)
          loop_dicho (k_mid, res) k_l (k_mid - 1)
  in

  (* Start with interval [1; kmax] *)
  loop_dicho (-1, Not_inductive) 1 kmax


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
  
  (debug certif "Trying to simplify up to k = %d\ninvs = %a\n@."
    k_orig Term.pp_print_term (Term.mk_and invs) in ());
  
  
  (* Creating solver that will be used to replay and minimize inductive step *)
  let solver =
    SMTSolver.create_instance ~produce_cores:true
      (TransSys.get_logic sys) (Flags.smtsolver ())
  in

  (* Helper function to declare a symbol and the associated constraints if
     needed *)
  let decl_w_constr f =
    SMTSolver.declare_fun solver f;
    match SMTSolver.kind solver with
    | `Yices_native ->
      (* Don't declare subranges constraints for yices 1 *)
      ()
    | _ ->
      let qconstr = typing_constr f in
      if not (Term.equal qconstr Term.t_true) then 
        SMTSolver.assert_term solver qconstr
  in
  
    
  
  (* Defining uf's and declaring variables. *)
  TransSys.init_define_fun_declare_vars_of_bounds
    sys
    (SMTSolver.define_fun solver)
    decl_w_constr
    Numeral.(~- one) (Numeral.of_int (k+1));

  (* The property we want to re-verify the conjunction of all the properties *)
  let prop = Term.mk_and props in

  (* Depending on the minimizxation strategy, we use different variants to find
     the minimum bound kmin, and the set of useful invariants for the proof of
     prop *)
  let kmin, uinvs = match Flags.certif_min () with
    | `Fwd -> find_bound sys solver 1 k invs prop
    | `Bwd -> find_bound_back sys solver k invs prop
    | `Dicho -> find_bound_dicho sys solver k invs prop
    | `No -> assert false
  in

  (* We are done with this step of minimization and we don't neet the solver
     anylonger *)
  SMTSolver.delete_instance solver;
  
  (debug certif "Simplification found for k = %d\ninv = %a\n@."
     kmin Term.pp_print_term (Term.mk_and uinvs) in ());

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

(* Add a set-info header *)
let set_info fmt tag str =
  fprintf fmt
    "@[<hv 1>(set-info@ :%s@ @[<hv>%s@])@]@." 
    tag str

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
    (sprintf "\"Certificate generated by %s %s\""
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



(**********************************************)
(* Creation of certificate and checker script *)
(**********************************************)


(* Generate a certificate from a (possibly) proved system sys. It is written in
   the file <input_file>.certificate.smt2 placed in the current directory by
   default *)
let generate_certificate sys =

  Event.set_module `Certif;

  (* Time statistics *)
  Stat.start_timer Stat.certif_gen_time;
  
  let dirname = Flags.certif_dir () in

  create_dir dirname;

  let certificate_filename = 
    Filename.concat
      dirname
      (Format.sprintf "%s.certificate.smt2" 
         (Filename.basename (Flags.input_file ()))
      )
  in

  let certif_oc = open_out certificate_filename in
  
  let fmt = formatter_of_out_channel certif_oc in

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
  
  
  (* Names of predicates *)
  let init_n = "__I__" in
  let prop_n = "__P__" in
  let trans_n = "__T__" in
  let phi_n = "__PHI__" in

  
  (* add headers for info *)
  add_header fmt sys k init_n prop_n trans_n phi_n;

  add_section ~double:true fmt "INPUT SYSTEM";

  let consts, svars = List.partition StateVar.is_const (TS.state_vars sys) in
  
  (* Declaring constant symbols *)
  add_section fmt "Constants";
  List.iter (fun sv ->
      declare_const fmt (StateVar.uf_symbol_of_state_var sv)
    ) consts;
  
  (* Declaring state variables upto k *)
  add_section fmt "State variables";
  List.iter (fun sv ->
      declare_state_var ~instantiate_constr:(0, k+1)
        fmt (StateVar.uf_symbol_of_state_var sv)
    ) svars;
  
  (* Declaring function symbols *)
  add_section fmt "Function symbols";
  List.iter (fun (f, (a, d)) ->
      define_fun fmt f a Type.t_bool d) (TS.uf_defs sys);

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
  let init_def = roll sigma_0i (TS.init_term sys) in
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

      Event.log L_fatal
        "[Warning] Using potentially incorrect check for base case";

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


  (* Close file *)
  close_out certif_oc;

  (* Time statistics *)
  Stat.record_time Stat.certif_gen_time;

  (* Show which file contains the certificate *)
  printf "Certificate was written in %s@." certificate_filename



(*****************************************)
(* Certificates for frontend translation *)
(*****************************************)

(* Name of the system observing the jKind and Kind2 systems and comparing
   values of their states *)
let obs_name = "OBS"

(* Add an additional scope to a state variable *)
let add_scope_state_var scope sv =
  if StateVar.equal_state_vars TransSys.init_flag_svar sv then sv
  else
    StateVar.mk_state_var
      ~is_input:(StateVar.is_input sv)
      ~is_const:(StateVar.is_const sv)
      ~for_inv_gen:(StateVar.for_inv_gen sv)
      (StateVar.name_of_state_var sv)
      (scope @ StateVar.scope_of_state_var sv)
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


(* Helper function for creating an initial term with scoping information *)
let mk_init_term scope sys =
  Term.mk_uf (TS.init_uf_symbol sys)
    (List.map (fun v -> Term.mk_var (add_scope_var scope v))
       (TS.init_vars sys))


(* Helper function for creating a transition term with scoping information *)
let mk_trans_term scope sys =
  Term.mk_uf (TS.trans_uf_symbol sys)
    (List.map (fun v -> Term.mk_var (add_scope_var scope v))
       (TS.trans_vars sys))


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


(* Create a term for the observational equivalence of the original state
   variables of Kind2 ([orig_kind2_vars]) and their computed jKind
   counterparts. The optional parameter [prime] controls if the resulting
   eqaulities should be on primed varaibles. *)
let mk_prop_obs ?(prime=false) lustre_vars orig_kind2_vars =

  let term_state_var =
    if prime then term_state_var1 [obs_name]
    else term_state_var0 [obs_name] in
  
  let eqs =
    List.fold_left (fun acc sv ->
        try
          List.fold_left (fun acc jv ->
              Term.mk_eq [term_state_var sv; term_state_var jv] :: acc
            ) acc (JkindParser.jkind_vars_of_kind2_statevar lustre_vars sv)

        (* Ignore this variable if it does not have a jKind counterpart *)
        with Not_found -> acc
      ) [] orig_kind2_vars
  in

  (* Conjunction of equalities between state varaibles *)
  Term.mk_and eqs


(* Create additional constraints that force the input state varaibles to be the
   same in Kind2 and jKind. *)
let same_inputs ?(prime=false) lustre_vars orig_kind2_vars =
  mk_prop_obs ~prime
    lustre_vars (List.filter StateVar.is_input orig_kind2_vars)


(* Create a system that calls the Kind2 system [kind2_sys] and the jKind system
   [jkind_sys] in parallel and observes the values of their state
   variables. All variables are put under a new scope. *)
let merge_systems lustre_vars kind2_sys jkind_sys =

  (* Remember the original state variables*)
  let orig_kind2_vars = TS.state_vars kind2_sys in
  let orig_jkind_vars = TS.state_vars jkind_sys in

  (* Create versions of variables with the new scope *)
  let kind2_vars = List.map (add_scope_state_var [obs_name]) orig_kind2_vars in
  let jkind_vars = List.map (add_scope_state_var [obs_name]) orig_jkind_vars in
  let state_vars = kind2_vars @ jkind_vars in
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
      same_inputs lustre_vars orig_kind2_vars;
      mk_init_term [obs_name] kind2_sys;
      mk_init_term [obs_name] jkind_sys] in

  (* Term describing the transition relation: [inputs1' = inputs2' /\
     T1(X1,X1') /\ T2(X2,X2')]. Here [inputs1'] is the subset of [X1'] which
     are input varaibles. *)
  let trans_term =
    Term.mk_and [
      same_inputs ~prime:true lustre_vars orig_kind2_vars;
      mk_trans_term [obs_name] kind2_sys;
      mk_trans_term [obs_name] jkind_sys] in

  let init = init_uf, (state_vars0, init_term) in
  let trans = trans_uf, (state_vars1 @ state_vars0, trans_term) in

  (* Create property *)
  let prop =
    ("Observational_Equivalence",
     TermLib.Generated [],
     mk_prop_obs lustre_vars orig_kind2_vars) in

  (* Create observer system *)
  let obs_sys =
    TS.mk_trans_sys [obs_name]
      state_vars init trans [kind2_sys; jkind_sys] [prop] TS.Native
  in

  (* Add caller info to subnodes *)
  TS.add_caller kind2_sys
    obs_sys ((List.combine orig_kind2_vars kind2_vars), (fun t -> t));

  TS.add_caller jkind_sys
    obs_sys ((List.combine orig_jkind_vars jkind_vars), (fun t -> t));

  (* Return the observer system *)
  obs_sys
  

(* Generate a certificate for the frontend translation / simplification phases
   as a system in native input. To be verified, this certificate is expected to
   be fed back to Kind 2. *)
let generate_frontend_certificate kind2_sys =
  match TS.get_source kind2_sys with

  (* Only generate the frontend certificate if the system comes from a Lustre
     file *)
  | TS.Lustre nodes ->

    (* Time statistics *)
    Stat.start_timer Stat.certif_frontend_time;

    printf "Generating frontend certificate with jKind ...@.";

    (* Call jKind and get back its internal transition system for the same
       file *)
    let jkind_sys = JkindParser.get_jkind_transsys (Flags.input_file ()) in

    (* Find original Lustre names (with callsite info) for the state variables
       in the Kind2 system. *)
    let lustre_vars =
      LustrePath.reconstruct_lustre_streams nodes (TS.state_vars kind2_sys) in

    (* Create the observer system with the property of observational
       equivalence. *)
    let obs_sys = merge_systems lustre_vars kind2_sys jkind_sys in

    (* Dump the observer system as in native format in the same directory as
       the certificate. *)
    let dirname = Flags.certif_dir () in
    create_dir dirname;

    let filename =
      Filename.concat
        dirname
        (Format.sprintf "%s.frontend_certificate.kind2" 
           (Filename.basename (Flags.input_file ()))
        )
    in

    (* Output certificate in native format *)
    NativeInput.dump_native_to obs_sys filename;

    (* Time statistics *)
    Stat.record_time Stat.certif_gen_time;

    (* Show which file contains the certificate *)
    printf "Frontend certificate was written in %s@." filename;

  | _ -> assert false



(********************************)
(* Creation of all certificates *)
(********************************)

(* Generate all certificates in the directory given by {!Flags.certif_dir}. *)
let generate_all_certificates sys =

  generate_certificate sys;

  begin match TS.get_source sys with
  | TS.Lustre _ -> generate_frontend_certificate sys
  | _ -> printf "No certificate for frontend."
  end;

  (* Send statistics *)
  Event.stat [Stat.certif_stats_title, Stat.certif_stats]
