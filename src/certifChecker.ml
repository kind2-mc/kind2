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
module SMT  : SolverDriver.S = GenericSMTLIBDriver


let file_width = 220
let quant_free = true
let monolithic_base = true
let simple_base = false


let t0 = Term.mk_num_of_int 0
let t1 = Term.mk_num_of_int 1

let hactlits = TH.create 2001

let actlitify solver t =
  let a = generate_actlit t in
  let ta = term_of_actlit a in
  if not (TH.mem hactlits ta) then begin
    TH.add hactlits ta ();
    SMTSolver.declare_fun solver a;
    Term.mk_eq [ta; t] |> SMTSolver.assert_term solver;
  end;
  ta


(* Transform unrolled state variables back to functions *)
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



(* Assert the expression *)
let assert_expr fmt expr =
  fprintf fmt
    "@[<hv 1>(assert@ @[<hov>%a@])@]@." 
    SMT.pp_print_expr expr


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



let push fmt = fprintf fmt "@[<hv 1>\n(push 1)@]@." 

let pop fmt = fprintf fmt "@[<hv 1>(pop 1)@]\n@." 

let check_sat fmt = fprintf fmt "@[<hv 1>(check-sat)@]@." 

let sexit fmt = fprintf fmt "@[<hv 1>(exit)@]@." 


let create_dir dir =
  try if not (Sys.is_directory dir) then failwith (dir^" is not a directory")
  with Sys_error _ -> Unix.mkdir dir 0o755


let extract_props_certs sys =
  let certs, props = List.fold_left (fun ((c_acc, p_acc) as acc) -> function
      | _, p, TS.PropInvariant c -> c :: c_acc, p :: p_acc
      | p_name, _, _ ->
        Event.log L_fatal "[Warning] Property %s is not valid" p_name;
        acc
    ) ([], []) (TS.get_properties sys) in

  let certs = List.fold_left (fun c_acc (i, c) ->
      if List.exists (Term.equal i) props then c_acc
      else c :: c_acc
    ) certs (TS.get_invariants sys) in

  List.rev props, certs


let s_and = Symbol.mk_symbol `AND
let s_or = Symbol.mk_symbol `OR
let s_not = Symbol.mk_symbol `NOT


let rec split_inv inv =
  match Term.destruct inv with
  | Term.T.App (s, l) when s == s_and ->
    List.flatten (List.map split_inv l)
  | _ -> [inv]

let split_certs certs =
  List.fold_left (fun acc (k, c) ->
      let cs = List.map (fun c' -> k, c') (split_inv c) in
      List.rev_append cs acc
    ) [] certs



let global_certificate sys =
  let props, certs = extract_props_certs sys in
  Term.mk_and props, Certificate.merge certs



let rec fixpoint acc solver invs_acts prev_props_act prop'act neg_prop'act =

  let if_sat () =
    (debug certif "[Fixpoint] fail@." in ());
    raise Exit
    
  in
  
  let if_unsat () =
    
    (* Activation literals in unsat core *)
    let uc = SMTSolver.get_unsat_core_lits solver in

    let uinvs_acts =
      List.filter (fun (a, _) -> List.exists (Term.equal a) uc) invs_acts in

    (debug certif "[Fixpoint] extracted %d useful invariants@."
      (List.length uinvs_acts)in ());
  
    let uinvs, uinvs' = List.split uinvs_acts in

    let new_prop = Term.mk_and (prev_props_act :: uinvs) in
    let new_prop_act = actlitify solver new_prop in
    let new_prop_acts = prev_props_act :: uinvs in

    let new_prop' = Term.mk_and (prop'act :: uinvs') in
    let new_prop'act = actlitify solver new_prop' in
    
    let neg_new_prop' = Term.mk_not new_prop' in
    let neg_new_prop'act = actlitify solver neg_new_prop' in

    let acc = (uinvs' @ acc) in
    
    SMTSolver.check_sat_assuming solver
      
      (fun () ->
         (* SAT try to find what invariants are missing *)
         (debug certif "[Fixpoint] could not verify inductiveness@." in ());

         fixpoint acc solver
           invs_acts new_prop_act new_prop'act neg_new_prop'act)
      
      (fun () ->
         (* UNSAT: return accumulated invariants *)
         (debug certif "[Fixpoint] OK@."
           (* (pp_print_list Term.pp_print_term "@ ") acc *) in ());
  
         acc)

      (new_prop_acts @ [neg_new_prop'act])
    
  in

  let invs = List.map fst invs_acts in

  SMTSolver.trace_comment solver "fixpoint cs;";

  SMTSolver.check_sat_assuming solver if_sat if_unsat
    (neg_prop'act :: prev_props_act :: invs)




let try_at_bound sys solver k invs prop =
  
  (debug certif "Try bound %d@." k in ());

  (* let invs', invs_acts = List.split invs_and_acts in *)

  let prev_props_l = ref [prop] in
  for i = 1 to k - 1 do
    prev_props_l := Term.bump_state (Numeral.of_int i) prop :: !prev_props_l;
  done;

  let prev_props_act =
    actlitify solver (Term.mk_and (List.rev !prev_props_l)) in

  let invs_acts = List.map (fun inv ->
      let l = ref [inv] in
      for i = 1 to k - 1 do
        l := Term.bump_state (Numeral.of_int i) inv :: !l;
      done;
      let prev_invs_act = actlitify solver (Term.mk_and (List.rev !l)) in
      let pa1 = Term.bump_state (Numeral.of_int k) inv |> actlitify solver in
      prev_invs_act, pa1
    ) invs in

  let prop' = Term.bump_state (Numeral.of_int k) prop in
  let prop'act = actlitify solver prop' in

  let neg_prop' = Term.mk_not prop' in
  let neg_prop'act = actlitify solver neg_prop' in

  (* Can fail and raise Exit *)
  let useful_acts =
    fixpoint [] solver invs_acts prev_props_act prop'act neg_prop'act in

  let uinvs =
    List.fold_left (fun acc i ->
        let a = Term.bump_state (Numeral.of_int k) i
                |> generate_actlit |> term_of_actlit in
        if List.exists (Term.equal a) useful_acts &&
           not (List.exists (Term.equal i) acc) then
          i :: acc
        else acc
      ) [] invs in

  uinvs

(* Find the minimum bound by increasing k *)
let rec find_bound sys solver k kmax invs prop =

  if k > kmax then failwith
      (sprintf "[Certification] simplification of inductive invariant \
                went over bound %d" kmax);

  
  (* Asserting transition relation. *)
  TransSys.trans_of_bound sys (Numeral.of_int k)
  |> SMTSolver.assert_term solver;

  try k, try_at_bound sys solver k invs prop
  with Exit ->
    (* Not k-inductive *)
    find_bound sys solver (k+1) kmax invs prop


(* Find the minimum bound starting from kmax and going backwards *)
let find_bound_back sys solver kmax invs prop =

  for i = 1 to kmax do
    (* Asserting transition relation. *)
    TransSys.trans_of_bound sys (Numeral.of_int i)
    |> SMTSolver.assert_term solver
  done;
  
  let rec loop acc k =

    try
      (* Reached min k, check if the previous were inductive *)
      if k = 0 then raise Exit;

      let uinvs = try_at_bound sys solver k invs prop in
      let acc = Some (k, uinvs) in
      loop acc (k - 1)

    with Exit ->

      match acc with
      | None ->
        (* Not k-inductive *)
        failwith
          (sprintf
             "[Certification] Could not verify %d-inductiveness of invariant" k);

      | Some (k, uinvs) ->
        (* The last one was inductive *)
        k, uinvs
  in

  loop None kmax


(* Find the minimum bound by dichotomy between k_l and k_u *)
let rec find_bound_dicho sys solver kmax invs prop =

  for i = 1 to kmax do
    (* Asserting transition relation. *)
    TransSys.trans_of_bound sys (Numeral.of_int i)
    |> SMTSolver.assert_term solver
  done;
    
  let rec loop_dicho acc k_l k_u =

    if k_l > k_u then
      match acc with
      | Some (k, uinvs) -> k, uinvs
      | None ->
        failwith "[Certification] Could not verify inductiveness of invariant"

    else

      let k_mid = (k_l + k_u) / 2 in
      try

        let uinvs = try_at_bound sys solver k_mid invs prop in
        let acc = Some (k_mid, uinvs) in
        loop_dicho acc k_l (k_mid - 1)

      with Exit ->
        loop_dicho acc (k_mid + 1) k_u
  in

  loop_dicho None 1 kmax
  

  

let typing_constr svuf =
  create_typing_constraint
    svuf
    (UfSymbol.arg_type_of_uf_symbol svuf)
    (UfSymbol.res_type_of_uf_symbol svuf)


let simplify_certificate sys =
  printf "Certificate minimization@.";

  Event.set_module `Certif;
  
  let props, certs = extract_props_certs sys in
  let certs = split_certs certs in
  let k, invs = List.fold_left (fun (m, invs) (k, i) ->
      max m k,
      if List.exists (Term.equal i) props ||
         List.exists (Term.equal i) invs
      then invs
      else i :: invs) (0, []) certs in

  let k_orig, nb_invs = k, List.length invs in
  
  (debug certif "Trying to simplify up to k = %d\ninvs = %a\n@."
    k_orig Term.pp_print_term (Term.mk_and invs) in ());
  
  
  (* Creating solver. *)
  let solver =
    SMTSolver.create_instance ~produce_cores:true
      (TransSys.get_logic sys) (Flags.smtsolver ())
  in

  let decl_w_constr f =
    SMTSolver.declare_fun solver f;
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

  let prop = Term.mk_and props in

  let kmin, uinvs = match Flags.certif_min () with
    | `Fwd -> find_bound sys solver 1 k invs prop
    | `Bwd -> find_bound_back sys solver k invs prop
    | `Dicho -> find_bound_dicho sys solver k invs prop
  in

  SMTSolver.delete_instance solver;
  
  (debug certif "Simplification found for k = %d\ninv = %a\n@."
     kmin Term.pp_print_term (Term.mk_and uinvs) in ());

  printf "Kept %d (out of %d) invariants at bound %d (down from %d)@."
    (List.length uinvs) nb_invs kmin k_orig;

  kmin, uinvs
  













let linestr = String.make 79 '-'
let doublelinestr = String.make 79 '='

let print_line fmt str = fprintf fmt ";%s\n" str

let add_section ?(double=false) fmt title =
  fprintf fmt "\n\n";
  if double then print_line fmt doublelinestr else print_line fmt linestr;
  fprintf fmt "; %s :\n" title;
  if double then print_line fmt doublelinestr else print_line fmt linestr;
  fprintf fmt "@."



let echo fmt s = fprintf fmt "(echo \"%s\")@." (String.escaped s)


type s_info = {
  (* s_prop : Term.t; *)
  s_trans : Term.t;
  s_phi : Term.t;
}


let set_info fmt tag str =
  fprintf fmt
    "@[<hv 1>(set-info@ :%s@ @[<hv>%s@])@]@." 
    tag str

let add_header fmt sys k init_n prop_n trans_n phi_n =
  set_info fmt "origin"
    (sprintf "\"Certificate generated by %s %s\""
       Version.package_name Version.version);
  set_info fmt "input" ("\""^(Flags.input_file ())^"\"");
  set_info fmt "status" "unsat";
  fprintf fmt "@.";
  set_info fmt "init " init_n;
  set_info fmt "trans" trans_n;
  set_info fmt "prop " prop_n;
  fprintf fmt "@.";
  set_info fmt "certif" (sprintf "\"(%d , %s)\"" k phi_n);
  fprintf fmt "@."




let generate_certificate sys =

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


  
  let prop, (k, phi) = global_certificate sys in


  Stat.start_timer Stat.certif_min_time;
  
  let k , phi = match Flags.certif_min () with
    | `No -> k, phi
    | _ ->
      (* Simplify certificate *)
      let k, uinvs = simplify_certificate sys in
      k, Term.mk_and (prop :: uinvs)
    
  in

  Stat.record_time Stat.certif_min_time;  

  Stat.set k Stat.certif_k;

  Stat.set (List.length (split_inv phi)) Stat.certif_size;

  
  
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

  let fvi = Var.mk_free_var (HString.mk_hstring "i") Type.t_int in
  let fvj = Var.mk_free_var (HString.mk_hstring "j") Type.t_int in

  let sigma_0i = TM.singleton t0 (Term.mk_var fvi) in
  let sigma_0i1j = TM.add t1 (Term.mk_var fvj) sigma_0i in
  
  (* Declaring initial state *)
  add_section fmt "Initial states";
  let init_s = UfSymbol.mk_uf_symbol init_n [Type.t_int] Type.t_bool in
  let init_def = roll sigma_0i (TS.init_term sys) in
  define_fun fmt init_s [fvi] Type.t_bool init_def;
  let init_t0 = Term.mk_uf init_s [t0] in
  
  (* Declaring property *)
  add_section fmt "Original property";
  let prop_s = UfSymbol.mk_uf_symbol prop_n [Type.t_int] Type.t_bool in
  let prop_def = roll sigma_0i prop in
  define_fun fmt prop_s [fvi] Type.t_bool prop_def;
  (* let prop_t i = Term.mk_uf prop_s [Term.mk_num_of_int i] in *)
  let prop_v v = Term.mk_uf prop_s [Term.mk_var v] in
  let prop_u u l = Term.mk_uf prop_s [Term.mk_uf u l] in

  
  (* Declaring transition steps *)
  add_section fmt "Transition_relation";  
  let trans_s = UfSymbol.mk_uf_symbol trans_n
      [Type.t_int; Type.t_int] Type.t_bool in
  let t01 = TransSys.trans_fun_of sys Numeral.zero Numeral.one in
  let trans_def = roll sigma_0i1j t01 in
  define_fun fmt trans_s [fvi; fvj] Type.t_bool trans_def;
  let trans_t i j = Term.mk_uf trans_s
      [Term.mk_num_of_int i; Term.mk_num_of_int j] in


  (* Declaring k-inductive invariant *)
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
      for i = k downto 0 do
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
    
  

  (* Checking inductive case *)
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

  
  (* Checking implication *)
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

  Event.stat [Stat.certif_stats_title, Stat.certif_stats];
  
  printf "Certificate was written in %s@." certificate_filename
