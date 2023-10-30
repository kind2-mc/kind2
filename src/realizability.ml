(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020-2021 by the Board of Trustees of the University of Iowa

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

module VS = Var.VarSet
module ME = ModelElement
module TSys = TransSys
module ScMap = Scope.Map


type 'a analyze_func =
  Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> unit

type unrealizable_result =
  | BaseCase of Term.t
  (* Valid region for initial states *)
  | InductiveCase of (Term.t * Term.t)
  (* One-step valid region without (fst) and with (snd) uncontrollable variables *)

type realizability_result =
  | Realizable of Term.t (* Fixpoint *)
  | Unrealizable of unrealizable_result
  | Unknown

let result_to_string = function
  | Realizable _ -> "realizable"
  | Unrealizable _ -> "unrealizable"
  | Unknown -> "unknown"

let term_partition vars_of_term var_lst term_lst =
  let var_set = VS.of_list var_lst in
  term_lst |> List.partition (fun c ->
    VS.inter (vars_of_term c) var_set
    |> VS.is_empty
  )


let rec get_conjucts term =
  match Term.destruct term with
  | Term.T.App (s, args) when s == Symbol.s_and ->
     List.map get_conjucts args |> List.flatten
  | _ -> [term]


(*
let compute_and_print_core solver terms =
  let actlit_term_map =
    terms |> List.map (fun t ->
      let actlit_uf = Actlit.fresh_actlit () in
      SMTSolver.declare_fun solver actlit_uf;
      let actlit = Actlit.term_of_actlit actlit_uf in
      actlit, t
    )
  in

  let impls =
    List.map (fun (al, t) -> Term.mk_implies [al; t]) actlit_term_map
  in

  SMTSolver.assert_term solver (Term.mk_and impls) ;

  let unsat_core_lits =
    let actlits = List.map fst actlit_term_map in
    SMTSolver.check_sat_assuming solver
      (fun _ -> assert false)
      (fun _ -> SMTSolver.get_unsat_core_lits solver)
      actlits
  in

  let unsat_core_terms =
    unsat_core_lits |> List.map (fun l -> List.assoc l actlit_term_map)
  in

  Debug.realiz "@[<hv>Unsat core:@.@[<hv>%a@]@]@."
    (Lib.pp_print_list Term.pp_print_term "@,") unsat_core_terms


let compute_unsat_core sys context requirements ex_var_lst =
  let solver =
    SMTSolver.create_instance
      ~produce_unsat_assumptions:true
      ~produce_models:true
      ~minimize_cores:true
      (TSys.get_logic sys)
      (Flags.Smt.solver ())
  in

  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero Numeral.one;

  SMTSolver.push solver ;

  SMTSolver.assert_term solver context ;

  assert (SMTSolver.check_sat solver) ;

  let model = SMTSolver.get_model solver in

  SMTSolver.pop solver ;

  let assigns =
    let ex_var_set = VS.of_list ex_var_lst in
    Model.to_list model
    |> List.filter (fun (v,_) -> VS.mem v ex_var_set |> not)
    |> List.map (fun (v, vl) -> 
      match vl with
      | Model.Term e -> Term.mk_eq [Term.mk_var v; e]
      | _ -> assert false)
  in

  let terms = List.rev_append assigns requirements in

  compute_and_print_core solver terms ;

  SMTSolver.delete_instance solver


let compute_unsat_core_if_debugging sys context requirements ex_var_lst =
  let debugging =
    let dflags = Flags.debug () in
    List.mem "all" dflags || List.mem "contractck" dflags
  in
  if debugging then
    compute_unsat_core sys context requirements ex_var_lst
*)


let realizability_check ?(include_invariants=false) vars_of_term
  sys controllable_vars_at_0 vars_at_1 controllable_vars_at_1 =
  
  let term_partition = term_partition vars_of_term in

  (* Solver for term simplification *)
  let solver =
    SMTSolver.create_instance
      (TSys.get_logic sys)
      (Flags.Smt.solver ())
  in

  SMTSolver.trace_comment solver "Realizability Check (term simplification)" ;

  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero Numeral.one;

  (*Format.printf "%a@." (TSys.pp_print_subsystems true) sys ;*)

  let uncontrollable_varset_is_non_empty =
    List.length controllable_vars_at_1 < List.length vars_at_1
  in

  let free_of_controllable_vars_at_1, contains_controllable_vars_at_1 =
    let trans =
      if include_invariants then
        let invars =
          (TransSys.invars_of_bound sys ~one_state_only:true Numeral.zero)
        in
        Term.mk_and
          (TSys.trans_of_bound None sys Numeral.one :: invars)
      else
        TSys.trans_of_bound None sys Numeral.one
    in
    (* term_partion assumes constraints over controllable variables contains
       at least a controllable variable in the current state. This is the case
       if the transition system is the direct translation of a Lustre model
       since all constraints are introduced through the definition
       and assertion of a boolean state variable.
       When invariants are included, the partitioning adds them to
       the first part (free_of_controllable_vars_at_1) *)
    term_partition controllable_vars_at_1 (get_conjucts trans)
  in

  (*Format.printf "U: %a@."
    (Format.pp_print_list Term.pp_print_term) free_of_controllable_vars_at_1 ;
  Format.printf "C: %a@."
    (Format.pp_print_list Term.pp_print_term) contains_controllable_vars_at_1 ;*)

  (* free_of_uncontrollable_vars_at_1 will usually be the empty list,
     but it is possible to write an assumption that only contains
     previous values of variables
  *)
  let free_of_uncontrollable_vars_at_1, contains_uncontrollable_vars_at_1 =
    term_partition vars_at_1 free_of_controllable_vars_at_1
  in

  let free_of_controllable_vars_at_0, contains_controllable_vars_at_0 =
    let init = TSys.init_of_bound None sys Numeral.zero in
    let constraints_at_0 =
      (TransSys.global_constraints sys) @ (get_conjucts init)
    in
    term_partition controllable_vars_at_0 constraints_at_0
  in

  let rec loop fp1 fp =

    let fp_at_1 = Term.bump_state Numeral.one fp in

    let premises = Term.mk_and (fp :: free_of_controllable_vars_at_1) in

    let conclusion = Term.mk_and (fp_at_1 :: contains_controllable_vars_at_1) in

    (*Format.printf "T: %a@." Term.pp_print_term premises ;
    Format.printf "C: %a@." Term.pp_print_term conclusion ;*)

    let ae_val_reponse =
      QE.ae_val sys premises controllable_vars_at_1 conclusion
    in

    match ae_val_reponse with
    | QE.Unknown -> Unknown
    | QE.Valid _ -> (

      Debug.realiz
        "@[<hv>Computed fixpoint:@ @[<hv>%a@]@]@." Term.pp_print_term fp ;

      let premises' = Term.mk_and free_of_controllable_vars_at_0 in

      let conclusion' = Term.mk_and (fp :: contains_controllable_vars_at_0) in

      let ae_val_reponse' =
        QE.ae_val sys premises' controllable_vars_at_0 conclusion'
      in

      match ae_val_reponse' with
      | QE.Unknown -> Unknown
      | QE.Valid _ -> Realizable fp
      | QE.Invalid _ (* valid_region *) -> (
        (*Debug.realiz
            "@[<hv>(INITIAL) Valid region:@ @[<hv>%a@]@]@."
            Term.pp_print_term valid_region ;*)

        (*
        let neg_region = SMTSolver.simplify_term solver (Term.negate valid_region) in

        let context = Term.mk_and [premises'; neg_region] in

        let requirements =
          (get_conjucts fp) @ contains_controllable_vars_at_0
        in

        compute_unsat_core_if_debugging
          sys context requirements controllable_vars_at_0 ;
        *)

        Unrealizable (InductiveCase fp1)
      )

    )
    | QE.Invalid valid_region -> (

      Debug.realiz
        "@[<hv>Valid region:@ @[<hv>%a@]@]@." Term.pp_print_term valid_region ;

      if uncontrollable_varset_is_non_empty then (

        let premises' = Term.mk_and (fp :: free_of_uncontrollable_vars_at_1) in

        let neg_region = SMTSolver.simplify_term solver (Term.negate valid_region) in

        let conclusion' =
          Term.mk_and (neg_region :: contains_uncontrollable_vars_at_1)
        in

        let ae_val_reponse' = QE.ae_val sys premises' vars_at_1 conclusion' in

        match ae_val_reponse' with
        | QE.Unknown -> Unknown
        | QE.Valid _ -> (
          Debug.realiz "@[<hv>Violating region: true@]@." ;

          (*
          let context = Term.mk_and [premises'; conclusion'] in

          let requirements =
            (get_conjucts fp_at_1) @ contains_controllable_vars_at_1
          in

          compute_unsat_core_if_debugging
            sys context requirements controllable_vars_at_1 ;
          *)

          let fp1' =
            if (fst fp1) == Term.t_true then
              (Term.t_false, valid_region)
            else
              fp1
          in

          Unrealizable (InductiveCase fp1')
        )
        | QE.Invalid violating_region -> (
          Debug.realiz
              "@[<hv>Violating region:@ @[<hv>%a@]@]@."
              Term.pp_print_term violating_region ;

          let fp' =
            Term.mk_and [Term.negate violating_region; fp]
            |> SMTSolver.simplify_term solver
          in

          let fp1' =
            if (fst fp1) == Term.t_true then
              (fp', valid_region)
            else
              fp1
          in

          loop fp1' fp'
        )

      )
      else (

        let fp' =
          Term.mk_and [valid_region; fp]
          |> SMTSolver.simplify_term solver
        in

        let fp1' =
          if (fst fp1) == Term.t_true then
            (fp', fp')
          else
            fp1
        in

        loop fp1' fp'

      )
    )
  in

  (* Check initial state constraints *)
  let premises = Term.mk_and free_of_controllable_vars_at_0 in
  let conclusion = Term.mk_and contains_controllable_vars_at_0 in

  QE.set_ubound Numeral.one ; (* Required when Flags.QE.ae_val_use_ctx is false *)

  let res =
    match QE.ae_val sys premises controllable_vars_at_0 conclusion with
    | QE.Unknown -> Unknown
    | QE.Valid r ->
      if r == Term.t_false then ( (* Premises are inconsistent *)
        Debug.realiz
        "@[<hv>Initial state premises are inconsistent@]@." ;
        Realizable Term.t_true
      )
      else (
        loop (Term.t_true, Term.t_true)  Term.t_true
      )
    | QE.Invalid valid_region -> (
      Debug.realiz
        "@[<hv>Valid initial region:@ @[<hv>%a@]@]@." Term.pp_print_term valid_region ;
      Unrealizable (BaseCase valid_region)
    )
  in

  QE.on_exit () ; (* Required when Flags.QE.ae_val_use_ctx is false *)

  res


let get_contract_cores in_sys sys =
  let full_loc_core =
    ME.full_loc_core_for_sys in_sys sys ~only_top_level:true
  in
  (* We need to include mode requires too since 
     they may constraint current values of outputs
  *)
  let guarantee_mode_elt_core, other_core =
    ME.partition_loc_core_elts_by_guarantees_and_mode_elts full_loc_core
  in
  ME.loc_core_to_new_core guarantee_mode_elt_core,
  ME.loc_core_to_new_core other_core


let get_contract_terms init sys guarantee_core other_core =
  let scope = TransSys.scope_of_trans_sys sys in
  let terms_of init g_core o_core =
    let aux with_act init core =
      List.fold_left (fun acc s ->
        let eqs =
          ME.get_actlits_of_scope core s
          |> List.map
            (fun a ->
              let eq = ME.eq_of_actlit_uf core ~with_act:with_act a in
              ME.term_of_ts_eq ~init ~closed:(Scope.equal s scope) eq
            )
        in
        ScMap.add s eqs acc
      ) ScMap.empty (ME.scopes_of_core core)
    in
    let g_term = aux true init g_core in
    let o_term = aux false init o_core in
    g_term, o_term
  in
  let offset = if init then Numeral.zero else Numeral.one in
  terms_of init guarantee_core other_core
  |> fun (guarantee_sc, other_sc) ->
    (ScMap.find scope guarantee_sc
     |> List.map (fun t -> Term.bump_state offset t),
     ScMap.find scope other_sc
     |> List.map (fun t -> Term.bump_state offset t)
    )


exception Trace_or_conflict_computation_failed of string

let get_and_declare_actlits solver sys core =
  let actlits =
    let scope = TransSys.scope_of_trans_sys sys in
    ME.get_actlits_of_scope core scope
  in
  List.iter (SMTSolver.declare_fun solver) actlits ;
  actlits

let get_var_values_at_offset solver sys offset =
  (* Get variables values at offset 0 (base) or 1 (!base) *)
  SMTSolver.get_var_values
    solver
    (TransSys.get_state_var_bounds sys)
    (TransSys.vars_of_bounds sys offset offset)

let filter_and_mk_assign model pred =
  Model.to_list model
  |> List.filter pred
  |> List.map (fun (v, vl) ->
    match vl with
    | Model.Term e -> Term.mk_eq [Term.mk_var v; e]
    | _ -> assert false)
  |> Term.mk_and

let mk_assign_uncontr model contr_vars =
  let var_set = VS.of_list contr_vars in
  filter_and_mk_assign
    model
    (fun (v,_) -> VS.mem v var_set |> not)

let check_sat_and_get_minimal_unsat_core_lits solver act_terms =
  let rec minimize tested rest =
    match tested, rest with
    | [], [] -> assert false
    | [], [_] -> rest
    | _, [] -> tested
    | _, h :: tl -> (
      let res =
        SMTSolver.check_sat_assuming_ab solver
          (fun _ -> (* Sat *) ())
          (fun _ -> (* Unsat *)
           let core' = SMTSolver.get_unsat_core_lits solver in
           Lib.list_subtract core' tested
          )
          (tested @ tl)
      in
      match res with
      | Sat _  -> minimize (h :: tested) tl
      | Unsat core' -> minimize tested core'
    )
  in
  let core =
    SMTSolver.check_sat_assuming solver
      (fun _ -> assert false)
      (fun _ -> SMTSolver.get_unsat_core_lits solver)
      act_terms
  in
  match Flags.Smt.solver () with
  | `Z3_SMTLIB -> core (* Unsat core is minimal *)
  | _ -> minimize [] core

let build_conflict_set in_sys unsat_core_lits core =
  let actlits =
    let actlit_of_term t =
      match Term.destruct t with
      | Const s -> Symbol.uf_of_symbol s
      | _ -> assert false
    in
    List.map actlit_of_term unsat_core_lits
  in
  let core' = ME.filter_core actlits core in
  ME.core_to_loc_core in_sys core'

let build_countertrace cex m =
  match cex with
  | [] -> (
    Model.to_list m |> List.map (fun (v, vl) ->
      Var.state_var_of_state_var_instance v, [vl]
    )
  )
  | _ -> (
    cex |> List.map (fun (sv, values) ->
      let v = Var.mk_state_var_instance sv Numeral.one in
      match Var.VarHashtbl.find_opt m v with
      | Some vl -> (
        (* let t = Var.type_of_var v in
        Format.printf "VAR: %a = %a@."
          Var.pp_print_var v (Model.pp_print_value ~as_type:t) vl; *)
        sv, List.rev (vl :: (List.rev values))
      )
      | None -> assert false
    )
  )


let compute_deadlocking_trace_max_smt_impl solver sys cex offset act_terms =
  List.iter
    (fun a ->
      SMTSolver.assert_soft_term solver a 1
    )
    act_terms
  ;

  assert (SMTSolver.check_sat solver) ;

  let model = get_var_values_at_offset solver sys offset in

  model, build_countertrace cex model


let compute_deadlocking_trace_mus_impl solver sys cex offset minimal_unsat_core =
  (* Drop one activation literal from minimal unsat core, assert the rest to
     satisfy the maximum number of constraints in the core
  *)
  let actlits = List.tl (List.rev minimal_unsat_core) in
  SMTSolver.assert_term solver (Term.mk_and actlits);

  assert (SMTSolver.check_sat solver) ;

  let model = get_var_values_at_offset solver sys offset in

  build_countertrace cex model

(*
let compute_independent_conflict_and_deadlocking_trace
  solver in_sys sys cex offset act_terms guarantee_mode_elts_core
=
  let unsat_core_lits =
    check_sat_and_get_minimal_unsat_core_lits solver act_terms
  in

  let conflict_set =
    build_conflict_set in_sys unsat_core_lits guarantee_mode_elts_core
  in

  let _, cex' =
    match Flags.Smt.solver () with
    | `Z3_SMTLIB -> (
      compute_deadlocking_trace_max_smt_impl solver sys cex offset act_terms
    )
    | _ -> (
      compute_deadlocking_trace_mus_impl solver sys cex offset unsat_core_lits
    )
  in

  cex', conflict_set
*)

let compute_dependent_conflict_and_deadlocking_trace
  solver in_sys sys cex offset act_terms guarantee_mode_elts_core contr_vars
=
  match Flags.Smt.solver () with
  | `Z3_SMTLIB -> (
    SMTSolver.push solver ;

    let model, cex' =
      compute_deadlocking_trace_max_smt_impl solver sys cex offset act_terms
    in

    let uncontr_assign = mk_assign_uncontr model contr_vars in

    SMTSolver.pop solver ;

    SMTSolver.assert_term solver uncontr_assign ;

    let unsat_core_lits =
      check_sat_and_get_minimal_unsat_core_lits solver act_terms
    in

    let conflict_set =
      build_conflict_set in_sys unsat_core_lits guarantee_mode_elts_core
    in

    cex', conflict_set
  )
  | _ -> (
    assert (SMTSolver.check_sat solver) ;

    let model = get_var_values_at_offset solver sys offset in

    (*
      Assignments for all uncontrollable variables
      either of offset 0 (base) or offset 1 (not base)
    *)
    let uncontr_assign = mk_assign_uncontr model contr_vars in

    SMTSolver.assert_term solver uncontr_assign ;

    let unsat_core_lits =
      check_sat_and_get_minimal_unsat_core_lits solver act_terms
    in

    let cex' =
      compute_deadlocking_trace_mus_impl solver sys cex offset unsat_core_lits
    in

    let conflict_set =
      build_conflict_set in_sys unsat_core_lits guarantee_mode_elts_core
    in

    cex', conflict_set
  )


let compute_deadlocking_trace_and_conflict
  analyze in_sys param sys controllable_vars_at_0 controllable_vars_at_1 u_result =

  let sys =
    let scope = (Analysis.info_of_param param).top in
    match InputSystem.get_lustre_node in_sys scope with
    | None -> sys
    | Some { LustreNode.is_function } ->
      if is_function && Flags.Contracts.enforce_func_congruence () then (
        (* Recompute transition system adding functional constraints *)
        let sys, _ =
          InputSystem.trans_sys_of_analysis
            ~add_functional_constraints:true in_sys param
        in
        sys
      )
      else sys
  in

  let vr, cex, is_base, offset, contr_vars =
    match u_result with

    | BaseCase vr -> vr, [], true, Numeral.zero, controllable_vars_at_0

    | InductiveCase (vr_wo, vr_w) -> (

      let prop_name = "OneStepVR" in

      let prop =
        Property.{
          prop_name ;
          prop_source = Property.Generated (None, []) ;
          prop_term = vr_wo ;
          prop_status = PropUnknown ;
          prop_kind = Invariant ;
        }
      in

      let sys = TSys.add_properties sys [prop] in

      let modules = [`BMC; `IC3] in

      let old_log_level = Lib.get_log_level () in
      Lib.set_log_level L_off ;

      analyze modules in_sys param sys ;

      Lib.set_log_level old_log_level;

      match TSys.get_prop_status sys prop_name with
      | Property.PropFalse cex ->

        vr_w, cex, false, Numeral.one, controllable_vars_at_1

      | Property.PropKTrue _
      | Property.PropUnknown ->
        raise (Trace_or_conflict_computation_failed
          "Trace computation returned Unknown")

      | Property.PropInvariant _ -> assert false
    )
  in

  let cex_assigns =
    cex |> List.map (fun (sv, values) ->
      Var.mk_state_var_instance sv Numeral.zero,
      List.rev values |> List.hd
    )
    |> List.map (fun (v, vl) ->
      match vl with
      | Model.Term e -> Term.mk_eq [Term.mk_var v; e]
      | _ -> assert false
    )
  in

  let solver =
    SMTSolver.create_instance
      ~produce_unsat_assumptions:true
      ~produce_models:true
      ~minimize_cores:true
      (TSys.get_logic sys)
      (Flags.Smt.solver ())
  in

  SMTSolver.trace_comment solver
    "Computing set of conflicting guarantees and mode elements" ;

  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero offset;

  let guarantee_mode_elts_core, other_core = get_contract_cores in_sys sys in

  let guarantee_mode_elts_term, other_term =
    get_contract_terms is_base sys guarantee_mode_elts_core other_core
  in

  let act_terms =
    let actlits =
      get_and_declare_actlits solver sys guarantee_mode_elts_core
    in
    List.map Actlit.term_of_actlit actlits
  in

  let constraints =
    let neg_vr =
      SMTSolver.simplify_term solver (Term.negate vr)
    in
    Term.mk_and
      (neg_vr :: (cex_assigns @ guarantee_mode_elts_term @ other_term))
  in

  TransSys.assert_global_constraints sys (SMTSolver.assert_term solver) ;

  SMTSolver.assert_term solver constraints ;

  (*let cex', conflict_set =
    compute_independent_conflict_and_deadlocking_trace
      solver in_sys sys cex offset act_terms guarantee_mode_elts_core
  in*)

  let cex', conflict_set =
    compute_dependent_conflict_and_deadlocking_trace
      solver in_sys sys cex offset act_terms
      guarantee_mode_elts_core contr_vars
  in

  SMTSolver.delete_instance solver ;

  cex', conflict_set
