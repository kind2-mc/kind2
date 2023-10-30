(* This file is part of the Kind 2 model checker.

   Copyright (c) 2017-2018, 2021 by the Board of Trustees of the University of Iowa

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
open Realizability

module ISys = InputSystem
module TSys = TransSys

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module VS = Var.VarSet


type t =
{
  (* Initial predicate *)
  init: Term.t ;

  (* Transition relation predicate *)
  trans: Term.t;
}

let empty = { init = Term.t_true; trans = Term.t_true }

let is_empty { init; trans } = init == Term.t_true && trans == Term.t_true

let print_init_debug init =
  Debug.assump "  @[<hov 2>Initial predicate:@ %a@]@."
    (LustreExpr.pp_print_term_as_expr true) init

let print_trans_debug trans =
  let trans' = Term.bump_state (Numeral.of_int (-1)) trans in

  Debug.assump "  @[<hov 2>Transition predicate:@ %a@]@."
    (LustreExpr.pp_print_term_as_expr true) trans'

let print_assump_debug {init; trans} =
  print_init_debug init ; print_trans_debug trans

let print_predicate_debug pred =
  Debug.assump "  @[<hov 2>Candidate:@ %a@]@."
    (LustreExpr.pp_print_term_as_expr true) pred

let state_vars_of_init { init } = Term.state_vars_of_term init

let state_vars_of_trans { trans } = Term.state_vars_of_term trans

let map_vars f { init; trans } =
  { init = Term.map_state_vars f init;
    trans = Term.map_state_vars f trans }

let lustre_assumption { init; trans } =
  let mk_expr_of_term t =
    LustreExpr.mk_of_expr (LustreExpr.unsafe_expr_of_term t)
  in
  let bump_minus_one term =
    Term.bump_state (Numeral.of_int (- 1)) term
  in
  let init_expr = mk_expr_of_term init in
  let trans_expr = trans |> bump_minus_one |> mk_expr_of_term in
  LustreExpr.mk_arrow init_expr trans_expr


type 'a variable_filter_func = 'a InputSystem.t -> Scope.t -> Var.t list -> Var.t list

type 'a pair_of_filters = ('a variable_filter_func * 'a variable_filter_func)


type response =
  | Success of t
  | Failure
  | Unknown


let filter_non_input _ _ =
  List.filter
    (fun v -> Var.state_var_of_state_var_instance v |> StateVar.is_input |> not)

let get_output_svars in_sys scope =
  match ISys.get_lustre_node in_sys scope with
  | Some { LustreNode.outputs } ->
    List.map snd (LustreIndex.bindings outputs)
  | None -> []

let get_assumption_svars in_sys scope =
  match ISys.get_lustre_node in_sys scope with
  | Some { LustreNode.assumption_svars } -> assumption_svars
  | None -> SVS.empty

let has_assumptions in_sys scope =
  match ISys.get_lustre_node in_sys scope with
  | Some { LustreNode.contract } -> (
    match contract with
    | Some { assumes } -> assumes <> []
    | None -> false
  )
  | None -> false

let filter_non_output in_sys scope =
  let output_svars = get_output_svars in_sys scope in
  List.filter
    (fun v ->
     let sv = Var.state_var_of_state_var_instance v in
     List.exists (fun o -> StateVar.equal_state_vars o sv) output_svars
     |> not
    )


let open_file_and_dump_header node path contract_name =

  let out_channel = open_out path in
  let fmt = Format.formatter_of_out_channel out_channel in

  let fmt_sig fmt =
    Format.fprintf fmt "@[<hov>%a@]" LustreNode.pp_print_node_signature
  in

  Format.fprintf fmt
    "(* Automatically generated assumption *)@.contract %s %a@.let@[<v -1>@ "
    contract_name fmt_sig node ;

  (out_channel, fmt)


let dump_footer fmt =
  Format.fprintf fmt "@]@.tel@.@."


let dump_assumption ?(prefix="assume") fmt { init ; trans } =

  let pp_print_lustre_expr = LustreExpr.pp_print_term_as_expr false in

  let trans' = Term.bump_state (Numeral.of_int (-1)) trans in

  if (init == trans') then (
    Format.fprintf fmt "@[<hov 2>%s@ %a;@]"
      prefix pp_print_lustre_expr init
  )
  else (
    Format.fprintf fmt "@[<hov 2>%s@ (%a)@ ->@ (%a);@]"
      prefix pp_print_lustre_expr init pp_print_lustre_expr trans'
  )


let dump_contract_for_assumption in_sys scope assumption path contract_name =

  match ISys.get_lustre_node in_sys scope with
  | Some node -> (

    let out_channel, fmt =
      open_file_and_dump_header node path contract_name
    in
    dump_assumption fmt assumption;
    dump_footer fmt;
    close_out out_channel

  )
  | None ->
    KEvent.log L_error "Assumption dump is only supported for Lustre models"


let create_assumpion_init fmt_assump sys solver vars fp prop =

  let premise =
    Term.mk_and
      ((TransSys.global_constraints sys) @
       [TSys.init_of_bound None sys Numeral.zero])
  in

  let conclusion = Term.mk_and [prop.Property.prop_term; fp] in

  let assump_init =
    Abduction.abduce_simpl solver vars premise conclusion
    |> SMTSolver.simplify_term solver
  in

  (*Format.printf "Assump Init: %a@." Term.pp_print_term assump_init;*)

  KEvent.log_uncond "  @[<hov 2>Initial predicate:@ %a@]" fmt_assump assump_init;

  assump_init


let create_assumpion_trans fmt_assump sys solver vars fp prop =

  let trans =
    let invars =
      (TransSys.invars_of_bound sys ~one_state_only:true Numeral.zero) @
      TransSys.invars_of_bound sys Numeral.one
    in  
    Term.mk_and
      ((TransSys.global_constraints sys) @
       TSys.trans_of_bound None sys Numeral.one :: invars)
  in

  let premises = Term.mk_and [fp ; trans] in

  let fp_at_1 = Term.bump_state Numeral.one fp in

  let prop_at_1 = Term.bump_state Numeral.one prop.Property.prop_term  in

  let conclusion = Term.mk_and [prop_at_1; fp_at_1] in

  let assump_trans = Abduction.abduce_simpl solver vars premises conclusion in

  (*Format.printf "Assump Trans: %a@." Term.pp_print_term assump_trans;*)

  let assump_trans' = Term.bump_state (Numeral.of_int (-1)) assump_trans in

  KEvent.log_uncond "  @[<hov 2>Transition predicate:@ %a@]" fmt_assump assump_trans';

  assump_trans


type 'a analyze_func =
  bool -> bool -> 
  Lib.kind_module list ->
  'a InputSystem.t ->
  Analysis.param ->
  TransSys.t ->
  unit


let create_solver_and_context sys k =
  let solver =
    SMTSolver.create_instance
      (TermLib.add_quantifiers (TSys.get_logic sys))
      (Flags.Smt.solver ())
  in

  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero (Numeral.of_int k);

  solver


let get_uf_symbol sv_to_ufs sv o =
  match SVM.find_opt sv sv_to_ufs with
  | Some lst -> (
    match List.nth_opt lst o with
    | Some uf -> uf
    | None -> assert false
  )
  | None -> assert false


let mk_equality sv_to_ufs f sv i j =
  let v = Var.mk_state_var_instance sv (Numeral.of_int i) in
  let uf = get_uf_symbol sv_to_ufs sv j in
  Term.mk_eq [Term.mk_var v; f (Term.mk_uf uf [])]


let mk_equalities ?(no_prev = false) (sys_svars, env_svars) sv_to_ufs f i j =
  let env_eqs =
    env_svars
    |> List.map (fun sv -> mk_equality sv_to_ufs f sv i j)
    |> Term.mk_and
  in
  if i=0 then
    env_eqs
  else (
    let sys_eqs =
      sys_svars
      |> List.map (fun sv -> mk_equality sv_to_ufs f sv (i-1) (j-1))
      |> Term.mk_and
    in
    if no_prev then (
      if sys_eqs = Term.t_true then
        env_eqs
      else
        Term.mk_and [sys_eqs; env_eqs]
    ) 
    else (
      let prev_env_eqs =
        env_svars
        |> List.map (fun sv -> mk_equality sv_to_ufs f sv (i-1) (j-1))
        |> Term.mk_and
      in
      if sys_eqs = Term.t_true then
        Term.mk_and [prev_env_eqs; env_eqs]
      else
        Term.mk_and [sys_eqs; prev_env_eqs; env_eqs]
    )
  )


let mk_forall_vars c svars last =
  List.fold_left
    (fun acc sv ->
      let vars =
        List.init
          last
          (fun i -> Var.mk_state_var_instance sv (Numeral.of_int (i+c)))
      in
      List.rev_append vars acc
    )
    []
    svars
  |> List.rev


let mk_forall_term ?disj ?(init_conds=Term.t_true) init assump_svars one_state sv_to_ufs k abduct =
  let mk_equalities' =
    mk_equalities ~no_prev:one_state assump_svars sv_to_ufs identity
  in
  let forall_vars =
    let sys_svars, env_svars = assump_svars in 
    List.rev_append
      (mk_forall_vars 0 sys_svars k |> List.rev)
      (mk_forall_vars 0 env_svars (k+1))
  in
  let oterms' l c =
    List.init l (fun i ->
      let eqs = List.init l (fun j -> mk_equalities' (i+c) (j+c)) in
      Term.mk_or (
        match disj with
        | None -> eqs
        | Some d -> Term.bump_state (Numeral.of_int i) d :: eqs
      )
    )
  in
  let cterms =
    if one_state then
      oterms' (k+1) 0
    else
      if init then
        mk_equalities' 0 0 :: (oterms' k 1)
      else
        init_conds :: oterms' k 1
  in
  Term.mk_forall forall_vars
    (Term.mk_implies [Term.mk_and cterms; abduct])


let init_soln one_state solver assump_svars sv_to_ufs k system_unrolling abduct =

  let full_term =
    let qterm =
      mk_forall_term true assump_svars one_state sv_to_ufs k abduct
    in
    let sigma =
      SVM.fold
        (fun sv ufs acc ->
          let sv_sigma =
            ufs |> List.mapi (fun i uf ->
              (Var.mk_state_var_instance sv (Numeral.of_int i),
               Term.mk_uf uf [])
            )
          in
          List.rev_append sv_sigma acc
        )
        sv_to_ufs
        []
    in
    Term.mk_and [Term.apply_subst sigma system_unrolling; qterm]
  in

  SMTSolver.push solver;

  SMTSolver.assert_term solver full_term;

  (* Init predicate, transition relation predicate, and the latter
     without previous values of the environment variables *)
  let soln =
    let all_ufs =
      SVM.fold
        (fun _ ufs acc -> List.rev_append ufs acc)
        sv_to_ufs
        []
      |> List.map (fun uf -> Term.mk_uf uf [])
    in
    SMTSolver.check_sat_and_get_term_values
      solver
      (fun _ term_values -> (* If sat. *)
        let f t =
          match List.assoc_opt t term_values with
          | Some v -> v
          | None -> assert false
        in
        let mk_equalities' no_prev =
          mk_equalities ~no_prev assump_svars sv_to_ufs f
        in
        if one_state then
          let pred_at_0 =
            List.init (k+1) (fun j -> mk_equalities' true 0 j)
            |> Term.mk_or
          in
          let pred_at_1 = Term.bump_state Numeral.one pred_at_0 in
          Some { init=pred_at_0; trans=pred_at_1 }
        else
          let init = mk_equalities' false 0 0 in
          let trans =
            List.init k (fun j -> mk_equalities' false 1 (j+1))
            |> Term.mk_or
          in
          Some { init; trans }
      )
      (fun _ -> None) (* If unsat. *)
      all_ufs
  in

  SMTSolver.pop solver;
 
  soln


exception UnknownResult

let iso_decomp
  one_state sys abd_solver uf_solver assump_svars sv_to_ufs pred init_conds k abduct
=
  let sys_svars, env_svars = assump_svars in
  let all_forall_vars =
    List.rev_append
      (mk_forall_vars 0 sys_svars k |> List.rev)
      (mk_forall_vars 0 env_svars (k+1))
  in

  let generalize_step_predicate pred_unrolling' init_conds' i =
    let forall_vars =
      all_forall_vars |> List.filter (fun v ->
        let sv = Var.state_var_of_state_var_instance v in
        let equal_to_sv = StateVar.equal_state_vars sv in
        let offset = Var.offset_of_state_var_instance v in
        if one_state then
          Numeral.equal offset (Numeral.of_int i) |> not
        else
          ( Numeral.equal offset (Numeral.of_int i) ||
            (
              Numeral.equal offset (Numeral.of_int (i+1)) &&
              List.exists equal_to_sv env_svars
            )
          )
          |> not
      )
    in
    let pred_unrolling' = Lib.list_remove_nth i pred_unrolling' in
    let premises = Term.mk_and (init_conds' :: pred_unrolling') in
    let trans_at_i =
      SMTSolver.trace_comment abd_solver (Format.sprintf "Iter: %d" i);
      Abduction.abduce abd_solver forall_vars premises abduct
      |> SMTSolver.simplify_term abd_solver
    in
    Lib.list_insert_at trans_at_i i pred_unrolling'
  in

  let distribute_and_generalize pred_unrolling init_conds' =
    let pred_unrolling, init_conds' =
      if one_state then
        pred_unrolling, init_conds'
      else
        List.fold_left
          (fun (pred_unrolling', init_conds') i ->
            let ae_val_reponse =
              let controllable_vars =
                List.map
                  (fun sv ->
                    Var.mk_state_var_instance sv Numeral.one
                  )
                  env_svars
              in
              let conclusion =
                List.nth pred_unrolling' i
                |> Term.bump_state (Numeral.of_int (- i))
              in
              QE.ae_val sys Term.t_true controllable_vars conclusion
            in
            match ae_val_reponse with
            | QE.Unknown -> raise UnknownResult
            | QE.Valid _ -> (pred_unrolling', init_conds')
            | QE.Invalid conds -> (
              let pred_unrolling', init_conds' =
                if i=0 then (
                  pred_unrolling',
                  Term.mk_and [init_conds'; conds]
                  |> SMTSolver.simplify_term abd_solver
                )
                else (
                  let conds =
                    conds |> Term.bump_state (Numeral.of_int i)
                  in
                  Lib.list_apply_at
                    (fun p ->
                      Term.mk_and [p; conds]
                      |> SMTSolver.simplify_term abd_solver
                    )
                    (i-1)
                    pred_unrolling',
                  init_conds'
                )
              in
              generalize_step_predicate pred_unrolling' init_conds' i,
              init_conds'
            )
          )
          (pred_unrolling, init_conds')
          (List.init k identity |> List.rev)
    in
    pred_unrolling
    |> List.mapi (fun i t ->
      Term.bump_state (Numeral.of_int (- i)) t
    )
    |> Term.mk_and
    |> SMTSolver.simplify_term abd_solver,
    init_conds'
  in

  let rec loop pred' init_conds' iter =
    let term =
      List.init (if one_state then k+1 else k) (fun i ->
        let sigma =
          SVM.fold
            (fun sv ufs acc ->
              let add o j m =
                let v = Var.mk_state_var_instance sv (Numeral.of_int o) in
                let uf =
                  match List.nth_opt ufs j with
                  | Some uf -> uf
                  | None -> assert false
                in
                (v, Term.mk_uf uf []) :: m
              in
              if one_state then
                add 0 i acc
              else
                add 0 i (add 1 (i+1) acc)
            )
            sv_to_ufs
            []
        in
        Term.apply_subst sigma pred' |> Term.negate
      )
      |> Term.mk_and
    in

    let qterm =
      mk_forall_term
        ~disj:pred' ~init_conds:init_conds' false
        assump_svars one_state sv_to_ufs k abduct
    in

    SMTSolver.trace_comment uf_solver (Format.sprintf "Looking for new assignments (k=%d)" k);

    SMTSolver.assert_term uf_solver qterm;

    SMTSolver.push uf_solver;

    SMTSolver.assert_term uf_solver term;

    let res =
      let all_ufs =
        SVM.fold
          (fun _ ufs acc -> List.rev_append ufs acc)
          sv_to_ufs
          []
        |> List.map (fun uf -> Term.mk_uf uf [])
      in
      SMTSolver.check_sat_and_get_term_values
        uf_solver
        (fun _ term_values -> (* If sat. *)
          let f t =
            match List.assoc_opt t term_values with
            | Some v -> v
            | None -> assert false
          in
          let mk_equalities' =
            mk_equalities assump_svars sv_to_ufs f
          in
          let l, s, c =
            if one_state then (k+1, 0, 0)
            else (k, 1, 1)
          in
          Some (
            List.init l (fun j -> mk_equalities' s (j+c))
            |> Term.mk_or
          )
        )
        (fun _ -> (* If unsat. *)
          None
        )
        all_ufs
    in

    SMTSolver.pop uf_solver;

    match res with
    | None -> (
      if iter=1 && not one_state then (
        let pred_unrolling =
          List.init k (fun i -> Term.bump_state (Numeral.of_int i) pred')
        in
        distribute_and_generalize pred_unrolling init_conds'
      )
      else
        pred', init_conds'
    )
    | Some sol -> (
      let pred'', init_conds'' =
        let pred_unrolling =
          let pred' = Term.mk_or [pred'; sol] in
          List.init
            (if one_state then k+1 else k)
            (fun i -> Term.bump_state (Numeral.of_int i) pred')
        in
        let pred_unrolling =
          List.fold_left
            (fun pred_unrolling' i ->
              generalize_step_predicate pred_unrolling' init_conds' i
            )
            pred_unrolling
            (List.init (if one_state then k+1 else k) identity)
        in
        distribute_and_generalize pred_unrolling init_conds'
      in

      if (pred' == pred'') then (
        pred'', init_conds''
      )
      else (
        if one_state then (
          Debug.assump "Generalized candidate@." ;
          print_predicate_debug pred''
        )
        else (
          Debug.assump "Generalized transition relation predicate@." ;
          print_trans_debug pred''
        ) ;

        let max_iters = Flags.Contracts.assumption_gen_iter () in 

        if (max_iters>0 && iter >= max_iters) then
          pred'', init_conds''
        else
          loop pred'' init_conds'' (iter+1)
      )
    )
  in

  loop pred init_conds 1


let cart_decomp one_state abd_solver assump_svars sys k system_unrolling abduct =

  let uf_solver = create_solver_and_context sys k in

  let sys_svars, env_svars = assump_svars in

  let sv_to_ufs, _ =
    let mk_uf_symbol sv id o =
      let name = Printf.sprintf "__assump_v%i_%i" id o in
      let typ = StateVar.type_of_state_var sv in
      let ufs = UfSymbol.mk_uf_symbol name [] typ in
      SMTSolver.declare_fun uf_solver ufs;
      ufs
    in
    List.fold_left
      (fun (map, id) sv ->
        let lst =
          List.init (k+1) (fun o -> mk_uf_symbol sv id o)
        in
        (SVM.add sv lst map, id+1)
      )
      (SVM.empty, 0)
      (sys_svars @ env_svars)
  in

  let decomp {init; trans} =
    if one_state then (
      let init, _ =
        iso_decomp
          one_state sys abd_solver uf_solver assump_svars
          sv_to_ufs init Term.t_true k abduct
      in
      init, Term.bump_state Numeral.one init
    )
    else (
      let init =
        let premises =
          Term.mk_and
            (List.init k
              (fun i -> Term.bump_state (Numeral.of_int i) trans))
        in
        let forall_vars =
          List.rev_append
            (mk_forall_vars 0 sys_svars k |> List.rev)
            (mk_forall_vars 1 env_svars k)
        in
        Abduction.abduce abd_solver forall_vars premises abduct
        |> SMTSolver.simplify_term abd_solver
      in

      Debug.assump "Generalized initial predicate@." ;

      print_init_debug init;

      let trans, init =
        iso_decomp
          one_state sys abd_solver uf_solver assump_svars
          sv_to_ufs trans init k abduct
      in

      Debug.assump "Refined initial predicate@." ;

      print_init_debug init;

      init, trans
    )
  in

  let soln =
    init_soln
      one_state uf_solver assump_svars sv_to_ufs k system_unrolling abduct
  in

  match soln with
  | None -> Failure
  | Some assump -> (

    Debug.assump "Generated initial solution@." ;

    print_assump_debug assump;

    try (
      let init, trans = decomp assump in

      SMTSolver.delete_instance uf_solver ;

      Success { init; trans }
    )
    with UnknownResult -> (

      SMTSolver.delete_instance uf_solver ;

      Unknown
    )
  )


type abduct_info =
{
  term: Term.t;
  forall_varset: VS.t;
  system_unrolling: Term.t list;
}

let no_abduct = {
  term = Term.t_true;
  forall_varset = VS.empty;
  system_unrolling = [];
}

let get_length { system_unrolling } =
  List.length system_unrolling


let generate_assumption_for_k_and_below one_state assump_svars last_abduct sys props k =

  Debug.assump "Generating assumption for k=%d...@." k ;

  let abd_solver = create_solver_and_context sys k in

  let props_conj =
    props
    |> List.map (fun { Property.prop_term } -> prop_term)
    |> Term.mk_and
  in

  let sys_svars, env_svars = assump_svars in

  let compute_next_abduct { term; forall_varset; system_unrolling } =
    let n = List.length system_unrolling in
    let num_n = Numeral.of_int n in
    let forall_varset =
      let forall_varset =
        if one_state || n=0 then
          forall_varset
        else
          (* Remove outputs in (n-1) *)
          List.fold_left
            (fun set sv ->
              let v = Var.mk_state_var_instance sv (Numeral.of_int (n-1)) in
              VS.remove v set
            )
            forall_varset
            sys_svars
      in
      let vars_at_n =
        TSys.vars_of_bounds ~with_init_flag:true sys num_n num_n
      in
      List.fold_left
        (fun set v ->
          let keep =
            let sv = Var.state_var_of_state_var_instance v in
            let equal_to_sv = StateVar.equal_state_vars sv in
            (* No input *)
            (List.exists equal_to_sv env_svars |> not)
            &&
            (
              one_state
              ||
              (* No output in n *)
              (List.exists equal_to_sv sys_svars |> not
               ||
               Numeral.(equal (Var.offset_of_state_var_instance v) num_n)
              )
            )
          in
          if keep then VS.add v set else set
        )
        forall_varset
        vars_at_n
    in
    let system_unrolling =
      if n=0 then
        let init = TSys.init_of_bound None sys Numeral.zero in
        (TransSys.global_constraints sys) @ [init]
      else
        system_unrolling @ [TSys.trans_of_bound None sys num_n]
    in
    let abduct =
      let forall_vars = VS.elements forall_varset in
      let system_unrolling_term = Term.mk_and system_unrolling in
      let props_at_n = Term.bump_state num_n props_conj in
      Abduction.abduce
        abd_solver forall_vars system_unrolling_term props_at_n
    in
    if abduct = Term.t_false then
      { term=Term.t_false; forall_varset; system_unrolling }
    else
      let term =
        Term.mk_and [term; abduct]
        |> SMTSolver.simplify_term abd_solver
      in
      { term; forall_varset; system_unrolling }
  in

  let last_abduct =
    let rec iterate n current_abduct =
      if n <= 0 then
        current_abduct
      else
        let new_abduct = compute_next_abduct current_abduct in
        if new_abduct.term = Term.t_false then
          new_abduct
        else
          iterate (n-1) new_abduct
    in
    let l = get_length last_abduct in
    iterate (k+1-l) last_abduct
  in

  let abduct_term = last_abduct.term in

  Debug.assump "@[<hv>Initial abduct:@ @[<hv>%a@]@]@."
    Term.pp_print_term abduct_term ;

  let res =
    if abduct_term = Term.t_false then
      Failure
    else (
      if k=0 then
        Success { init=abduct_term; trans=Term.t_true }
      else
        let system_unrolling_term =
          let { system_unrolling } = last_abduct in
          Term.mk_and system_unrolling
        in
        cart_decomp
          one_state abd_solver assump_svars sys k system_unrolling_term abduct_term
    )
  in

  SMTSolver.delete_instance abd_solver ;

  res, last_abduct


let satisfy_input_requirements in_sys param top =
  let model_contains_assert =
    ISys.retrieve_lustre_nodes_of_scope in_sys top
    |> List.exists
      (fun { LustreNode.asserts } -> asserts <> [])
  in
  not model_contains_assert &&
  not (ISys.contain_partially_defined_system in_sys top) &&
  Analysis.no_system_is_abstract param


let generate_assumption ?(one_state=false) analyze in_sys param sys =

  match TSys.get_split_properties sys with
  | _, [], [] -> Success { init = Term.t_true; trans = Term.t_true }
  | _, [], _ -> Unknown
  | _, invalid, _ -> (

    let get_min_k props =
      let k_list =
        props |> List.map (fun p ->
          match Property.get_prop_status p with
          | Property.PropFalse cex -> (Property.length_of_cex cex) - 1
          | _ -> assert false
        )
      in
      List.fold_left min (List.hd k_list) (List.tl k_list)
    in  

    let modules = Flags.enabled () in
    let old_log_level = Lib.get_log_level () in
  
    let scope = TSys.scope_of_trans_sys sys in
    
    (* To uniformly handle systems with constant streams,
       we create a semantically equivalent system where
       constantness is enforced by making the current value 
       of the constant stream equal to its previous value in
       the transition relation predicate
    *)
    let c_sys, const_svars =
      TSys.enforce_constantness_via_equations sys
    in
  
    let assump_svars =
      let user_selection = get_assumption_svars in_sys scope in
      let input_svars, other_svars =
          TSys.state_vars c_sys
          |> List.partition (fun sv -> StateVar.is_input sv)
      in
      let input_svars =
        if SVS.is_empty user_selection then
          input_svars
        else
          List.filter (fun sv -> SVS.mem sv user_selection) input_svars
      in
      if one_state then
        [], input_svars
      else (  
        let output_svars =
          let in_sys_output_svars = get_output_svars in_sys scope in
          other_svars
          |> List.filter (fun sv ->
            List.exists (fun o -> StateVar.equal_state_vars o sv) in_sys_output_svars
          )
        in
        let output_svars =
          if SVS.is_empty user_selection then
            output_svars
          else
            List.filter (fun sv -> SVS.mem sv user_selection) output_svars
        in
        output_svars, input_svars
      )
    in  

    let map_back_const_input v =
      let sv = Var.state_var_of_state_var_instance v in
      if List.mem sv const_svars then
        Var.mk_const_state_var sv
      else
        v
    in

    let rec loop props last_abduct k =
      List.iter (fun sv -> StateVar.set_const false sv) const_svars;
      let res, last_abduct =
        generate_assumption_for_k_and_below
          one_state assump_svars last_abduct c_sys props k
      in
      List.iter (fun sv -> StateVar.set_const true sv) const_svars;
      match res with
      | Success ({init; trans}) -> (

        let init', trans' =
          match const_svars with
          | [] -> init, trans
          | _ -> 
            init |> Term.map_vars map_back_const_input,
            trans |> Term.map_vars map_back_const_input
        in

        let assump = { init=init'; trans=trans' } in

        Debug.assump "Generated new assumption candidate@." ;

        print_assump_debug assump ; 

        props |> List.iter (fun { Property.prop_name = n } ->
          TSys.set_prop_unknown sys n) ;

        let sys' =
          let (_, init_eq, trans_eq) = TSys.init_trans_open sys in
          let init_eq = Term.mk_and [init_eq; init'] in
          let trans_eq = Term.mk_and [trans_eq; trans'] in
          TSys.set_subsystem_equations sys scope init_eq trans_eq
        in

        Lib.set_log_level L_off ;

        analyze false false modules in_sys param sys' ;

        Lib.set_log_level old_log_level;

        match TSys.get_split_properties sys' with
        | _, [], [] -> (

          let only_current_state { trans } =
            one_state
            ||
            match Term.var_offsets_of_term trans with
            | Some lo, Some up -> Numeral.(equal lo up && equal lo one)
            | _ -> true
          in

          if not (only_current_state assump) &&
             not (satisfy_input_requirements in_sys param scope)
          then
            KEvent.log L_warn "Assumption may contain constraints over underspecified outputs"
          ;

          KEvent.log L_note "Generated assumption:@,%a"
            (dump_assumption ~prefix:"") assump;

          let no_previous_temporal_assumption =
            (* We approximate the result for now.
               TODO: Allow previous assumptions with only current values *)
            not (has_assumptions in_sys scope)
          in

          if (only_current_state assump && no_previous_temporal_assumption) then (
            Success assump
          )
          else (
            KEvent.log L_note "Checking assumption is realizable..." ;

            List.iter (fun sv -> StateVar.set_const false sv) const_svars;

            let c_sys' =
              let (_, init_eq, trans_eq) = TSys.init_trans_open c_sys in
              let init_eq = Term.mk_and [init_eq; init] in
              let trans_eq = Term.mk_and [trans_eq; trans] in
              TSys.set_subsystem_equations c_sys scope init_eq trans_eq
            in

            let result =
              let vars_at_0 =
                TSys.vars_of_bounds ~with_init_flag:true c_sys' Numeral.zero Numeral.zero
              in
              let vars_at_1 =
                TSys.vars_of_bounds ~with_init_flag:true c_sys' Numeral.one Numeral.one
              in
              let controllable_vars_at_0 = vars_at_0 in
              let controllable_vars_at_1 = vars_at_1 in
              realizability_check
                Term.vars_of_term (* It doesn't matter since all variables are controllable *)
                c_sys' controllable_vars_at_0 vars_at_1 controllable_vars_at_1
            in

            List.iter (fun sv -> StateVar.set_const true sv) const_svars;

            match result with
            | Realizable _ -> Success { init=init'; trans=trans' }
            | Unrealizable _ -> Unknown
            | Unknown -> Unknown
          )
        )
        | _, [], _ -> Unknown
        | _, invalid, _ ->
          let k' = get_min_k invalid in
          assert (k' > k);
          loop props last_abduct k'
      )
      | r -> r
    in

    loop invalid no_abduct (get_min_k invalid)
  )


let generate_assumption_vg in_sys sys var_filters prop =

  (* The current implementation does not restrict global free constants.
     Should we offer a version that allows it?
  *)

  let vars_at_0 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.zero Numeral.zero
    |> List.filter (fun v -> not (Var.is_const_state_var v))
  in

  let vars_at_1 =
    TSys.vars_of_bounds ~with_init_flag:true sys Numeral.one Numeral.one
    |> List.filter (fun v -> not (Var.is_const_state_var v))
  in

  let controllable_vars_at_0 = vars_at_0 in
  
  let controllable_vars_at_1 = vars_at_1 in

  let scope = TSys.scope_of_trans_sys sys in

  let sys' =
    let (_, init_eq, trans_eq) = TSys.init_trans_open sys in
    let init_eq =
      Term.mk_and [init_eq; prop.Property.prop_term]
    in
    let trans_eq =
      let prop_at_1 = Term.bump_state Numeral.one prop.Property.prop_term in
      Term.mk_and [trans_eq; prop_at_1]
    in
    TSys.set_subsystem_equations sys scope init_eq trans_eq
  in

  let result =
    let include_invariants =
      (* Assumes invariants were generated from a consistent (non-empty) system model,
         like a full specified Lustre model with realizable assumptions (unrealizable
         assumptions may introduce spurious invariants)
      *)
      not (has_assumptions in_sys scope)
    in
    realizability_check ~include_invariants
      Term.vars_of_term (* It doesn't matter since all variables are controllable *)
      sys' controllable_vars_at_0 vars_at_1 controllable_vars_at_1
  in

  match result with
  | Realizable fp -> (

    KEvent.log L_note
      "Generating assumption's initial and transition predicates..." ;

    let vf_pre, vf_curr = var_filters in

    let fmt_assump = ISys.pp_print_term_as_expr in_sys sys in

    let solver =
      SMTSolver.create_instance 
        (TermLib.add_quantifiers (TSys.get_logic sys))
        (Flags.Smt.solver ())
    in
  
    TransSys.define_and_declare_of_bounds
      sys
      (SMTSolver.define_fun solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero Numeral.one;
  
    let init_vars = vf_curr in_sys scope vars_at_0 in

    let init = create_assumpion_init fmt_assump sys solver init_vars fp prop in

    if Term.equal init Term.t_false then Unknown

    else (

      let trans_vars =
        List.rev_append (vf_pre in_sys scope vars_at_0) (vf_curr in_sys scope vars_at_1)
      in

      let trans = create_assumpion_trans fmt_assump sys solver trans_vars fp prop in

      if Term.equal trans Term.t_false then Unknown

      else Success { init; trans }

    )
  )
  | Unrealizable _ -> Failure
  | Unknown -> Unknown
