(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

module SVar = StateVar
module SvMap = SVar.StateVarMap
module SvSet = SVar.StateVarSet

module TSet = Term.TermSet
module TMap = Term.TermMap
module Tree = Term.T

module Sys = TransSys
module Expr = LustreExpr
module Node = LustreNode

(* type term = Term.t *)
type term_set = TSet.t
type 'a term_map = 'a TMap.t

(** State variables of a term. *)
let svars_of = Term.state_vars_of_term

(** List formatter. *)
let fmt_list = pp_print_list

(** (Lustre) expression formatter. *)
let fmt_lus two_state fmt term =
  if two_state then Format.fprintf fmt "true -> (" ;
  Format.fprintf fmt "@[<hov 2>%a@]" (Expr.pp_print_term_as_expr false) term ;
  if two_state then Format.fprintf fmt ")"

(** Node signature formatter. *)
let fmt_sig fmt = Format.fprintf fmt "@[<hov>%a@]" Node.pp_print_node_signature

(** Helper functions to analyze invariants and decide whether they qualify as
Assumptions, guarantees, or modes.

TERM CONVENTION: one-state terms have offset [0], two-state terms have offset
[-1,0].*)
module Contract = struct

  (** Contract building and dependency tracing context. *)
  type dep = {
    node: Node.t ;
    (** Original node, for dependency tracing. *)

    mutable cache: (bool * SvSet.t) option term_map ;
    (** Dependency tracing cache. Boolean indicates whether term can be traced
    to current version of the outputs ([None] if no svar). *)

    ass: term_set ;
    (** Assumptions. *)

    gua: term_set ;
    (** Guarantees. *)

    modes: term_set term_map ;
    (** Modes: maps requires to lists of ensures. *)
  }

  (** Returns [None] if term contains an oracle. Otherwise, returns true iff
  term only contains input variables, along with the set of svars in the term.
  First parameter yields the source of a state variable of the node.

  See below for cached version. *)
  let mentions_only_inputs src_of term =

    let rec analyze_by_source known locals svar tail = function

      (* Skip inputs and outputs *)
      | Some Node.Input -> (
        match (loop known locals tail) with
        | Some (all_inputs, new_locals) -> Some (all_inputs, new_locals)
        | None -> None
      )
      | Some Node.Output -> (
        match (loop known locals tail) with
        | Some (_, new_locals) -> Some (false, new_locals)
        | None -> None
      )

      (* Found oracle , illegal invariant. *)
      | Some Node.Oracle -> None

      (* | Some Node.Alias (_, source) ->
         analyze_by_source known locals svar tail source *)

      | _ -> (
        let locals = SvSet.add svar locals in
        match (loop known locals tail) with
        | Some (_, new_locals) -> Some (false, new_locals)
        | None -> None
      )

    and loop known locals = function

      | svar :: tail -> (
        let known = SvSet.add svar known in
        analyze_by_source known locals svar tail (src_of svar)
      )

      | [] -> Some (true, locals)
    
    in

    match svars_of term |> SvSet.elements with
    | [] -> None
    | svars -> loop SvSet.empty SvSet.empty svars

  (** Returns [None] if term contains an oracle. Otherwise, returns true iff
  term only contains input variables, along with the set of svars in the term. *)
  let mentions_only_inputs dep term =
    let { node ; cache } = dep in
    try TMap.find term cache with Not_found -> (
      let res =
        try (
          mentions_only_inputs
            (* Source of svar. *)
            (Node.source_of_svar node)
            term
        ) with Not_found ->
          None
      in
      dep.cache <- TMap.add term res cache ;
      res
    )

  (** Adds an invariant to the contract context:
  - does not add it if it mentions an oracle,
  - to assumptions if it only mentions inputs,
  - to guarantees otherwise.
  
  Returns the set of locals that must be defined for this term. *)
  let add_inv dep term =
    match mentions_only_inputs dep term with
    | None -> (
      (* KEvent.log L_info "discarding %a" Term.pp_print_term term ; *)
      dep, SvSet.empty
    )
    | Some (true, locals) -> {
      dep with ass = TSet.add term dep.ass
    }, locals
    | Some (false, locals) -> {
      dep with gua = TSet.add term dep.gua
    }, locals

  (** Adds an invariant implication to the contract context:
  - does not add if it lhs or rhs mentions an oracle,
  - adds to assumptions if lhs and rhs only mention inputs,
  - adds to modes if lhs only mention inputs but rhs doesn't,
  - adds to guarantees otherwise.
  
  Returns the set of locals that must be defined for this term. *)
  let add_impl_inv dep lhs rhs =
    match mentions_only_inputs dep lhs, mentions_only_inputs dep rhs with
    | None, _
    | _, None -> dep, SvSet.empty
    | Some (true, lhs_locals), Some(true, rhs_locals) -> {
      dep with ass = TSet.add (Term.mk_implies [lhs ; rhs]) dep.ass
    }, SvSet.union lhs_locals rhs_locals
    | Some (true, lhs_locals), Some (_, rhs_locals) ->
      let lhs_set =
        ( try TMap.find lhs dep.modes with Not_found -> TSet.empty )
        |> TSet.add rhs
      in
      { dep with modes = TMap.add lhs lhs_set dep.modes },
      SvSet.union lhs_locals rhs_locals
    | Some (_, lhs_locals), Some (_, rhs_locals) -> {
      dep with gua = TSet.add (Term.mk_implies [ lhs ; rhs ]) dep.gua
    }, SvSet.union lhs_locals rhs_locals

  (** Adds an invariant to the contract context.
  
  Returns the set of locals that must be defined for this term. *)
  let add_inv dep inv = match Term.destruct inv with
    | Tree.App (sym, [lhs ; rhs])
    when Symbol.node_of_symbol sym = `IMPLIES -> add_impl_inv dep lhs rhs
    | _ -> add_inv dep inv

  (** Creates an empty contract generation context. *)
  let empty node = {
    node ;
    cache = TMap.empty ;
    ass = TSet.empty ;
    gua = TSet.empty ;
    modes = TMap.empty ;
  }


  (** Removes tautologies and does a bit of pruning. *)
  (*let simplify (
    { ass ; gua ; modes } as contract
  ) =
    Format.printf "ass:@." ;
    ass |> TSet.iter (
      fun ass -> Format.printf "  %a@." fmt_term ass
    ) ;
    Format.printf "@.gua:@." ;
    gua |> TSet.iter (
      fun gua -> Format.printf "  %a@." fmt_term gua
    ) ;
    Format.printf "@.modes:@." ;
    modes |> TMap.iter (
      fun req ens ->
        Format.printf "  %a@." fmt_term req ;
        ens |> TSet.iter (
          fun ens -> Format.printf "    %a@." fmt_term ens
        ) ;
    ) ;
    Format.printf "@." ;
    contract*)

  (** Splits some invariants into assumptions, guarantees, and modes.
  Second parameter is normal invariants, then invariant implications.
  
  Returns the set of locals that must be defined for this contract. *)
  let build node invs =
    TSet.fold (
      fun inv (dep, locals) ->
        let dep, new_locals = add_inv dep inv in
        dep, SvSet.union locals new_locals
    ) invs (empty node, SvSet.empty)

  (* |===| Printing stuff. *)

  (** Assumption formatter. *)
  let fmt_ass two_state f fmt term=
    Format.fprintf fmt "assume @[<hov 2>%a@] ;" (fmt_lus two_state) (f term)

  (** Guarantee formatter. *)
  let fmt_gua two_state f fmt term =
    Format.fprintf fmt "guarantee @[<hov 2>%a@] ;" (fmt_lus two_state) (f term)

  (** Ensure formatter. *)
  let fmt_ens two_state f fmt term =
    Format.fprintf fmt "ensure @[<hov 2>%a@] ;" (fmt_lus two_state) (f term)

  (** Mode formatter. *)
  let fmt_mode (two_state, count) f fmt (req, ens) =
    TSet.elements ens
    |> List.map f
    |> Format.fprintf fmt
      "mode mode_%d (@   @[<v>require @[<hov 2>%a@] ;@ %a@]@ ) ;@ "
      count (fmt_lus two_state) (f req) (fmt_list (fmt_ens two_state f) "@ ")

  (** Mode map formatter. *)
  let fmt_mode_map (two_state, count) f fmt modes =
    let rec loop fmt count = function
      | mode :: tail ->
        fmt_mode (two_state, count) f fmt mode ;
        let count = count + 1 in
        (* Term.mk_implies [
          fst mode ;
          snd mode |> TSet.elements |> Term.mk_and
        ]
        |> Format.fprintf fmt "%a@ " (fmt_gua two_state) ; *)
        if tail <> [] then (
          Format.fprintf fmt "@ " ;
          loop fmt count tail
        ) else count
      | [] -> count
    in
    TMap.bindings modes |> loop fmt count

  (** Prints the contract corresponding to a context. *)
  let fmt (two_state, count) f fmt { ass ; gua ; modes } =
    Format.fprintf fmt "@[<v>" ;

    let ass_cnt, gua_cnt, mod_cnt =
      TSet.cardinal ass, TSet.cardinal gua, TMap.cardinal modes
    in

    TSet.elements ass |> Format.fprintf fmt "%a" (
      fmt_list (fmt_ass two_state f) "@ "
    ) ;

    if ass_cnt > 0 && gua_cnt + mod_cnt > 0 then
      Format.fprintf fmt "@ @ " ;

    TSet.elements gua |> Format.fprintf fmt "%a" (
      fmt_list (fmt_gua two_state f) "@ "
    ) ;

    if gua_cnt > 0 && mod_cnt > 0 then
      Format.fprintf fmt "@ @ " ;

    let count = fmt_mode_map (two_state, count) f fmt modes in

    Format.fprintf fmt "@]" ;

    count

end


(** Scope of a transition sys. *)
let scope_of = Sys.scope_of_trans_sys

(** Trans sys name formatter. *)
let fmt_sys_name fmt sys =
  scope_of sys |> Scope.pp_print_scope fmt

(** Name of a trans sys as a string. *)
let sys_name sys =
  scope_of sys |> Scope.to_string

let get_node_of_sys in_sys sys =
  let scope = scope_of sys in
  let _, node_of_scope =
    InputSystem.contract_gen_param in_sys scope
  in
  try scope |> node_of_scope with
  | Not_found ->
    Format.asprintf "unknown system %a" fmt_sys_name sys
    |> failwith

(** Ghost instance carries the info to identify and generate a ghost variable
    that is necessary for the specification of a node, and that represents
    a variable defined in that node, or a variable defined in a called subnode. *)
module GhostInstance = struct

  type context = {
    call_inst: Sys.instance option;
    (** Instance of a node call or [None].

        - None, if the represented variable is defined in the node.
        - Some call_inst, if it is defined in a called subnode.
    *)

    tsys: Sys.t;
    (** System of the node where the represented variable is defined. *)
  }

  (* type t = (context list * SVar.t) *)

  (** Returns a unique lustre name based on a context and a state var *)
  let get_name (context, svar) =
    let pp_print_cxt ppf = function
      | {call_inst = None} -> Format.fprintf ppf ""
      | {call_inst = Some ci} ->
          let _, line, col = file_row_col_of_pos ci.Sys.pos in
          Format.fprintf ppf "_%d_%d" line col
    in
    let pp_print_svar_lustre_name ppf (n, s, c) =
      if s = [] then
        Format.fprintf ppf "%s%a" n pp_print_cxt c
      else
        Format.fprintf ppf "%a_%s%a"
          (pp_print_list Format.pp_print_string "_") s
          n pp_print_cxt c
    in
    let n = SVar.name_of_state_var svar in
    let s = SVar.scope_of_state_var svar in
    string_of_t pp_print_svar_lustre_name (n, s, context)

  (** Returns a unique lustre name based on a context stack and a state var *)
  let get_name_st (cxt_stack, svar) =
    match cxt_stack with
    | cxt :: _ -> get_name (cxt, svar)
    | [] -> assert false

  (** Returns a ghost variable from a context and a state var *)
  let mk_ghost_var cxt sv =
    let is_input = SVar.is_input sv in
    let is_const = SVar.is_const sv in
    let for_inv_gen = SVar.for_inv_gen sv in
    let n = get_name (cxt, sv) in
    let t = SVar.type_of_state_var sv in
    SVar.mk_state_var ~is_input ~is_const ~for_inv_gen n [] t

  (** Returns a ghost variable from a context stack and a state var *)
  let mk_ghost_var_st cxt_stack sv =
    match cxt_stack with
    | cxt :: _ -> mk_ghost_var cxt sv
    | [] -> assert false

  module IdSet = Set.Make(String)

  (** Returns a list of pending ghost instances and a set of the ghost
      variables included in the pending list. The list is created from
      the given context and state variable set. *)
  let create_initial_pending_list cxt svar_set =
    SvSet.fold (
      fun svar (pending, known) ->
        let ghost_inst = ([cxt], svar) in
        let gi_name = get_name_st ghost_inst in
        ( ghost_inst :: pending, IdSet.add gi_name known )
    )
    svar_set ([], IdSet.empty)

  (** Add the ghost instance to the pending list if it is not known yet,
      and returns the updated list and set *)
  let add_to_pending pending known ghost_inst =
    let name = get_name_st ghost_inst in
    if IdSet.mem name known then (pending, known)
    else (ghost_inst :: pending, IdSet.add name known)


  (** Creates a list of equations defining all necessary ghost
      variables from a set of state variables. *)
  let create_ghost_definitions in_sys cxt svar_set =

    let get_node = get_node_of_sys in_sys in

    let process_equation pending known cxt_stack eq =
      let eq_svars = Expr.state_vars_of_expr (snd eq)
      in
      let pending, known =
        SvSet.fold (
          fun svar (p, k) -> add_to_pending p k (cxt_stack, svar)
        )
        eq_svars (pending, known)
      in
      let svar_to_ghost_var = mk_ghost_var_st cxt_stack in
      let ghost_eq = Node.map_svars_in_equation svar_to_ghost_var eq in
      (ghost_eq, pending, known)
    in

    let rec find_var_in_subsystem v subsystems =
      let rec find_var_in_instance v = function
        | [] -> None
        | inst :: tail ->
          try
            let sub_svar = SvMap.find v inst.Sys.map_down in
            Some (inst, sub_svar)
          with Not_found ->
            find_var_in_instance v tail
      in
      match subsystems with
      | [] -> None
      | (sub_tsys, inst_list) :: tail ->
        match find_var_in_instance v inst_list with
        | Some (ci, sub_svar) ->
            Some ({call_inst = Some ci; tsys = sub_tsys}, sub_svar)
        | None -> find_var_in_subsystem v tail
    in

    let create_argument_eq pending known (lhs_cxt, lhs_svar) (rhs_cxt_stack, rhs_svar) =
      let lhs_g_var = mk_ghost_var lhs_cxt lhs_svar in
      let rhs_g_var = mk_ghost_var_st rhs_cxt_stack rhs_svar in
      let ghost_eq = ((lhs_g_var, []), Expr.mk_var rhs_g_var) in
      let pending, known =
        add_to_pending pending known (rhs_cxt_stack, rhs_svar) in
      (ghost_eq, pending, known)
    in

    let is_top_node_input svar = function
    | [] -> assert false
    | [{tsys}] ->
      Node.source_of_svar (get_node tsys) svar = (Some Node.Input)
    | _ -> false
    in

    let create_input_eq (lhs_cxt, lhs_svar) in_svar =
      let lhs_g_var = mk_ghost_var lhs_cxt lhs_svar in
      ((lhs_g_var, []), Expr.mk_var in_svar)
    in

    let rec loop known = function
      | [] -> []
      | ([], _) :: _ -> assert false
      | ({call_inst; tsys} as cxt :: stack, svar) :: pending ->
        let node = get_node tsys in
        if svar = node.Node.init_flag then
          let ghost_var = mk_ghost_var cxt svar in
          let lhs = (ghost_var, []) in
          let rhs = Expr.mk_arrow Expr.t_true Expr.t_false in
          (lhs, rhs) :: loop known pending
        else
          match Node.equation_of_svar node svar with
          | Some eq ->
            let ghost_eq, pending, known =
              process_equation pending known (cxt :: stack) eq
            in
            ghost_eq :: loop known pending

          | None ->
            match Node.source_of_svar node svar with
            | Some Node.Input -> (
              match call_inst with
              | None -> loop known pending
              | Some ci -> 
                try
                  let svar_arg = SvMap.find svar ci.Sys.map_up in
                  let svar_arg_inst = (stack, svar_arg) in
                  let ghost_eq, pending, known =
                    if is_top_node_input svar_arg stack then
                      (create_input_eq (cxt, svar) svar_arg, pending, known)
                    else
                      create_argument_eq pending known (cxt, svar) svar_arg_inst
                  in
                  ghost_eq :: loop known pending
                with Not_found -> assert false
            )
            | _ ->
              let subsystems = Sys.get_subsystem_instances tsys in
              match find_var_in_subsystem svar subsystems with
              | None -> loop known pending (* Output or oracle? *)
              | Some (sub_cxt, sub_svar) ->
                let sub_ghost_inst = (sub_cxt :: cxt :: stack, sub_svar) in
                let ghost_eq, pending, known =
                  create_argument_eq pending known (cxt, svar) sub_ghost_inst
                in
                ghost_eq :: loop known pending
    in

    let pending, known = create_initial_pending_list cxt svar_set in
    loop known pending

end

(** Ghost definition formatter. *)
let fmt_ghost_def fmt ((var, bounds), expr) =
  Format.fprintf fmt "@[<hv 2>var %a%a: %a = %a ;@]"
  (Expr.pp_print_lustre_var false) var
  (pp_print_listi
     (fun ppf i -> function
        | Expr.Bound e | Expr.Unbound e ->
          Format.fprintf
            ppf
            "[%a(%a)]"
            (LustreIdent.pp_print_ident false)
            (LustreIdent.push_index LustreIdent.index_ident i)
            (Expr.pp_print_expr false) e
        | Expr.Fixed e ->
          Format.fprintf ppf "[%a]" (Expr.pp_print_expr false) e)
     "")
  bounds
  (Expr.pp_print_lustre_type true) (SVar.type_of_state_var var)
  (Expr.pp_print_lustre_expr true) expr

let [@ocaml.warning "-27"] generate_contract_for in_sys param sys path invs name =
  let node = get_node_of_sys in_sys sys in
  let contract, locals =
    TSet.of_list invs |> Contract.build node
  in

  (* KEvent.log_uncond "invs: @[<v>%a@]"
    (pp_print_list Term.pp_print_term "@ ") invs ;
  KEvent.log_uncond "contract has @[<v>%d ass@ %d guas@ %d modes"
    (TSet.cardinal contract.ass)
    (TSet.cardinal contract.gua)
    (TMap.cardinal contract.modes) ; *)

  let out_channel = open_out path in
  let fmt = Format.formatter_of_out_channel out_channel in

  Format.fprintf fmt
    "(*@[<v>@ \
      The contract below was generated automatically by the Kind 2@ \
      model-checker.@ \
      @ http://kind2-mc.github.io/kind2/\
    @]@ *)@.@.@.@." ;

  Format.fprintf fmt
    "(* Contract for node %s. *)@.contract %s %a@.let@[<v 2>"
    (sys_name sys) name fmt_sig node ;

  let ghost_definitions, local_ghost_instances =
    let cxt = {GhostInstance.call_inst = None; tsys = sys} in
    (GhostInstance.create_ghost_definitions in_sys cxt locals,
     SvSet.fold (fun sv lst -> (cxt, sv) :: lst) locals [])
  in

  (* Map to new state var names. *)
  let sv_map =
    List.fold_left (
      fun map (cxt, svar) ->
        SvMap.add svar (GhostInstance.mk_ghost_var cxt svar) map
    )
    SvMap.empty local_ghost_instances
  in

  (* Declare necessary locals. *)
  ghost_definitions |> List.iter (
    fun eq -> Format.fprintf fmt "@ " ; fmt_ghost_def fmt eq
  ) ;
  if List.length ghost_definitions > 0 then Format.fprintf fmt "@ " ;

  (* Dump sub contracts. *)
  let _ =
    Format.fprintf fmt "@ " ;
    Contract.fmt (true, 0) (
      Term.map_state_vars (
        fun svar ->
          try SvMap.find svar sv_map with Not_found -> svar
      )
    ) fmt contract
  in

  Format.fprintf fmt "@]@.tel@.@."

let [@ocaml.warning "-27"] generate_contracts in_sys param sys path contract_name =
  KEvent.log_uncond "%d invariants@.@." (
    TransSys.invars_of_bound sys Numeral.zero |> List.length
  ) ;
(*   KEvent.log_uncond "  \
    @{<b>Generating contracts@}@ for system %a to file \"%s\"\
  " fmt_sys_name sys path ;

  let teks = Flags.invgen_enabled () in
  let is_active tek = List.mem tek teks in
  let run_bool two_state =
    KEvent.log_uncond "  Running %s bool invgen..." (
      if two_state then "two-state" else "one-state"
    ) ;
    InvGen.BoolInvGen.main
      (Some max_depth) true true two_state
      in_sys param sys
  in
  let run_int two_state =
    KEvent.log_uncond "  Running %s int invgen..." (
      if two_state then "two-state" else "one-state"
    ) ;
    InvGen.IntInvGen.main
      (Some max_depth) true true two_state
      in_sys param sys
  in
  let run_real two_state =
    KEvent.log_uncond "  Running %s real invgen..." (
      if two_state then "two-state" else "one-state"
    ) ;
    InvGen.RealInvGen.main
      (Some max_depth) true true two_state
      in_sys param sys
  in
  let cond_cons cond_f cond_arg f two_state rest =
    if cond_f cond_arg then (two_state, f two_state) :: rest else rest
  in

  let results = []
    |> cond_cons is_active `INVGENOS run_bool false
    |> cond_cons is_active `INVGENINTOS run_int false
    |> cond_cons is_active `INVGENREALOS run_real false
    |> cond_cons is_active `INVGEN run_bool true
    |> cond_cons is_active `INVGENINT run_int true
    |> cond_cons is_active `INVGENREAL run_real true
  in *)

  (* KEvent.log_uncond "Generating contracts." ; *)

  let node = get_node_of_sys in_sys sys in
  (* Build a map from scopes to a list of contract builders. *)
  let locals, contract_os, contract_ts =
    let invs = sys |> Sys.get_invariants in
    let os, l_os = Invs.get_os invs |> Contract.build node in
    let ts, l_ts = Invs.get_ts invs |> Contract.build node in
    SvSet.union l_os l_ts, os, ts
  in
    (* results |> fold (
      fun map (two_state, result) ->
        result |> fold (
          fun map (sys, invs, _) ->
            let scope = scope_of sys in
            let node = get_node sys in
            let (_, _, locals, contracts) =
              try SMap.find scope map
              with Not_found -> sys, node, SvSet.empty, []
            in
            let contract, new_locals = Contract.build node invs in
            SMap.add scope (
              sys, node, SvSet.union locals new_locals,
              (two_state, contract) :: contracts
            ) map
        ) map
    ) SMap.empty
  in *)

  KEvent.log_uncond "  Dumping contract to `%s`..." path ;

  let out_channel = open_out path in
  let fmt = Format.formatter_of_out_channel out_channel in

  Format.fprintf fmt
    "(*@[<v>@ \
      The contract below was generated automatically by the Kind 2@ \
      model-checker.@ \
      @ http://kind2-mc.github.io/kind2/\
    @]@ *)@.@.@.@." ;

  (
    let ghost_definitions, local_ghost_instances =
      let cxt = {GhostInstance.call_inst = None; tsys = sys} in
      (GhostInstance.create_ghost_definitions in_sys cxt locals,
       SvSet.fold (fun sv lst -> (cxt, sv) :: lst) locals [])
    in

    (* Map to new state var names. *)
    let sv_map =
    List.fold_left (
      fun map (cxt, svar) ->
        SvMap.add svar (GhostInstance.mk_ghost_var cxt svar) map
    )
    SvMap.empty local_ghost_instances
    in

    (* KEvent.log L_info "  Generating contract for %a..." fmt_sys_name sys ; *)
    
    Format.fprintf fmt
      "(* Contract for node %s. *)@.contract %s %a@.let@[<v 2>"
      (sys_name sys) contract_name fmt_sig node ;
    
    (* Declare necessary locals. *)
    ghost_definitions |> List.iter (
      fun eq -> Format.fprintf fmt "@ " ; fmt_ghost_def fmt eq
    ) ;
    if List.length ghost_definitions > 0 then Format.fprintf fmt "@ " ;

    (* Dump contracts. *)
    Format.fprintf fmt "@ " ;
    let count =
      1 + Contract.fmt (false, 0) (
        Term.map_state_vars (
          fun svar ->
            try SvMap.find svar sv_map with Not_found -> svar
        )
      ) fmt contract_os
    in
    Format.fprintf fmt "@ @ " ;
    let _ =
      Contract.fmt (true, count) (
        Term.map_state_vars (
          fun svar ->
            try SvMap.find svar sv_map with Not_found -> svar
        )
      ) fmt contract_ts
    in

    Format.fprintf fmt "@]@.tel@.@."
  ) ;

  KEvent.log_uncond "  Done with contract generation." ;

  close_out out_channel ;



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
