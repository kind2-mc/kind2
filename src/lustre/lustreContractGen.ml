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

module Num = Numeral

module SMap = Scope.Map

module SVar = StateVar
module SvMap = SVar.StateVarMap
module SvSet = SVar.StateVarSet
module VSet = Var.VarSet

module TSet = Term.TermSet
module TMap = Term.TermMap
module Tree = Term.T

module Sys = TransSys
module Expr = LustreExpr
module Node = LustreNode

type term = Term.t
type term_set = TSet.t
type 'a term_map = 'a TMap.t

(** State variables of a term. *)
let svars_of = Term.state_vars_of_term
(** State variables of a term at [0]. *)
let curr_svars_of = Term.state_vars_at_offset_of_term Num.zero

(** List formatter. *)
let fmt_list = pp_print_list
(** State variable formatter. *)
let fmt_svar = StateVar.pp_print_state_var
(** Term formatter. *)
let fmt_term = Term.pp_print_term
(** (Lustre) expression formatter. *)
let fmt_lus two_state fmt term =
  if two_state then Format.fprintf fmt "true -> (" ;
  Format.fprintf fmt "@[<hov 2>%a@]" (Expr.pp_print_term_as_expr true) term ;
  if two_state then Format.fprintf fmt ")"
(** Node signature formatter. *)
let fmt_sig = Node.pp_print_node_signature

(** Map over [option]. *)
let omap f = function
  | Some x -> Some (f x)
  | None -> None

(** Third. *)
let thrd (_, _, third) = third

(** Fold left over lists. *)
let fold = List.fold_left

(** Helper functions to analyze invariants and decide whether they qualify as
Assumptions, guarantees, or modes.

TERM CONVENTION: one-state terms have offset [0], two-state terms have offset
[-1,0].*)
module Contract = struct

  (** Contract building and dependency tracing context. *)
  type dep = {
    (** Original node, for dependency tracing. *)
    node: Node.t ;
    (** Dependency tracing cache. Boolean indicates whether term can be traced
    to current version of the outputs ([None] if no svar). *)
    mutable cache: (bool * SvSet.t) option term_map ;
    (** Assumptions. *)
    ass: term_set ;
    (** Guarantees. *)
    gua: term_set ;
    (** Modes: maps requires to lists of ensures. *)
    modes: term_set term_map ;
  }

  (** Returns [None] if terms does not contain any state variables. Otherwise,
  returns true iff term can be traced back to current version of the
  outputs, along with the set of local svars in the term's COI.
  First parameter yields the source of a state variable of the node, second
  yields the expression of the lhs of its definition.

  See below for cached version. *)
  let mentions_outputs src_of expr_of term =

    (** Stops as soon as an output in the current state as been reached.

    Note that this would not work if there was any cyclic dependency. But if
    there was, they were rejected by the frontend. *)
    let rec loop known locals = function
    
      | svar :: tail -> (
        let known = SvSet.add svar known in
    
        match src_of svar with

        (* Found output, done. *)
        | Some Node.Output -> Some (true, locals)

        (* Skip inputs. *)
        | Some Node.Input -> loop known locals tail
        
        (* Found oracle or node call svar, illegal invariant. *)
        | Some Node.Oracle
        | Some Node.Call -> None

        | Some Node.Alias (sv, _) when SvSet.mem sv known |> not ->
          sv :: tail |> loop known locals
        | Some Node.Alias _ -> loop known locals tail

        (* Rest should have a definition. *)
        | Some Node.Local
        | Some Node.Ghost -> (
          let locals = SvSet.add svar locals in
          
          match expr_of svar with
          
          | Some expr ->
            let svars =
              (* Extract all **current** state vars of definition. *)
              Expr.base_state_vars_of_init_expr expr
              |> SvSet.union (
                Expr.cur_state_vars_of_step_expr expr
              )
              (* Remove known. *)
              |> SvSet.filter (fun svar -> SvSet.mem svar known |> not)
              |> SvSet.elements
            in
            (* Append to tail and loop. *)
            List.rev_append svars tail |> loop known locals
          
          | None ->
            (* No definition, does not depend on anything. *)
            Format.asprintf "no definition for state variable `%a`"
              fmt_svar svar
            |> failwith
        )

        | None ->
          Format.printf "unknown svar %a@.@." SVar.pp_print_state_var svar ;
          raise Not_found
    
      )
    
      | [] -> Some (false, locals)
    
    in

    match curr_svars_of term |> SvSet.elements with
    | [] -> None
    | svars -> loop SvSet.empty SvSet.empty svars

  (** Returns [None] if terms does not contain any state variables. Otherwise,
  returns true iff term can be traced back to current version of the
  outputs, along with the set of local svars in the term's COI..
  First parameter yields the source of a state variable of the node, second
  yields the expression of the lhs of its definition. *)
  let mentions_outputs ( { node ; cache } as dep ) term =
    try TMap.find term cache with Not_found -> (
      let res =
        try (
          mentions_outputs
            (* Source of svar. *)
            (Node.source_of_svar node)
            (* Expression of svar definition's lhs. *)
            (fun svar -> Node.equation_of_svar node svar |> omap thrd)
            term
        ) with Not_found ->
          (* There was one unknown state variable, should be the init flag.
          We don't take risks and just ignore the term. *)
          None
      in
      dep.cache <- TMap.add term res cache ;
      res
    )

  (** Adds an invariant to the contract context:
  - does not add it if it does not mention any state variable,
  - to assumptions if it does not mention outputs,
  - to guarantees otherwise.
  
  Returns the set of locals that must be defined for this term. *)
  let add_inv dep term =
    match mentions_outputs dep term with
    | None -> (
      Event.log_uncond "discarding %a" Term.pp_print_term term ;
      dep, SvSet.empty
    )
    | Some (true, locals) -> {
      dep with gua = TSet.add term dep.gua
    }, locals
    | Some (false, locals) -> {
      dep with ass = TSet.add term dep.ass
    }, locals

  (** Adds an invariant implication to the contract context:
  - does not add if it lhs or rhs do not mention any state variable,
  - adds to assumptions if lhs and rhs do not mention outputs,
  - adds to modes if lhs does not mention outputs but rhs does,
  - adds to guarantees otherwise.
  
  Returns the set of locals that must be defined for this term. *)
  let add_impl_inv dep lhs rhs =
    match mentions_outputs dep lhs, mentions_outputs dep rhs with
    | None, _
    | _, None -> dep, SvSet.empty
    | Some (false, lhs_locals), Some (false, rhs_locals) -> {
      dep with ass = TSet.add (Term.mk_implies [lhs ; rhs]) dep.ass
    }, SvSet.union lhs_locals rhs_locals
    | Some (false, lhs_locals), Some (true, rhs_locals) ->
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

  (** Two state prefix. *)
  let fmt_ts_pref fmt two_state =
    if two_state then Format.fprintf fmt "true -> ("
  (** Two state suffix. *)
  let fmt_ts_suff fmt two_state =
    if two_state then Format.fprintf fmt ")"

  (** Assumption formatter. *)
  let fmt_ass two_state fmt =
    Format.fprintf fmt "assume @[<hov 2>%a@] ;" (fmt_lus two_state)

  (** Guarantee formatter. *)
  let fmt_gua two_state fmt =
    Format.fprintf fmt "guarantee @[<hov 2>%a@] ;" (fmt_lus two_state)

  (** Ensure formatter. *)
  let fmt_ens two_state fmt =
    Format.fprintf fmt "ensure @[<hov 2>%a@] ;" (fmt_lus two_state)

  (** Mode formatter. *)
  let fmt_mode (two_state, count) fmt (req, ens) =
    TSet.elements ens
    |> Format.fprintf fmt
      "mode mode_%d (@   @[<v>require @[<hov 2>%a@] ;@ %a@]@ ) ;@ "
      count (fmt_lus two_state) req (fmt_list (fmt_ens two_state) "@ ")

  (** Mode map formatter. *)
  let fmt_mode_map (two_state, count) fmt modes =
    let rec loop fmt count = function
      | mode :: tail ->
        fmt_mode (two_state, count) fmt mode ;
        (* Term.mk_implies [
          fst mode ;
          snd mode |> TSet.elements |> Term.mk_and
        ]
        |> Format.fprintf fmt "%a@ " (fmt_gua two_state) ; *)
        if tail <> [] then (
          Format.fprintf fmt "@ " ;
          loop fmt (count + 1) tail
        ) else count
      | [] -> count
    in
    TMap.bindings modes |> loop fmt count

  (** Prints the contract corresponding to a context. *)
  let fmt (two_state, count) fmt { ass ; gua ; modes } =
    Format.fprintf fmt "@[<v>" ;

    let ass_cnt, gua_cnt, mod_cnt =
      TSet.cardinal ass, TSet.cardinal gua, TMap.cardinal modes
    in

    TSet.elements ass |> Format.fprintf fmt "%a" (
      fmt_list (fmt_ass two_state) "@ "
    ) ;

    if ass_cnt > 0 && gua_cnt + mod_cnt > 0 then
      Format.fprintf fmt "@ @ " ;

    TSet.elements gua |> Format.fprintf fmt "%a" (
      fmt_list (fmt_gua two_state) "@ "
    ) ;

    if gua_cnt > 0 && mod_cnt > 0 then
      Format.fprintf fmt "@ @ " ;

    let count = fmt_mode_map (two_state, count) fmt modes in

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

(** Ghost definition formatter. *)
let fmt_def node fmt svar =
  let (var, bounds, expr) =
    match Node.equation_of_svar node svar with
    | Some eq -> eq
    | None ->
      Format.asprintf "state variable `%a` has no definition"
        fmt_svar svar
      |> failwith
  in
  Format.fprintf fmt "@[<hv 2>var %a%a: %a = %a ;@]"
    (Expr.pp_print_lustre_var false) var
    (pp_print_listi
       (fun ppf i -> function 
          | Node.Bound e -> 
            Format.fprintf
              ppf
              "[%a(%a)]"
              (LustreIdent.pp_print_ident false)
              (LustreIdent.push_index LustreIdent.index_ident i)
              (Expr.pp_print_expr false) e
          | Node.Fixed e ->
            Format.fprintf ppf "[%a]" (Expr.pp_print_expr false) e)
       "") 
    bounds
    (Expr.pp_print_lustre_type true) (SVar.type_of_state_var svar)
    (Expr.pp_print_lustre_expr true) expr

let generate_contract_for in_sys param sys path invs =
  let scope = scope_of sys in
  let _, node_of_scope =
    InputSystem.contract_gen_param in_sys
  in
  let node = node_of_scope scope in
  let contract, locals =
    TSet.of_list invs |> Contract.build node
  in

  (* Event.log_uncond "invs: @[<v>%a@]"
    (pp_print_list Term.pp_print_term "@ ") invs ;
  Event.log_uncond "contract has @[<v>%d ass@ %d guas@ %d modes"
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
      "(* Contract for node %s. *)@.contract %s_spec %a@.let@[<v 2>"
      (sys_name sys) (sys_name sys) fmt_sig node ;

    (* Declare necessary locals. *)
    locals |> SvSet.iter (
      fun svar ->
        Format.fprintf fmt "@ " ;
        fmt_def node fmt svar
    ) ;
    if SvSet.cardinal locals > 0 then Format.fprintf fmt "@ " ;

    (* Dump sub contracts. *)
    let _ =
      Format.fprintf fmt "@ " ;
      Contract.fmt (true, 0) fmt contract
    in

    Format.fprintf fmt "@]@.tel@.@."

let generate_contracts in_sys param sys path =
  let max_depth = Flags.Contracts.contract_gen_depth () |> Num.of_int in
  let _, node_of_scope =
    InputSystem.contract_gen_param in_sys
  in
  let get_node sys = try scope_of sys |> node_of_scope with
    | Not_found ->
      Format.asprintf "unknown system %a" fmt_sys_name sys
      |> failwith
  in
  
  Event.log_uncond "  \
    @{<b>Generating contracts@}@ for system %a to file \"%s\"\
  " fmt_sys_name sys path ;

  let teks = Flags.invgen_enabled () in
  let is_active tek = List.mem tek teks in
  let run_bool two_state =
    Event.log_uncond "  Running %s bool invgen..." (
      if two_state then "two-state" else "one-state"
    ) ;
    InvGen.BoolInvGen.main
      (Some max_depth) true true two_state
      in_sys param sys
  in
  let run_int two_state =
    Event.log_uncond "  Running %s int invgen..." (
      if two_state then "two-state" else "one-state"
    ) ;
    InvGen.IntInvGen.main
      (Some max_depth) true true two_state
      in_sys param sys
  in
  let run_real two_state =
    Event.log_uncond "  Running %s real invgen..." (
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
  in

  (* Event.log_uncond "Generating contracts." ; *)

  let trivial_too = Flags.Contracts.contract_gen_fine_grain () in

  (* Build a map from scopes to a list of contract builders. *)
  let contracts =
    results |> fold (
      fun map (two_state, result) ->
        result |> fold (
          fun map (sys, non_trivial, trivial) ->
            let invs =
              non_trivial
              |> if trivial_too then TSet.union trivial else identity
            in
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
  in

  Event.log_uncond "  Dumping contracts to `%s`..." path ;

  let out_channel = open_out path in
  let fmt = Format.formatter_of_out_channel out_channel in

  Format.fprintf fmt
    "(*@[<v>@ \
      The contract below was generated automatically by the Kind 2@ \
      model-checker.@ \
      @ http://kind2-mc.github.io/kind2/\
    @]@ *)@.@.@.@." ;

  contracts |> SMap.iter (
    fun _ (sys, node, locals, sub_contracts) ->
      Event.log L_info "Generating contract for %a..." fmt_sys_name sys ;
      
      Format.fprintf fmt
        "(* Contract for node %s. *)@.contract %s_spec %a@.let@[<v 2>"
        (sys_name sys) (sys_name sys) fmt_sig node ;
      
      (* Declare necessary locals. *)
      locals |> SvSet.iter (
        fun svar ->
          Format.fprintf fmt "@ " ;
          fmt_def node fmt svar
      ) ;
      if SvSet.cardinal locals > 0 then Format.fprintf fmt "@ " ;

      (* Dump sub contracts. *)
      let _ =
        sub_contracts |> fold (
          fun count (two_state, sub) ->
            Format.fprintf fmt "@ " ;
            Contract.fmt (two_state, count) fmt sub
        ) 0
      in

      Format.fprintf fmt "@]@.tel@.@."
  ) ;

  Event.log_uncond "  Done with contract generation." ;

  close_out out_channel ;



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
