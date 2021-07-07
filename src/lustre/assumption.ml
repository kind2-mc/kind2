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

type t =
{
  (* Initial predicate *)
  init: Term.t ;

  (* Transition relation predicate *)
  trans: Term.t;
}

let empty = { init = Term.t_true; trans = Term.t_true }

let is_empty { init; trans } = init == Term.t_true && trans == Term.t_true

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

let filter_non_output in_sys scope =
  let output_svars = get_output_svars in_sys scope in
  List.filter
    (fun v ->
     let sv = Var.state_var_of_state_var_instance v in
     List.exists (fun o -> StateVar.equal_state_vars o sv) output_svars
     |> not
    )

let create_assumpion_init fmt_assump sys solver vars fp prop =

  let init = TSys.init_of_bound None sys Numeral.zero in

  let conclusion = Term.mk_and [prop.Property.prop_term; fp] in

  let assump_init =
    Abduction.abduce solver vars init conclusion
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
      (TSys.trans_of_bound None sys Numeral.one :: invars)
  in

  let premises = Term.mk_and [fp ; trans] in

  let fp_at_1 = Term.bump_state Numeral.one fp in

  let prop_at_1 = Term.bump_state Numeral.one prop.Property.prop_term  in

  let conclusion = Term.mk_and [prop_at_1; fp_at_1] in

  let assump_trans = Abduction.abduce solver vars premises conclusion in

  (*Format.printf "Assump Trans: %a@." Term.pp_print_term assump_trans;*)

  let assump_trans' = Term.bump_state (Numeral.of_int (-1)) assump_trans in

  KEvent.log_uncond "  @[<hov 2>Transition predicate:@ %a@]" fmt_assump assump_trans';

  assump_trans


let generate_assumption in_sys sys var_filters prop =

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
    realizability_check
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
  | Unrealizable -> Failure
  | Unknown -> Unknown


let generate_filename prop =

  let prop_name = prop.Property.prop_name in

  let rindex =
    try Some (String.rindex prop_name '.') with Not_found -> None
  in

  let prefix, name = match rindex with
    | None -> "", prop_name
    | Some i -> (
      let len = String.length prop_name in
      String.sub prop_name 0 (i+1),
      String.sub prop_name (i+1) (len-i-1)
    )
  in

  let contains_invalid_char s invalid =
    List.exists (fun c -> String.contains s c) invalid
  in

  let invalid = [' '; '('; '>'; '<'; '='] in

  let rec get_line_and_column prop =
    match prop.Property.prop_source with
    | Property.PropAnnot pos ->
      let _, l, c = file_row_col_of_pos pos in l, c
    | Property.Instantiated (_, p) ->
      get_line_and_column p
    | _ -> failwith "unexpected property"
  in

  if contains_invalid_char name invalid then (
    let l, c = get_line_and_column prop in
    Format.asprintf "%sl%dc%d.lus" prefix l c
  )
  else (
    Format.asprintf "%s.lus" prop_name
  )


let open_file_and_dump_header prop_name node path contract_name =

  let out_channel = open_out path in
  let fmt = Format.formatter_of_out_channel out_channel in

  let fmt_sig fmt =
    Format.fprintf fmt "@[<hov>%a@]" LustreNode.pp_print_node_signature
  in

  Format.fprintf fmt
    "(* Assumptions for property %s. *)@.contract %s %a@.let@[<v -1>@ "
    prop_name contract_name fmt_sig node ;

  (out_channel, fmt)


let dump_footer fmt =
  Format.fprintf fmt "@]@.tel@.@."


let dump_assumption fmt { init ; trans } =

  let pp_print_lustre_expr = LustreExpr.pp_print_term_as_expr false in

  let trans' = Term.bump_state (Numeral.of_int (-1)) trans in

  Format.fprintf fmt "@[<hov 2>assume@ (%a)@ ->@ (%a);@]"
    pp_print_lustre_expr init pp_print_lustre_expr trans'


let dump_contract_for_assumption in_sys scope assumption prop path contract_name =

  let path = Filename.concat path (generate_filename prop) in

  match ISys.get_lustre_node in_sys scope with
  | Some node -> (

    let out_channel, fmt =
      let prop_name = prop.Property.prop_name in
      open_file_and_dump_header prop_name node path contract_name
    in
    dump_assumption fmt assumption;
    dump_footer fmt;
    close_out out_channel

  )
  | None ->
    KEvent.log L_error "Assumption dump is only supported for Lustre models"

