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

module Ids = Lib.ReservedIds

module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module C = LustreContract
module N = LustreNode
module S = LustreSlicing
module G = LustreGlobals

module A = Analysis
module P = Property

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module SCM = Scope.Map

(* Hash map from node scopes to their index for fresh state variables.
   Used to make sure fresh state variables are indeed fresh after a restart,
   without risking to reach [MAXINT]. *)
let scope_index_map = ref SCM.empty
(* Returns a fresh index for a scope. *)
let index_of_scope s =
  let curr =
    try !scope_index_map |> SCM.find s with Not_found -> 0
  in
  scope_index_map := !scope_index_map |> SCM.add s (curr + 1) ;
  curr

(* Transition system and information needed when calling it *)
type node_def =

  { 

    (* Node the transition system was created from *)
    node : LustreNode.t;

    (* Initial state predicate *)
    init_uf_symbol : UfSymbol.t;

    (* Transition relation predicate *)
    trans_uf_symbol : UfSymbol.t;

    (* Transition system for node *)
    trans_sys : TransSys.t;

    (* Stateful local variables to be instantiated by the caller 

       Local variables of the callees of the node *)
    stateful_locals : StateVar.t list;

    (* Init flags to be set to true *)
    init_flags : StateVar.t list;

    (* Properties to be instantiated by the caller 

       Properties of the callees of the node *)
    properties : P.t list;

  }


(* ********************************************************************** *)
(* Instantiate in calling node                                            *)
(* ********************************************************************** *)

(* Instantiate state variable to the scope of a different node *)
let lift_state_var state_var_map state_var = 

  try 

    (* Find state variable in map *)
    SVM.find state_var state_var_map

  (* Fail, because we don't want a term with state variables of mixed
     scopes *)
  with Not_found -> 

    Format.printf "state_var_map: @[<v>%a@]@."
      (pp_print_list (fun fmt (k,b) ->
        Format.fprintf fmt "%a -> %a"
          StateVar.pp_print_state_var k
          StateVar.pp_print_state_var b)
        "@ "
      ) (SVM.bindings state_var_map) ;

    raise
      (Invalid_argument
         (Format.asprintf 
            "lift_term: state variable %a not found in map"
            StateVar.pp_print_state_var state_var))


(* Instantiate the variables of the term to the scope of a different
   node *)
let lift_term state_var_map term =

  Term.map

    (function _ -> function 

       (* Need to instantiate free variables *)
       | term when Term.is_free_var term -> 

         (* Get variable of term, this will not fail *)
         let var = Term.free_var_of_term term in

         (* Only if variable is an instance of a state variable *)
         if Var.is_state_var_instance var then 

           (* Get state variable of free variable *)
           let state_var = Var.state_var_of_state_var_instance var in

           (* Get offset of variable instance *) 
           let offset = Var.offset_of_state_var_instance var in

           (* Lift state variable to scope of calling node *)
           let state_var' = lift_state_var state_var_map state_var in


           (* Return state variable instance of the lifted state
              variable at the same offset *)
           Term.mk_var (Var.mk_state_var_instance state_var' offset)

         else

           (* No change if free variable is not an instance of a state
              variable *)
           term

       (* No change term that are not free variables *)
       | term -> term)

    term


(* Lift the name of a property in a subnode by adding the position of
   the node call *)
let lift_prop_name node_name pos prop_name =

  (* Pretty-print a file position *)
  let pp_print_file ppf pos_file = 

    if pos_file = "" then () else
      Format.fprintf ppf "%s" pos_file

  in

  (* Pretty-print a position as attributes *)
  let pp_print_pos ppf pos = 

    (* Do not print anything for a dummy position *)
    if is_dummy_pos pos then () else 

      (* Get file, line and column of position *)
      let pos_file, pos_lnum, pos_cnum = 
        file_row_col_of_pos pos
      in

      (* Print attributes *)
      Format.fprintf 
        ppf
        "[%al%dc%d]"
        pp_print_file pos_file
        pos_lnum
        pos_cnum
  in


  string_of_t
    (fun ppf prop_name ->
       Format.fprintf
         ppf
         "%a%a.%s"
         (LustreIdent.pp_print_ident true) node_name
         pp_print_pos pos
         prop_name)
    prop_name



(* ********************************************************************** *)
(* Properties of contracts                                                *)
(* ********************************************************************** *)

(* Create a property from Lustre expression *)
let property_of_expr 
    prop_name
    prop_status
    prop_source
    { E.expr_step; E.expr_init } =

  (* Terms for initial state and step state must be equal. Otherwise
     we would need to abstract to a fresh variable. *)
  assert (E.equal_expr expr_step expr_init);

  (* Term of expresssion *)
  let prop_term = E.cur_term_of_expr TransSys.prop_base expr_step in

  (* Return property *)
  { P.prop_name; P.prop_source; P.prop_term; P.prop_status }

(* Creates the conjunction of a list of contract svar. *)
let conj_of l = List.map (fun { C.svar } -> E.mk_var svar) l |> E.mk_and_n

(* Creates the term conjunction of a list of contract svar. *)
let term_conj_of l = List.map (
  fun { C.svar } ->
    Var.mk_state_var_instance svar Numeral.zero |> Term.mk_var
) l |> Term.mk_and

(* The assumption of the contract. *)
let assumption_of_contract { C.assumes } = conj_of assumes

(* The mode requirements of a contract, for test generation. *)
let ass_and_mode_requires_of_contract = function
| Some { C.assumes ; C.modes } -> (
    match assumes with
      | [] -> None
      | _ -> Some (term_conj_of assumes)
  ), modes |> List.map (
    fun { C.path ; C.requires } -> path, term_conj_of requires
  )
| None -> None, []

(* The guarantees of a contract, including mode implications, as properties. *)
let guarantees_of_contract scope { C.assumes ; C.guarantees ; C.modes } =
  (* Originally properties are unknown. *)
  let prop_status = P.PropUnknown in
  (* Creates a property for a guarantee. *)
  let guarantee_of_svar ({ C.svar ; C.pos } as sv) =
    E.mk_var svar
    |> property_of_expr
      (C.prop_name_of_svar sv "guarantee" "")
      prop_status
      (P.Guarantee (pos, scope))
  in
  (* Creates properties for mode implications of a mode. *)
  let implications_of_modes modes acc =
    modes |> List.fold_left (
      fun acc { C.name ; C.pos ; C.requires ; C.ensures } ->
        let name = Format.asprintf "%a" (I.pp_print_ident true) name in
        (* LHS of the implication. *)
        let guard = conj_of requires in
        (* Generating one property per ensure. *)
        ensures |> List.fold_left (
          fun acc ({ C.num ; C.pos ; C.svar } as sv) -> (
            E.mk_var svar |> E.mk_impl guard
            |> property_of_expr
              (C.prop_name_of_svar sv name ".ensure")
              prop_status
              (P.GuaranteeModeImplication (pos, scope))
          ) :: acc
        ) acc
    ) acc
  in

  guarantees |> List.map guarantee_of_svar |> implications_of_modes modes

(* The assumptions of a contract as properties. *)
let subrequirements_of_contract call_pos scope svar_map { C.assumes } =
  assumes |> List.map (
    fun { C.pos ; C.num ; C.svar } ->
      let prop_term =
        Var.mk_state_var_instance svar TransSys.prop_base
        |> Term.mk_var
        |> lift_term svar_map
      in
      let prop_name =
        Format.asprintf
          "%a%a.assume%a[%d]"
          Scope.pp_print_scope scope pp_print_pos call_pos
          pp_print_pos pos num
      in
      let prop_status = P.PropUnknown in
      let prop_source = P.Assumption (pos, scope) in
      { P.prop_name ;
        P.prop_source ;
        P.prop_term ;
        P.prop_status }
  )

(* Builds the abstraction of a node given its contract.
If the contract is [(a, g, {r_i, e_i})], then the abstraction is
[ a => ( g and /\ {r_i => e_i} ) ]. *)
let abstraction_of_contract { C.assumes ; C.guarantees ; C.modes } =
  (* LHS of the implication. *)
  let lhs = conj_of assumes in
  (* Guarantee. *)
  let gua = guarantees |> List.map (fun { C.svar } -> E.mk_var svar) in
  (* Adding mode implications to guarantees. *)
  modes |> List.fold_left (
    fun acc { C.requires ; C.ensures } ->
      (E.mk_impl (conj_of requires) (conj_of ensures)) :: acc
  ) gua
  |> E.mk_and_n
  (* Building actual abstraction. *)
  |> E.mk_impl lhs

(* The property corresponding to at least one mode of a contract being
active. *)
let one_mode_active scope { C.modes } =
  if modes = [] then failwith "one_mode_active asked on mode-less contract" ;
  (* Disjunction of mode requirements. *)
  modes |> List.map (fun { C.requires } -> conj_of requires) |> E.mk_or_n
  (* Building property. *)
  |> property_of_expr
    "_one_mode_active" P.PropUnknown (P.GuaranteeOneModeActive scope)




(* ********************************************************************** *)
(* Constraints from types                                                 *)
(* ********************************************************************** *)

(* Add constraint for subrange if variable is of that type *)
let add_constraints_of_type init terms state_var = 

  (* Get type of state variable *)
  let state_var_type = StateVar.type_of_state_var state_var in

  (* Variable is of integer range type? *)
  if Type.is_int_range state_var_type ||
     Type.is_enum state_var_type  then 

    (* Get bounds of integer range *)
    let l, u = Type.bounds_of_int_range state_var_type in

    (* Constrain values of variable between bounds *)
    Term.mk_leq
      [ Term.mk_num l; 
        Var.mk_state_var_instance
          state_var
          (if init then 
             TransSys.init_base 
           else 
             TransSys.trans_base)
        |> Term.mk_var;
        Term.mk_num u]

    (* Add to terms *)
    :: terms 

  else

    (* No contraints to add*)
    terms
                  


(* ********************************************************************** *)
(* Node calls                                                             *)
(* ********************************************************************** *)

(* Add instance of called node to list of subsystems

   Group instances of the same node together, each has a different
   state variable map and guarding function. *)
let rec add_subsystem' trans_sys instance accum =

  function 

    (* No other instance of this node found: add as a singleton list  *) 
    | [] -> 

      (trans_sys, [instance]) :: accum

    (* Check if there is another instance of this node  *)
    | (trans_sys', inst) as h :: tl -> 

      (* Compare transition systems by name *)
      if TransSys.equal_scope trans_sys trans_sys' then 

        (* Add node instance to previous instances, append remainder of
           list of subsystems and return *)
        List.rev_append
          ((trans_sys, (instance :: inst)) :: accum)
          tl

      else

        (* Keep searching for transition system in tail of list *)
        add_subsystem' 
          trans_sys
          instance
          (h :: accum)
          tl
      
(* Add instance of called node to list of subsystems *)
let add_subsystem
    trans_sys
    pos
    map_up
    map_down
    guard_clock
    subsystems =

  let instance =
    { TransSys.pos; 
      TransSys.map_up; 
      TransSys.map_down; 
      TransSys.guard_clock }
  in

  (* Use recursive function with empty accumulator *)
  add_subsystem'
    trans_sys
    instance
    []
    subsystems


(* Change the bounds of state variables to the ones corresponding to actual
   parameters of the node call *)
let register_call_bound globals map_up sv =
  let bounds =
    try StateVar.StateVarHashtbl.find globals.G.state_var_bounds sv
    with Not_found -> [] in

  let bounds = List.map (fun b -> match b with
      | E.Fixed _ | E.Unbound _ -> b
      | E.Bound e ->
        let t = E.unsafe_term_of_expr e in
        let svs = Term.state_vars_of_term t |> SVS.elements in
        let sigma =
          List.fold_left (fun acc s ->
              assert (StateVar.is_const s);
              let v = Var.mk_const_state_var s in
              try
                let sv' = SVM.find s map_up in
                assert (StateVar.is_const sv');
                let tv' = Var.mk_const_state_var sv' |> Term.mk_var in
                (v, tv') :: acc
              with Not_found -> acc) [] svs
          |> List.rev in
        if sigma = [] then b
        else
          E.Bound (Term.apply_subst sigma t |> E.unsafe_expr_of_term)
    ) bounds in
  StateVar.StateVarHashtbl.add globals.G.state_var_bounds sv bounds



(* Return term and lifted property for node call 

   This factors out node calls with or without an activation
   condition *)
let call_terms_of_node_call mk_fresh_state_var globals
    { N.call_node_name ;
      N.call_pos       ;
      N.call_inputs    ;
      N.call_oracles   ;
      N.call_outputs   ;}
    node_locals
    node_props
    { init_uf_symbol  ;
      trans_uf_symbol ;
      node = {
        N.init_flag ;
        N.instance  ;
        N.inputs    ;
        N.oracles   ;
        N.outputs   ;
        N.locals    ;
        N.props     ;
        N.contract  ;
      }               ;
      stateful_locals ;
      properties      ;
    } =

  (* Initialize map of state variable in callee to instantiated state
     variable in caller *)
  let state_var_map_up, state_var_map_down = 

    (SVM.empty, SVM.empty)

    (* Map actual to formal inputs *)
    |> D.fold2 (
      fun _ state_var inst_state_var (state_var_map_up, state_var_map_down) -> 
         (SVM.add state_var inst_state_var state_var_map_up,
          SVM.add inst_state_var state_var state_var_map_down)
     ) inputs call_inputs

    (* Map actual to formal outputs *)
    |> D.fold2 (
      fun _ state_var inst_state_var (state_var_map_up, state_var_map_down) -> 
         (SVM.add state_var inst_state_var state_var_map_up,
          SVM.add inst_state_var state_var state_var_map_down)
    ) outputs call_outputs

    |> fun (state_var_map_up, state_var_map_down) ->

        (* Map actual to formal oracles *)
        List.fold_left2 (
          fun (state_var_map_up, state_var_map_down) state_var inst_state_var -> 
             (SVM.add state_var inst_state_var state_var_map_up,
              SVM.add state_var inst_state_var state_var_map_down)
        ) (state_var_map_up, state_var_map_down)
          oracles
          call_oracles

  in

  (* Create fresh state variable for each state variable local
     to the called node and add to the respective data
     structures *)
  let node_locals, call_locals, (state_var_map_up, state_var_map_down) = 

    (* Need to preserve the order of the stateful_locals in call_locals *)
    List.fold_right

      (fun state_var (locals, call_locals, (state_var_map_up, state_var_map_down)) -> 

         (* Create a fresh state variable in the caller *)
         let inst_state_var = 
           mk_fresh_state_var
             ?is_const:(Some (StateVar.is_const state_var))
             ?for_inv_gen:(Some true)
             ?inst_for_sv:(Some state_var)
             (StateVar.type_of_state_var state_var)
         in

         N.set_state_var_instance
           inst_state_var call_pos call_node_name state_var;
         
         (* Add fresh state variable to locals of this node, to actual
            input parameters of node call and to map of state variable
            instances *)
         (inst_state_var :: locals,
          inst_state_var :: call_locals,
          (SVM.add state_var inst_state_var state_var_map_up,
           SVM.add inst_state_var state_var state_var_map_down)))

      (* All stateful local variables of the called node

         This includes the init flag and the instance variable. *)
      stateful_locals

      (* Add to local variables of the node, start with empty list of
         variables instantiated at the call, and extend the state
         variable map *)
      (node_locals, [], (state_var_map_up, state_var_map_down))

  in
  
  (* Instantiate all properties of the called node in this node *)
  let node_props = 
    properties |> List.fold_left (
      fun a ({ P.prop_name = n; P.prop_term = t } as p) -> 

        (* Lift name of property *)
        let prop_name =
          lift_prop_name call_node_name call_pos n
        in

        (* Lift state variable of property

          Property is a local variable, thus it has been
          instantiated and is in the map *)
        let prop_term = lift_term state_var_map_up t in

        (* Property is instantiated *)
        let prop_source = 
          P.Instantiated (I.to_scope call_node_name, p)
        in

        (* Property status is unknown *)
        let prop_status = P.PropUnknown in

        (* Create and append property *)
        { P.prop_name ;
          P.prop_source ;
          P.prop_term ;
          P.prop_status } :: a
    ) node_props
  in

  (* Instantiate assumptions from contracts in this node. *)
  let node_props = match contract with
    | None -> node_props
    | Some contract -> (
      subrequirements_of_contract
        call_pos (I.to_scope call_node_name) state_var_map_up contract
    ) @ node_props
  in

  (* Return actual parameters of initial state constraint at bound in
     the correct order *)
  let init_params_of_bound term_of_state_var =
    List.map 
      term_of_state_var
      ((D.values call_inputs) @ 
       call_oracles @ 
       (D.values call_outputs) @
       call_locals)
  in

  (* Return actual parameters of transition relation at bound in the
     correct order *)
  let trans_params_of_bound term_of_state_var pre_term_of_state_var =
    init_params_of_bound term_of_state_var @
    List.map 
      pre_term_of_state_var
      ((List.filter 
          (fun sv -> StateVar.is_const sv |> not) 
          ((D.values call_inputs) @ 
           D.values call_outputs @
           call_locals)))
  in

  (* Term for initial state constraint at initial state *)
  let init_call_term =
    init_params_of_bound
      (E.base_term_of_state_var TransSys.init_base)

    |> Term.mk_uf init_uf_symbol

  in

  (* Term for initial state constraint at current state *)
  let init_call_term_trans = 
    init_params_of_bound
      (E.cur_term_of_state_var TransSys.trans_base)

    |> Term.mk_uf init_uf_symbol

  in

  (* Term for transition relation at current state *)
  let trans_call_term =
    trans_params_of_bound
      (E.cur_term_of_state_var TransSys.trans_base)
      (E.pre_term_of_state_var TransSys.trans_base)

    |> Term.mk_uf trans_uf_symbol

  in

  (* apply subsitutions on bounds also *)
  LustreIndex.iter (fun _ ->
      register_call_bound globals state_var_map_up) call_inputs;
  LustreIndex.iter (fun _ ->
      register_call_bound globals state_var_map_up) call_outputs;
  List.iter (register_call_bound globals state_var_map_up) call_oracles;
  List.iter (register_call_bound globals state_var_map_up) call_locals;
  
  (* Return information to build constraint for node call with or
     without activation condition *)
  state_var_map_up, 
  state_var_map_down, 
  node_locals, 
  node_props, 
  call_locals,
  init_call_term, 
  init_call_term_trans,
  trans_call_term
  

(* Add constraints from node calls to initial state constraint and
   transition relation *)
let rec constraints_of_node_calls 
  mk_fresh_state_var
    globals
  trans_sys_defs
  node_locals
  node_init_flags
  node_props 
  subsystems
  init_terms
  trans_terms
= function

  (* Definitions for all node calls created, return *)
  | [] -> (
    subsystems, 
    node_locals, 
    node_init_flags, 
    node_props, 
    init_terms, 
    trans_terms
  )

  (* Node call without an activation condition or restart *)
  | { N.call_pos; N.call_node_name; N.call_cond = [] }
    as node_call :: tl ->

    (* Get generated transition system of callee *)
    let { trans_sys } as node_def =
      try I.Map.find call_node_name trans_sys_defs 
      (* Fail if transition system for node not found *)
      with Not_found -> assert false
    in

    let 
      state_var_map_up,
      state_var_map_down,
      node_locals,
      node_props,
      _,
      init_term,
      _,
      trans_term
    =
      (* Create node call *)
      call_terms_of_node_call
        mk_fresh_state_var
        globals
        node_call
        node_locals
        node_props
        node_def
    in

    (* Add node instance to list of subsystems *)
    let subsystems =
      add_subsystem
        trans_sys
        call_pos
        state_var_map_up
        state_var_map_down

        (* No guarding necessary when instantiating term, because
           this node instance does not have an activation
           condition *)
        (fun _ t -> t)

        subsystems
    in

    (* Continue with next node calls *)
    constraints_of_node_calls 
      mk_fresh_state_var
      globals
      trans_sys_defs
      node_locals
      node_init_flags
      node_props
      subsystems
      (init_term :: init_terms)
      (trans_term :: trans_terms)
      tl

  (* Node call with restart condition *)
  | { N.call_pos; N.call_node_name; N.call_cond = [N.CRestart restart] }
    as node_call :: tl ->

    (* Get generated transition system of callee *)
    let { trans_sys } as node_def =
      try I.Map.find call_node_name trans_sys_defs 
      (* Fail if transition system for node not found *)
      with Not_found -> assert false
    in

    let state_var_map_up, state_var_map_down, node_locals, node_props, _,
        init_term, _, trans_term =
      (* Create node call *)
      call_terms_of_node_call
        mk_fresh_state_var globals node_call node_locals node_props node_def
    in

    (* Add node instance to list of subsystems *)
    let subsystems =
      add_subsystem trans_sys call_pos state_var_map_up state_var_map_down
        (* No guarding necessary when instantiating term, because this node
           instance does not have an activation condition *)
        (fun _ t -> t)
        subsystems
    in

    let restart_trans = E.cur_term_of_state_var TransSys.trans_base restart in
    (* Reset state of node to initial state when restart condition is true *)
    let trans_term = Term.mk_ite restart_trans
        (Term.bump_state Numeral.(TransSys.trans_base - E.cur_offset) init_term)
        trans_term in
    
    (* Continue with next node calls *)
    constraints_of_node_calls 
      mk_fresh_state_var
      globals
      trans_sys_defs
      node_locals
      node_init_flags
      node_props
      subsystems
      (init_term :: init_terms)
      (trans_term :: trans_terms)
      tl


  (* Node call with activation condition *)
  | { N.call_pos; 
      N.call_node_name; 
      N.call_cond = N.CActivate clock :: other_conds;
      N.call_inputs;
      N.call_outputs; 
      N.call_defaults } as node_call :: tl -> 

    (* Get generated transition system of callee *)
    let { node = { N.inputs; }; trans_sys; init_flags } as node_def =

      try 

        I.Map.find call_node_name trans_sys_defs 

      (* Fail if transition system for node not found *)
      with Not_found -> assert false

    in


    (* Create shadow variable for each non-constant input *)
    let 
      
      (* Add shadow state variable to local variables, return term
         at previous instant, equation with corresponding inputs,
         and equation with previous state value *)
      (shadow_inputs,
       node_locals,
       propagate_inputs_init, 
       propagate_inputs_trans, 
       interpolate_inputs) =

      D.fold2
        (fun
          formal_idx 
          formal_sv 
          actual_sv
          (shadow_inputs, 
           node_locals,
           propagate_inputs_init, 
           propagate_inputs_trans, 
           interpolate_inputs) ->

          (* Skip over constant formal inputs *)
          if StateVar.is_const formal_sv then 

            (D.add formal_idx formal_sv shadow_inputs, 
             node_locals,
             propagate_inputs_init, 
             propagate_inputs_trans, 
             interpolate_inputs )

          else

            (* Create fresh shadow variable for input *)
            let shadow_sv = 
              mk_fresh_state_var
                ?is_const:None
                ?for_inv_gen:(Some false)
                ?inst_for_sv:(Some formal_sv)
                (StateVar.type_of_state_var formal_sv) 
            in

            (* Shadow variable takes value of input *)
            let p_i = 
              Term.mk_eq
                [E.base_term_of_state_var TransSys.init_base actual_sv; 
                 E.base_term_of_state_var TransSys.init_base shadow_sv]
            in

            (* Shadow variable takes value of input *)
            let p_t = 
              Term.mk_eq
                [E.cur_term_of_state_var TransSys.trans_base actual_sv; 
                 E.cur_term_of_state_var TransSys.trans_base shadow_sv]
            in

            (* Shadow variable takes its previous value *)
            let i = 
              Term.mk_eq
                [E.cur_term_of_state_var TransSys.trans_base shadow_sv; 
                 E.pre_term_of_state_var TransSys.trans_base shadow_sv]
            in

            (* Add shadow variable and equations to accumulator *)
            (D.add formal_idx shadow_sv shadow_inputs,
             shadow_sv :: node_locals,
             p_i :: propagate_inputs_init, 
             p_t :: propagate_inputs_trans, 
             i :: interpolate_inputs))

        inputs
        call_inputs

        (D.empty, node_locals, [], [], [])

    in

    let 

      state_var_map_up, 
      state_var_map_down, 
      node_locals, 
      node_props, 
      call_locals,
      init_term, 
      init_term_trans, 
      trans_term =

      call_terms_of_node_call
        mk_fresh_state_var
        globals
        (* Modify node call to use shadow inputs *)
        { node_call with N.call_inputs = shadow_inputs }
        node_locals
        node_props
        node_def
    in

    (* Add restart conditions if any *)
    let trans_term = match other_conds with
      | [] -> trans_term
      | [N.CRestart restart] ->
        let restart_trans =
          E.cur_term_of_state_var TransSys.trans_base restart in
        (* Reset state of node to initial state when restart condition is
           true *)
        Term.mk_ite restart_trans
          (Term.bump_state
             Numeral.(TransSys.trans_base - E.cur_offset) init_term)
          trans_term
      | _ -> assert false
    in

    
    let clock_init = 
      E.base_term_of_state_var TransSys.init_base clock 
    in

    let clock_trans = 
      E.cur_term_of_state_var TransSys.trans_base clock 
    in

    let clock_prop = 
      E.cur_term_of_state_var TransSys.prop_base clock 
    in

    let clock_trans_pre = 
      E.pre_term_of_state_var TransSys.trans_base clock 
    in

    let has_ticked =
      mk_fresh_state_var
        ?is_const:None
        ?for_inv_gen:(Some false)
        ?inst_for_sv:(Some clock)
        Type.t_bool
    in

    let node_locals = 
      has_ticked :: node_locals
    in

    let has_ticked_init = 
      E.base_term_of_state_var TransSys.init_base has_ticked
    in

    let has_ticked_trans = 
      E.cur_term_of_state_var TransSys.trans_base has_ticked
    in

    let has_ticked_trans_pre = 
      E.pre_term_of_state_var TransSys.trans_base has_ticked
    in

    let init_flags = 
      List.map (fun sv -> SVM.find sv state_var_map_up) init_flags
    in

    let init_flags_init =
      List.map
        (E.base_term_of_state_var TransSys.init_base) 
        init_flags
    in

    let init_term = 

      Term.mk_and 

        ([
          
          (* [has_ticked] is false in the first instant, because
             it becomes true only after the first clock tick. *)
          Term.negate has_ticked_init;
          
          (* Propagate input values to shadow variables on clock
             tick *)
          Term.mk_implies 
            [clock_init;
             Term.mk_and propagate_inputs_init];
          
          (* Initial state constraint on clock tick *)
          Term.mk_implies [clock_init; init_term]
            
        ] @

          (match call_defaults with
            
            (* No defaults for outputs *)
            | None -> 

              (* Init flags are false if clock is not ticking *)
              [Term.mk_implies 
                 [Term.mk_not clock_init;
                  Term.mk_and init_flags_init]]

            (* Defaults for outputs *)
            | Some d -> 

              (* Init flags are true and defaults for outputs if no
                 clock tick *)
              [Term.mk_implies 
                 [Term.mk_not clock_init;
                  Term.mk_and
                    (D.fold2
                       (fun _ sv { E.expr_init } accum ->
                          Term.mk_eq 
                            [E.base_term_of_state_var TransSys.init_base sv;
                             E.base_term_of_expr TransSys.init_base expr_init] :: 
                          accum)
                       call_outputs
                       d
                       init_flags_init)]]))
          
    in

    let trans_term =
      Term.mk_and
        [

          (* has_ticked flag becomes true in the instant after
             the first clock tick and stays true *)
          Term.mk_eq 
            [has_ticked_trans;
             Term.mk_or
               [has_ticked_trans_pre; 
                clock_trans_pre]];

          (* Propagate input values to shadow variables on clock
             tick *)
          Term.mk_implies 
            [clock_trans;
             Term.mk_and propagate_inputs_trans];

          (* Interpolate input values in shadow variable between
             clock ticks *)
          Term.mk_implies 
            [Term.mk_not clock_trans; 
             Term.mk_and interpolate_inputs];

          (* Transition relation with true activation condition
               on the first clock tick *)
          Term.mk_implies
            [Term.mk_and 
               [clock_trans; Term.negate has_ticked_trans];
             init_term_trans];

          (* Transition relation with true activation condition
             on following clock ticks *)
          Term.mk_implies
            [Term.mk_and
               [clock_trans; has_ticked_trans];
             trans_term];

          (* Transition relation with false activation
             condition *)
          Term.mk_implies 
            [Term.mk_not clock_trans;
             Term.mk_and 
               (List.fold_left
                  (fun accum state_var ->
                     Term.mk_eq 
                       [E.cur_term_of_state_var
                          TransSys.trans_base 
                          state_var; 
                        E.pre_term_of_state_var
                          TransSys.trans_base
                          state_var] :: 
                     accum)
                  []
                  call_locals
                |> D.fold
                  (fun _ state_var accum -> 
                     Term.mk_eq 
                       [E.cur_term_of_state_var
                          TransSys.trans_base 
                          state_var; 
                        E.pre_term_of_state_var
                          TransSys.trans_base
                          state_var] :: 
                     accum)
                  call_outputs) ]

        ]

    in
    
    
    (* Guard lifted property with activation condition of node *)
    let node_props = 
      List.map
        (fun ({ P.prop_term } as p) -> 
           { p with P.prop_term = Term.mk_implies [clock_prop; prop_term] })
        node_props
    in

    (* Add node instance as subsystem *)
    let subsystems =
      add_subsystem
        trans_sys
        call_pos
        state_var_map_up
        state_var_map_down
        (fun i t ->  
           Term.mk_implies
             [Var.mk_state_var_instance clock i
              |> Term.mk_var; 
              t])

        subsystems
    in

    constraints_of_node_calls
      mk_fresh_state_var
      globals
      trans_sys_defs
      node_locals
      (init_flags @ node_init_flags)
      node_props
      subsystems
      (init_term :: init_terms)
      (trans_term :: trans_terms)
      tl


  | _ -> assert false


(* Add constraints from assertions to initial state constraint and
   transition relation *)
let rec constraints_of_asserts init_terms trans_terms = function

  (* All assertions consumed, return term for initial state
     constraint and transition relation *)
  | [] -> (init_terms, trans_terms)
          
  (* Assertion with term for initial state and term for transitions *)
  | { E.expr_init; E.expr_step } :: tl ->

     (* Term for assertion in initial state *)
    let init_term = E.base_term_of_expr TransSys.init_base expr_init
                    |> Term.convert_select in 

     (* Term for assertion in step state *)
    let trans_term = E.cur_term_of_expr TransSys.trans_base expr_step
                     |> Term.convert_select in 

     (* Add constraint unless it is true *)
     let init_terms = 
      if Term.equal init_term Term.t_true then init_terms
      else init_term :: init_terms in

     (* Add constraint unless it is true *)
     let trans_terms = 
      if Term.equal trans_term Term.t_true then trans_terms
      else trans_term :: trans_terms in

    (* Continue with next assertions *)
    constraints_of_asserts init_terms trans_terms tl


module MBounds = Map.Make (struct
    type t = E.expr E.bound_or_fixed list
    let compare_bounds b1 b2 = match b1, b2 with
      | E.Fixed e1, E.Fixed e2
      | E.Bound e1, E.Bound e2
      | E.Unbound e1, E.Unbound e2 -> E.compare_expr e1 e2
      | E.Fixed _, _ -> -1
      | _, E.Fixed _ -> 1
      | E.Unbound _, _ -> 1
      | _, E.Unbound _ -> -1
    let compare l1 l2 =
      let n1, n2 = List.length l1, List.length l2 in
      let c = n2 - n1 in
      if c <> 0 then c else
        let rec cmp = function
          | b1 :: r1, b2 :: r2 ->
            let c = compare_bounds b1 b2 in
            if c <> 0 then c else cmp (r1, r2)
          | [], [] -> 0
          | _ -> assert false
        in
        cmp (l1, l2)
  end)


(* Add constraints from equations to initial state constraint and
   transition relation *)
let rec constraints_of_equations_wo_arrays
    eq_bounds init stateful_vars terms lets = function 

  (* Constraints for all equations generated *)
  | [] -> terms, lets, eq_bounds

  (* Stateful variable must have an equational constraint *)
  | ((state_var, []), { E.expr_init; E.expr_step }) :: tl 
    when List.exists (StateVar.equal_state_vars state_var) stateful_vars -> 

    (* Equation for stateful variable *)
    let def = 
      Term.mk_eq 
        (if init then 
           (* Equation for initial constraint on variable *)
           [E.base_term_of_state_var TransSys.init_base state_var; 
            E.base_term_of_expr TransSys.init_base expr_init] 
         else
           (* Equation for transition relation on variable *)
           [E.cur_term_of_state_var TransSys.trans_base state_var; 
            E.cur_term_of_expr TransSys.trans_base expr_step])
      (* Convert select operators to uninterpreted functions *)
      |> Term.convert_select
    in

    (* Add terms of equation *)
    constraints_of_equations_wo_arrays
      eq_bounds init stateful_vars (def :: terms) lets tl


  (* Can define state variable with a let binding *)
  | ((state_var, []), ({ E.expr_init; E.expr_step } as expr)) :: tl ->

    (* Let binding for stateless variable, in closure form *)
    let let_closure =
      Term.mk_let 
        (if init then 
           (* Binding for the variable at the base instant only *)
           [(E.base_var_of_state_var TransSys.init_base state_var, 
             E.base_term_of_expr TransSys.init_base expr_init)] 
         else
           (* Binding for the variable at the current instant *)
           (E.cur_var_of_state_var TransSys.trans_base state_var, 
            E.cur_term_of_expr TransSys.trans_base expr_step) :: 
           (if 
             (* Does the state variable occur at the previous
                instant? *)
             try
             Term.state_vars_at_offset_of_term 
               Numeral.(TransSys.trans_base |> pred) 
               (Term.mk_and terms)
             |> SVS.mem state_var  
             with Invalid_argument _ -> true

              
            then
              ((* Definition must not contain a [pre] operator, otherwise we'd
                  have a double [pre]. The state variable is not stateless in
                  this case, and we should not be here. *)
                assert (not (E.has_pre_var E.base_offset expr));
                (* Binding for the variable at the previous instant *)
                [(E.pre_var_of_state_var TransSys.trans_base state_var, 
                  E.pre_term_of_expr TransSys.trans_base expr_step)])
            else (* No binding for the variable at the previous instant
                    necessary *)
              [])
           )
    in

    (* Start with singleton lists of let-bound terms *)
    constraints_of_equations_wo_arrays
      eq_bounds init stateful_vars terms (let_closure :: lets) tl

  (* Array state variable *)
  | (((state_var, bounds), { E.expr_init; E.expr_step }) as eq) :: tl -> 

    let other_eqs = try MBounds.find bounds eq_bounds with Not_found -> [] in

    (* map equation to its bounds for future treatment and continue *)
    let eq_bounds = MBounds.add bounds (eq :: other_eqs) eq_bounds in
    
    constraints_of_equations_wo_arrays
      eq_bounds init stateful_vars terms lets tl



(* create quantified (or no) constraints for recursive arrays definitions *)
let constraints_of_arrays init terms eq_bounds =

    (* Return the i-th index variable *)
  let index_var_of_int i = E.var_of_expr (E.mk_index_var i) in

    (* Add quantifier or let binding for indexes of variable *)
  let add_bounds term bounds =
    let term, quant_v, _ =
      List.fold_left (fun (term, quant_v, i) ->
          let v = index_var_of_int i in
          function
          | E.Fixed e ->
            Term.mk_let [v, E.unsafe_term_of_expr e] term, quant_v, pred i

          | E.Bound e when Flags.Arrays.inline () && E.is_numeral e ->
            (* inline if static bound and option given *)
            let b = E.numeral_of_expr e |> Numeral.to_int in
            let cj = ref [] in
            for x = (b - 1) downto 0 do
              cj := Term.mk_let [v, Term.mk_num_of_int x] term :: !cj
            done;
            Term.mk_and !cj, quant_v, pred i

          | E.Bound e ->
            let term =
              if Flags.Arrays.recdef () then term
              else
                let te = E.unsafe_term_of_expr e
                         |> fun t -> if init then t
                            else Term.bump_state Numeral.one t in
                Term.(
                  mk_implies [
                    mk_leq [mk_num Numeral.zero; mk_var v; 
                            mk_minus [te; mk_num Numeral.one]];
                    term])
            in
            term, v :: quant_v, pred i

          | E.Unbound _ ->
            (* let v' = Term.free_var_of_term (E.unsafe_term_of_expr v) in *)
            term, v :: quant_v, pred i
                             
        ) (term, [], List.length bounds - 1) bounds
    in

    match List.rev quant_v with
    | [] -> term
    | qvars -> Term.mk_forall ~fundef:(Flags.Arrays.recdef ()) quant_v term

    in
  
  
  MBounds.fold (fun bounds eqs terms ->
      let cstrs_eqs =
        List.map (function
            | (state_var, bounds), { E.expr_init; E.expr_step } ->
              (* Array state variable term *)
              let sv_term =
                if init then E.base_term_of_state_var TransSys.init_base state_var
                else E.cur_term_of_state_var TransSys.trans_base state_var
              in
              (* Select array *)
              let select_term, _ =
                List.fold_left
                  (fun (st, i) _ ->
                     Term.mk_select st (Term.mk_var (index_var_of_int i)),
                     succ i)
                  (sv_term, 0)
             bounds 
    in
    (* Assign value to array position *)
              (Term.mk_eq 
                 [select_term;
                  if init then 
                    (* Expression at base instant *)
                    E.base_term_of_expr TransSys.init_base expr_init
                  else
                    (* Expression at current instant *)
                    E.cur_term_of_expr TransSys.trans_base expr_step]
                 (* Convert select operators to uninterpreted functions *)
              ) |> Term.convert_select
          ) eqs
      in

      (* group constraints under same quantifier when not using recursive
         encoding *)
      let cstrs =
        if Flags.Arrays.recdef () then cstrs_eqs
        else [Term.mk_and cstrs_eqs] in
      
      (* Wrap equations in let binding and/or quantifiers for indexes and add
         definitions to terms *)        
      List.fold_left (fun terms cstr ->
            add_bounds cstr bounds :: terms
        ) terms cstrs
           
    ) eq_bounds terms              
           
           
let constraints_of_equations init stateful_vars terms equations =
        
  (* make constraints for equations which do not redefine arrays first *)
  let terms, lets, eq_bounds =
    constraints_of_equations_wo_arrays
      MBounds.empty init stateful_vars terms [] equations
    in

  (* then make constraints for recursive arrays so as to merge quantifiers as
     much as possible *)
  let terms = constraints_of_arrays init terms eq_bounds in

  if lets = [] then terms
  else
    (* Apply let bindings *)
    [List.fold_left (fun t let_bind -> let_bind t)
       (Term.mk_and terms) (List.rev lets)
     |> Term.convert_select]


let rec trans_sys_of_node'
  globals
  top_name
  analysis_param
  trans_sys_defs
  output_input_dep
  nodes
= function

  (* Transition system for all nodes created *)
  | [] -> trans_sys_defs

  (* Create transition system for top node *)
  | node_name :: tl ->

    (* Transition system for node has been created and added to
       accumulator meanwhile? *)
    if I.Map.mem node_name trans_sys_defs then

      (* Continue with next transition systems *)
      trans_sys_of_node'
        globals
        top_name
        analysis_param
        trans_sys_defs 
        output_input_dep
        nodes
        tl

    (* Transition system has not been created *)
    else

      (* Node to create a transition system for *)
      let { N.instance;
            N.init_flag;
            N.inputs;
            N.oracles;
            N.outputs;
            N.locals;
            N.equations;
            N.calls;
            N.asserts;
            N.props;
            N.contract;
            N.is_function } as node =

        try 

          (* Find node in abstract or implementation nodes by name *)
          N.node_of_name node_name nodes

        with Not_found ->

          (* Node must be in the list of nodes *)
          raise
            (Invalid_argument
               (Format.asprintf 
                  "trans_sys_of_node: node %a not found"
                  (I.pp_print_ident false) node_name))

      in
        
      (* Scope of node name *)
      let scope = [I.string_of_ident false node_name] in

      (* Create a fresh state variable *)
      let mk_fresh_state_var
          ?is_const
          ?for_inv_gen
          ?inst_for_sv
          state_var_type =

        (* Increment counter for fresh state variables *)
        let index = index_of_scope scope in

        (* Create state variable *)
        let fsv =
          StateVar.mk_state_var
            ~is_input:false
            ?is_const:is_const
            ?for_inv_gen:for_inv_gen
            ((I.push_index I.inst_ident index) 
             |> I.string_of_ident true)
            (N.scope_of_node node @ I.reserved_scope)
            state_var_type
        in

          (* Register bounds *)
        let bounds = match inst_for_sv with
          | None -> []
          | Some sv ->
            try StateVar.StateVarHashtbl.find globals.G.state_var_bounds sv
            with Not_found -> []
        in
          StateVar.StateVarHashtbl.add globals.G.state_var_bounds fsv bounds;
          
          fsv
          
      in

      (* Subnodes for which we have not created a transition
         system

         Collect only the nodes to add here, thus we can eliminate
         duplicates from tl'. A node may need to appear in both tl'
         and tl. *)
      let tl' = 

        List.fold_left 
          (fun accum { N.call_node_name } -> 
             if 

               (* Transition system for node created? *)
               I.Map.mem call_node_name trans_sys_defs || 

               (* Node already pushed to stack before this node? *)
               List.exists (I.equal call_node_name) accum

             then 

               (* Continue with stack unchanged *)
               accum

             else

               (* Push node to top of stack *)
               call_node_name :: accum)

          []
          calls

      in

      (* Are there subnodes for which a transition system needs to
         be created first? *)
      match tl' with

        (* Some transitions systems of called nodes have not been
           created *)
        | _ :: _ -> 

          (* We could check here that the call graph does not have
             cycles, although that should not be allowed as long as
             we don't accept recursive calls in Lustre. *)

          (* Recurse to create transition system for called nodes,
             then return to this node *)
          trans_sys_of_node'
            globals
            top_name
            analysis_param
            trans_sys_defs
            output_input_dep
            nodes
            (tl' @ node_name :: tl)

        (* All transitions systems of called nodes have been
           created *)
        | [] ->


          (* If node is a function, create a UF `f` for each output. Also,
          create the term `(= (f <inputs>) output)` to add it to `init` and
          `trans`. *)
          let function_ufs, function_constraints_at_0 =
            if not is_function then [], [] else (
              let inputs = D.values inputs in
              let type_of = StateVar.type_of_state_var in
              let term_0_of svar =
                Var.mk_state_var_instance svar Numeral.zero
                |> Term.mk_var
              in
              let input_types, input_terms_at_0 =
                inputs
                |> List.rev
                |> List.fold_left (
                  fun (types, terms) input ->
                    (* Retrieving type of input. *)
                    type_of input :: types,
                    (* Creating term at 0. *)
                    term_0_of input :: terms
                ) ([], [])
              in

              D.values outputs
              |> List.fold_left (
                fun (ufs, eqs) output ->
                  let uf_name =
                    Format.asprintf "%a.%s.%s"
                      Scope.pp_print_scope scope
                      (StateVar.name_of_state_var output)
                      Lib.ReservedIds.function_of_inputs
                  in
                  let uf =
                    UfSymbol.mk_uf_symbol
                      uf_name input_types (type_of output)
                  in
                  uf :: ufs,
                  Term.mk_eq [
                    term_0_of output ;
                    Term.mk_uf uf input_terms_at_0
                  ] :: eqs
              ) ([], [])
            )
          in


          (* Filter assumptions for this node's assumptions *)
          let node_assumptions = 
            A.param_assumptions_of_scope analysis_param scope
          in


          (* ****************************************************** *)
          (* Assertions from contracts and init flag                *)

          (* Start with asserts and properties for contracts *)
          let contract_asserts, properties = match contract with
            | None -> [], []
            | Some contract ->

              (* Add requirements to invariants if node is the top node *)
              let contract_asserts, properties = 
                if I.equal node_name top_name then
                  (* Node is top, forcing contract assumption. *)
                  [ assumption_of_contract contract ],
                  (* Add property for completeness of modes if top node is
                    abstract. *)
                  if A.param_scope_is_abstract analysis_param scope then
                    [ one_mode_active scope contract ]
                  else []
                else
                  [], []
              in

              (* Add mode implications to invariants if node is abstract,
                 otherwise add ensures as properties *)
              if A.param_scope_is_abstract analysis_param scope then
                abstraction_of_contract contract :: contract_asserts,
                properties 
              else
                contract_asserts,
                guarantees_of_contract scope contract @ properties
          in

          (* Initial state constraint *)
          let init_terms = 

            (* Init flag is true on first tick of node *)
            E.base_term_of_state_var TransSys.init_base init_flag :: 

            (* Add invariants from contracts as assertions *)
            List.map
              (E.base_term_of_t TransSys.init_base)
              contract_asserts

            (* Add functional constraints on ouputs if any. *)
            |> List.rev_append function_constraints_at_0

          in

          (* Transition relation *)
          let trans_terms = 

            (* Init flag becomes and stays false at the second
               tick *)
            (E.cur_term_of_state_var TransSys.trans_base init_flag
             |> Term.negate) :: 

            (* Add invariants from contracts as assertions *)
            List.map
              (E.cur_term_of_t TransSys.trans_base)
              contract_asserts

            (* Add functional constraints on ouputs if any. *)
            |> List.rev_append (
              (* Bump to `1`. *)
              function_constraints_at_0
              |> List.map (Term.bump_state Numeral.one)
            )

          in


          (* ****************************************************** *)
          (* Assertions from types                                  *)

          let all_state_vars = 
            (D.values inputs) @
            oracles @
            (D.values outputs) @ 
            (List.concat (List.map D.values locals))
          in

          let init_terms = 
            List.fold_left
              (add_constraints_of_type true)
              init_terms
              all_state_vars
          in

          let trans_terms = 
            List.fold_left
              (add_constraints_of_type false)
              trans_terms
              all_state_vars
          in

          (* ****************************************************** *)
          (* Node calls 

             We must add node calls before equations so that local
             variables can be let bound in
             {!constraints_of_equations}.                           *)

          (* Instantiated state variables and constraints from node
             calls *)
          let
            subsystems, 
            lifted_locals, 
            init_flags,
            lifted_props, 
            init_terms, 
            trans_terms
          =
            constraints_of_node_calls
              mk_fresh_state_var
              globals
              trans_sys_defs
              []  (* No lifted locals *)
              [init_flag]
              []  (* No lifted properties *)
              []  (* No subsystems *)
              init_terms
              trans_terms
              calls
          in

          (* Add lifted properties *)
          let properties = properties @ lifted_props in

          (* ****************************************************** *)
          (* Assertions 

             We must add contracts before equations so that local
             variables can be let bound in
             {!constraints_of_equations}.                           *)

          (* Constraints from assertions *)
          let init_terms, trans_terms = 
              constraints_of_asserts init_terms trans_terms asserts in


          (* ****************************************************** *)
          (* Equations                                              *)

          (* Stateful variables in node, including state
             variables for node instance, first tick flag, and state
             variables capturing outputs of node calls *)
          let stateful_vars = 
            init_flag ::
              (N.stateful_vars_of_node node |> SVS.elements)
              @ lifted_locals in


          let global_consts =
            (* Format.eprintf "Global constants: %d@." *)
            (*   (List.length globals.G.free_constants); *)
            List.fold_left (fun acc (_, vt) ->
                D.fold (fun _ v acc ->
                    (* Format.eprintf "Gobal constant: %a@." Var.pp_print_var v; *)
                    v :: acc) vt acc
              ) [] globals.G.free_constants
            |> List.rev
          in
          
          let global_consts_sv =
            List.map Var.state_var_of_state_var_instance global_consts
            |> SVS.of_list in
          let stateful_vars = List.filter (fun sv ->
              not (SVS.mem sv global_consts_sv)
            ) stateful_vars
          in
          
          (* Order initial state equations by dependency and
             generate terms *)
          let init_terms, node_output_input_dep_init =
            S.order_equations true output_input_dep node
              |> (fun (e, d) ->
               constraints_of_equations
                    true stateful_vars init_terms (List.rev e), d)
          in

          (* Order transition relation equations by dependency and
             generate terms *)
          let trans_terms, node_output_input_dep_trans =
            S.order_equations false output_input_dep node
              |> (fun (e, d) ->
               constraints_of_equations
                    false stateful_vars trans_terms (List.rev e), d)
          in

          (* ****************************************************** *)
          (* Properties                                         

             We can only add properties after node calls, because
             properties may have been lifted from calls.            *)

          (* Create properties from annotations *)
          let properties = 

            (* Property status is unknown *)
            let prop_status = P.PropUnknown in

            (* Iterate over each property annotation *)
            List.map (
              fun (state_var, prop_name, prop_source) -> 

              (* Property is just the state variable *)
              let prop_term =
                E.cur_term_of_state_var
                  TransSys.prop_base
                  state_var
              in

              { P.prop_name; 
                P.prop_source; 
                P.prop_term;
                P.prop_status }
            ) props
              
            (* Add to existing properties *)
            @ properties 

          in

          (* Extract requirements. *)
          let mode_requires = ass_and_mode_requires_of_contract contract in

          (* ****************************************************** *)
          (* Turn assumed properties into assertions                *)

          (* Make assumed properties assertions *)
          let init_terms, trans_terms, properties = 

            (* Iterate over each property annotation *)
            List.fold_left
              (fun 
                (init_terms, trans_terms, properties)
                ({ P.prop_name; 
                   P.prop_source; 
                   P.prop_term;
                   P.prop_status } as p) -> 

                if 

                  (* Property is assumed invariant? *)
                  List.exists (Term.equal prop_term) node_assumptions

                then

                  (* Bump term to offset of initial state constraint *)
                  let prop_term_init = 
                    Term.bump_state
                      Numeral.(TransSys.init_base - TransSys.prop_base)
                      prop_term
                  in

                  (* Bump term to offset of transition relation *)
                  let prop_term_trans = 
                    Term.bump_state
                      Numeral.(TransSys.trans_base - TransSys.prop_base)
                      prop_term
                  in

                  (* Add property as assertion *)
                  (prop_term_init :: init_terms,
                   prop_term_trans :: trans_terms,
                   properties)

                else

                  (* Add to properties *)
                  (init_terms,
                   trans_terms,
                   p :: properties))

              (init_terms, trans_terms, [])

              properties

          in

          (* ****************************************************** *)
          (* Signatures of predicates                               *)

          (* State variables that are inputs, outputs or oracles and
             thus have instances in each caller *)
          let signature_state_vars = 
            (D.values inputs) @ 
            oracles @
            (D.values outputs)
          in

          (* Stateful variables that are not inputs, outputs or
             oracles, and must be instantiated in each caller *)
          let stateful_locals =
            List.filter
              (fun sv -> 
                 not
                   (List.exists
                      (fun sv' -> StateVar.equal_state_vars sv sv')
                      signature_state_vars))
              stateful_vars
          in

            (* State variables in the signature of the initial state constraint
               in correct order *)
          let signature_state_vars = 
            signature_state_vars @ stateful_locals
          in

          (* Formal parameters of initial state constraint *)
          let init_formals = 
            List.map
              (fun sv -> 
                 Var.mk_state_var_instance sv TransSys.init_base)
              signature_state_vars
          in

            (* Create uninterpreted symbol for initial state predicate *)
          let init_uf_symbol = 
            UfSymbol.mk_uf_symbol
              (Format.asprintf
                 "%s_%a_%d"
                 Ids.init_uf_string
                 (LustreIdent.pp_print_ident false) node_name
                 (A.info_of_param analysis_param).A.uid)
              (List.map Var.type_of_var init_formals)
              Type.t_bool
          in

          (* Create instances of state variables in signature *)
          let trans_formals = 

            (* All state variables at the current instant *)
            List.map 
              (fun sv ->
                 Var.mk_state_var_instance sv TransSys.trans_base)
              signature_state_vars @

              (* Not constant state variables at the previous instant *)
            List.map 
              (fun sv -> 
                 Var.mk_state_var_instance 
                   sv
                   (TransSys.trans_base |> Numeral.pred))
              (List.filter
                 (fun sv -> not (StateVar.is_const sv)) 
                 signature_state_vars)
          in

            (* Create uninterpreted symbol for transition relation predicate *)
          let trans_uf_symbol = 
            UfSymbol.mk_uf_symbol
              (Format.asprintf
                 "%s_%a_%d"
                 Ids.trans_uf_string
                 (LustreIdent.pp_print_ident false) node_name
                 (A.info_of_param analysis_param).A.uid)
              (List.map Var.type_of_var trans_formals)
              Type.t_bool
          in

          (* UFs of the system. *)
          let ufs = function_ufs in
          
          
          (* ****************************************************** *)
          (* Create transition system                               *)
          (* ****************************************************** *)

          (* Create transition system *)
          let trans_sys, _ = 
            TransSys.mk_trans_sys 
              [I.string_of_ident false node_name]
              None (* instance_state_var *)
              init_flag
              [] (* global_state_vars *)
              (signature_state_vars)
              globals.G.state_var_bounds
              global_consts
              ufs
              init_uf_symbol
              init_formals
              (Term.mk_and init_terms)
              trans_uf_symbol
              trans_formals
              (Term.mk_and trans_terms)
              subsystems
              properties
              mode_requires
              [] (* One-state invariants *)
              [] (* Two-state invariants *)
          in

          trans_sys_of_node'
            globals
            top_name
            analysis_param
            (I.Map.add 
               node_name
               { node;
                 trans_sys;
                 init_uf_symbol;
                 trans_uf_symbol;
                 stateful_locals;
                 init_flags;
                 properties }
               trans_sys_defs)
            ((node_name, 
              (node_output_input_dep_init, node_output_input_dep_trans))
             :: output_input_dep)
            nodes
            tl
          

let trans_sys_of_nodes
    ?(preserve_sig = false)
    globals
    subsystem analysis_param
  =

  (* Prevent the garbage collector from running too often during the frontend
     operations *)
  Lib.set_liberal_gc ();
  
  let { A.top; A.abstraction_map; A.assumptions } =
    A.info_of_param analysis_param
  in
  (* Make sure top level system is not abstract

     Contracts would be trivially satisfied otherwise *)
  ( match analysis_param with
    | A.ContractCheck _ -> ()
    | _ -> if A.param_scope_is_abstract analysis_param top then raise (
      Invalid_argument
        "trans_sys_of_nodes: Top-level system must not be abstract"
    )
  );

  (* TODO: Find top subsystem by name *)
  let subsystem' = subsystem in
  
  let { SubSystem.source = { N.name = top_name } as node } as subsystem' =
    S.slice_to_abstraction
      ~preserve_sig:preserve_sig analysis_param subsystem'
  in

  let nodes = N.nodes_of_subsystem subsystem' in


  let { trans_sys } =   

    try 

      (* Create a transition system for each node *)
      trans_sys_of_node'
        globals
        top_name
        analysis_param
        I.Map.empty
        [] 
        nodes
        [top_name]

      (* Return the transition system of the top node *)
      |> I.Map.find top_name

    (* Transition system must have been created *)
    with Not_found -> assert false

  in
  
  ( match analysis_param with
    | A.Refinement (_,result) ->
      (* The analysis that's going to run is a refinement. *)
      TransSys.get_prop_status_all_nocands result.A.sys
      |> List.iter (function
        | name, P.PropUnknown -> (* Unknown is still unknown, do nothing. *)
          ()
        
        | name, (P.PropKTrue k as status) -> (* K-true is still k-true. *)
          TransSys.set_prop_status trans_sys name status
        
        | name, P.PropInvariant cert -> (* Invariant is still invariant. *)
          TransSys.set_prop_invariant trans_sys name cert;
          (* Adding to invariants of the system. *)
          let t = TransSys.get_prop_term trans_sys name in
          TransSys.add_invariant trans_sys t cert
          |> ignore
        
        | name, P.PropFalse cex -> (
          match P.length_of_cex cex with
          | l when l > 1 -> (* False at k>0 is now (k-1)-true. *)
            (* Minus 2 because l = k + 1. *)
            TransSys.set_prop_status trans_sys name (P.PropKTrue (l-2))
          | _ -> (* False at 0 is now unknown, do nothing. *)
            ()
        )
      )
    | _ -> ()
  ) ;

  (* Reset garbage collector to its initial settings *)
  Lib.reset_gc_params ();

  trans_sys, subsystem'



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
