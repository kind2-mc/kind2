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

module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module N = LustreNode
module F = LustreFunction
module G = LustreGlobals
module S = LustreSlicing

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


(* Creates one term per require for each global mode, and one term for
   the disjunction of the mode requirement. Applies
   [f_global contract_name_as_string ensure_pos] to each global require, and
   [f_mode contract_name] to the mode requirement. *)
let contract_req_map f_global f_mode global_contracts mode_contracts =

  (* One term per require for each global mode *)
  ( global_contracts
    |> List.fold_left (fun prop_list { N.contract_name ; N.contract_reqs } ->
        let name = I.string_of_ident false contract_name in
        contract_reqs |> List.fold_left (fun prop_list (pos,count,sv) ->
          (sv |> E.mk_var |> f_global name pos count) :: prop_list
        ) prop_list
    ) [] )

  @

  (* No mode requirement if node has no mode *)
  if mode_contracts = [] then [] else 
    
    (* Disjunction of requirements from all modes *)
    [ mode_contracts
      |> List.map (fun { N.contract_reqs } -> 
          contract_reqs |> List.map (fun (_,_,sv) -> sv |> E.mk_var)
          |> E.mk_and_n
      )
      |> E.mk_or_n
      |> f_mode ]


(* Generates a list of triplets
   [(is_contract_global, contract_name, require_term)]. *)
let contract_extract_requires global_contracts mode_contracts = (
  global_contracts |> List.map (fun { N.contract_name ; N.contract_reqs } ->
    true,
    I.string_of_ident false contract_name,
    contract_reqs |> List.map (fun (pos,_,sv) -> sv |> E.mk_var)
    |> E.mk_and_n |> E.cur_term_of_t TransSys.prop_base
  )
) @ (
  mode_contracts |> List.map (fun { N.contract_name ; N.contract_reqs } ->
    false,
    I.string_of_ident false contract_name,
    contract_reqs |> List.map (fun (pos,_,sv) -> sv |> E.mk_var)
    |> E.mk_and_n |> E.cur_term_of_t TransSys.prop_base
  )
)


(* Creates one term per ensure clause in each global mode, and one term per
   ensure ([/\ require => ensure]) in each mode. Applies
   [f_global contract_name_as_string ensure_pos] to each global require, and
   [f_mode contract_name_as_string ensure_pos] to each require implication for
   each mode. *)
let contract_ens_map f_global f_mode global_contracts mode_contracts = 

  (* One term per ensures clause in each global contract *)
  List.fold_left
    (fun accum { N.contract_name ; N.contract_enss } ->
      let name = LustreIdent.string_of_ident false contract_name in
       List.map
         (fun (pos, count, sv_ens) -> 
            E.mk_var sv_ens
            |> f_global name pos count)
         contract_enss @ accum)
    []
    global_contracts

  @

  (* One property per ensures clause in a mode contract *)
  List.fold_left
    ( fun accum { N.contract_name ; N.contract_reqs ; N.contract_enss } ->
        let name = LustreIdent.string_of_ident false contract_name in
      
        (* Guard for property is requirement *)
        let t_req =
          contract_reqs |> List.map (fun (_,_,sv) -> E.mk_var sv)
          |> E.mk_and_n
        in
         
        (* Each property in mode contract is implication between
           requirement and ensures *)
        List.map
          (fun (pos, count, sv_ens) -> 
             E.mk_impl t_req (E.mk_var sv_ens)
             |> f_mode name pos count)
          contract_enss @ accum )
    []
    mode_contracts


(* Quiet pretty printer for non dummy positions. *)
let pprint_pos fmt pos =
  let f,l,c = file_row_col_of_pos pos in
  let f = if f = "" then "" else f ^ "@" in
  Format.fprintf fmt "%sl%dc%d" f l c

(* Return properties from contracts of node *)
let caller_props_of_req scope { N.global_contracts; N.mode_contracts } =
  (* Property is unknown *)
  let prop_status = P.PropUnknown in
  (* Create property from terms of global requires. *)
  global_contracts
  |> List.fold_left (
    fun prop_list { N.contract_name ; N.contract_reqs ; N.contract_pos } ->
      contract_reqs |> List.fold_left (fun prop_list (pos,count,sv) ->
        let name =
          Format.asprintf "%a.require[%a][%d]"
            (LustreIdent.pp_print_ident true)
            contract_name pprint_pos pos count
        in
        let var = E.mk_var sv in
        (property_of_expr
          name prop_status (
            P.Assumption (contract_pos, scope)
          ) var) :: prop_list
    ) prop_list
  ) []

let one_mode_active scope { N.mode_contracts } =
  match mode_contracts with
  | [] -> [] | _ -> [
    (* Originally prop is unknown. *)
    let prop_status = P.PropUnknown in
    let name = "__one_mode_active" in
    (* Create disjunction of mode requirements. *)
    mode_contracts |> List.map (
      fun { N.contract_name ; N.contract_pos ; N.contract_reqs } ->
        (* Conjunction of the requires of the mode. *)
        contract_reqs |> List.map (fun (_,_,sv) -> E.mk_var sv) |> E.mk_and_n
    ) |> E.mk_or_n
    (* Building property. *)
    |> property_of_expr
      "__one_mode_active"
      P.PropUnknown
      (P.GuaranteeOneModeActive scope)
  ]

(* Return terms from contracts of node *)
let assumption_of_contract scope { N.global_contracts } = 
  match global_contracts with
  | [ { N.contract_reqs } ] -> contract_reqs |> List.map (
    fun (pos, count, sv) -> sv |> E.mk_var
  ) |> E.mk_and_n
  | [] -> E.t_true
  | _ -> failwith "more than one global contract"

  (* Return terms of global and mode requires unchanged *)
  (* contract_req_map 
    (fun _ _ _ -> identity)
    identity
    global_contracts
    mode_contracts *)


(* Return properties from contracts of node *)
let props_of_ens scope { N.global_contracts; N.mode_contracts } =

  (*  *)
  let guarantee_name_of count _ pos =
    Format.asprintf "guarantee[%a][%d]" pprint_pos pos count
  in
  let ensure_name_of count name pos =
    Format.asprintf "%s.ensure[%a][%d]" name pprint_pos pos count
  in

  (* Property is unknown *)
  let prop_status = P.PropUnknown in
       
  (* Create property with fixed name and status *)
  let guarantee_of_expr' count name pos =
    property_of_expr (guarantee_name_of count name pos) prop_status
  in
  let ensure_of_expr' count name pos =
    property_of_expr (ensure_name_of count name pos) prop_status
  in

  (* Create property from terms of global and mode requires *)
  contract_ens_map (
      fun name pos count ->
        guarantee_of_expr' count name pos (P.Guarantee (pos, scope))
    ) (
      fun name pos count ->
        ensure_of_expr' count name pos (
          P.GuaranteeModeImplication (pos, scope)
        )
    )
    global_contracts
    mode_contracts


(* Return terms from contracts of node *)
let abstraction_of_node scope { N.global_contracts; N.mode_contracts } = 

  (* Collect assumption and guarantees. *)
  let assumption, guarantees =
    global_contracts |> List.fold_left (
      fun (a,g) { N.contract_reqs ; N.contract_enss } ->
        contract_reqs |> List.fold_left (
          fun acc (_,_,sv) -> (E.mk_var sv) :: a
        ) a,
        contract_enss |> List.fold_left (
          fun acc (_,_,sv) -> (E.mk_var sv) :: a
        ) g
    ) ([],[])
    |> fun (a,g) -> E.mk_and_n a, g
  in

  (* Collect mode implications modulo assumption. *)
  mode_contracts |> List.fold_left (
    fun acc { N.contract_reqs ; N.contract_enss } ->
      E.mk_impl (
        contract_reqs |> List.map(
          fun (_,_,sv) -> E.mk_var sv
        ) |> E.mk_and_n
      ) (
        contract_enss |> List.map(
          fun (_,_,sv) -> E.mk_var sv
        ) |> E.mk_and_n
      ) :: acc
  ) guarantees
  (* More readable if guarantees are first. *)
  |> List.rev |> E.mk_and_n
  (* Only valid when assumption holds. *)
  |> E.mk_impl assumption

  (* Return terms of global and mode requires unchanged *)
  (* contract_ens_map 
    (fun _ _ _ -> identity)
    (fun _ _ _ -> identity)
    global_contracts
    mode_contracts *)


let convert_select instance term = 
  
  Term.map
    
    (fun _ t ->
       
       (* Term is a select operation? *)
       if Term.is_select t then

         (* Get array variable and indexes of term *)
         let var, indexes = 
           Term.indexes_and_var_of_select t
         in

         (* Get indexes of type of variable *)
         let index_types = 
           Var.type_of_var var |> Type.all_index_types_of_array
         in

         (* Skip if not all indexes of array in term *)
         if List.length indexes < List.length index_types then t else

           (

             (* Must not have more indexes than defined in type *)
             assert (List.length indexes = List.length index_types);

             (* Uninterpreted function application for array *)
             Term.mk_uf
               (Var.state_var_of_state_var_instance var
                |> StateVar.uf_symbol_of_state_var)
               
               ((* First parameter is node instance *)
                 (Var.mk_const_state_var instance
                  |> Term.mk_var) :: 
                 
                 (* Following parameters are indexes *)
                 indexes)
               
           )

       else t
    )
    term



(* ********************************************************************** *)
(* Constraints from types                                                 *)
(* ********************************************************************** *)

(* Add constraint for subrange if variable is of that type *)
let add_constraints_of_type init terms state_var = 

  (* Get type of state variable *)
  let state_var_type = StateVar.type_of_state_var state_var in

  (* Variable is of integer range type? *)
  if Type.is_int_range state_var_type then 

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


(* Return term and lifted property for node call 

   This factors out node calls with or without an activation
   condition *)
let call_terms_of_node_call mk_fresh_state_var {
  N.call_node_name ;
  N.call_pos       ;
  N.call_inputs    ;
  N.call_oracles   ;
  N.call_outputs   ;
} node_locals node_props {
  init_uf_symbol  ;
  trans_uf_symbol ;
  node = {
    N.init_flag        ;
    N.instance         ;
    N.inputs           ;
    N.oracles          ;
    N.outputs          ;
    N.locals           ;
    N.props            ;
    N.global_contracts ;
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
  let node_props =
    global_contracts |> List.fold_left (
      fun a { N.contract_reqs } ->
        contract_reqs |> List.fold_left (
          fun a (pos,n,sv) ->
            (* Create assumption nameh and lift it. *)
            let prop_name =
              Format.asprintf "assumption[%a][%d]" pprint_pos pos n
              |> lift_prop_name call_node_name call_pos
            in
            (* Lift svar of assumption. Should be in the map. *)
            let prop_term =
              Var.mk_state_var_instance sv TransSys.prop_base
              |> Term.mk_var |> lift_term state_var_map_up
            in
            (* Property is an assumption. *)
            let prop_source =
              P.Assumption (pos, I.to_scope call_node_name)
            in
            (* Property status is unknown. *)
            let prop_status = P.PropUnknown in
            (* Create and append property. *)
            { P.prop_name ;
              P.prop_source ;
              P.prop_term ;
              P.prop_status } :: a
        ) a
    ) node_props
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

  (* Node call without an activation condition *)
  | { N.call_pos; N.call_node_name; N.call_clock = None } as node_call :: tl ->

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
      N.call_clock = Some clock;
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

        (* Modify node call to use shadow inputs *)
        { node_call with N.call_inputs = shadow_inputs }

        node_locals
        node_props
        node_def
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
      trans_sys_defs
      node_locals
      (init_flags @ node_init_flags)
      node_props
      subsystems
      (init_term :: init_terms)
      (trans_term :: trans_terms)
      tl


(* Add functionality constraints and contracts from function calls *)
let rec constraints_of_function_calls
  mk_fresh_state_var locals functions init_terms trans_terms properties
= function

  (* All function calls processed *)
  | [] -> locals, init_terms, trans_terms, properties

  (* Take name of called function, inputs and outputs *)
  | {
    N.call_pos; N.call_function_name; N.call_inputs; N.call_outputs
  } :: tl ->

    (* Definition of called function *)
    let {
      F.inputs; 
      F.outputs; 
      F.output_ufs; 
      F.global_contracts; 
      F.mode_contracts
    } as fn =

      (* Get called function by name *)
      try F.function_of_name call_function_name functions 

      (* We must have the function in the globals, otherwise we
         should have failed earlier *)
      with Not_found -> assert false 

    in

    (* Add constraints to init and trans terms *)
    let init_terms, trans_terms = 
      D.fold2
        (fun _ uf o (i, t) -> 

          (* Add constraint for output *)
          let mk_i_or_t f_o f_e = 

            (* Add [o = uf_f(i1, ..., In)] *)
            Term.mk_eq
              [Term.mk_uf 
                  uf
                  (D.values call_inputs |> List.map f_e); 
               f_o o]
          in
          
          (* Create constraint in initial state *)
          mk_i_or_t 
            (E.base_term_of_state_var TransSys.init_base)
            (E.base_term_of_t TransSys.init_base)
          :: i,

          (* Create constraint in step state *)
          mk_i_or_t 
            (E.cur_term_of_state_var TransSys.trans_base)
            (E.cur_term_of_t TransSys.trans_base)
          :: t)
        output_ufs
        call_outputs
        (init_terms, trans_terms)
    in

    (* Prefix string for properties created from contracts *)
    let prop_scope =

      (* Identify call site with line and column number *)
      let _, call_pos_lnum, call_pos_cnum =
        file_row_col_of_pos call_pos
      in

      (* String of function name and call position *)
      Format.asprintf
        "%a[l%dc%d]"
        (I.pp_print_ident true) call_function_name
        call_pos_lnum
        call_pos_cnum
    in

    (* Scope of function name *)
    let scope = I.to_scope call_function_name in

    (* Properties are unknown *)
    let prop_status = P.PropUnknown in

    let

        (* Substitutions of actual for formal input parameters in
           init, trans and property terms

           Functions are stateless, therefore we don't have state
           variables at the previous instant to substitute. *)
        actuals_for_formals_init,
        actuals_for_formals_trans,
        actuals_for_formals_prop =
      
      D.fold2
        (fun _ sv e (i, t, p) ->
          (Var.mk_state_var_instance sv TransSys.init_base,
           E.base_term_of_t TransSys.init_base e) :: i,
          (Var.mk_state_var_instance sv TransSys.trans_base,
           E.cur_term_of_t TransSys.trans_base e) :: t,
          (Var.mk_state_var_instance sv TransSys.prop_base,
           E.cur_term_of_t TransSys.prop_base e) :: p)
        inputs
        call_inputs
        ([], [], [])
    in
    
    let

        (* Substitutions of actual for formal output parameters in
           init, trans and property terms

           Functions are stateless, therefore we don't have state
           variables at the previous instant to substitute. *)
        actuals_for_formals_init,
        actuals_for_formals_trans,
        actuals_for_formals_prop =
      
      D.fold2
        (fun _ sv sv' (i, t, p) ->
          (Var.mk_state_var_instance sv TransSys.init_base,
           Var.mk_state_var_instance sv' TransSys.init_base
           |> Term.mk_var) :: i, 
          (Var.mk_state_var_instance sv TransSys.trans_base,
           Var.mk_state_var_instance sv' TransSys.trans_base
           |> Term.mk_var) :: t, 
          (Var.mk_state_var_instance sv TransSys.prop_base,
           Var.mk_state_var_instance sv' TransSys.prop_base
           |> Term.mk_var) :: p)
        outputs
        call_outputs
        (actuals_for_formals_init,
         actuals_for_formals_trans,
         actuals_for_formals_prop)
    in

    (* let pp_print_binding title binding =
      Format.printf "%s:@." title ;
      binding |> List.iter (fun (v, t) ->
        Format.printf "  %a -> %a@."
          Var.pp_print_var v Term.pp_print_term t
      ) ;
      Format.printf "@."
    in

    pp_print_binding "actuals_for_formals_init" actuals_for_formals_init ;
    pp_print_binding "actuals_for_formals_trans" actuals_for_formals_trans ;
    pp_print_binding "actuals_for_formals_prop" actuals_for_formals_prop ; *)

    (* Partially evaluate constructor for let binding to substitute
       actuals for formals in initial state *)
    let mk_let_init =
      Term.mk_let actuals_for_formals_init
    in
    
    (* Partially evaluate constructor for let binding to substitute
       actuals for formals in transition state *)
    let mk_let_trans =
      Term.mk_let actuals_for_formals_trans
    in

    (* Adds the constraints for a property state variable to some init and
       trans terms, prepends the new svar to a list of locals. Returns updated
       locals, init and trans terms and the svar created. *)
    let add_prop_sv_constraints locals init trans lexpr =

      (* Creating new state var for lifted requirement. *)
      let sv = mk_fresh_state_var
        ?is_const:(Some false)
        ?for_inv_gen:(Some true)
        (Type.t_bool)
      in

      sv :: locals,
      ( Term.mk_eq [
          Var.mk_state_var_instance sv TransSys.init_base
          |> Term.mk_var ;
          E.base_term_of_t TransSys.init_base lexpr |> mk_let_init
        ]
      ) :: init,
      ( Term.mk_eq [
          Var.mk_state_var_instance sv TransSys.trans_base
          |> Term.mk_var ;
          E.cur_term_of_t TransSys.trans_base lexpr |> mk_let_trans
        ]
      ) :: trans,
      sv
    in
    
    (* Partially evaluate constructor for let binding to substitute
       actuals for formals in property state *)
    (* let mk_let_prop =
      Term.mk_let actuals_for_formals_prop
    in *)

    (* Add properties and assertions from global contracts *)
    let locals, init_terms, trans_terms, properties =
      List.fold_left (fun (l, i, t, p) { F.contract_reqs; F.contract_enss } ->

        (* Adding ensure constraints for init and trans. *)
        let i, t = (
            contract_enss |> List.map (fun (ens,_) ->
              E.base_term_of_expr TransSys.init_base ens |> mk_let_init
            )
          ) @ i, (
            contract_enss |> List.map (fun (ens,_) ->
              E.cur_term_of_expr TransSys.trans_base ens |> mk_let_trans
            )
          ) @ t
        in

        (* Adding a property for each requirement. *)
        contract_reqs |> List.fold_left (
          fun (l,i,t,p) (req,pos) ->

            (* Creating fresh svar, adding constraints, updating locals. *)
            let l, i, t, sv =
              E.mk_of_expr req |> add_prop_sv_constraints l i t
            in

            l, i, t, { (* Creating new property for the requirement. *)
              P.prop_name =
                Format.asprintf "%s.func_global_req%a"
                  prop_scope
                  pp_print_pos pos ;
              (* We cannot give the svars for the ensures following from this
                 requirement because they're not svars... *)
              P.prop_source = P.Assumption (pos, scope);
              P.prop_status;
              P.prop_term =
                Var.mk_state_var_instance sv TransSys.prop_base
                |> Term.mk_var
            } :: p
        ) (l,i,t,p)
      )
      (locals, init_terms, trans_terms, properties)
      global_contracts
    in

    (* Add assertions from mode contracts and collect requirements *)
    let init_terms, trans_terms, mode_contracts_req =
      List.fold_left (fun (i, t, r) { F.contract_reqs; F.contract_enss } ->

        ( Term.mk_implies [
            contract_reqs |> List.map (fun (e,_) ->
              E.base_term_of_expr TransSys.init_base e
            ) |> Term.mk_and ;

            contract_enss |> List.map (fun (e,_) ->
              E.base_term_of_expr TransSys.init_base e
            ) |> Term.mk_and ;
          ] |> mk_let_init
        ) :: i,

        ( Term.mk_implies [
            contract_reqs |> List.map (fun (e,_) ->
              E.base_term_of_expr TransSys.trans_base e
            ) |> Term.mk_and ;

            contract_enss |> List.map (fun (e,_) ->
              E.base_term_of_expr TransSys.trans_base e
            ) |> Term.mk_and ;
          ] |> mk_let_trans
        ) :: t,

        ( contract_reqs |> List.map (fun p -> fst p |> E.mk_of_expr)
          |> E.mk_and_n) :: r
      )
      (init_terms, trans_terms, [])
      mode_contracts
    in

    (* Continue with next function call *)
    constraints_of_function_calls
      mk_fresh_state_var
      locals
      functions 
      init_terms
      trans_terms
      properties
      tl


(* Add constraints from assertions to initial state constraint and
   transition relation *)
let rec constraints_of_asserts instance init_terms trans_terms = function

  (* All assertions consumed, return term for initial state
     constraint and transition relation *)
  | [] -> (init_terms, trans_terms)
          
  (* Assertion with term for initial state and term for transitions *)
  | { E.expr_init; E.expr_step } :: tl ->

     (* Term for assertion in initial state *)
     let init_term =
       E.base_term_of_expr TransSys.init_base expr_init
       |> convert_select instance
     in 

     (* Term for assertion in step state *)
     let trans_term =
       E.cur_term_of_expr TransSys.trans_base expr_step
       |> convert_select instance
     in 

     (* Add constraint unless it is true *)
     let init_terms = 
       if Term.equal init_term Term.t_true then
         init_terms
       else
         init_term :: init_terms 
     in

     (* Add constraint unless it is true *)
     let trans_terms = 
       if Term.equal trans_term Term.t_true then
         trans_terms
       else
         trans_term :: trans_terms 
     in

    (* Continue with next assertions *)
    constraints_of_asserts instance init_terms trans_terms tl
      

(* Add constraints from equations to initial state constraint and
   transition relation *)
let rec constraints_of_equations init stateful_vars instance terms = function 

  (* Constraints for all equations generated *)
  | [] -> terms 

  (* Stateful variable must have an equational constraint *)
  | (state_var, [], { E.expr_init; E.expr_step }) :: tl 
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
      |> convert_select instance

    in

    (* Add terms of equation *)
    constraints_of_equations 
      init
      stateful_vars
      instance
      (def :: terms)
      tl


  (* Can define state variable with a let binding *)
  | (state_var, [], ({ E.expr_init; E.expr_step } as expr)) :: tl ->

    (* Let binding for stateless variable *)
    let def =

      (* Conjunction of previous terms of definitions *)
      (Term.mk_and terms)

      |>

      (* Define variable with a let *)
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
             Term.state_vars_at_offset_of_term 
               Numeral.(TransSys.trans_base |> pred) 
               (Term.mk_and terms)
             |> SVS.mem state_var  

            then
              
              (

                (* Definition must not contain a [pre] operator,
                   otherwise we'd have a double [pre]. The state
                   variable is not stateless in this case, and we
                   should not be here. *)
                assert (not (E.has_pre_var E.base_offset expr));

                (* Binding for the variable at the previous instant *)
                [(E.pre_var_of_state_var TransSys.trans_base state_var, 
                  E.pre_term_of_expr TransSys.trans_base expr_step)])
              
            else

              (* No binding for the variable at the previous
                 instant necessary *)
              [])

           )

      (* Convert select operators to uninterpreted functions *)
      |> convert_select instance

    in

    (* Start with singleton lists of let-bound terms *)
    constraints_of_equations 
      init
      stateful_vars
      instance
      [def]
      tl

  (* Array state variable *)
  | (state_var, bounds, { E.expr_init; E.expr_step }) :: tl -> 

    (* TODO: If bounds are not fixed, unroll to fixed bounds and
       generate equations without quantifiers *)


    (* Return the i-th index variable *)
    let index_var_of_int i = 
      E.mk_index_var i
      |> E.state_var_of_expr
      |> (fun sv ->
          Var.mk_state_var_instance
            sv
            (if init then TransSys.init_base else TransSys.trans_base))
    in

    (* Add quantifier or let binding for indexes of variable *)
    let add_bounds = function 

      (* Fixed index [e] *)
      | N.Fixed e -> 

        (* Let bind index variable to value [e] *)
        fun (a, i) ->
          (Term.mk_let 
             [index_var_of_int i,
              (e : E.expr :> Term.t)]
             a,
           pred i)

      (* Variable index of size [e] *)
      | N.Bound e -> 

        (* Quantify over index variable between zero and upper bound *)
        fun (a, i) -> 

          (* Index variable *)
          let v = index_var_of_int i in

          (* Quantify over index variable between 0 and [e] *)
          (Term.mk_forall
             [v]
             (Term.mk_implies 
                [Term.mk_leq [Term.mk_num Numeral.zero; Term.mk_var v; 
                              (e : E.expr :> Term.t)]; a]),
           pred i)
    in

    (* Uninterpreted function application for array *)
    let uf_term = 
      Term.mk_uf
        (StateVar.uf_symbol_of_state_var state_var)

        ((* First parameter is node instance *)
          (Var.mk_const_state_var instance
           |> Term.mk_var) :: 

          (* Following parameters are indexes *)
          (List.fold_left
             (fun (a, i) _ -> 
                (index_var_of_int i
                 |> Term.mk_var) :: a,
                pred i)
             ([], List.length bounds |> pred)
             bounds 
           |> fst))
    in

    (* Assign value to array position *)
    let eq = 

      Term.mk_eq 

        (uf_term::

         if init then 
           
           (* Expression at base instant *)
           [E.base_term_of_expr TransSys.init_base expr_init
            |> convert_select instance]
           
         else
           
           (* Expression at current instant *)
           [E.cur_term_of_expr TransSys.trans_base expr_step
            |> convert_select instance])
        
    in

    (* Wrap equation in let binding and quantifiers for indexes *)
    let def, _ = 
      List.fold_right
        add_bounds
        bounds
        (eq, List.length bounds |> pred)
    in

    (* Add definition and continue *)
    constraints_of_equations 
      init
      stateful_vars
      instance
      (def :: terms)
      tl


let rec trans_sys_of_node'
  top_name
  analysis_param
  trans_sys_defs
  output_input_dep
  nodes
  ({ G.functions } as globals)
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
        top_name
        analysis_param
        trans_sys_defs 
        output_input_dep
        nodes 
        globals
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
            N.function_calls; 
            N.asserts; 
            N.props;
            N.global_contracts;
            N.mode_contracts } as node = 

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
          state_var_type =

        (* Increment counter for fresh state variables *)
        let index = index_of_scope scope in

        (* Create state variable *)
        StateVar.mk_state_var
          ~is_input:false
          ?is_const:is_const
          ?for_inv_gen:for_inv_gen
          ((I.push_index I.inst_ident index) 
           |> I.string_of_ident true)
          (N.scope_of_node node @ I.reserved_scope)
          state_var_type

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
            top_name
            analysis_param
            trans_sys_defs
            output_input_dep
            nodes
            globals
            (tl' @ node_name :: tl)

        (* All transitions systems of called nodes have been
           created *)
        | [] ->

          (* Filter assumptions for this node's assumptions *)
          let node_assumptions = 
            A.param_assumptions_of_scope analysis_param scope
          in

          (* Start without properties *)
          let properties = [] in


          (* ****************************************************** *)
          (* Assertions from contracts and init flag                *)

          (* Start without invariants for contracts *)
          let contract_asserts = [] in

          (* Add requirements to invariants if node is the top node,
             otherwise add requirements as properties *)
          let contract_asserts, properties = 
            if I.equal node_name top_name then 
              assumption_of_contract scope node :: contract_asserts,
              one_mode_active scope node @ properties
            else
              contract_asserts, properties
          in            

          (* Add enusres to invariants if node is abstract,
             otherwise add ensures as properties *)
          let contract_asserts, properties = 
            if A.param_scope_is_abstract analysis_param scope then
              abstraction_of_node scope node :: contract_asserts, properties 
            else
              contract_asserts, props_of_ens scope node @ properties 
          in            

          (* Initial state constraint *)
          let init_terms = 

            (* Init flag is true on first tick of node *)
            E.base_term_of_state_var TransSys.init_base init_flag :: 

            (* Add invariants from contracts as assertions *)
            List.map
              (E.base_term_of_t TransSys.init_base)
              contract_asserts

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
          (* Function calls 

             We must add function calls before equations so that local
             variables can be let bound in
             {!constraints_of_equations}.                           *)

          (* Instantiated state variables and constraints from node
             calls *)
          let lifted_locals, init_terms, trans_terms, properties =
            constraints_of_function_calls
              mk_fresh_state_var
              lifted_locals
              functions
              init_terms
              trans_terms
              properties
              function_calls 
          in

          (* Format.printf "equations: @[<hov>%a@]@.@."
            (pp_print_list (N.pp_print_node_equation false) ",@ ") equations ;

          Format.printf "properties: @[<hov>%a@]@.@."
            (pp_print_list P.pp_print_property ",@ ")
            properties ; *)

          (* ****************************************************** *)
          (* Assertions 

             We must add contracts before equations so that local
             variables can be let bound in
             {!constraints_of_equations}.                           *)

          (* Constraints from assertions *)
          let init_terms, trans_terms = 
            constraints_of_asserts  
              instance
              init_terms
              trans_terms
              asserts
          in


          (* ****************************************************** *)
          (* Equations                                              *)

          (* Stateful variables in node, including state
             variables for node instance, first tick flag, and state
             variables capturing outputs of node calls *)
          let stateful_vars = 
            init_flag ::
            (N.stateful_vars_of_node node |> SVS.elements)
            @ lifted_locals
          in

          (* Order initial state equations by dependency and
             generate terms *)
          let init_terms, node_output_input_dep_init =

            S.order_equations true output_input_dep node

            |>

            (fun (e, d) -> 
               constraints_of_equations
                 true
                 stateful_vars
                 instance
                 init_terms
                 (List.rev e),

               d)

          in

          (* Order transition relation equations by dependency and
             generate terms *)
          let trans_terms, node_output_input_dep_trans =

            S.order_equations false output_input_dep node

            |>

            (fun (e, d) -> 
               constraints_of_equations
                 false
                 stateful_vars
                 instance
                 trans_terms
                 (List.rev e),

               d)

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
            List.map
              (fun (state_var, prop_name, prop_source) -> 

                 (* Property is just the state variable *)
                 let prop_term =
                   E.cur_term_of_state_var
                     TransSys.prop_base
                     state_var
                 in

                   { P.prop_name; 
                     P.prop_source; 
                     P.prop_term;
                     P.prop_status })

              props
              
            (* Add to existing properties *)
            @ properties 

          in

          (* Extract requirements. *)
          let mode_requires =
            contract_extract_requires global_contracts mode_contracts
          in

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

          (* State variables in the signature of the initial state
             constraint in correct order *)
          let signature_state_vars = 
            signature_state_vars @ stateful_locals
          in

          (* Arrays become global state variables and are removed
             from signature *)
          let global_state_vars, signature_state_vars = 
            List.partition
              (fun sv -> StateVar.type_of_state_var sv |> Type.is_array)
              signature_state_vars 
          in

          (* TODO: add actual bound of state variable *)
          let global_state_vars = 
            List.map
              (fun sv -> (sv, []))
              global_state_vars
          in

          (* Need to add an instance variable when we have arrays *)
          let signature_state_vars, instance_state_var =
            if global_state_vars = [] then 
              signature_state_vars, None 
            else 
              instance :: signature_state_vars, Some instance 
          in

          (* Formal parameters of initial state constraint *)
          let init_formals = 
            List.map
              (fun sv -> 
                 Var.mk_state_var_instance sv TransSys.init_base)
              signature_state_vars
          in

          (* Create uninterpreted symbol for initial state
             predicate *)
          let init_uf_symbol = 
            UfSymbol.mk_uf_symbol
              (Format.asprintf
                 "%s_%a_%d"
                 I.init_uf_string
                 (LustreIdent.pp_print_ident false) node_name
                 analysis_param.A.uid)
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

            (* Not constant state variables at the previous
               instant *)
            List.map 
              (fun sv -> 
                 Var.mk_state_var_instance 
                   sv
                   (TransSys.trans_base |> Numeral.pred))
              (List.filter
                 (fun sv -> not (StateVar.is_const sv)) 
                 signature_state_vars)
          in

          (* Create uninterpreted symbol for transition relation
             predicate *)
          let trans_uf_symbol = 
            UfSymbol.mk_uf_symbol
              (Format.asprintf
                 "%s_%a_%d"
                 I.trans_uf_string
                 (LustreIdent.pp_print_ident false) node_name
                 analysis_param.A.uid)
              (List.map Var.type_of_var trans_formals)
              Type.t_bool
          in

          (* Collect uninterpreted function symbols from globals

             TODO: We could first reduce the list of uninterpreted
             function symbols to the ones used in this system and
             its subsystems. *)
          let ufs =
            List.fold_left
              (fun accum { F.output_ufs } ->
                D.fold
                  (fun _ u a -> u :: a)
                  output_ufs
                  accum)
              []
              functions
          in
                
          
          (* ****************************************************** *)
          (* Create transition system                               *)

          (* Create transition system *)
          let trans_sys, _ = 
            TransSys.mk_trans_sys 
              [I.string_of_ident false node_name]
              instance_state_var
              init_flag
              global_state_vars
              (signature_state_vars)
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
(*
          Format.printf "%a@." TransSys.pp_print_trans_sys trans_sys;
*)
          trans_sys_of_node'
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
            globals
            tl
          

let trans_sys_of_nodes 
  subsystem
  globals
  ({ A.top; A.abstraction_map; A.assumptions } as  analysis_param)
=
  
  (* Make sure top level system is not abstract

     Contracts would be trivially satisfied otherwise *)
  (if A.param_scope_is_abstract analysis_param top then
     raise
       (Invalid_argument
          "trans_sys_of_nodes: Top-level system must not be abstract"));

  (* TODO: Find top subsystem by name *)
  let subsystem' = subsystem in

  let { SubSystem.source = { N.name = top_name } as node } as subsystem', globals' = 
      LustreSlicing.slice_to_abstraction analysis_param subsystem' globals
  in

  let nodes = N.nodes_of_subsystem subsystem' in 
(*
  Format.printf 
    "@[<v>%a@]@."
    (pp_print_list (F.pp_print_function false) "@,") globals'.G.functions;

  Format.printf
    "@[<v>%a@]@."
    (pp_print_list (N.pp_print_node false) "@,") (List.rev nodes);
*)
  let { trans_sys } =   

    try 

      (* Create a transition system for each node *)
      trans_sys_of_node'
        top_name
        analysis_param
        I.Map.empty
        [] 
        nodes
        globals
        [top_name]

      (* Return the transition system of the top node *)
      |> I.Map.find top_name

    (* Transition system must have been created *)
    with Not_found -> assert false

  in
(*
  let s1, s2, s3, s4, s5, s6 = Term.T.stats () in

  Format.printf 
    "@[<v>Table length: %d@,\
          Number of entries: %d@,\
          Sum of bucket lengths: %d@,\
          Smallest bucket length: %d@,\
          Median bucket length: %d@,\
          Biggest bucket length: %d@]@."
    s1 s2 s3 s4 s5 s6;
*)

  trans_sys, subsystem', globals'

(*

let test () = 

  let  { SubSystem.source = { N.name = top_name } as node } as lustre_subsystem = 
    LustreInput.of_file Sys.argv.(1) 
  in

  let analysis = 
    { A.top = [I.string_of_ident false top_name]; 
      A.abstraction_map = Scope.Map.empty; 
      A.assumptions = [] }
  in

  let trans_sys, lustre_subsystem = trans_sys_of_nodes lustre_subsystem analysis in

  (* Test declarations and definitions *)

  let define uf_symbol vars term = 
    Format.printf
      "@[<hv 1>(define-fun %a@ @[<hv 1>(%a)@]@ @[<hv 1>%a@])@]@."
      UfSymbol.pp_print_uf_symbol uf_symbol
      (pp_print_list Var.pp_print_var "@ ") vars
      Term.pp_print_term term
  in

  let declare uf_symbol = 
    Format.printf
      "(declare-fun %a@)@."
      UfSymbol.pp_print_uf_symbol uf_symbol
  in

  TransSys.define_and_declare_of_bounds
    ~declare_sub_vars:false
    trans_sys 
    define
    declare
    TransSys.init_base
    TransSys.trans_base;

(* Test path reconstruction

  let vars = 
    TransSys.vars_of_bounds
      trans_sys
      TransSys.init_base
      TransSys.init_base
  in

  let next_of_value t = match Term.type_of_term t |> Type.node_of_type with
    | Type.Bool -> Term.negate t 
    | Type.Int | Type.Real -> Term.mk_succ t |> Simplify.simplify_term []
    | _ -> t
  in

  let model = 
    List.map
      (fun v -> 
         let t1 = Var.type_of_var v |> TermLib.default_of_type in
         let sv = Var.state_var_of_state_var_instance v in
         let t2 = next_of_value t1 in
         let t3 = next_of_value t2 in
         let t4 = next_of_value t3 in
         (sv, [t4; t3; t2; t1]))
      vars
    |> Model.path_of_term_list
  in
                
  Format.printf 
    "%a@."
    (LustrePath.pp_print_path_pt trans_sys lustre_subsystem true) model;


  Format.printf 
    "%a@."
    (LustrePath.pp_print_path_pt trans_sys lustre_subsystem false) model
*)

  (* Test lifintg of terms *)

  let scope_x =  ["X"] in
  let scope_y =  ["Y"] in
  let scope_z =  ["Z"] in

  let trans_sys_x = 
    TransSys.find_subsystem_of_scope trans_sys scope_x 
  in 

  let trans_sys_y = 
    TransSys.find_subsystem_of_scope trans_sys scope_y
  in 

  let trans_sys_z = 
    trans_sys
  in 

  let vars_x = 
    TransSys.vars_of_bounds
      trans_sys_x
      TransSys.init_base
      TransSys.init_base
  in

  let vars_y = 
    TransSys.vars_of_bounds
      trans_sys_y
      TransSys.init_base
      TransSys.init_base
  in

  let vars_z = 
    TransSys.vars_of_bounds
      trans_sys_z
      TransSys.init_base
      TransSys.init_base
  in

  let top_x, below_x = 
    TransSys.instantiate_term_all_levels
      trans_sys
      TransSys.init_base
      scope_x 
      (Term.mk_eq (List.map Term.mk_var vars_x))
  in
  
  let top_y, below_y = 
    TransSys.instantiate_term_all_levels
      trans_sys
      TransSys.init_base
      scope_y 
      (Term.mk_eq (List.map Term.mk_var vars_y))
  in

  let top_z, below_z = 
    TransSys.instantiate_term_all_levels
      trans_sys
      TransSys.init_base
      scope_z 
      (Term.mk_eq (List.map Term.mk_var vars_z))
  in
  
  let pp_print_top ppf (t, l) = 

    let s = 
      TransSys.scope_of_trans_sys t 
      |> string_of_t Scope.pp_print_scope 
    in
    
    Format.fprintf ppf
      "@[<hv %d>%s: @[<hv>%a@]@]"
      (String.length s + 2) s
      (pp_print_list Term.pp_print_term ",@ ") l

  in

  let pp_print_below ppf l = 
    Format.fprintf ppf
      "@{<v>%a@]"
      (pp_print_list pp_print_top "@,") l
  in

  Format.printf
    "@[<v>X: top@,%a@,X: below@,%a@]@."
    pp_print_top top_x
    pp_print_below below_x;

  Format.printf
    "@[<v>Y: top@,%a@,Y: below@,%a@]@."
    pp_print_top top_y
    pp_print_below below_y;

  Format.printf
    "@[<v>Z: top@,%a@,Z: below@,%a@]@."
    pp_print_top top_z
    pp_print_below below_z;

   ()
;;

test ()

*)


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
