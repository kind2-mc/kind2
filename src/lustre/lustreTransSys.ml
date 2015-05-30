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

open Lib

module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module N = LustreNode
module S = LustreSlicing

module A = Analysis
module P = Property

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap


(* Transition system and information needed when calling it *)
type node_def =

  { 

    (* Node the transition system was created from *)
    node : LustreNode.t;

    (* Initial state predicate *)
    init_uf_symbol : UfSymbol.t;

    (* Transition relation predicate *)
    trans_uf_symbol : UfSymbol.t;

    trans_sys : TransSys.t;

    (* Stateful local variables to be instantiated by the caller 

       Local variables of the callees of the node *)
    stateful_vars : StateVar.t list;

    (* Properties to be instantiated by the caller 

       Properties of the callees of the node *)
    lifted_props : P.t list;

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
(* Node calls                                                             *)
(* ********************************************************************** *)

(* Add instance of called node to list of subsystems

   Group instances of the same node together, each has a different
   state variable map and guarding function. *)
let rec add_subsystem' trans_sys state_var_map guard_fun accum = function 

  (* No other instance of this node found: add as a singleton list  *) 
  | [] -> (trans_sys, [(state_var_map, guard_fun)]) :: accum

  (* Check if there is another instance of this node  *)
  | (trans_sys', inst) as h :: tl -> 

    (* Compare transition systems by name *)
    if TransSys.equal_scope trans_sys trans_sys' then 
      
      (* Add node instance to previous instances, append remainder of
         list of subsystems and return *)
      List.rev_append
        ((trans_sys, ((state_var_map, guard_fun) :: inst)) :: accum)
        tl
        
    else

      (* Keep searching for transition system in tail of list *)
      add_subsystem' 
        trans_sys
        state_var_map
        guard_fun
        (h :: accum)
        tl
      
(* Add instance of called node to list of subsystems *)
let add_subsystem trans_sys state_var_map guard_fun subsystems =

  (* Use recursive function with empty accumulator *)
  add_subsystem' trans_sys state_var_map guard_fun [] subsystems


(* Return term and lifted property for node call 

   This factors out node calls with or without an activation
   condition *)
let call_terms_of_node_call
    mk_fresh_state_var 
    { N.call_node_name; 
      N.call_pos;
      N.call_inputs; 
      N.call_oracles; 
      N.call_outputs } 
    node_locals
    node_props
    { init_uf_symbol;
      trans_uf_symbol;
      node = { N.init_flag;
               N.instance;
               N.inputs;
               N.oracles;
               N.outputs;
               N.locals; 
               N.props;
               N.global_contracts;
               N.mode_contracts } as node;
      stateful_vars; 
      lifted_props } =

  (* Initialize map of state variable in callee to instantiated state
     variable in caller *)
  let state_var_map = 

    (* Map actual to formal inputs *)
    D.fold2
      (fun _ state_var inst_state_var state_var_map -> 
         SVM.add state_var inst_state_var state_var_map)
      inputs
      call_inputs
      SVM.empty

    |> 

    (* Map actual to formal outputs *)
    D.fold2
      (fun _ state_var inst_state_var state_var_map -> 
         SVM.add state_var inst_state_var state_var_map)
      outputs
      call_outputs

    |> (fun state_var_map ->

        (* Map actual to formal oracles *)
        List.fold_left2 
          (fun state_var_map state_var inst_state_var -> 
             SVM.add state_var inst_state_var state_var_map)
          state_var_map
          oracles
          call_oracles)

  in

  (* Create fresh state variable for each state variable local
     to the called node and add to the respective data
     structures *)
  let node_locals, call_locals, state_var_map = 

    List.fold_left

      (fun (locals, call_locals, state_var_map) state_var -> 

         (* Create a fresh state variable in the caller *)
         let inst_state_var = 
           mk_fresh_state_var
             ?is_const:(Some (StateVar.is_const state_var))
             ?for_inv_gen:(Some true)
             (StateVar.type_of_state_var state_var)
         in

         (* Add fresh state variable to locals of this node, to actual
            input parameters of node call and to map of state variable
            instances *)
         (inst_state_var :: locals,
          inst_state_var :: call_locals,
          SVM.add state_var inst_state_var state_var_map))

      (* Add to local variables of the node, start with empty list of
         variables instantiated at the call, and extend the state
         variable map *)
      (node_locals, [], state_var_map)

      (* Take the init flag, the instance identifier and all stateful
         variables of the callee *)
      (init_flag :: instance :: stateful_vars)

  in

  (* Instantiate all properties of the called node in this node *)
  let node_props = 
    List.fold_left 

      (fun a (sv, n, src) -> 

         (* Lift name of property *)
         let prop_name =
           lift_prop_name call_node_name call_pos n
         in

         (* Lift state variable of property

            Property is a local variable, thus it has been
            instantiated and is in the map *)
         let prop_term = 
           lift_state_var state_var_map sv
           |> E.cur_term_of_state_var TransSys.trans_base  
         in

         (* Property is instantiated *)
         let prop_source = 
           Property.Instantiated
             ([I.string_of_ident false call_node_name], n)
         in

         (* Property status is unknown *)
         let prop_status = P.PropUnknown in

         (* Create and append property *)
         { P.prop_name;
           P.prop_source;
           P.prop_term;
           P.prop_status } :: a)

      node_props
      props 

  in

  (* Add requirements of node as property if any *)
  let node_props = 

    (* Does the node have mode contracts? *)
    (match mode_contracts with 

      (* No requirement from mode contracts *)
      | [] -> None

      (* Disjunction of requirements from mode contracts *)
      | _ -> 

        Some

          (

            (* Lift name of property *)
            let prop_name = 
              lift_prop_name 
                call_node_name 
                call_pos
                "mode_requirements"
            in

            (* Disjunction of requirements of mode contracts *)
            let prop_term =
              List.map
                (fun { N.contract_req } -> 
                   lift_state_var state_var_map contract_req
                   |> E.cur_term_of_state_var TransSys.trans_base)
                mode_contracts

              |> Term.mk_or

            in

            (* Property is a requirement *)
            let prop_source = 
              Property.ContractCallRequire
                (call_pos, [I.string_of_ident false call_node_name], [])
            in
            
            (* Property status is unknown *)
            let prop_status = P.PropUnknown in

            (* Create property *)
            { P.prop_name;
              P.prop_source;
              P.prop_term;
              P.prop_status })

    )

    (* Add to head of list if not [None] *)
    @::

    (* Iterate over requirements of global contracts *)
    List.mapi
      (fun i { N.contract_req } ->

         (* Lift name of property *)
         let prop_name = 
           lift_prop_name 
             call_node_name 
             call_pos
             (Format.sprintf "global_requirement_%d" i)
         in

         (* Lift state variable of requirement

            Property is a local variable, thus it has been instantiated
            and is in the map *)
         let prop_term = 
           lift_state_var state_var_map contract_req
           |> E.cur_term_of_state_var TransSys.trans_base  
         in

         (* Property is a requirement *)
         let prop_source = 
           Property.ContractCallRequire
             (call_pos, [I.string_of_ident false call_node_name], [])
         in

         (* Property status is unknown *)
         let prop_status = P.PropUnknown in

         (* Create property *)
         { P.prop_name;
           P.prop_source;
           P.prop_term;
           P.prop_status })
      global_contracts

    (* Add to properties of node *)
    @ node_props

  in

(* Return actual parameters of initial state constraint at bound in
   the correct order *)
let init_params_of_bound term_of_state_var =
  List.map 
    term_of_state_var
    ((D.values call_inputs) @ 
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

let contract_guarantees_of_bound term_of_state_var = 
  Term.mk_and

    [

      (* Iterate over all global contracts *)
      List.map 
        (fun { N.contract_enss } -> 

           (* Conjunction of all ensures *)
           Term.mk_and
             (List.map
                (fun sv -> 
                   lift_state_var state_var_map sv
                   |> term_of_state_var)
                contract_enss))

        global_contracts 

      (* Conjunction of ensures of all global contracts *)
      |> Term.mk_and;

      (* Iterate over all mode contracts *)
      List.map 
        (fun { N.contract_req; N.contract_enss } -> 

           (* Mode requirement implies conjuncion of ensures *)
           Term.mk_implies
             [lift_state_var state_var_map contract_req
              |> term_of_state_var;
              Term.mk_and
                (List.map
                   (fun sv -> 
                      lift_state_var state_var_map sv
                      |> term_of_state_var)
                   contract_enss)])

        mode_contracts 

      (* Conjunction of ensures of all mode contracts *)
      |> Term.mk_and

    ]

in

(* Guarantees of contracts at initial state *)
let contract_guarantees_init = 
  contract_guarantees_of_bound
    (E.base_term_of_state_var TransSys.init_base)
in

(* Guarantees of contracts at current state *)
let contract_guarantees_trans = 
  contract_guarantees_of_bound
    (E.cur_term_of_state_var TransSys.trans_base)
in

(* Return information to build constraint for node call with or
   without activation condition *)
state_var_map, 
node_locals, 
node_props, 
call_locals,
init_call_term, 
init_call_term_trans, 
trans_call_term,
contract_guarantees_init,
contract_guarantees_trans
  

(* Add constraints from node calls to initial state constraint and
   transition relation *)
let rec constraints_of_node_calls 
    mk_fresh_state_var
    trans_sys_defs
    node_locals
    node_props 
    subsystems
    init_terms
    trans_terms = 

  function

    (* Definitions for all node calls created, return *)
    | [] -> (subsystems, node_locals, node_props, init_terms, trans_terms)

    (* Node call without an activation condition *)
    | { N.call_node_name; N.call_clock = None } as node_call :: tl -> 


      (* Get generated transition system of callee *)
      let { trans_sys } as node_def =

        try 

          I.Map.find call_node_name trans_sys_defs 

        (* Fail if transition system for node not found *)
        with Not_found -> assert false

      in

      let 

        state_var_map, 
        node_locals, 
        node_props, 
        _, 
        init_term, 
        _, 
        trans_term,
        contract_guarantees_init,
        contract_guarantees_trans =

        (* Create node call *)
        call_terms_of_node_call
          mk_fresh_state_var
          node_call
          node_locals
          node_props
          node_def
      in

      (* Assert guarantees of contract with initial state constraint
         of called node *)
      let init_term = 
        Term.mk_and [contract_guarantees_init; init_term]
      in

      (* Assert guarantees of contract with transition relation of
         called node *)
      let trans_term = 
        Term.mk_and [contract_guarantees_trans; trans_term]
      in

      (* Add node instance to list of subsystems *)
      let subsystems =
        add_subsystem
          trans_sys
          state_var_map

          (* No guarding necessary when instantiating term, because
             this node instance does not have an activation
             condition *)
          (fun t -> t)

          subsystems
      in

      (* Continue with next node calls *)
      constraints_of_node_calls 
        mk_fresh_state_var
        trans_sys_defs
        node_locals
        node_props
        subsystems
        (init_term :: init_terms)
        (trans_term :: trans_terms)
        tl

    (* Node call with activation condition *)
    | { N.call_node_name; 
        N.call_clock = Some clock;
        N.call_inputs;
        N.call_outputs; 
        N.call_defaults } as node_call :: tl -> 

      (* Get generated transition system of callee *)
      let { node = { N.inputs }; trans_sys } as node_def =

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
         propagate_inputs_init, 
         propagate_inputs_trans, 
         interpolate_inputs) =

        D.fold2
          (fun
            formal_idx 
            formal_sv 
            actual_sv
            (shadow_inputs, 
             propagate_inputs_init, 
             propagate_inputs_trans, 
             interpolate_inputs) ->

            (* Skip over constant formal inputs *)
            if StateVar.is_const formal_sv then 

              (D.add formal_idx formal_sv shadow_inputs, 
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

              Format.printf
                "%a is shadow for %a@."
                StateVar.pp_print_state_var shadow_sv
                StateVar.pp_print_state_var formal_sv;

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
               p_i :: propagate_inputs_init, 
               p_t :: propagate_inputs_trans, 
               i :: interpolate_inputs))

          inputs
          call_inputs

          (D.empty, [], [], [])

      in

      let 

        state_var_map, 
        node_locals, 
        node_props, 
        call_locals,
        init_term, 
        init_term_trans, 
        trans_term,
        contract_guarantees_init,
        contract_guarantees_trans =

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

      let clock_trans_pre = 
        E.pre_term_of_state_var TransSys.trans_base clock 
      in

      let has_ticked =
        mk_fresh_state_var
          ?is_const:None
          ?for_inv_gen:(Some false)
          Type.t_bool
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

      let init_term = 

        Term.mk_and 

          [


            (* [has_ticked] is false in the first instant, because
               it becomes true only after the first clock tick. *)
            Term.negate has_ticked_init;

            (* Propagate input values to shadow variables on clock
               tick *)
            Term.mk_implies 
              [clock_init;
               Term.mk_and propagate_inputs_init];

            (* Initial state constraint on clock tick *)
            Term.mk_implies [clock_init; init_term];

            (* Defaults on no clock tick *)
            Term.mk_implies 
              [Term.mk_not clock_init;
               Term.mk_and
                 (D.fold2
                    (fun _ sv { E.expr_init } accum ->
                       Term.mk_eq 
                         [E.base_term_of_state_var TransSys.init_base sv;
                          E.base_term_of_expr TransSys.init_base expr_init] :: 
                       accum)
                    call_outputs
                    call_defaults
                    [])]

          ]

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

      let subsystems =
        add_subsystem
          trans_sys
          state_var_map
          (fun t ->  Term.mk_implies [clock_trans; t])
          subsystems
      in

      constraints_of_node_calls
        mk_fresh_state_var
        trans_sys_defs
        node_locals
        node_props
        subsystems
        (init_term :: init_terms)
        (trans_term :: trans_terms)
        tl


let rec constraints_of_asserts
    init_terms
    trans_terms = 

  function

    (* All assertions consumed, return term for initial state
       constraint and transition relation *)
    | [] -> (init_terms, trans_terms)
            
    (* Assertion with term for initial state and term for transitions *)
    | { E.expr_init; E.expr_step } :: tl ->

       (* Term for assertion in initial state *)
       let init_term =
         E.base_term_of_expr TransSys.init_base expr_init
       in 

       (* Term for assertion in step state *)
       let trans_term =
         E.cur_term_of_expr TransSys.trans_base expr_step
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
      constraints_of_asserts init_terms trans_terms tl
      

(* Add constraints from equations to initial state constraint and
   transition relation *)
let rec constraints_of_equations 
    init
    stateful_vars
    instance
    terms = 

  function 

    (* Constraints for all equations generated *)
    | [] -> terms 

    (* State variable must have an equational constraint *)
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

      in

      (* Add terms of equation *)
      constraints_of_equations 
        init
        stateful_vars
        instance
        (def :: terms)
        tl


    (* Can define state variable with a let binding *)
    | (state_var, [], { E.expr_init; E.expr_step }) :: tl ->

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
             [(E.cur_var_of_state_var TransSys.trans_base state_var, 
               E.cur_term_of_expr TransSys.trans_base expr_step);

              (* Binding for the variable at the previous instant *)
              (E.pre_var_of_state_var TransSys.trans_base state_var, 
               E.pre_term_of_expr TransSys.trans_base expr_step)])

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

      (* Return the i-th index variable *)
      let index_var_of_int i = 
        E.mk_index_var i
        |> E.state_var_of_expr
        |> Var.mk_const_state_var
      in

      (* Add quantifier or let binding for indexes of variable *)
      let add_bounds = function 

        (* Fixed index [e] *)
        | N.Fixed e -> 

          (* let bind index variable to value [e] *)
          fun (a, i) ->
            (Term.mk_let 
               [index_var_of_int i,
                (e : E.expr :> Term.t)]
               a,
             pred i)

        (* Variable index of size [e] *)
        | N.Bound e -> 
          fun (a, i) -> 

            (* Index variable *)
            let v = index_var_of_int i in

            (* Qunatify over index variable between 0 and [e] *)
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
                  succ i)
               ([], 0)
               bounds 
             |> fst))
      in

      (* Assign value to array position *)
      let eq = 

        Term.mk_eq 

          (uf_term::

           if init then 
             
             (* Expression at base instant *)
             [E.base_term_of_expr TransSys.init_base expr_init]
             
           else
             
             (* Expression at current instant *)
             [E.cur_term_of_expr TransSys.trans_base expr_step])

      in

      (* Wrap equation in let binding and quantifiers for indexes *)
      let def, _ = 
        List.fold_right
          add_bounds
          bounds
          (eq, List.length bounds)
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
    trans_sys_defs
    output_input_dep
    nodes =

  function

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

        (* Index for fresh state variables *)
        let index_ref = ref 0 in

        (* Create a fresh state variable *)
        let mk_fresh_state_var
            ?is_const
            ?for_inv_gen
            state_var_type =

          (* Increment counter for fresh state variables *)
          incr index_ref; 

          (* Create state variable *)
          StateVar.mk_state_var
            ~is_input:false
            ?is_const:is_const
            ?for_inv_gen:for_inv_gen
            ((I.push_index I.inst_ident !index_ref) 
             |> I.string_of_ident false)
            [(I.string_of_ident false) node_name]
            state_var_type

        in

        (* Subnodes for which we have not created a transition
           system *)
        let tl' = 

          List.fold_left 
            (fun accum { N.call_node_name } -> 
               if 

                 (* Transition system for node created? *)
                 I.Map.mem call_node_name trans_sys_defs || 

                 (* Node already pushed to stack? *)
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

        (* Are there subnodes for which a transition system needs to be
           created first? *)
        match tl' with

          (* Some transitions systems of called nodes have not been
             created *)
          | _ :: _ -> 

            (* We could check here that the call graph does not have
               cycles, although that should not be allowed in
               the Lustre currently accepted. *)

            (* Recurse to create transition system for called nodes,
               then return to this node *)
            trans_sys_of_node'
              top_name
              trans_sys_defs
              output_input_dep
              nodes
              (tl' @ node_name :: tl)

          (* All transitions systems of called nodes have been
             created *)
          | [] ->

            (* Assumptions from contracts *)
            let contract_assumptions_of_bound term_of_state_var = 

              (* Disjunction of assumptions from mode contracts: the
                 requirements of at least one mode are always true *)
              Term.mk_or
                (List.map
                   (fun { N.contract_req } -> 
                      term_of_state_var contract_req)
                   mode_contracts) ::
              
              (* Assumptions from global contracts: requirements are
                 always true *)
              List.map
                (fun { N.contract_req } -> 
                   term_of_state_var contract_req)
                global_contracts

            in

            (* Initial state constraint *)
            let init_terms = 

              (* Init flag is true on first tick of node *)
              E.base_term_of_state_var TransSys.init_base init_flag ::

              (* Only if node is top node *)
              if I.equal node_name top_name then 
                
                (* Assumptions from contracts *)
                contract_assumptions_of_bound
                  (E.base_term_of_state_var TransSys.init_base)

              else 

                (* Don't add assumption in nodes below the top *)
                []

            in

            (* Transition relation *)
            let trans_terms = 


              (* Init flag becomes and stays false at the second
                 tick *)
              (E.cur_term_of_state_var TransSys.trans_base init_flag
               |> Term.negate) ::

              (* Only if node is top node *)
              if I.equal node_name top_name then 
                
                (* Assumptions from contracts *)
                contract_assumptions_of_bound
                  (E.cur_term_of_state_var TransSys.trans_base)

              else

                (* Don't add assumption in nodes below the top *)
                []
                  
            in

            (* Instantiated state variables and constraints from node
               calls *)
            let 

              subsystems, 
              lifted_locals, 
              lifted_props, 
              init_terms, 
              trans_terms = 

              constraints_of_node_calls
                mk_fresh_state_var
                trans_sys_defs
                []  (* No lifted locals *)
                []  (* No lifted properties *)
                []  (* No subsystems *)
                init_terms
                trans_terms
                calls 
            in

            (* Stateful state variables in node, including state
               variables for node instance, first tick flag, and state
               variables capturing outputs of node calls *)
            let stateful_vars = 
              init_flag ::
              (N.stateful_vars_of_node node 
               |> SVS.elements)
              @ lifted_locals
            in

            (* State variables in the signature of the predicate in
               the correct order *)
            let signature_state_vars = 
              init_flag ::
              (D.values inputs) @ 
              oracles @
              (D.values outputs) 
            in

            (* Append local stateful variables *)
            let signature_state_vars = 
              signature_state_vars @
              List.filter
                (fun sv -> 
                   not
                     (List.exists
                        (fun sv' -> StateVar.equal_state_vars sv sv')
                        signature_state_vars))
                stateful_vars
            in

            (* Constraints from assertions

               Must add assertions and contract first so that local variables
               can be let bound in constraints_of_equations *)
            let init_terms, trans_terms = 
              constraints_of_asserts  
                init_terms
                trans_terms
                asserts
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

            (* Arrays become global state variables and are removed
               from signature *)
            let global_state_vars, signature_state_vars = 
              List.partition
                (fun sv -> StateVar.type_of_state_var sv |> Type.is_array)
                signature_state_vars 
            in

            (* Need to add an instance variable when we have arrays *)
            let signature_state_vars, instance_state_var =
              if global_state_vars = [] then 
                signature_state_vars, None 
              else 
                instance :: signature_state_vars, Some instance 
            in

            (* All property annotations and lifted properties from
               subnodes *)
            let props_annot = 

              (* Iterate over each property annotation and lifted
                 property *)
              List.map
                (fun (state_var, prop_name, prop_source) -> 

                   (* Property is just the state variable *)
                   let prop_term =
                     E.cur_term_of_state_var
                       TransSys.trans_base
                       state_var
                   in

                   (* Property status is unknown *)
                   let prop_status = P.PropUnknown in

                   { P.prop_name; 
                     P.prop_source; 
                     P.prop_term;
                     P.prop_status })

                props

            in

            (* Properties from global contracts *)
            let props_global_contracts = 

              (* Iterate over each contract *)
              List.fold_left
                (fun accum { N.contract_name; N.contract_pos; N.contract_enss } ->

                   (* Iterate over each ensures of the contract *)
                   List.mapi 
                     (fun i state_var -> 

                        (* Index name of contract with count of
                           ensures clause *)
                        let prop_name  = 
                          Format.asprintf
                            "%a_%d" 
                            (I.pp_print_ident false) contract_name
                            i
                        in

                        (* Property is from a global contract *)
                        let prop_source = 
                          P.ContractGlobalEnsures
                            (contract_pos, [I.string_of_ident false contract_name])
                        in

                        (* Property is just the state variable *)
                        let prop_term = 
                          E.cur_term_of_state_var
                            TransSys.trans_base
                            state_var
                        in

                        (* Property status is unknown *)
                        let prop_status = P.PropUnknown in

                        { P.prop_name; 
                          P.prop_source;
                          P.prop_term; 
                          P.prop_status })
                     contract_enss

                   @ accum)
                []
                global_contracts
            in

            (* Properties from mode contracts *)
            let props_mode_contracts = 

              (* Iterate over each contract *)
              List.fold_left
                (fun 
                  accum
                  { N.contract_name; 
                    N.contract_pos; 
                    N.contract_req; 
                    N.contract_enss } ->

                  (* Iterate over each ensures of the contract *)
                  List.mapi 
                    (fun i state_var -> 

                       (* Index name of contract with count of
                          ensures clause *)
                       let prop_name =
                         Format.asprintf "%a_%d" 
                           (I.pp_print_ident false) contract_name 
                           i
                       in

                       (* Property is from a mode contract *)
                       let prop_source = 
                         P.ContractModeEnsures
                           (contract_pos, [I.string_of_ident false contract_name])
                       in

                       (* Property is implication between conjunction
                          of requires and state variable of ensures *)
                       let prop_term = 
                         Term.mk_implies
                           [E.cur_term_of_state_var
                              TransSys.trans_base 
                              contract_req;
                            E.cur_term_of_state_var
                              TransSys.trans_base
                              state_var]
                       in

                       (* Property status is unknown *)
                       let prop_status = P.PropUnknown in

                       { P.prop_name;
                         P.prop_source;
                         P.prop_term;
                         P.prop_status })
                    contract_enss

                  @ accum)
                
                []
                mode_contracts
            in

            (* Create transition system *)
            let trans_sys, _ = 
              TransSys.mk_trans_sys 
                [I.string_of_ident false node_name]
                instance_state_var
                global_state_vars
                (signature_state_vars @ global_state_vars)
                (Term.mk_and init_terms)
                (Term.mk_and trans_terms)
                subsystems
                (props_annot @ 
                 lifted_props @ 
                 props_global_contracts @ 
                 props_mode_contracts)
                [] (* One-state invariants *)
                [] (* Two-state invariants *)
            in                

            Format.printf 
              "%a@."
              TransSys.pp_print_trans_sys trans_sys;

            (* Create instances of state variables in signature *)
            let init_signature_vars = 
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
                   "%s_%a"
                   I.init_uf_string
                   (LustreIdent.pp_print_ident false) node_name)
                (List.map Var.type_of_var init_signature_vars)
                Type.t_bool
            in

            (* Create instances of state variables in signature *)
            let trans_signature_vars = 

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
                   "%s_%a"
                   I.trans_uf_string
                   (LustreIdent.pp_print_ident false) node_name)
                (List.map Var.type_of_var trans_signature_vars)
                Type.t_bool
            in

            trans_sys_of_node'
              (I.Map.add 
                 node_name
                 { node;
                   trans_sys;
                   init_uf_symbol;
                   trans_uf_symbol;
                   stateful_vars;
                   lifted_props }
                 trans_sys_defs)
              ((node_name, 
                (node_output_input_dep_init, node_output_input_dep_trans))
               :: output_input_dep)
              nodes
              tl
          

let trans_sys_of_nodes subsystem { A.top; A.abstraction_map; A.assumptions } = 
  
  (* Make sure top level system is not abstract

     Contracts would be trivially satisfied otherwise *)
  match List.find (fun (s, _) -> Scope.equal top s) abstraction_map with
    | (_, true) -> 
      raise
        (Invalid_argument
           "trans_sys_of_nodes: Top-level system must not be abstract")
    | (_, false) -> ()
    | exception Not_found -> ();

  (* TODO: Find top subsystem by name *)
  let subsystem' = subsystem in

  let { SubSystem.source = { N.name = top_name } as node } as subsystem = 
    LustreSlicing.slice_to_abstraction abstraction_map subsystem 
  in

  let nodes = N.nodes_of_subsystem subsystem in 

  Format.printf
    "@[<v>%a@]@."
    (pp_print_list (N.pp_print_node false) "@,") (List.rev nodes);

  let { trans_sys } =   

    try 

      (* Create a transition system for each node *)
      trans_sys_of_node' top_name I.Map.empty [] nodes [top_name]

      (* Return the transition system of the top node *)
      |> I.Map.find top_name

    (* Transition system must have been created *)
    with Not_found -> assert false

  in

  Format.printf "%a@." TransSys.pp_print_trans_sys trans_sys;

  trans_sys



let test () = 

  let  { SubSystem.source = { N.name = top_name } as node } as lustre_subsystem = 
    LustreInput.of_file Sys.argv.(1) 
  in

  let analysis = 
    { A.top = [I.string_of_ident false top_name]; 
      A.abstraction_map = []; 
      A.assumptions = [] }
  in

  trans_sys_of_nodes lustre_subsystem analysis



;;

test ()





(*

let trans_sys_of_nodes nodes { A.top; A.abstraction_map; A.assumptions } = 

  (* Find top node in LustreNode.t SubSystem.t, then slice to
     abstraction map *)






        (* Is node abstract? *)
        let is_abstr = 

          try 

            (* Find abstraction flag for node in map *)
            List.assoc node_name abst_impl_map

          (* Default to implementation *)
          with Not_found -> false

        in

        (* Node to create a transition system for, sliced to
           abstraction or to implementation *)
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
              N.contracts } as node = 

          try 

            (* Find node in abstract or implementation nodes by name *)
            N.node_of_name
              node_name
              (if is_abstr then nodes_abst else node_impl)

          (* Fall back to implementation if no abstraction for node
             exists *)
          with Not_found -> 

            try 

              (* Find node in implementation nodes by name *)
              N.node_of_name node_name node_impl

            with Not_found -> 

              (* Must have at least implementation of node *)
              raise
                (Invalid_argument
                   (Format.asprintf 
                      "trans_sys_of_node: node %a not found"
                      (I.pp_print_ident false) node_name))

        in


  trans_sys_of_node' [] [] [] [] nodes [] [List.hd nodes |> fun { N.name } -> name]

*)


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
