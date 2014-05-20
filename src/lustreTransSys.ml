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
module E = LustreExpr
module N = LustreNode

module VS = Var.VarSet
module SVS = StateVar.StateVarSet

(*
(* Use configured SMT solver *)
module MySolver = SMTSolver.Make (Config.SMTSolver)

(* High-level methods for PDR solver *)
module S = SolverMethods.Make (MySolver)
*)


let base_offset = Numeral.zero

let cur_offset = Numeral.one

let name_of_local_var i n = 
  Format.sprintf "__local_%d_%s" i n

let init_uf_symbol_name_of_node n = 
  Format.asprintf
    "%s_%a"
    I.init_uf_string
    (LustreIdent.pp_print_ident false) n
  
let trans_uf_symbol_name_of_node n = 
  Format.asprintf
    "%s_%a"
    I.trans_uf_string
    (LustreIdent.pp_print_ident false) n

(* Set of state variables of list *)
let svs_of_list list = 
  List.fold_left (fun a e -> SVS.add e a) SVS.empty list

(* Add a list of state variables to a set *)
let add_to_svs set list = 
  List.fold_left (fun a e -> SVS.add e a) set list 
  
(* Create a copy of the state variable at the top level *)
let state_var_of_top_scope is_input ?is_const ?is_clock top_node state_var =

(* 

  let state_var' = 
    StateVar.mk_state_var
      ?is_input
      ?is_const:(Some (StateVar.is_const state_var))
      (StateVar.name_of_state_var state_var) 
      ("__top" :: (StateVar.scope_of_state_var state_var))
      (StateVar.type_of_state_var state_var)
  in
*)

  let state_var' = 
    E.mk_state_var_of_ident 
      is_input
      (StateVar.is_const state_var)
      I.top_scope_index
      (fst (E.ident_of_state_var state_var))
      (StateVar.type_of_state_var state_var)
  in

  (* State variable is instance of local variable *)
  E.set_state_var_source
    state_var'
    (E.Instance (LustreAst.dummy_pos, top_node, state_var));

  state_var'
  
  
type node_def =

  { 

    (* Input variables *)
    inputs : StateVar.t list;

    (* Output variables *)
    outputs : StateVar.t list;

    (* Stateful local variables *)
    locals : StateVar.t list;

    (* Name of predicate for initial state constraint *)
    init_uf_symbol : UfSymbol.t;

    (* Definition of predicate for initial state constraint *)
    init_term : Term.t; 

    (* Name of predicate for transition relation *)
    trans_uf_symbol : UfSymbol.t;

    (* Definition of predicate for transition relation *)
    trans_term : Term.t;

  }


(* Fold list of equations to definition *)
let rec definitions_of_equations vars init trans = function 

  (* All equations consumed, return term for initial state constraint
     and transition relation *)
  | [] -> (init, trans)

  (* Take first equation *)
  | (state_var, ({ E.expr_init; E.expr_step } as expr)) :: tl -> 

    (* Modified definitions *)
    let init', trans' = 

      if 

        (* Variable must to have a definition? *)
        SVS.mem state_var vars

      then 

        (

          (* Equation for initial constraint on variable *)
          let init_def = 
            Term.mk_eq 
              [E.base_term_of_state_var base_offset state_var; 
               E.base_term_of_expr base_offset expr_init] 
          in
         
          (* Equation for transition relation on variable *)
          let trans_def = 
            Term.mk_eq 
              [E.cur_term_of_state_var cur_offset state_var; 
               E.cur_term_of_expr cur_offset expr_step] 
          in
         
          (* Add term of equation and continue *)
          (init_def :: init, trans_def :: trans))
        
      else
        
        (

          (* Define variable with a let *)
          let init' =
            Term.mk_let 
              [(E.base_var_of_state_var base_offset state_var, 
                E.base_term_of_expr base_offset expr_init)] 
              (Term.mk_and init) 
          in

          (* Define variable with a let *)
          let trans' = 
            Term.mk_let
              [(E.cur_var_of_state_var cur_offset state_var, 
                E.cur_term_of_expr cur_offset expr_step)] 
              (Term.mk_and trans)
          in
          
          (* Start with singleton lists *)
          ([init'], [trans']))
        
    in
(*
    let t_tl, t_ne, t_bl, t_sb, t_mb, t_bb = Term.stats () in

    Format.printf 
      "@[<v>%s:@,\
       table length: %d@,\
       number of entries: %d@,\
       sum of bucket lengths: %d@,\
       smallest bucket length: %d@,\
       median bucket length: %d@,\
       biggest bucket length %d@]@." 
      "Term"
      t_tl 
      t_ne 
      t_bl
      t_sb
      t_mb
      t_bb;
*)
  
    (* Continue with next equations *)
    definitions_of_equations vars init' trans' tl


(* Fold list of node calls to definition *)
let rec definitions_of_node_calls 
    scope
    mk_ticked_state_var
    node_defs
    local_vars
    init trans = 

  function

    (* All node calls consumed, return term for initial state
       constraint and transition relation *)
    | [] -> (local_vars, init, trans)

    (* Node call with or without activation condition *)
    | { N.call_returns = output_vars;
        N.call_clock = act_cond;
        N.call_node_name = node_name;
        N.call_inputs = input_exprs;
        N.call_defaults = init_exprs;
        N.call_pos = pos } :: tl -> 

      (* Create a new state variable for abstractions *)
      let mk_new_state_var  = 
        let r = ref Numeral.(- one) in
        fun state_var_type ->
          Numeral.incr r; 
          E.mk_state_var_of_ident
            false
            false
            scope
            (I.push_int_index !r I.abs_ident)
            state_var_type
      in

      (* Signature of called node *)
      let { init_uf_symbol; trans_uf_symbol; inputs; outputs; locals } = 

        (* Find definition of called node by name *)
        try 
          List.assoc node_name node_defs 
        with Not_found -> assert false
          
      in

      (* Initial state value of activation condition *)
      let act_cond_init = 
        E.base_term_of_expr base_offset act_cond.E.expr_init 
      in 

      (* Step state value of activation condition *)
      let act_cond_trans = 
        E.cur_term_of_expr cur_offset act_cond.E.expr_step 
      in 

      (* Previous step state value of activation condition *)
      let act_cond_trans_pre = 
        E.pre_term_of_expr cur_offset act_cond.E.expr_step 
      in

      (* Initial state values of default values *)
      let init_terms_init = 
        List.map 
          (function { E.expr_init } -> 
            E.base_term_of_expr base_offset expr_init) 
          init_exprs
      in

      (* Input for node call in initial state *)
      let input_terms_init = 
        List.map
          (function { E.expr_init } -> 
            E.base_term_of_expr base_offset expr_init) 
          input_exprs
      in

      (* Input for node call in step state *)
      let input_terms_trans = 
        List.map
          (function { E.expr_step } -> 
            E.cur_term_of_expr cur_offset expr_step) 
          input_exprs
      in

      (* Input for node call in step state *)
      let input_terms_trans_pre = 
        List.map
          (function { E.expr_step } -> 
            E.pre_term_of_expr cur_offset expr_step) 
          input_exprs
      in

      (* Variables capturing the output of the node in the initial
         state *)
      let output_terms_init = 
        List.map (E.base_term_of_state_var base_offset) output_vars
      in

      (* Variables capturing the output of the node in the current
         state *)
      let output_terms_trans = 
        List.map (E.cur_term_of_state_var cur_offset) output_vars
      in

      (* Variables capturing the output of the node in the previous
         state *)
      let output_terms_trans_pre = 
        List.map (E.pre_term_of_state_var cur_offset) output_vars
      in

      (* Variables local to the node for this instance *)
      let local_vars', call_local_vars = 

        (* Need to preserve order of variables *)
        List.fold_right
          (fun state_var (local_vars, call_local_vars) -> 

             (* Type of state variable *)
             let var_type = StateVar.type_of_state_var state_var in

             (* Name of state variable *)
             let var_name = StateVar.string_of_state_var state_var in

             (* New state variable for node call *)
             let local_state_var = 
(*
               StateVar.mk_state_var
                 (name_of_local_var (List.length local_vars) var_name)
                 scope
                 var_type
*)

               mk_new_state_var var_type
             in
             
             (* State variable is instance of local variable *)
             E.set_state_var_source
               local_state_var
               (E.Instance (pos, node_name, state_var));

             (local_state_var :: local_vars, 
              local_state_var :: call_local_vars))
          locals
          (output_vars @ local_vars, [])

      in

      (* Variables local to node call for current state *)
      let call_local_vars_init = 
        List.map (E.base_term_of_state_var base_offset) call_local_vars
      in

      (* Variables local to node call for previous state *)
      let call_local_vars_trans = 
        List.map (E.cur_term_of_state_var cur_offset) call_local_vars
      in

      (* Variables local to node call for previous state *)
      let call_local_vars_trans_pre = 
        List.map (E.pre_term_of_state_var cur_offset) call_local_vars
      in

      (* Arguments for node call in initial state *)
      let init_call_args = 

        (* Current state input variables *)
        input_terms_init @ 

        (* Current state output variables *)
        output_terms_init @ 

        (* Current state local variables *)
        call_local_vars_init

      in

      (* Arguments for node call in transition relation *)
      let trans_call_args = 

        (* Current state input variables *)
        input_terms_trans @ 

        (* Current state output variables *)
        output_terms_trans @ 

        (* Current state local variables *)
        call_local_vars_trans @

        (* Previous state input variables *)
        input_terms_trans_pre @

        (* Previous state output variables *)
        output_terms_trans_pre @

        (* Previous state local variables *)
        call_local_vars_trans_pre  

      in

      (* Constraint for node call in initial state *)
      let init_call = Term.mk_uf init_uf_symbol init_call_args in

      (* Constraint for node call in transition relation *)
      let trans_call = Term.mk_uf trans_uf_symbol trans_call_args in

      (* Constraint for node call in initial state and transtion
         relation with activation condition *)
      let local_vars'', init_call_act_cond, trans_call_act_cond = 

        if 

          (* Activation condition of node is constant true *)
          E.equal_expr act_cond E.t_true

        then 

          (* Return predicates unguarded *)
          local_vars', init_call, trans_call 

        else
(*
          let local_vars'', output_default_vars = 
            List.fold_right
              (fun state_var (local_vars, output_default_vars) -> 

                 (* Type of state variable *)
                 let var_type = StateVar.type_of_state_var state_var in

                 (* Name of state variable *)
                 let var_name = StateVar.string_of_state_var state_var in

                 (* New state variable for node call *)
                 let local_state_var = 
                   StateVar.mk_state_var
                     (name_of_local_var (List.length local_vars) var_name)
                     scope
                     var_type

                 in

                 (* State variable is instance of local variable *)
                 E.set_state_var_source
                   local_state_var
                   (E.Instance (pos, node_name, state_var));

                 (local_state_var :: local_vars, 
                  local_state_var :: output_default_vars))
              output_vars 
              (local_vars', [])
          in

          (* Arguments for node call in initial state *)
          let init_call_args = 

            (* Current state input variables *)
            input_terms_init @ 

            (* Current state output variables *)
            (List.map 
               (E.base_term_of_state_var base_offset) 
               output_default_vars) @ 

            (* Current state local variables *)
            call_local_vars_init

          in

          (* Constraint for node call in initial state *)
          let init_call = Term.mk_uf init_uf_symbol init_call_args in

          (* Arguments for node call in transition relation *)
          let trans_call_args = 

            (* Current state input variables *)
            input_terms_trans @ 

            (* Current state output variables *)
            (List.map 
               (E.cur_term_of_state_var cur_offset)
               output_default_vars) @ 

            (* Current state local variables *)
            call_local_vars_init @

            (* Previous state input variables *)
            input_terms_trans_pre @

            (* Previous state output variables *)
            (List.map 
               (E.pre_term_of_state_var cur_offset)
               output_default_vars) @ 

            (* Previous state local variables *)
            call_local_vars_trans_pre  

          in

          (* Constraint for node call in transition relation *)
          let trans_call = Term.mk_uf trans_uf_symbol trans_call_args in

          (* Local variables extended by output variables for condact *)
          (local_vars'',

           Term.mk_and

             (* Initial state constraint *)
             [init_call;

              (* Initial state constraint with true activations
                  condition *)
              Term.mk_implies 
                [E.base_term_of_expr base_offset act_cond_init; 
                 Term.mk_and
                   (List.fold_left2 
                      (fun accum v1 v2 ->
                         Term.mk_eq 
                           [E.base_term_of_state_var base_offset v1; 
                            E.base_term_of_state_var base_offset v2] :: 
                         accum)
                      []
                      output_vars
                      output_default_vars)];

              (* Initial state constraint with false activation
                  condition *)
              Term.mk_implies 
                [Term.mk_not (E.base_term_of_expr base_offset act_cond_init);
                 Term.mk_and
                   (List.fold_left2 
                      (fun accum state_var { E.expr_init } ->
                         Term.mk_eq 
                           [E.base_term_of_state_var base_offset state_var; 
                            E.base_term_of_expr base_offset expr_init] :: 
                         accum)
                      []
                      output_vars
                      init_exprs)]

             ],

           (* Transition relation *)
           Term.mk_and

             [

               (* Transition relation with true activation condition *)
               Term.mk_implies
                 [E.cur_term_of_expr cur_offset act_cond_trans; 
                  Term.mk_and 
                    (List.fold_left2
                       (fun accum sv1 sv2 ->
                          Term.mk_eq 
                            [E.cur_term_of_state_var cur_offset sv1; 
                             E.cur_term_of_state_var cur_offset sv2] :: 
                          accum)
                       [trans_call]
                       output_vars
                       output_default_vars)];
                  
               (* Transition relation with false activation condition *)
               Term.mk_implies 
                 [Term.mk_not (E.cur_term_of_expr cur_offset act_cond_trans);
                  Term.mk_and 
                    (List.fold_left
                       (fun accum state_var ->
                          Term.mk_eq 
                            [E.cur_term_of_state_var cur_offset state_var; 
                             E.pre_term_of_state_var cur_offset state_var] :: 
                          accum)
                       []
                       (output_vars @ output_default_vars @ call_local_vars))];

             ]
*)

          (* Arguments for node call in transition relation *)
          let init_call_trans_args = 
            
            (* Current state input variables *)
            input_terms_trans @ 
            
            (* Current state output variables *)
            output_terms_trans @ 
            
            (* Current state local variables *)
            call_local_vars_trans 

          in

          (* Constraint for node call in initial state *)
          let init_call_trans = 
            Term.mk_uf init_uf_symbol init_call_trans_args 
          in

          (* New state variable for node call *)
          let ticked_state_var = mk_ticked_state_var () in
          
          (* State variable is instance of local variable *)
          E.set_state_var_source
            ticked_state_var
            E.Abstract;

          let ticked_init =
            E.base_term_of_state_var base_offset ticked_state_var 
          in

          let ticked_trans =
            E.cur_term_of_state_var cur_offset ticked_state_var 
          in

          let ticked_trans_pre =
            E.pre_term_of_state_var cur_offset ticked_state_var 
          in

          (* Local variables extended by state variable indicating if
             node has ticked once *)
          (ticked_state_var :: local_vars',

           Term.mk_and

             (* Initial state constraint *)
             [

               (* Equation for ticked state variable *)
               Term.mk_eq [ticked_init; act_cond_init];

               (* Initial state constraint with true activations
                  condition *)
               Term.mk_implies [act_cond_init; init_call];
               
               (* Initial state constraint with false activation
                  condition *)
               Term.mk_implies 
                 [Term.mk_not act_cond_init;
                  Term.mk_and
                    (List.fold_left2 
                       (fun accum state_var { E.expr_init } ->
                          Term.mk_eq 
                            [E.base_term_of_state_var base_offset state_var; 
                             E.base_term_of_expr base_offset expr_init] :: 
                          accum)
                       []
                       output_vars
                       init_exprs)]
                 
             ],

           (* Transition relation *)
           Term.mk_and

             [

               Term.mk_eq 
                 [ticked_trans;
                  Term.mk_or [act_cond_trans; act_cond_trans_pre]];

               (* Transition relation with true activation condition *)
               Term.mk_implies
                 [Term.mk_and 
                    [act_cond_trans; Term.mk_not ticked_trans_pre];
                  init_call_trans];

               (* Transition relation with true activation condition *)
               Term.mk_implies
                 [Term.mk_and 
                    [act_cond_trans; ticked_trans_pre];
                  trans_call];

               (* Transition relation with false activation condition *)
               Term.mk_implies 
                 [Term.mk_not act_cond_trans;
                  Term.mk_and 
                    (List.fold_left
                       (fun accum state_var ->
                          Term.mk_eq 
                            [E.cur_term_of_state_var cur_offset state_var; 
                             E.pre_term_of_state_var cur_offset state_var] :: 
                          accum)
                       []
                       (output_vars @ call_local_vars))];

             ]

          )

      in

      (* Continue with next node call *)
      definitions_of_node_calls 
        scope
        mk_ticked_state_var
        node_defs
        local_vars''
        (init_call_act_cond :: init)
        (trans_call_act_cond :: trans) 
        tl


let definitions_of_asserts init trans = 

  function

    (* All node calls consumed, return term for initial state
       constraint and transition relation *)
    | [] -> (init, trans)

    (* Assertion with term for initial state and term for transitions *)
    | { E.expr_init; E.expr_step } :: tl ->

      let term_init = E.base_term_of_expr base_offset expr_init in 
      let term_trans = E.cur_term_of_expr cur_offset expr_step in 

      (* Add constraint unless it is true *)
      ((if term_init == Term.t_true then init else term_init :: init), 
       (if term_trans == Term.t_true then trans else term_trans :: trans))
      
(*
let definitions_of_contract init trans requires ensures = 

  (* Split expresssion into terms for intial state constraint and
         transition relation *)
  let ensures_init, ensures_trans = E.split_expr_list ensures in

  (* Split expresssion into terms for intial state constraint and
     transition relation *)
  let requires_init, requires_trans = E.split_expr_list requires in 

  match requires, ensures with 

    (* No contract *)
    | [], [] -> init, trans

    (* No preconditions *)
    | [], _ -> 

      (ensures_init @ init, ensures_trans @ trans)

    (* No postconditions *)
    | _, [] -> 

      (requires_init @ init, requires_trans @ trans)


    (* Pre- and postconditions *)
    | _, _ -> 

      (Term.mk_implies 
         [Term.mk_and requires_init; Term.mk_and ensures_init] :: init,
       Term.mk_implies 
         [Term.mk_and requires_trans; Term.mk_and ensures_trans] :: trans) 
*)



let rec trans_sys_of_nodes'
    main_node 
    node_defs 
    fun_defs = function 

  (* All nodes converted, now create the top-level formulas *)
  | [] -> 

    (match node_defs, fun_defs with 

      (* Take the head of the list as top node *)
      | (_, { inputs; outputs; locals }) :: _, 
        (init_uf_symbol, (init_vars, _)) :: 
        (trans_uf_symbol, (trans_vars, _)) :: _ -> 

        (* Create copies of the state variables of the top node,
           flagging input variables *)
        let state_vars_top = 
          List.map (state_var_of_top_scope true main_node) inputs @
          List.map (state_var_of_top_scope false main_node) (outputs @ locals)
        in

        (

          (* Definitions of predicates *)
          List.rev fun_defs, 

          (* State variables *)
          state_vars_top, 

          (* Initial state constraint *)
          Term.mk_uf 
            init_uf_symbol
            (List.map (E.base_term_of_state_var base_offset) state_vars_top),

          (* Transition relation *)
          Term.mk_uf 
            trans_uf_symbol
            ((List.map (E.cur_term_of_state_var cur_offset) state_vars_top) @
             (List.map (E.pre_term_of_state_var cur_offset) state_vars_top))

        )

      (* List of nodes must not be empty *)
      | _ -> raise (Invalid_argument "trans_sys_of_nodes")

    )


  | ({ N.name = node_name;
       N.inputs = node_inputs;
       N.oracles = node_oracles;
       N.outputs = node_outputs; 
       N.locals = node_locals; 
       N.equations = node_equations; 
       N.calls = node_calls; 
       N.asserts = node_asserts; 
       N.props = node_props; 
       N.requires = node_requires; 
       N.ensures = node_ensures } as node) :: tl ->


    debug lustreTransSys
        "@[<v>trans_sys_of_node:@,@[<hv 1>%a@]@]@."
        (N.pp_print_node false) node
    in

    (* Create scope from node name *)
    let scope = 
      LustreIdent.index_of_ident node_name
    in

    (* Create a new state variable for abstractions *)
    let mk_ticked_state_var = 
      let r = ref Numeral.(- one) in
      fun () ->
        Numeral.incr r; 
        E.mk_state_var_of_ident
          false
          false
          (LustreIdent.index_of_ident node_name)
          (I.push_int_index !r I.ticked_ident)
          Type.t_bool
    in

    (* Input variables *)
    let inputs = List.map fst node_inputs in

    (* Oracle input variables *)
    let oracles = node_oracles in

    (* Output variables *)
    let outputs = List.map fst node_outputs in

    (* Variables in properties that are not outputs *)
    let props_locals_set = 
      List.fold_left 
        (fun accum state_var -> 
           if 
             List.exists 
               (StateVar.equal_state_vars state_var)
               outputs 
           then 
             accum 
           else 
             SVS.add state_var accum)
        SVS.empty
        node_props
    in

    (* Add constraints from node calls *)
    let call_locals, init_defs_calls, trans_defs_calls = 
      definitions_of_node_calls 
        scope
        mk_ticked_state_var
        node_defs
        []
        []
        []
        node_calls
    in

    (* Variables capturing outputs of node calls are new local
       variables unless they are inputs or outputs *)
    let call_locals_set = 
      List.fold_left 
        (fun accum sv  -> 
           if 
             (List.exists
                (StateVar.equal_state_vars sv) 
                outputs)
             || (List.exists 
                   (StateVar.equal_state_vars sv) 
                   inputs)
           then 
             accum 
           else 
             SVS.add sv accum)
        SVS.empty
        call_locals
    in

    (* Variables occurring under a pre are new local variables unless
       they are inputs or outputs *)
    let node_locals_set = 
      SVS.filter 
        (fun sv -> 
           not
             ((List.exists 
                 (StateVar.equal_state_vars sv)
                 inputs)
              || (List.exists 
                    (StateVar.equal_state_vars sv)
                    outputs)
              || (List.exists
                    (StateVar.equal_state_vars sv) 
                    oracles)))
        (N.stateful_vars_of_node node)
    in

    debug lustreTransSys
        "@[<hv>Node local vars in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        (SVS.elements node_locals_set)
    in
        
    (* Local variables are those occurring under a pre, properties or
       variables capturing outputs of node calls *)
    let locals_set = 
      List.fold_left 
        SVS.union
        SVS.empty
        [node_locals_set; call_locals_set; props_locals_set]
    in

    (* Convert set to a list *)
    let locals = SVS.elements locals_set in

    debug lustreTransSys
        "@[<hv>Local vars in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        locals
    in
        

    (* Variables visible in the signature of the definition are local
       variables, inputs and outputs *)
    let signature_vars_set = 
      List.fold_left 
        add_to_svs 
        locals_set
        [inputs; outputs]
    in

    (* Constraints from assertions

       Must add assertions and contract first so that local variables
       can be let bound in definitions_of_equations *)
    let (init_defs_asserts, trans_defs_asserts) = 
      definitions_of_asserts  
        init_defs_calls
        trans_defs_calls
        node_asserts
    in

    (* Constraints from equations *)
    let (init_defs_eqs, trans_defs_eqs) = 
      definitions_of_equations 
        signature_vars_set
        init_defs_asserts
        trans_defs_asserts
        (List.rev node_equations)
    in

    (* Types of input variables *)
    let input_types = 
      List.map StateVar.type_of_state_var inputs
    in

    (* Types of output variables *)
    let output_types =
      List.map StateVar.type_of_state_var outputs
    in

    (* Types of local variables *)
    let local_types =
      List.map StateVar.type_of_state_var locals
    in

    (* Types of variables in the signature *)
    let signature_types = 
      (List.map StateVar.type_of_state_var inputs) @ 
      (List.map StateVar.type_of_state_var outputs) @ 
      (List.map StateVar.type_of_state_var locals) 
    in

    (* Symbol for initial state constraint for node *)
    let init_uf_symbol = 
      UfSymbol.mk_uf_symbol

        (* Name of symbol *)
        (init_uf_symbol_name_of_node node_name)

        (* Types of variables in the signature *)
        signature_types 

        (* Symbol is a predicate *)
        Type.t_bool

    in

    (* Symbol for initial state constraint for node *)
    let fun_def_init = 

      (* Name of symbol *)
      (init_uf_symbol,

       (* Input variables *)
       (((List.map (E.base_var_of_state_var base_offset) inputs) @

         (* Oracle inputs *)
         (List.map (E.base_var_of_state_var base_offset) oracles) @

         (* Output variables *)
         (List.map 
            (E.base_var_of_state_var base_offset) 
            outputs) @

         (* Local variables *)
         (List.map (E.base_var_of_state_var base_offset) locals)),

        (Term.mk_and init_defs_eqs)))

    in

    (* Symbol for transition relation for node *)
    let trans_uf_symbol = 
      UfSymbol.mk_uf_symbol

        (* Name of symbol *)
        (trans_uf_symbol_name_of_node node_name)

        (* Types of variables in the signature *)
        (signature_types @ signature_types)

        (* Symbol is a predicate *)
        Type.t_bool

    in

    (* Symbol for initial state constraint for node *)
    let fun_def_trans = 

      (trans_uf_symbol,

       (* Input variables *)
       (((List.map (E.cur_var_of_state_var cur_offset) inputs) @

         (* Oracle inputs *)
         (List.map (E.cur_var_of_state_var cur_offset) oracles) @

         (* Output variables *)
         (List.map 
            (E.cur_var_of_state_var cur_offset)
            outputs) @

         (* Local variables *)
         (List.map (E.cur_var_of_state_var cur_offset) locals) @ 

         (* Input variables *)
         (List.map (E.pre_var_of_state_var cur_offset) inputs) @

         (* Oracle inputs *)
         (List.map (E.pre_var_of_state_var cur_offset) oracles) @

         (* Output variables *)
         (List.map (E.pre_var_of_state_var cur_offset) outputs) @

         (* Local variables *)
         (List.map (E.pre_var_of_state_var cur_offset) locals)),

        (Term.mk_and trans_defs_eqs)))

    in

    let node_def = 
      { inputs = inputs @ oracles;
        outputs = outputs;
        locals = locals;
        init_uf_symbol = init_uf_symbol;
        init_term = Term.mk_and init_defs_calls;
        trans_uf_symbol = trans_uf_symbol;
        trans_term = Term.mk_and trans_defs_calls }
    in

    trans_sys_of_nodes'
      main_node
      ((node_name, node_def) :: node_defs)
      (fun_def_init :: fun_def_trans :: fun_defs)
      tl


let trans_sys_of_nodes main_node nodes = 
  let nodes' = 
    List.fold_right
      (fun node accum -> N.equations_order_by_dep accum node :: accum)
      nodes
      []
  in
  trans_sys_of_nodes' main_node [] [] nodes'


let prop_of_node_prop main_node state_var =

  (* Name of state variable is name of property *)
  let prop_name = StateVar.name_of_state_var state_var in
  
  (* Term of property *)
  let prop_term = 
    E.base_term_of_state_var 
      base_offset
      (state_var_of_top_scope false main_node state_var) 
  in
  
  (prop_name, prop_term)

let props_of_nodes main_node nodes = 

  try 

    let { LustreNode.props } = LustreNode.node_of_name main_node nodes in

    List.map 
      (prop_of_node_prop main_node)
      props


  with Not_found -> 
    raise 
      (Failure 
         (Format.asprintf
            "props_of_nodes: Node %a not found" 
            (LustreIdent.pp_print_ident false) main_node))


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
