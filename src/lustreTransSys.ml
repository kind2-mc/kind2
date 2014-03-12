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


module E = LustreExpr
module N = LustreNode


(* Use configured SMT solver *)
module PDRSolver = SMTSolver.Make (Config.SMTSolver)

(* High-level methods for PDR solver *)
module S = SolverMethods.Make (PDRSolver)



let name_of_local_var i n = 
  Format.sprintf "__local_%d_%s" i n

let init_uf_symbol_name_of_node n = 
  Format.asprintf "__node_init_%a" (LustreIdent.pp_print_ident false) n
  
let trans_uf_symbol_name_of_node n = 
  Format.asprintf "__node_trans_%a"  (LustreIdent.pp_print_ident false) n
  
type node_def =
  { 

    (* Name of predicate for initial state constraint *)
    init_uf_symbol : UfSymbol.t;

    (* Name of predicate for transition relation *)
    trans_uf_symbol : UfSymbol.t;

    (* Input variables *)
    inputs : StateVar.t list;

    (* Positions of input parameters under a pre *)
    inputs_stateful : int list;

    (* Output variables *)
    outputs : StateVar.t list;

    (* Positions of output parameters under a pre *)
    outputs_stateful : int list;

    (* Stateful local variables *)
    locals : StateVar.t list;

    (* Definition of predicate for initial state constraint *)
    init_term : Term.t; 

    (* Definition of predicate for transition relation *)
    trans_term : Term.t;

  }

let rec definitions_of_equations 
    stateful_vars
    (init, trans) = function 

  | [] -> (init, trans)

  | (state_var, ({ E.expr_init; E.expr_step } as expr)) :: tl -> 

    let init', trans' = 

      if 

        (* Variable is stateful or output? *)
        StateVar.StateVarSet.mem state_var stateful_vars

      then 

        (

          (*
          Format.printf
            "@[<v>Equation for stateful variable %a:@,%a@]@." 
            StateVar.pp_print_state_var state_var
            (LustreExpr.pp_print_lustre_expr false) expr;
         *)

         (* Current state variable of state variable *)
         let var = 
           Term.mk_var
             (Var.mk_state_var_instance state_var Numeral.zero) 
         in
         
         (* Equation for initial constraint on variable *)
         let init_def = Term.mk_eq [var; expr_init] in
         
         (* Equation for transition relation on variable *)
         let trans_def = Term.mk_eq [var; expr_step] in
         
         (* Add term of equation and continue *)
         (init_def :: init, trans_def :: trans))
        
      else
        
        (

          (*
          Format.printf
            "@[<v>Equation for stateless variable %a:@,%a@]@." 
            StateVar.pp_print_state_var state_var
            (LustreExpr.pp_print_lustre_expr false) expr;
          *)

         (* Current state variable of state variable *)
         let var = 
           Var.mk_state_var_instance state_var Numeral.zero
         in
         
         let init' = 
           Term.mk_let 
             [(var, expr_init)]
             (Term.mk_and init)
         in


         let trans' = 
           Term.mk_let 
             [(var, expr_step)]
             (Term.mk_and trans)
         in

         ([init'], [trans']))
        
    in

    definitions_of_equations 
      stateful_vars 
      (init', trans') 
      tl


let rec definitions_of_node_calls 
    scope
    node_defs
    local_vars
    init
    trans = 

  function

    | [] -> (local_vars, init, trans)

    (* Node call without activation condition *)
    | (output_vars, act_cond, node_name, input_exprs, init_exprs) :: tl -> 

      let 

        (* Signature of called node *)
        { init_uf_symbol; 
          trans_uf_symbol; 
          locals; 
          inputs_stateful; 
          outputs_stateful } = 

        try List.assoc node_name node_defs with Not_found -> assert false

      in

      (* Initial state value and step state value of activation
         condition *)
      let
        { E.expr_init = act_cond_init; 
          E.expr_step = act_cond_trans } = 
        act_cond 
      in 

      (* Initial state values of default values *)
      let init_exprs_init = 
        List.map (function { E.expr_init } -> expr_init) init_exprs
      in

      (* Terms for node call in initial state *)
      let input_terms_init = 
        List.map (function { E.expr_init } -> expr_init) input_exprs
      in

      (* Terms for node call in step state *)
      let input_terms_trans = 
        List.map (function { E.expr_step } -> expr_step) input_exprs
      in

      (* Terms for node call in step state *)
      let input_terms_trans_pre = 
        List.map (Term.bump_state Numeral.(- one)) input_terms_trans
      in

      (* Variables capturing the output of the node *)
      let output_terms = 
        List.map
          (fun state_var -> 
             Term.mk_var
               (Var.mk_state_var_instance state_var Numeral.zero))
          output_vars
      in

      (* Variables capturing the output of the node *)
      let output_terms_pre = 
        List.map
          (fun state_var -> 
             Term.mk_var
               (Var.mk_state_var_instance state_var Numeral.(- one)))
          output_vars
      in

      (* Variables local to the node for this instance *)
      let local_vars', call_local_vars = 
        List.fold_right
          (fun state_var (local_vars, call_local_vars) -> 

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
             (local_state_var :: local_vars, 
              local_state_var :: call_local_vars))
          locals
          (local_vars, [])
      in

      (* Variables local to node call for current state *)
      let call_local_vars_init = 
        List.map
          (function state_var -> 
            Term.mk_var
              (Var.mk_state_var_instance state_var Numeral.zero))
          call_local_vars
      in

      (* Variables local to node call for previous state *)
      let call_local_vars_pre = 
        List.map
          (function state_var -> 
            Term.mk_var
              (Var.mk_state_var_instance state_var Numeral.(- one)))
          call_local_vars
      in

      (* Arguments for node call in initial state *)
      let init_call_args = 

        (* Current state input variables *)
        input_terms_init @ 

        (* Current state output variables *)
        output_terms @ 

        (* Current state local variables *)
        call_local_vars_init

      in

      (* Arguments for node call in transition relation *)
      let trans_call_args = 

        (* Current state input variables *)
        input_terms_trans @ 

        (* Current state output variables *)
        output_terms @ 

        (* Current state local variables *)
        call_local_vars_init @

        (* Previous state local variables *)
        call_local_vars_pre @ 

        (list_filter_nth input_terms_trans_pre inputs_stateful) @

        (list_filter_nth output_terms_pre outputs_stateful)

      in

      (* Constraint for node call in initial state *)
      let init_call = Term.mk_uf init_uf_symbol init_call_args in

      (* Constraint for node call in transition relation *)
      let trans_call = Term.mk_uf trans_uf_symbol trans_call_args in

      let init_call_act_cond, trans_call_act_cond = 

        if 

          (* Activation condition of node is constant true *)
          act_cond_init == Term.t_true && 
          act_cond_trans == Term.t_true 

        then 

          (* Return predicates unguarded *)
          init_call, trans_call 

        else

          (* Initial state constraint *)
          (Term.mk_and

             [

               (* Initial state constraint with true activation
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
                            [Term.mk_var
                               (Var.mk_state_var_instance 
                                  state_var 
                                  Numeral.zero); 
                             expr_init] :: accum)
                       []
                       output_vars
                       init_exprs)]

             ],

           (* Transition relation *)
           Term.mk_and

             [

               (* Transition relation with true activation condition *)
               Term.mk_implies [act_cond_trans; trans_call];
               
               (* Transition relation with false activation condition *)
               Term.mk_implies 
                 [Term.mk_not act_cond_trans;
                  Term.mk_and 
                    (List.fold_left
                       (fun accum state_var ->
                          Term.mk_eq 
                            [Term.mk_var
                               (Var.mk_state_var_instance 
                                  state_var 
                                  Numeral.zero); 
                             Term.mk_var
                               (Var.mk_state_var_instance 
                                  state_var 
                                  Numeral.(- one))] :: accum)
                       []
                       (output_vars @ local_vars))]
               

             ]



          )

      in

      (* Continue with next node call *)
      definitions_of_node_calls 
        scope
        node_defs
        local_vars'
        (init_call_act_cond :: init)
        (trans_call_act_cond :: trans) 
        tl


let definition_of_node 
  solver
  node_defs 
  ({ N.name = node_name;
     N.inputs = node_inputs;
     N.outputs = node_outputs; 
     N.locals = node_locals; 
     N.equations = node_equations; 
     N.calls = node_calls; 
     N.asserts = node_asserts;
     N.props = node_props } as node) =
  
  (* Scope from node name *)
  let scope = 
    LustreIdent.scope_of_index (LustreIdent.index_of_ident node_name)
  in

  (* Input variables *)
  let inputs = List.map fst node_inputs in

  (* Output variables *)
  let output_vars = 
    List.fold_left 
      (fun a v -> StateVar.StateVarSet.add v a)
      StateVar.StateVarSet.empty 
      node_outputs
  in

  (* Property variables *)
  let prop_vars = 
    List.fold_left 
      (fun accum expr -> 
         if E.is_var expr then
           StateVar.StateVarSet.add (E.state_var_of_expr expr) accum
         else
           accum)
      StateVar.StateVarSet.empty 
      node_props
  in

  (* Variables occurring under a pre *)
  let stateful_vars = 

    (* Collect stateful variables of all expressions *)
    List.fold_left 
      (fun accum expr -> 
         StateVar.StateVarSet.union
           (E.stateful_vars_of_expr expr)
           accum)
      StateVar.StateVarSet.empty
      (N.exprs_of_node node)
  in

  (* Constraints from equations *)
  let (init_defs, trans_defs) = 
    definitions_of_equations 
      (StateVar.StateVarSet.union 
         (StateVar.StateVarSet.union output_vars prop_vars)
         stateful_vars)
      ([], [])
      (List.rev node_equations)
  in

  (* Add constraints from node calls *)
  let call_local_vars, init_defs_calls, trans_defs_calls = 
    definitions_of_node_calls
      scope
      node_defs
      []
      init_defs
      trans_defs
      node_calls
  in

  (* Indexes of stateful output variables *)
  let outputs_stateful = 
    list_indexes 
      (StateVar.StateVarSet.elements stateful_vars)
      node_outputs
  in

  (* Indexes of stateful input variables *)
  let inputs_stateful = 
    list_indexes 
      (StateVar.StateVarSet.elements stateful_vars)
      (List.map fst node_inputs)
  in

  (* Stateful local variables *)
  let locals = 

    (* Stateful variables that are not input or output *)
    StateVar.StateVarSet.elements
      (StateVar.StateVarSet.filter
         (fun state_var -> 
            not
              (List.mem state_var node_outputs || 
               List.mem_assoc state_var node_inputs))
         stateful_vars) @
    
    (* Stateful variables lifted from called nodes *)
    call_local_vars

  in

  (* Types of input variables *)
  let input_types = 
    List.map
      (fun (v, _) -> StateVar.type_of_state_var v) 
      node_inputs
  in

  (* Types of output variables *)
  let output_types =
    List.map
      StateVar.type_of_state_var
      node_outputs
  in

  (* Types of local variables *)
  let local_types =
    List.map
      StateVar.type_of_state_var
      locals
  in

  (* Symbol for initial state constraint for node *)
  let init_uf_symbol = 
    UfSymbol.mk_uf_symbol

      (* Name of symbol *)
      (init_uf_symbol_name_of_node node_name)

      (* Input variables *)
      (input_types @

       (* Output variables *)
       output_types @

       (* Local variables *)
       local_types)
       
      (* Symbol is a predicate *)
      Type.t_bool

  in

  (* Symbol for initial state constraint for node *)
  let _ = 
    PDRSolver.define_fun

      solver

      (* Name of symbol *)
      (init_uf_symbol_name_of_node node_name)
      
      (* Input variables *)
      ((List.map (fun sv -> Var.mk_state_var_instance sv Numeral.zero) inputs) @
       
       (* Output variables *)
       (List.map (fun sv -> Var.mk_state_var_instance sv Numeral.zero) node_outputs) @

       (* Local variables *)
       (List.map (fun sv -> Var.mk_state_var_instance sv Numeral.zero) locals))
       
      (* Symbol is a predicate *)
      Type.t_bool

      (Term.mk_and init_defs_calls)

  in

  (* Symbol for transition relation for node *)
  let trans_uf_symbol = 
    UfSymbol.mk_uf_symbol

      (* Name of symbol *)
      (trans_uf_symbol_name_of_node node_name)

      (* Input variables *)
      (input_types @

       (* Output variables *)
       output_types @

       (* Local variables at current and previous state *)
       local_types @ local_types @
       
       (* Stateful input variables *)
       (list_filter_nth input_types inputs_stateful) @
       
       (* Stateful output variables *)
       (list_filter_nth output_types outputs_stateful))
       
      (* Symbol is a predicate *)
      Type.t_bool

  in

  Format.printf
    "@[<v>@[<hv>%a@]@,\
     Intial state constraint:@,@[<hv>%a@]@,\
     Transition relation:@,@[<hv>%a@]@,@]@."
    (LustreNode.pp_print_node false) node
    Term.pp_print_term (Term.mk_and init_defs_calls)
    Term.pp_print_term (Term.mk_and trans_defs_calls);

  let node_def = 
    { init_uf_symbol = init_uf_symbol;
      trans_uf_symbol = trans_uf_symbol;
      inputs = inputs;
      inputs_stateful = inputs_stateful;
      outputs = node_outputs;
      outputs_stateful = outputs_stateful;
      locals = locals;
      init_term = Term.mk_and init_defs_calls;
      trans_term = Term.mk_and trans_defs_calls }
  in


  (node_name, node_def) :: node_defs




(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
