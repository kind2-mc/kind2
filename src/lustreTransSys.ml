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

module SVS = StateVar.StateVarSet

(*
(* Use configured SMT solver *)
module MySolver = SMTSolver.Make (Config.SMTSolver)

(* High-level methods for PDR solver *)
module S = SolverMethods.Make (MySolver)
*)


let name_of_local_var i n = 
  Format.sprintf "__local_%d_%s" i n

let init_uf_symbol_name_of_node n = 
  Format.asprintf "__node_init_%a" (LustreIdent.pp_print_ident false) n
  
let trans_uf_symbol_name_of_node n = 
  Format.asprintf "__node_trans_%a"  (LustreIdent.pp_print_ident false) n


(* Instance of state variable at current instant *)
let cur_var_of_state_var state_var = 
  Var.mk_state_var_instance state_var Numeral.zero

(* Instance of state variable at previous instant *)
let pre_var_of_state_var state_var = 
  Var.mk_state_var_instance state_var Numeral.(- one)
    
(* Term of instance of state variable at current instant *)
let cur_term_of_state_var state_var = 
  Term.mk_var (cur_var_of_state_var state_var)

(* Term of instance of state variable at previous instant *)
let pre_term_of_state_var state_var = 
  Term.mk_var (pre_var_of_state_var state_var)

(* Set of state variables of list *)
let svs_of_list list = 
  List.fold_left (fun a e -> SVS.add e a) SVS.empty list

(* Add a list of state variables to a set *)
let add_to_svs set list = 
  List.fold_left (fun a e -> SVS.add e a) set list 
  
  
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


    Format.printf "definitions_of_equations %a, %d left@." (E.pp_print_lustre_expr false) expr (List.length tl);

    (* Modified definitions *)
    let init', trans' = 

      if 

        (* Variable must to have a definition? *)
        SVS.mem state_var vars

      then 

        (

          Format.printf "Equation@.";

          (* Current state variable of state variable *)
          let var_term = cur_term_of_state_var state_var in
         
          (* Equation for initial constraint on variable *)
          let init_def = Term.mk_eq [var_term; expr_init] in
         
          (* Equation for transition relation on variable *)
          let trans_def = Term.mk_eq [var_term; expr_step] in
         
          (* Add term of equation and continue *)
          (init_def :: init, trans_def :: trans))
        
      else
        
        (

          Format.printf "Let binding@.";

          (* Current state variable of state variable *)
          let var = cur_var_of_state_var state_var in
          
          (* Define variable with a let *)
          let init' =
            Term.mk_let [(var, expr_init)] (Term.mk_and init) 
          in

          (* Define variable with a let *)
          let trans' = 
            Term.mk_let [(var, expr_step)] (Term.mk_and trans)
          in
          
          (* Start with singleton lists *)
          ([init'], [trans']))
        
    in

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
    
    (* Continue with next equations *)
    definitions_of_equations vars init' trans' tl


(* Fold list of node calls to definition *)
let rec definitions_of_node_calls scope node_defs local_vars init trans = 

  function

    (* All node calls consumed, return term for initial state
       constraint and transition relation *)
    | [] -> (local_vars, init, trans)

    (* Node call with or without activation condition *)
    | (output_vars, act_cond, node_name, input_exprs, init_exprs) :: tl -> 

      (* Signature of called node *)
      let { init_uf_symbol; trans_uf_symbol; inputs; outputs; locals } = 

        (* Find definition of called node by name *)
        try List.assoc node_name node_defs 
        with Not_found -> assert false
          
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
        List.map cur_term_of_state_var output_vars
      in

      (* Variables capturing the output of the node *)
      let output_terms_pre = 
        List.map pre_term_of_state_var output_vars
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
               StateVar.mk_state_var
                 (name_of_local_var (List.length local_vars) var_name)
                 scope
                 var_type
             in
             (local_state_var :: local_vars, 
              local_state_var :: call_local_vars))
          locals
          (output_vars @ local_vars, [])

      in

      (* Variables local to node call for current state *)
      let call_local_vars_init = 
        List.map cur_term_of_state_var call_local_vars
      in

      (* Variables local to node call for previous state *)
      let call_local_vars_pre = 
        List.map pre_term_of_state_var call_local_vars
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

        (* Previous state input variables *)
        input_terms_trans_pre @

        (* Previous state output variables *)
        output_terms_pre @

        (* Previous state local variables *)
        call_local_vars_pre  

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
          act_cond_init == Term.t_true && 
          act_cond_trans == Term.t_true 

        then 

          (* Return predicates unguarded *)
          local_vars', init_call, trans_call 

        else

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
            (List.map cur_term_of_state_var output_default_vars) @ 

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
            (List.map cur_term_of_state_var output_default_vars) @ 

            (* Current state local variables *)
            call_local_vars_init @

            (* Previous state input variables *)
            input_terms_trans_pre @

            (* Previous state output variables *)
            (List.map pre_term_of_state_var output_default_vars) @ 

            (* Previous state local variables *)
            call_local_vars_pre  

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
                [act_cond_init; 
                 Term.mk_and
                   (List.fold_left2 
                      (fun accum v1 v2 ->
                         Term.mk_eq 
                           [cur_term_of_state_var v1; 
                            cur_term_of_state_var v2] :: accum)
                      []
                      output_vars
                      output_default_vars)];

              (* Initial state constraint with false activation
                  condition *)
              Term.mk_implies 
                [Term.mk_not act_cond_init;
                 Term.mk_and
                   (List.fold_left2 
                      (fun accum state_var { E.expr_init } ->
                         Term.mk_eq 
                           [cur_term_of_state_var state_var; 
                            expr_init] :: accum)
                      []
                      output_vars
                      init_exprs)]

             ],

           (* Transition relation *)
           Term.mk_and

             [

               (* Transition relation with true activation condition *)
               Term.mk_implies
                 [act_cond_trans; 
                  Term.mk_and 
                    (List.fold_left2
                       (fun accum sv1 sv2 ->
                          Term.mk_eq 
                            [cur_term_of_state_var sv1; 
                             cur_term_of_state_var sv2] :: accum)
                       [trans_call]
                       output_vars
                       output_default_vars)];
                  
               (* Transition relation with false activation condition *)
               Term.mk_implies 
                 [Term.mk_not act_cond_trans;
                  Term.mk_and 
                    (List.fold_left
                       (fun accum state_var ->
                          Term.mk_eq 
                            [cur_term_of_state_var state_var; 
                             pre_term_of_state_var state_var] :: accum)
                       []
                       (output_vars @ output_default_vars @ call_local_vars))];

             ]

          )

      in

      (* Continue with next node call *)
      definitions_of_node_calls 
        scope
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

      (* Add constraint unless it is true *)
      ((if expr_init == Term.t_true then init else expr_init :: init), 
       (if expr_step == Term.t_true then trans else expr_step :: trans))
      

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


let rec trans_sys_of_nodes'
    node_defs 
    fun_defs = function 

  | [] -> 

    (match node_defs, fun_defs with 

      | (_, { inputs; outputs; locals }) :: _, 
        (init_uf_symbol, init_vars, _) :: 
        (trans_uf_symbol, trans_vars, _) :: _ -> 

    Format.printf 
      "@[<v>inputs: %a@,outputs: %a@,locals: %a@]@."
      (pp_print_list StateVar.pp_print_state_var "@ ") inputs
      (pp_print_list StateVar.pp_print_state_var "@ ") outputs
      (pp_print_list StateVar.pp_print_state_var "@ ") locals;

        let state_vars = inputs @ outputs @ locals in

        (List.rev fun_defs, 
         state_vars, 
         Term.mk_uf 
           init_uf_symbol
           (List.map cur_term_of_state_var state_vars),
         Term.mk_uf 
           trans_uf_symbol
           ((List.map pre_term_of_state_var state_vars) @
            (List.map cur_term_of_state_var state_vars)))

      | _ -> raise (Invalid_argument "trans_sys_of_nodes")

    )


  | ({ N.name = node_name;
       N.inputs = node_inputs;
       N.outputs = node_outputs; 
       N.locals = node_locals; 
       N.equations = node_equations; 
       N.calls = node_calls; 
       N.asserts = node_asserts; 
       N.requires = node_requires; 
       N.ensures = node_ensures } as node) :: tl ->

    Format.printf 
      "@[<v>inputs: %a@,outputs: %a@,locals: %a@]@."
      (pp_print_list StateVar.pp_print_state_var "@ ") (List.map fst node_inputs)
      (pp_print_list StateVar.pp_print_state_var "@ ") node_outputs
      (pp_print_list StateVar.pp_print_state_var "@ ") node_locals;

    (* Scope from node name *)
    let scope = 
      LustreIdent.scope_of_index (LustreIdent.index_of_ident node_name)
    in

    (* Input variables *)
    let inputs = List.map fst node_inputs in

    (* Output variables *)
    let outputs = node_outputs in

    (* Add constraints from node calls *)
    let call_locals, init_defs_calls, trans_defs_calls = 
      definitions_of_node_calls scope node_defs [] [] [] node_calls
    in

    (* Variables occurring under a pre that are not also outputs or inputs *)
    let node_locals_set = 
      List.fold_left 
        (fun accum expr -> 
           SVS.fold 
             (fun sv a -> 
                if List.mem sv outputs || List.mem sv inputs then 
                  a 
                else 
                  SVS.add sv a)
             (E.stateful_vars_of_expr expr)
             accum)
        SVS.empty
        (N.exprs_of_node node)
    in

    (* Variables occurring under a pre and variables capturing the
       output of a node call *)
    let locals_set = add_to_svs node_locals_set call_locals in

    (* Variables occurring under a pre and variables capturing the
       output of a node call *)
    let locals = SVS.elements node_locals_set @ call_locals in

    (* Variables visible in the signature of the definition *)
    let signature_vars_set = 
      List.fold_left add_to_svs locals_set [inputs; outputs]
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

    let (init_defs_contract, trans_defs_contract) = 
      definitions_of_contract  
        init_defs_asserts
        trans_defs_asserts
        node_requires
        node_ensures
    in

    (* Constraints from equations *)
    let (init_defs_eqs, trans_defs_eqs) = 
      definitions_of_equations 
        signature_vars_set
        init_defs_contract
        trans_defs_contract
        (List.rev node_equations)
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
       ((List.map cur_var_of_state_var inputs) @

        (* Output variables *)
        (List.map cur_var_of_state_var outputs) @

        (* Local variables *)
        (List.map cur_var_of_state_var locals)),

       (Term.mk_and init_defs_calls))

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
       ((List.map cur_var_of_state_var inputs) @

        (* Output variables *)
        (List.map cur_var_of_state_var outputs) @

        (* Local variables *)
        (List.map cur_var_of_state_var locals) @ 

        (* Input variables *)
        (List.map pre_var_of_state_var inputs) @

        (* Output variables *)
        (List.map pre_var_of_state_var outputs) @

        (* Local variables *)
        (List.map pre_var_of_state_var locals)),

       (Term.mk_and trans_defs_calls))

    in

    Format.printf
      "@[<v>@[<hv>%a@]@,\
       Intial state constraint:@,@[<hv>%a@]@,\
       Transition relation:@,@[<hv>%a@]@,@]@."
      (LustreNode.pp_print_node false) node
      Term.pp_print_term (Term.mk_and init_defs_calls)
      Term.pp_print_term (Term.mk_and trans_defs_calls);

    let node_def = 
      { inputs = inputs;
        outputs = node_outputs;
        locals = locals;
        init_uf_symbol = init_uf_symbol;
        init_term = Term.mk_and init_defs_calls;
        trans_uf_symbol = trans_uf_symbol;
        trans_term = Term.mk_and trans_defs_calls }
    in

    trans_sys_of_nodes'
      ((node_name, node_def) :: node_defs)
      (fun_def_init :: fun_def_trans :: fun_defs)
      tl


let trans_sys_of_nodes nodes = trans_sys_of_nodes' [] [] nodes



(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
