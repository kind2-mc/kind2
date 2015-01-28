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

(* A Lustre node

   Nodes are normalized for easy translation into a transition system,
   mainly by introducing new variables. A LustreExpr.t does not
   contain node calls, temporal operators or expressions under a pre
   operator. Node equations become a map of identifiers to expressions
   in [node_eqs], all node calls are in [node_calls] as a list of
   tuples containing fresh variables the node output is assigned to
   and the expressions for the node input.

   The node inputs are extended with oracles that are appended to the
   formal input parameters for each unguarded [pre] operator or oracle
   input of a called node.

   The node outpus are extended with observers for each property that
   is not an output, and each observer of a called node.

   Local constants are propagated and do not need to be stored. The
   inputs of a node can be extended by constant state variables in
   [node_oracles] for the initial value of unguarded pre operations.

   Assertions, properties to prove and contracts as assumptions and
   guarantees are lists of expressions in [node_asserts],
   [node_props], [node_requires], and [node_ensures].

   The flag [node_is_main] is set if the node has been annotated as
   main, it is not checked if more than one node or no node at all may
   have that annotation. *)

open Lib

(* Module abbreviations *)
module I = LustreIdent 
module E = LustreExpr

module SVS = StateVar.StateVarSet
module SVMap = StateVar.StateVarMap
module ISet = I.LustreIdentSet

(* Set of state variables of list *)
let svs_of_list list = 
  List.fold_left (fun a e -> SVS.add e a) SVS.empty list


(* Add a list of state variables to a set *)
let add_to_svs set list = 
  List.fold_left (fun a e -> SVS.add e a) set list 
  

(* A call of a node *)
type node_call = 

  { 

    (* Variables capturing the outputs *)
    call_returns : StateVar.t list;

    (* Variables capturing the outputs *)
    call_observers : StateVar.t list;

    (* Boolean activation condition *)
    call_clock : StateVar.t option;

    (* Name of called node *)
    call_node_name : LustreIdent.t;
    
    (* Position of node call in input file *)
    call_pos : position;

    (* Expressions for input parameters *)
    call_inputs : StateVar.t list;

    (* Expression for initial return values *)
    call_defaults : LustreExpr.t list;

  }

(*
  { call_returns; call_clock; call_node_name; call_pos; call_inputs; call_defaults }
*)



(* A Lustre node *)
type t = 

  { 

    (* Name of node *)
    name : LustreIdent.t;

    (* Input variables of node together with their index in the
       original model

       The order of the list is important, it is the order of the
       indexes and of the parameters in the declaration. *)
    inputs : (StateVar.t * I.index) list;

    (* Oracle inputs *)
    oracles : StateVar.t list;

    (* Output variables of node together with their index in the
       original model

       The order of the list is important, it is the order of the
       indexes and of the parameters in the declaration. *)
    outputs : (StateVar.t * I.index) list;

    (* Observer outputs *)
    observers : StateVar.t list;

    (* Local variables of node

       The order of the list is irrelevant, we are doing dependency
       analysis and cone of influence reduction later. *)
    locals : (StateVar.t * I.index) list; 

    (* Equations for local and output variables *)
    equations : (StateVar.t * LustreExpr.t) list;

    (* Node calls with activation condition: variables capturing the
       outputs, the Boolean activation condition, the name of the
       called node, expressions for input parameters and expression
       for initialization *)
    calls : node_call list;

    (* Assertions of node *)
    asserts : LustreExpr.t list;

    (* Proof obligations for node *)
    props : (StateVar.t * TermLib.prop_source) list;

    (* Contract for node, assumptions *)
    requires : LustreExpr.t list;

    (* Contract for node, guarantees *)
    ensures : LustreExpr.t list;

    (* Node is annotated as main node *)
    is_main : bool;

    (* Dependencies of the output variables on input variables *)
    output_input_dep : int list list;

    (* Index of last abstraction state variable *)
    fresh_state_var_index : Numeral.t ref;

    (* Index of last oracle state variable *)
    fresh_oracle_index : Numeral.t ref;

    (* Map of state variables to their oracles *)
    state_var_oracle_map : StateVar.t StateVar.StateVarHashtbl.t;

    (* Map of expressions to state variables *)
    expr_state_var_map : StateVar.t E.ExprHashtbl.t;

  }


(* An empty node *)
let empty_node name = 
  { name = name;
    inputs = [];
    oracles = [];
    outputs = [];
    observers = [];
    locals = [];
    equations = [];
    calls = [];
    asserts = [];
    props = [];
    requires = [];
    ensures = [];
    is_main = false;
    output_input_dep = [];
    fresh_state_var_index = ref Numeral.(- one);
    fresh_oracle_index = ref Numeral.(- one); 
    state_var_oracle_map = StateVar.StateVarHashtbl.create 7;
    expr_state_var_map = E.ExprHashtbl.create 7 }



(* Pretty-print a node input *)
let pp_print_input safe ppf (var, _) =

  Format.fprintf ppf
    "%t%a: %a"
    (function ppf -> 
      if StateVar.is_const var then Format.fprintf ppf "const ")
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)


(* Pretty-print a node output *)
let pp_print_output safe ppf (var, _) =

  Format.fprintf ppf
    "%a: %a"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)


(* Pretty-print a node local variable *)
let pp_print_local safe ppf (var, _) =

  Format.fprintf ppf
    "%a: %a"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)


(* Pretty-print a node equation *)
let pp_print_node_equation safe ppf (var, expr) = 

  Format.fprintf ppf
    "@[<hv 2>%a =@ %a;@]"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node call *)
let pp_print_call safe ppf = function 

  (* Node call on the base clock *)
  | { call_returns = out_vars; 
      call_observers = observer_vars; 
      call_clock = None; 
      call_node_name = node; 
      call_inputs = in_vars } ->

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>%a(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (out_vars @ observer_vars)
      (I.pp_print_ident safe) node
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") in_vars

  (* Node call not on the base clock is a condact *)
  |  { call_returns = out_vars; 
       call_observers = observer_vars; 
       call_clock = Some act_var;
       call_node_name = node; 
       call_inputs = in_vars; 
       call_defaults = init_exprs } ->
     
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>condact(%a,@,%a(%a),@,%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (out_vars @ observer_vars)
      (E.pp_print_lustre_var safe) act_var
      (I.pp_print_ident safe) node
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") in_vars
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") 
      (init_exprs @ (List.map (fun _ -> E.t_true) observer_vars))
          

(* Pretty-print an assertion *)
let pp_print_assert safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>assert@ %a;@]"
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a property *)
let pp_print_prop safe ppf var = 

  Format.fprintf ppf
    "@[<hv 2>--%%PROPERTY@ @[<h>%a@];@]"
    (E.pp_print_lustre_var safe) var
    

(* Pretty-print an assumption *)
let pp_print_requires safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--@@requires@ @[<h>%a@];@]"
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a guarantee *)
let pp_print_ensures safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--@@ensures @[<h>%a@];@]"
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node *)
let pp_print_node 
    safe
    ppf 
    { name;
      inputs; 
      oracles; 
      outputs; 
      observers; 
      locals; 
      equations; 
      calls; 
      asserts; 
      props; 
      requires; 
      ensures;
      output_input_dep;
      is_main } = 

  (* Output a space if list is not empty *)
  let space_if_nonempty = function
    | [] -> (function _ -> ())
    | _ -> (function ppf -> Format.fprintf ppf "@ ")
  in

  Format.fprintf ppf 
    "@[<hv>@[<hv 2>node %a@ @[<hv 1>(%a)@]@;<1 -2>\
     returns@ @[<hv 1>(%a)@];@]@ \
     @[<v>%a@]%t\
     %t%t\
     @[<hv 2>let@ \
     %a%t\
     %a%t\
     %a%t\
     %t\
     %a%t\
     %a%t\
     %a@;<1 -2>\
     tel;@]@]"  
    (I.pp_print_ident safe) name
    (pp_print_list (pp_print_input safe) ";@ ") 
    (inputs @ (List.map (fun sv -> (sv, I.empty_index)) oracles))
    (pp_print_list (pp_print_output safe) ";@ ") 
    (outputs @ (List.map (fun sv -> (sv, I.empty_index)) observers))
    (pp_print_list  
       (fun ppf l -> 
          Format.fprintf ppf "@[<h>-- %a@]"
            (pp_print_list Format.pp_print_int "@ ")
            l)
       "@,")
    output_input_dep
    (space_if_nonempty output_input_dep)
    (function ppf -> 
      if locals = [] then () else 
        Format.fprintf ppf 
          "@[<hv 2>var@ %a;@]" 
          (pp_print_list (pp_print_local safe) ";@ ") locals)
    (space_if_nonempty locals)
    (pp_print_list (pp_print_call safe) "@ ") calls
    (space_if_nonempty calls)
    (pp_print_list (pp_print_node_equation safe) "@ ") equations
    (space_if_nonempty equations)
    (pp_print_list (pp_print_assert safe) "@ ") asserts
    (space_if_nonempty asserts)
    (function ppf -> if is_main then Format.fprintf ppf "--%%MAIN@,")
    (pp_print_list (pp_print_requires safe) "@ ") requires
    (space_if_nonempty requires)
    (pp_print_list (pp_print_ensures safe) "@ ") ensures
    (space_if_nonempty ensures)
    (pp_print_list (pp_print_prop safe) "@ ") ((List.map fst props) @ observers)
    


(* Return the node of the given name from a list of nodes *)
let exists_node_of_name name nodes =

  List.exists
    (function { name = node_name } -> name = node_name)
    nodes


(* Return the node of the given name from a list of nodes *)
let node_of_name name nodes =

  try 

    List.find
      (function { name = node_name } -> name = node_name)
      nodes
      
  with Not_found -> 

    debug lustreNode 
      "@[<v>Node %a not found@,%a@]"
      (I.pp_print_ident false) name
      (pp_print_list (pp_print_node false) "@,") nodes
    in
    
    raise Not_found 


let rec ident_of_top = function 
  
  | [] -> raise (Invalid_argument "ident_of_top")

  | [{ name }] -> name 

  | h :: tl -> ident_of_top tl


(* Calculate dependencies of variables *)
let rec node_var_dependencies nodes node accum = 

(*
  (* Return expression either for the initial state or a step state *)
  let init_or_step_of_expr { E.expr_init; E.expr_step } = 
    if init_or_step then 
      E.base_term_of_expr E.base_offset expr_init 
    else 
      E.cur_term_of_expr E.cur_offset expr_step 
  in

  let init_or_step_offset = 
    if init_or_step then E.base_offset else E.cur_offset
  in
*)
  function 

    (* Return all calculated dependencies *)
    | [] -> accum

    (* Calculate dependency of variable [ident], which all variables
       in [dep] depend on *)
    | (state_var, dep) :: tl -> 

(*
      debug lustreNode
        "@[<v>node_var_dependencies %a @[<h>(%a)@]@,%a@]@."
        StateVar.pp_print_state_var state_var
        (pp_print_list StateVar.pp_print_state_var "@ ") dep 
        (pp_print_list (pp_print_node false) "@,") nodes
      in
*)

      if 

        (* Variable is an input variable *)
        List.exists 
          (fun (sv, _) -> StateVar.equal_state_vars sv state_var)
          node.inputs 

      then 

        (* No dependencies for inputs *)
        node_var_dependencies 
          nodes
          node
          ((state_var, SVS.empty) :: accum) 
          tl

      else

        (* Variables this variable depends on *)
        let vars = 

          try 

            (* Get expression defining variable *)
            let (_, expr) = 
              List.find 
                (fun (sv, _) -> StateVar.equal_state_vars sv state_var)
                node.equations 
            in

            (* Get variables in expression *)
            SVS.elements
              (SVS.union 
                 (Term.state_vars_at_offset_of_term
                    E.base_offset
                    (E.base_term_of_expr E.base_offset expr.E.expr_init))
                 (Term.state_vars_at_offset_of_term
                    E.cur_offset
                    (E.cur_term_of_expr E.cur_offset expr.E.expr_step)))

          (* Variable is not input or not defined in an equation *)
          with Not_found -> 

            try

              (* Iterate over node calls to find identifier in
                 variables capturing the output *)
              let rec aux ident = function
                | [] -> raise Not_found
                | { call_returns = o; call_observers = b } as n :: tl -> 

                  (* Iterate over variables capturing the output to
                     find variable and return the node call and the
                     position of the variable in the output
                     parameters *)
                  let rec aux2 i = function
                    | [] -> raise Not_found 
                    | sv :: _ 
                      when StateVar.equal_state_vars sv state_var -> (n, i)
                    | _ :: tl -> aux2 (succ i) tl
                  in

                  try aux2 0 (o @ b) with Not_found -> aux ident tl

              in

              (* Return node call and position of variable in output
                 parameters *)
              let 
                { call_node_name = node_ident; call_inputs = call_params }, 
                input_pos = 
                aux state_var node.calls 
              in

(*
              Format.printf 
                "%a is at position %d in call to node %a@."
                (I.pp_print_ident false) ident 
                input_pos
                (I.pp_print_ident false) node_ident;
*)

              (* Get dependencies of output parameters on input
                 parameters from called node *)
              let { output_input_dep } = 
                node_of_name node_ident nodes
              in
(*
              debug lustreNode
                "@[<v>Input output dependencies of node %a:@[<v>%a@]@]"
                (I.pp_print_ident false) node_ident
                (pp_print_list
                  (fun ppf l -> 
                    Format.fprintf ppf "@[<h>%a@]"
                      (pp_print_list Format.pp_print_int "@ ")
                      l)
                  "@,")
                output_input_dep
              in
*)
              (* Get expressions that output of node depends on *)
              let dep_expr = 
                List.fold_left
                  (fun a d -> 
                     (List.nth call_params d :: a))
                  []
                  (List.nth output_input_dep input_pos)
              in
(*
              (* Get variables in expression *)
              SVS.elements
                (List.fold_left
                   (fun a e -> 
                      SVS.union
                        (SVS.union 
                           (Term.state_vars_at_offset_of_term
                              E.base_offset
                              (E.base_term_of_expr 
                                 E.base_offset 
                                 e.E.expr_init))
                           (Term.state_vars_at_offset_of_term
                              E.cur_offset
                              (E.cur_term_of_expr 
                                 E.cur_offset 
                                 e.E.expr_step)))
                        a)
                   SVS.empty
                   dep_expr)
*)
              
              dep_expr

            (* Variable is not input or defined in an equation or node
               call, it could be in an assertion *)
            with Not_found -> []

        in

        (* Some variables have had their dependencies calculated
           already *)
        let vars_visited, vars_not_visited = 
          List.partition
            (fun sv -> 
               List.exists
                 (fun (sv', _) -> StateVar.equal_state_vars sv sv') 
                 accum)
            vars
        in

        (* All dependent variables visited? *)
        if vars_not_visited = [] then 

          (* Dependencies of this variable is set of dependencies of
             its variables *)
          let dependent_vars = 
            List.fold_left
              (fun a i -> 
                 SVS.union a (List.assq i accum))
              (List.fold_left (fun a v -> SVS.add v a) SVS.empty vars)
              vars_visited
          in

(*
          debug lustreNode
            "@[<hv>Dependencies of %a:@ @[<hv>%a@]@]"
            StateVar.pp_print_state_var state_var
            (pp_print_list
              StateVar.pp_print_state_var
              ",@ ")
            (SVS.elements dependent_vars)
          in
*)

          (* Add variable and its dependencies to accumulator *)
          node_var_dependencies 
            nodes
            node 
            ((state_var, dependent_vars) :: accum)
            tl

        else
          
        if 

          (* Circular dependency: a variable that this variable
             depends on occurs as a dependency *)
          List.exists
            (fun v -> List.memq v dep)
            (state_var :: vars_not_visited)

        then

          (* TODO: Output variables in circular dependency *)
          failwith 
            (Format.asprintf 
               "Circular dependency involving %a"
               StateVar.pp_print_state_var state_var)

        else

          (* First get dependencies of all dependent variables *)
          node_var_dependencies 
            nodes 
            node
            accum 
            ((List.map 
                (fun v -> (v, state_var :: dep)) 
                vars_not_visited) @ 
             ((state_var, dep) :: tl))

             
(* Calculate dependencies of outputs on inputs *) 
let output_input_dep_of_var_dep node var_deps =

  (* Return a list of positions in inputs for each output *)
  List.map
    (fun (o, _) -> 

       (* Get dependencies of output variable *)
       let deps = List.assoc o var_deps in 

       (* Iterate over all dependent variables to find input variables
          and their positions *)
       List.fold_left 
         (fun a v -> 
            try

              (* Iterate over input variables and return position of
                 given variable *)
              let rec aux i = function 
                | [] -> raise Not_found
                | (ident, _) :: tl 
                  when StateVar.equal_state_vars ident v -> i
                | _ :: tl -> aux (succ i) tl 
              in

              (* Append position of input variable if found *)
              (aux 0 node.inputs) :: a 

            (* Variable is not input *)
            with Not_found -> a)
         []
         (SVS.elements deps)
    )
    node.outputs




(* Order variables such that each variable occurs before the variables
   it depends on *)
let rec order_by_dep accum = function 

  (* All dependencies processed *)
  | [] -> accum
    
  (* Variable already visited *)
  | (h, _) :: tl when List.mem h accum -> order_by_dep accum tl

  (* Variables [h] and the set [d] of variables it depends on *)
  | (h, d) :: tl -> 

    if 

      (* All dependencies are in accumulator? *)
      SVS.for_all (fun v -> List.mem v accum) d 

    then 

      (* Add variable to accumulator and continue *)
      order_by_dep (h :: accum) tl

    else

      (* Need to add all dependent variables first *)
      order_by_dep 
        accum
        (SVS.fold
           (fun e a -> 
              (List.find
                 (fun (f, _) -> StateVar.equal_state_vars e f) 
                 tl) 
              :: a)
           d
           ((h,d) :: tl))
    

(* Return node with equations in dependency order *)
let equations_order_by_dep nodes node = 

  (* For each variable get the set of current state variables in its
     equation *)
  let var_dep = 
    node_var_dependencies 
      nodes
      node
      []
      ((List.map (fun (v, _) -> (v, [])) node.equations) @
       (List.map (fun (v, _) -> (v, [])) node.outputs))
  in

  (* Order variables such that variables defined in terms of other
     variables occur first *)
  let vars_ordered = order_by_dep [] var_dep in

  (* Order equations such that an equations defining a variable occurs
     before all equations using it *)
  let equations_ordered = 
    List.fold_left 
      (fun a v -> 
         try (v, List.assoc v node.equations) :: a with Not_found -> a)
      []
      vars_ordered
  in
    
  (* Return node with equations in dependency order *)
  { node with equations = equations_ordered }


let compute_output_input_dep nodes node = 
  
  (* For each variable get the set of current state variables in its
     equation *)
  let var_dep = 
    node_var_dependencies 
      nodes
      node
      []
      ((List.map (fun (v, _) -> (v, [])) node.equations) @
       (List.map (fun (v, _) -> (v, [])) node.outputs))
  in
  
  (* Order variables such that variables defined in terms of other
     variables occur first *)
  let vars_ordered = order_by_dep [] var_dep in
  
  (* Compute dependencies of output variables on inputs *)
  let output_input_dep = 
    output_input_dep_of_var_dep node var_dep 
  in

  (* Return node with equations in dependency order *)
  { node with output_input_dep = output_input_dep }


(* If x = y and x captures the output of a node, substitute y *)
let solve_eqs_node_calls node = 

  let calls', vars_eliminated =

    (* Iterate over all calls, collect modified calls and eliminated
       variables *)
    List.fold_left 
      (fun 
        (accum_calls, accum_vars_eliminated) 
        ({ call_returns = o } as n) -> 

         
         (* Modify list of variables capturing the output, add to list
              of eliminated variables *)
         let o', accum_vars_eliminated' = 
           
           (* Iterate over output variables from right to left, need
              to preserve the order *)
           List.fold_right 
             (fun v (accum_outputs, accum_vars_eliminated) ->

                try 

                  let v' =

                    fst

                      (* Find an equation [u = v] where v is the
                         variable capturing an output at the current
                         state *)
                      (List.find
                         (function 
                           | (_, e) when E.is_var e -> 

                             StateVar.equal_state_vars 
                               (E.state_var_of_expr e)
                               v

                           | _ -> false) 

                         node.equations)
                  in

                  (debug lustreNode
                    "Eliminating %a with %a"
                    StateVar.pp_print_state_var v
                    StateVar.pp_print_state_var v'
                  in
                  
                  List.iter
                    (fun (p, n, v'') -> E.set_state_var_instance v' p n v'')
                    (E.get_state_var_instances v);

                  (v' :: accum_outputs, v :: accum_vars_eliminated))

                (* Variable not found in a variable alias equation *)
                with Not_found -> 

                    (v :: accum_outputs, accum_vars_eliminated))
             
             o
             ([], accum_vars_eliminated)
         in
         { n with call_returns = o' }:: accum_calls, accum_vars_eliminated')
      ([], [])
      node.calls
  in
  (*  
  Format.printf
    "@[<v>Elminated variables:@,%a@]@."
    (pp_print_list (I.pp_print_ident false) "@,") 
    vars_eliminated;
*)

  (* Remove eliminated variables from local variable declarations *)
  let locals' = 
    List.filter
      (fun (sv, _) -> not (List.memq sv vars_eliminated))
      node.locals
  in

  (* Remove eliminated equations *)
  let equations' = 
    List.filter
      (function
        | (_, e) when E.is_var e -> 
          not (List.mem (E.state_var_of_expr e) vars_eliminated)
        | _ -> true)
      node.equations
  in

  { node with calls = calls'; locals = locals'; equations = equations' }


(* Return all expressions of a node *)
let exprs_of_node { equations; calls; asserts; props; requires; ensures } =

  (* Start with expressions in equations *)
  let exprs_equations = 
    List.fold_left 
      (fun accum (_, expr) -> expr :: accum)
      []
      equations
  in

  (* Add expressions in calls *)
  let exprs_calls = 
    List.fold_left
      (fun
        accum
        { call_clock = act_cond; call_inputs = args; call_defaults = inits } -> 

(*
        (List.map (E.cur_expr_of_state_var E.cur_offset) args) @
        (List.map (E.pre_term_of_state_var E.cur_offset) args) @
         (* Add previous state expression of arguments *)
         List.map 
           (fun e -> 
              (fst 
                 ((E.mk_pre

                     (* Immediately fail if expression under pre needs
                        to be abstracted *)
                     (fun _ -> assert false) [] e)))) 
           args @ *)
        inits @ 
         accum)
      exprs_equations
      calls
  in

  (* Add expressions in assertions *)
  let exprs_asserts = asserts @ exprs_calls in

  (* Add expressions in assumptions *)
  let exprs_requires = requires @ exprs_asserts in

  (* Add expressions in guarantees *)
  let exprs_ensures = ensures @ exprs_requires in

  (* Return collected expressions *)
  exprs_ensures


(* Return all stateful variables from expressions in a node *)
let stateful_vars_of_node
    { inputs; outputs; observers; oracles; equations; calls; asserts; props } =

  (* Input, output and oracle variables are always stateful *)
  let stateful_vars =
    add_to_svs
      SVS.empty
      ((List.map fst inputs)
       @ (List.map fst outputs)
       @ oracles 
       @ observers)
  in

  (* Add stateful variables from equations *)
  let stateful_vars = 
    List.fold_left 
      (fun accum (_, expr) -> 
         SVS.union accum (E.stateful_vars_of_expr expr))
      stateful_vars
      equations
  in

  (* Add property variables *)
  let stateful_vars = add_to_svs stateful_vars (List.map fst props) in

  (* Add stateful variables from assertions *)
  let stateful_vars = 
    List.fold_left 
      (fun accum expr -> 
         SVS.union accum (E.stateful_vars_of_expr expr))
      stateful_vars
      asserts
  in

  (* Add variables from node calls *)
  let stateful_vars = 
    List.fold_left
      (fun
        accum
        { call_returns = rets; 
          call_observers = obs; 
          call_clock = act_cond; 
          call_inputs = args; 
          call_defaults = inits } -> 

        (SVS.union accum
           (* Input and output variables are always stateful *)
           (add_to_svs
              (match act_cond with
               | Some var -> SVS.singleton var
               | None -> SVS.empty)
              (rets @ obs @ args))))
      stateful_vars
      calls
  in

  stateful_vars

(* Return name of the first node annotated with --%MAIN.  Raise
   [Not_found] if no node has a --%MAIN annotation or [Failure
   "find_main" if more than one node has a --%MAIN annotation.
*)
let find_main nodes =

  match 
  
    (* Iterate over nodes to find first node with --%MAIN
       annotation, fail if second node with --%MAIN found *)
    List.fold_left
      (fun a { name; is_main } -> 
         if is_main then
           if a = None then Some name else 
             raise
               (Failure 
                  "find_main: More than one --%MAIN annotation")
         else
           a)
      None
      nodes 

  with 

    (* No node with --%MAIN annotiaon *)
    | None -> 

      (* Return name of last node, fail if list of nodes empty *)
      (match nodes with 
        | [] -> raise Not_found 
        | { name } :: _ -> name)

    | Some n -> n


(* State variables in assertions *)
let state_vars_in_asserts { asserts } =
  
  (* Collect all state variables in each assertion *)
  List.fold_left
    (fun a e -> 
       (SVS.elements
          (LustreExpr.state_vars_of_expr e)) @ a)
    []
    asserts


(* 
  produces the set of all state variables contained in any of the nodes in the
  given list 
*)
let state_vars_of_node (node : t) =
  
  (* the set of all state variables in this nodes locals, outputs, & inputs *)
  let ret = 
    List.fold_left 
      (fun acc (sv,_) -> SVS.add sv acc) 
      SVS.empty 
      (node.locals @ node.outputs @ node.inputs)
  in

  (* ret with oracles added *)
  List.fold_left
    (fun acc sv -> SVS.add sv acc)
    ret
    (node.oracles @ node.observers)


(* Execption for reduce_to_coi: need to reduce node first *)
exception Push_node of I.t


(* Reduce list of nodes to cone of influence 

   Keep a stack of nodes to reduce, each entry on the stack is a tuple
   containing the set of state variables in the cone of influence, the
   set of state variables alread seen
*)
let rec reduce_to_coi' nodes accum : (StateVar.t list * StateVar.t list * t * t) list -> t list = function 

  | [] -> 

    (* Eliminate all unused nodes from accumulator and return *)
    accum


  (* All dependencies for this node processed, add to accumulator *)
  | ([], 
     sv_visited, 
     ({ outputs; 
        inputs; 
        oracles;
        observers;
        locals; 
        equations;
        asserts; 
        props; 
        requires; 
        ensures; 
        is_main; 
        output_input_dep;
        fresh_state_var_index } as node_orig), 
     ({ name = node_name } as node_coi)) :: ntl -> 

    (* Eliminate unused inputs, outputs and locals, record indexes of
       eliminated inputs and outputs and reduce signature *)
    let node_coi' = 

      { node_coi with 

          (* Keep signature of node even if variables are not
             constrained any more *)
          outputs = outputs;
          inputs = inputs;
          oracles = oracles;
          observers = observers;
          output_input_dep = output_input_dep;

          (* Keep only local variables with definitions *)
          locals = 
            List.filter
              (fun (sv, _) -> 
                 List.exists (StateVar.equal_state_vars sv) sv_visited) 
              locals;

          (* Keep assertions, properties and main annotations *)
          asserts = asserts;

          (* Keep only property variables with definitions *)
          props = props;

          requires = requires;
          ensures = ensures;
          is_main = is_main;
          fresh_state_var_index = fresh_state_var_index }

    in

    reduce_to_coi'
      nodes
      (node_coi' :: accum)
      ntl


  (* Head of state variable list has been visited, its dependent state
     variables are either in [state_var] or [sv_visited] *)
  | (state_var :: svtl, sv_visited, ({ name = node_name } as node_orig), node_coi) :: ntl 
    when List.mem state_var sv_visited -> 

    (* Continue with next state variable of node *)
    reduce_to_coi' 
      nodes 
      accum
      ((svtl, sv_visited, node_orig, node_coi) :: ntl)


  (* Head of state variable list has not been seen *)
  | ((state_var :: svtl as svl), 
     sv_visited, 
     ({ name = node_name } as node_orig), 
     node_coi) :: ntl as nl -> 

    try 

      (* Need to have all nodes with variables this variable
         instantiates *)
      List.iter
        (fun (_, n, sv') -> 
           
           (debug lustreNode
               "State variable %a is an instance of %a"
               StateVar.pp_print_state_var state_var
               StateVar.pp_print_state_var sv'
            in
            
            if 
              
              (* Called node is sliced already? *)
              not (exists_node_of_name n accum) &&

                (* Called node is not sliced away *)
                (exists_node_of_name n accum)
                
            then 
              
              (debug lustreNode
                  "State variable %a is an instance of %a, slicing %a first"
                  StateVar.pp_print_state_var state_var
                  StateVar.pp_print_state_var sv'
                  (I.pp_print_ident false) n
               in
               
               (* Slice called node first *)
               raise (Push_node n))))

        (E.get_state_var_instances state_var);

      (* Copy node call from original node to reduced node, do not
         modify original node, because additional variables may be found
         to be in the cone of influence *)
      let calls_coi', svtl, sv_visited' =

        try 

          (

            let 
              ({ call_returns = call_outputs;
                 call_observers = call_observers;
                 call_clock = call_act;
                 call_node_name = call_name;
                 call_inputs = call_inputs;
                 call_defaults = call_defaults } as call_coi) =

              (* Find variable in result of a node call *)
              List.find 
                (fun { call_returns = o; call_observers = b } -> 
                   List.exists 
                     (fun sv -> StateVar.equal_state_vars state_var sv) 
                     (o @ b))
                node_orig.calls
            in

            if 

              (* Called node is sliced already? *)
              List.exists 
                (function { name } -> name = call_name)
                accum

            then 

              (* All variables in inputs and defaults are in cone of
                 influence *)
              let svtl' = 
                List.fold_left
                  (fun a e -> 
                     (SVS.elements
                        (LustreExpr.state_vars_of_expr e)) @ a)
                  ((match call_act with Some v -> v :: svtl | _ -> svtl)
                   @ call_inputs)
                  call_defaults
              in

              (* Add called node to sliced node *)
              (call_coi :: node_coi.calls), 
              svtl', 
              (call_outputs @ call_observers @ sv_visited)

            else

              (* Slice called node first *)
              raise (Push_node call_name)

          )            

        (* Variable is not an output of a node call *)
        with Not_found -> node_coi.calls, svtl, sv_visited

      in

      (* Copy equation from original node to reduced node and add
           variables to stack *)
      let equations_coi', svtl, sv_visited' = 

        try 

          (* Get definition of state variable *)
          let state_var_def = List.assoc state_var node_orig.equations in

          (* Add definition of variable *)
          let equations_coi' = 
            (state_var, state_var_def) :: node_coi.equations 
          in

          (* All variables in defintion are in cone of influence *)
          let svtl' = 
            (SVS.elements
               (LustreExpr.state_vars_of_expr state_var_def)) @ svtl
          in

          (* Return with equation added and new variables in cone of
             influence *)
          equations_coi', svtl', (state_var :: sv_visited')

        (* Variable is not defined in an equation *)
        with Not_found -> 

          (* Keep previous equations *)
          node_coi.equations, svtl, sv_visited'

      in

      (* Add to equations, assertions and contract containing the
         variable to cone of influence *)
      let node_coi' = 
        { node_coi with 
            equations = equations_coi'; 
            calls = calls_coi' }
      in

      (* Continue with next variable, mark this variable as visited *)
      reduce_to_coi' 
        nodes
        accum
        ((svtl, sv_visited', node_orig, node_coi') :: ntl)

    with Push_node push_name ->
      
      (* Outputs and observers of node *)
      let { outputs = push_node_outputs; 
            observers = push_node_observers } as push_node = 

        try 

          (* Find node by name *)
          node_of_name push_name nodes 

        with Not_found -> assert false 
          
      in 

      (* Reduce called node first, then revisit calling node *)
      reduce_to_coi' 
        nodes
        accum
        (((List.map fst push_node_outputs) @ 
          push_node_observers @
          (state_vars_in_asserts push_node), 
          [], 
          push_node,
          (empty_node push_name)) :: nl)

(*

(* 
Given that [nodes] is the set of nodes in the lustre program and
[main_name] is the name of the main node, return a map which
maps the identifier of each property and assert stream to the
a list of all nodes in that assert or property's cone of influence.   
*)
let reduce_to_separate_property_cois nodes main_name =
  
  let nodes' = 
    List.fold_right
      (fun node accum -> compute_output_input_dep accum node :: accum)
      nodes
      []
  in

  try 

    (* Main node and its properties *)
    let main_node = node_of_name main_name nodes' in

    (* State variables in properties *)
    let state_vars = 
      main_node.props @ (state_vars_in_asserts main_node)
    in

    (* return the cone of influence of state variable [sv] *)
    let get_state_var_coi sv =
      List.rev
        (reduce_to_coi' 
           nodes'
           []
           [([sv], [], main_node, (empty_node main_name))])      
    in

    (* add [sv]'s coi to [coi_map], topologically sorting the equations 
       of each node in the coi *)
    let fold_sv coi_map sv =
      let coi = get_state_var_coi sv in
      let coi' = List.map (equations_order_by_dep coi) coi in
      SVMap.add sv coi' coi_map
    in

    List.fold_left fold_sv SVMap.empty state_vars 

  with Not_found -> 

    raise 
      (Invalid_argument
         (Format.asprintf
            "Main node %a not found."
            (I.pp_print_ident false) main_name))
*)


(* Reduce set of nodes to cone of influence of given state variables *)
let reduce_to_coi nodes main_name state_vars = 
  
    debug lustreNode
      "@[<v>reduce_to_coi nodes'@,%a@]"
      (pp_print_list (pp_print_node false) "@,") nodes
    in
    
  (* Compute input output dependencies for all nodes *)
  let nodes' = 
    List.fold_right
      (fun node accum -> compute_output_input_dep accum node :: accum)
      (List.rev nodes)
      []
  in

  try 

    (* Get main node by its identifier *)
    let main_node = node_of_name main_name nodes' in

    (* Variables in assertions are always in the cone of influence *)
    let state_vars' = 
      state_vars @ (state_vars_in_asserts main_node)
    in

    (* Call recursive function with initial arguments *)
    let nodes'' =
      List.rev
        (reduce_to_coi' 
           nodes'
           []
           [(state_vars', [], main_node, (empty_node main_name))])
    in

    debug lustreNode
      "@[<v>reduce_to_coi nodes''@,%a@]"
      (pp_print_list (pp_print_node false) "@,") nodes''
    in
    
    (* Return node with equations in topological order *)
    List.fold_right
      (fun node accum -> equations_order_by_dep nodes'' node :: accum)
      nodes''
      []
    
  with Not_found -> 

    raise 
      (Invalid_argument
         (Format.asprintf
            "Main node %a not found."
            (I.pp_print_ident false) main_name))


(* Reduce set of nodes to cone of influence of properties of main node *)
let reduce_wo_coi nodes main_name = 

  (* Get properties of main node *)
  let main_node = node_of_name main_name nodes in

  reduce_to_coi
    nodes 
    main_name
    (SVS.elements (state_vars_of_node main_node))


(* Reduce set of nodes to cone of influence of properties of main node *)
let reduce_to_props_coi nodes main_name = 

  (* Get properties of main node *)
  let { props; observers; inputs; outputs; locals } as main_node = 
    node_of_name main_name nodes 
  in

  match 

    List.fold_left
      (fun accum (state_var, prop_source) -> match prop_source with 

         (* Property annotations, contracts and generated constraints
            are in the cone of influence *)
         | TermLib.PropAnnot _ 
         | TermLib.Contract _ 
         | TermLib.Generated _ -> state_var :: accum

         (* Properties instantiated from subnodes are not *)
         | TermLib.Instantiated _-> accum) 
      []
      props 

  with
    
    (* No properties, don't reduce *)
    | [] -> reduce_wo_coi nodes main_name
              
    (* Reduce to cone of influence of all properties *)
    | props' -> 
(*      
      let props' = 
      SVS.elements 
        (SVS.union
           (svs_of_list (List.map fst props))
           (svs_of_list observers))
      in
  *)    
      reduce_to_coi nodes main_name props'
        
      
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
