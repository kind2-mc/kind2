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
module IdxMap = I.LustreIndexMap
module ITrie = I.LustreIdentTrie
module IdxTrie = I.LustreIndexTrie

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
    call_returns : StateVar.t IdxTrie.t;

    (* Variables capturing the outputs *)
    call_observers : StateVar.t list;

    (* Boolean activation condition *)
    call_clock : LustreExpr.t;

    (* Name of called node *)
    call_node_name : LustreIdent.t;
    
    (* Position of node call in input file *)
    call_pos : position;

    (* Expressions for input parameters *)
    call_inputs : StateVar.t IdxTrie.t;

    (* Expression for initial return values *)
    call_defaults : LustreExpr.t IdxTrie.t;

  }


(* A Lustre node *)
type t = 

  { 

    (* Name of node *)
    name : LustreIdent.t;

    (* Input variables of node together with their index in the
       original model *)
    inputs : StateVar.t IdxTrie.t;

    (* Oracle inputs *)
    oracles : StateVar.t list;

    (* Output variables of node together with their index in the
       original model *)
    outputs : StateVar.t IdxTrie.t;

    (* Observer outputs *)
    observers : StateVar.t list;

    (* Local variables of node *)
    locals : StateVar.t list;

    (* Equations for local and output variables, with a list of
       indexes and their bounds *)
    equations : 
      (StateVar.t * ((StateVar.t * LustreExpr.t) list * LustreExpr.t)) list;

    (* Node calls with activation condition: variables capturing the
       outputs, the Boolean activation condition, the name of the
       called node, expressions for input parameters and expression
       for initialization *)
    calls : node_call list;

    (* Assertions of node *)
    asserts : LustreExpr.t list;

    (* Proof obligations for node *)
    props : StateVar.t list;

    (* Contract for node, assumptions *)
    assumptions : (I.t * E.t) list;

    (* Contract for node, guarantees *)
    guarantees : (I.t * E.t) list;

    (* Node is annotated as main node *)
    is_main : bool;

    (* Dependencies of the output variables on input variables *)
    output_input_dep : I.index list IdxTrie.t;

    (* Dependencies of the observer variables on input variables *)
    observer_input_dep : I.index list list;

    (* Index of last abstraction state variable *)
    fresh_state_var_index : Numeral.t ref;

    (* Index of last oracle state variable *)
    fresh_oracle_index : Numeral.t ref;

    (* Map of state variables to their oracles *)
    state_var_oracle_map : StateVar.t StateVar.StateVarHashtbl.t;

    (* Map of state variables to their oracles *)
    expr_state_var_map : StateVar.t E.ExprHashtbl.t;

  }


(* An empty node *)
let empty_node name = 
  { name = name;
    inputs =  IdxTrie.empty;
    oracles = [];
    outputs = IdxTrie.empty;
    observers = [];
    locals = [];
    equations = [];
    calls = [];
    asserts = [];
    props = [];
    assumptions = [];
    guarantees = [];
    is_main = false;
    output_input_dep = IdxTrie.empty;
    observer_input_dep = [];
    fresh_state_var_index = ref Numeral.(- one);
    fresh_oracle_index = ref Numeral.(- one); 
    state_var_oracle_map = StateVar.StateVarHashtbl.create 7;
    expr_state_var_map = E.ExprHashtbl.create 7 }



(* Pretty-print a node input *)
let pp_print_input safe ppf (_, var) =

  Format.fprintf ppf
    "%t%a: %a"
    (function ppf -> 
      if StateVar.is_const var then Format.fprintf ppf "const ")
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)


(* Pretty-print a node output *)
let pp_print_output safe ppf (_, var) =

  Format.fprintf ppf
    "%a: %a"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)


(* Pretty-print a node local variable *)
let pp_print_local safe ppf var =

  Format.fprintf ppf
    "%a: %a"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)


(* Pretty-print a node equation *)
let pp_print_node_equation safe ppf (var, (idx_vars, expr)) = 

  Format.fprintf ppf
    "@[<hv 2>%a%a =@ %a;@]"
    (E.pp_print_lustre_var safe) var
    (pp_print_list
       (function ppf -> function (v, _) ->
         Format.fprintf ppf 
           "[%a]"
           (E.pp_print_lustre_var safe) v)
       "")
    idx_vars
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node call *)
let pp_print_call safe ppf = function 

  (* Node call on the base clock *)
  | { call_returns = out_vars; 
      call_observers = observer_vars; 
      call_clock = act_expr; 
      call_node_name = node; 
      call_inputs = in_vars } when E.equal_expr act_expr E.t_true -> 

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>%a(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (List.rev_map snd (IdxTrie.bindings out_vars) @ observer_vars)
      (I.pp_print_ident safe) node
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (List.rev_map snd (IdxTrie.bindings in_vars))

  (* Node call not on the base clock is a condact *)
  |  { call_returns = out_vars; 
       call_observers = observer_vars; 
       call_clock = act_expr;
       call_node_name = node; 
       call_inputs = in_vars; 
       call_defaults = init_exprs } ->
     
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>condact(%a,@,%a(%a),@,%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (List.rev_map snd (IdxTrie.bindings out_vars) @ observer_vars)
      (E.pp_print_lustre_expr safe) act_expr
      (I.pp_print_ident safe) node
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (List.rev_map snd (IdxTrie.bindings in_vars))
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") 
      (List.rev_map snd (IdxTrie.bindings init_exprs)
       @ (List.map (fun _ -> E.t_true) observer_vars))
          

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
let pp_print_assumption safe ppf (ident, expr) = 

  Format.fprintf ppf
    "@[<hv 2>assume %a :@ %a;@]"
    (I.pp_print_ident safe) ident
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a guarantee *)
let pp_print_guarantee safe ppf (ident, expr) = 

  Format.fprintf ppf
    "@[<hv 2>guarantee %a :@ %a;@]"
    (I.pp_print_ident safe) ident
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
      assumptions; 
      guarantees;
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
     @[<v>%t@]\
     @[<hv 2>let@ \
     %a%t\
     %a%t\
     %a%t\
     %t\
     %a%t\
     %a%t\
     %a@;<1 -2>\
     tel;@]@]"  

    (* %a *)
    (I.pp_print_ident safe) name

    (* %a *)
    (pp_print_list (pp_print_input safe) ";@ ") 
    (List.rev (IdxTrie.bindings inputs) @
     (List.map (fun sv -> (I.empty_index, sv)) oracles))

    (* %a *)
    (pp_print_list (pp_print_output safe) ";@ ") 
    (List.rev (IdxTrie.bindings outputs) @
     (List.map (fun sv -> (I.empty_index, sv)) observers))

    (* %t *)
    (function ppf -> 
      if not (locals = []) then
        Format.fprintf ppf 
          "@[<hv 2>var@ %a;@]@ " 
          (pp_print_list (pp_print_local safe) ";@ ") 
          locals)

    (* %a%t *)
    (pp_print_list (pp_print_call safe) "@ ") calls
    (space_if_nonempty equations)

    (* %a%t *)
    (pp_print_list (pp_print_node_equation safe) "@ ") equations
    (space_if_nonempty equations)

    (* %a%t *)
    (pp_print_list (pp_print_assert safe) "@ ") asserts
    (space_if_nonempty asserts)

    (* %t *)
    (function ppf -> if is_main then Format.fprintf ppf "--%%MAIN@,")

    (* %a%t *)
    (pp_print_list (pp_print_assumption safe) "@ ") assumptions
    (space_if_nonempty assumptions)

    (* %a%t *)
    (pp_print_list (pp_print_guarantee safe) "@ ") guarantees
    (space_if_nonempty guarantees)

    (* %a*)
    (pp_print_list (pp_print_prop safe) "@ ") props
    


(* Return the node of the given name from a list of nodes *)
let node_of_name name nodes =

  List.find
    (function { name = node_name } -> name = node_name)
    nodes


(* Calculate dependencies of variables *)
let rec node_var_dependencies nodes node accum = 

  function 

    (* Return all calculated dependencies *)
    | [] -> accum

    (* Calculate dependency of variable [ident], which all variables
       in [dep] depend on *)
    | (state_var, dep) :: tl -> 

      if 

        (* Variable is an input variable *)
        IdxTrie.exists 
          (fun _ sv -> StateVar.equal_state_vars sv state_var)
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
            let (_, (_, expr)) = 
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

              (* Find state variables this state variable depends on
                 if captures the output of a node call *)
              let rec dependent_state_vars_of_output = function 
                | [] -> raise Not_found 
                | { call_returns; call_node_name } :: tl -> 

                  match 

                    (* Collect indexes the given state variable occurs
                       with in the output *)
                    IdxTrie.fold
                      (fun i v a -> 
                         if 
                           StateVar.equal_state_vars 
                             state_var
                             v 
                         then
                           i :: a 
                         else 
                           a)
                      call_returns
                      []

                  with

                    (* State variable does not occur in the ouput:
                       continue search *)
                    | [] -> dependent_state_vars_of_output tl

                    (* State variable occurs in output at index *)
                    | [index] -> 

                      (* Get dependencies of outputs on input for
                         called node *)
                      let { output_input_dep } =
                        node_of_name call_node_name nodes 
                      in

                      (* Get inputs of node call that depend on
                         outputs of node call *)
                      List.map
                        (fun i -> IdxTrie.find i node.inputs)
                        (IdxTrie.find index output_input_dep)

                    (* State variable occurs in more than one
                       output *)
                    | _ -> assert false 

              in

              dependent_state_vars_of_output node.calls

            (* Variable is not an output of a node call *)
            with Not_found -> 

              (* Find state variables this state variable depends on
                 if captures an observer of a node call *)
              let rec dependent_state_vars_of_observer = function 
                | [] -> raise Not_found 
                | { call_observers; call_node_name } :: tl -> 

                  (* Get dependencies of observers on input for called node *)
                  let { observer_input_dep } =
                    node_of_name call_node_name nodes 
                  in

                  match 
                    
                    List.fold_left2
                      (fun a v i -> 
                         if 
                           StateVar.equal_state_vars 
                             state_var
                             v 
                         then
                           i :: a 
                         else 
                           a)
                      []
                      call_observers
                      observer_input_dep

                  with

                    (* State variable does not occur in the ouput:
                       continue search *)
                    | [] -> dependent_state_vars_of_observer tl

                    (* State variable depends on input variables at index *)
                    | [index] -> 

                      (* Get inputs of node call at indexes *)
                      List.map
                        (fun i -> IdxTrie.find i node.inputs)
                        index

                    (* State variable occurs in more than one
                       observer *)
                    | _ -> assert false 

              in

              dependent_state_vars_of_observer node.calls

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

  (* Return indexes in inputs for each output *)
  IdxTrie.map
    (fun o -> 

       (* Get dependencies of output variable *)
       let deps = List.assoc o var_deps in 

       (* Iterate over all dependent variables to find input variables
          and their positions *)
       SVS.fold
         (fun v a -> 

            match 

              (* Collect indexes the given state variable occurs with
                 in the input *)
              IdxTrie.fold
                (fun i v' a ->
                   if StateVar.equal_state_vars v' v then i :: a else a)
                node.inputs
                []

            with 

              (* We expect the list to contain at most one index. *)
              | [] -> a 
              | [v] -> v :: a

              (* Variable occurs in input twice *)
              | _ -> assert false)
         deps
         [])
    node.outputs


(* Calculate dependencies of observers on inputs *) 
let observer_input_dep_of_var_dep node var_deps =

  (* Return indexes in inputs for each output *)
  List.map
    (fun sv -> 

       (* Get dependencies of output variable *)
       let deps = List.assoc sv var_deps in 

       (* Iterate over all dependent variables to find input variables
          and their positions *)
       SVS.fold
         (fun v a -> 

            match 

              (* Collect indexes the given state variable occurs with
                 in the input *)
              IdxTrie.fold
                (fun i v' a ->
                   if StateVar.equal_state_vars v' v then i :: a else a)
                node.inputs
                []

            with 

              (* We expect the list to contain at most one index. *)
              | [] -> a 
              | [v] -> v :: a

              (* Variable occurs in input twice *)
              | _ -> assert false)
         deps
         [])
    node.observers



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
       (List.map (fun (_, v) -> (v, [])) (IdxTrie.bindings node.outputs)))
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
       (List.map (fun (_, v) -> (v, [])) (IdxTrie.bindings node.outputs)))
  in
(*  
  (* Order variables such that variables defined in terms of other
     variables occur first *)
  let vars_ordered = order_by_dep [] var_dep in
*)
  (* Compute dependencies of output variables on inputs *)
  let output_input_dep = 
    output_input_dep_of_var_dep node var_dep 
  in

  (* Compute dependencies of output variables on inputs *)
  let observer_input_dep = 
    observer_input_dep_of_var_dep node var_dep 
  in

  (* Return node with equations in dependency order *)
  { node with 
      output_input_dep = output_input_dep; 
      observer_input_dep = observer_input_dep }


(* If x = y and x captures the output of a node, substitute y *)
let solve_eqs_node_calls node = 

  let calls', vars_eliminated =

    (* Iterate over all calls, collect modified calls and eliminated
       variables *)
    List.fold_left 
      (fun 
        (calls, vars_eliminated) 
        ({ call_returns } as n) -> 

         
         (* Modify list of variables capturing the output, add to list
              of eliminated variables *)
        let call_returns', vars_eliminated' = 
          
          (* Iterate over output variables from right to left, need
              to preserve the order *)
          IdxTrie.fold 
            (fun i v (call_returns', vars_eliminated)  ->
               
                try 

                  let v' =

                    fst

                      (* Find an equation [u = v] where v is the
                         variable capturing an output at the current
                         state *)
                      (List.find
                         (function 
                           | (_, (_, e)) when E.is_var e -> 

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

                  (IdxTrie.add i v' call_returns', v :: vars_eliminated))

                (* Variable not found in a variable alias equation *)
                with Not_found -> 

                    (IdxTrie.add i v call_returns', vars_eliminated))
             
             call_returns
             (IdxTrie.empty, vars_eliminated)
         in
         { n with call_returns = call_returns' } :: calls, 
         vars_eliminated')
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
      (fun sv -> not (List.memq sv vars_eliminated))
      node.locals
  in

  (* Remove eliminated equations *)
  let equations' = 
    List.filter
      (function
        | (_, (_, e)) when E.is_var e -> 
          not (List.mem (E.state_var_of_expr e) vars_eliminated)
        | _ -> true)
      node.equations
  in

  { node with calls = calls'; locals = locals'; equations = equations' }


(* Return all expressions of a node *)
let exprs_of_node { equations; calls; asserts; props; assumptions; guarantees } =

  (* Start with expressions in equations *)
  let exprs_equations = 
    List.fold_left 
      (fun accum (_, (_, expr)) -> expr :: accum)
      []
      equations
  in

  (* Add expressions in calls *)
  let exprs_calls = 
    List.fold_left
      (fun
        accum
        { call_clock = act_cond; call_inputs = args; call_defaults = inits } -> 

        act_cond :: 
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
        (IdxTrie.values inits) @ 
         accum)
      exprs_equations
      calls
  in

  (* Add expressions in assertions *)
  let exprs_asserts = asserts @ exprs_calls in

  (* Add expressions in assumptions *)
  let exprs_assumptions = List.map snd assumptions @ exprs_asserts in

  (* Add expressions in guarantees *)
  let exprs_guarantees = List.map snd guarantees @ exprs_assumptions in

  (* Return collected expressions *)
  exprs_guarantees


(* Return all stateful variables from expressions in a node *)
let stateful_vars_of_node
    { inputs; outputs; observers; oracles; equations; calls; asserts; props } =

  (* Input, output and oracle variables are always stateful *)
  let stateful_vars =
    add_to_svs
      SVS.empty
      ((IdxTrie.values inputs)
       @ (IdxTrie.values outputs)
       @ oracles 
       @ observers)
  in

  (* Add stateful variables from equations *)
  let stateful_vars = 
    List.fold_left 
      (fun accum (_, (_, expr)) -> 
         SVS.union accum (E.stateful_vars_of_expr expr))
      stateful_vars
      equations
  in

  (* Add property variables *)
  let stateful_vars = add_to_svs stateful_vars props in

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
           (add_to_svs

              (* Variables in activation condition are always stateful *)
              (E.state_vars_of_expr act_cond)

              (* Input and output variables are always stateful *)
              ((IdxTrie.values rets) @ 
               obs @ 
               (IdxTrie.values args)))))
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
     { outputs; 
       inputs; 
       oracles;
       observers;
       locals; 
       asserts; 
       props; 
       assumptions; 
       guarantees; 
       is_main; 
       output_input_dep;
       observer_input_dep;
       fresh_state_var_index }, 
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
          observer_input_dep = observer_input_dep;

          (* Keep only local variables with definitions *)
          locals = 
            List.filter
              (fun sv -> 
                 List.exists (StateVar.equal_state_vars sv) sv_visited) 
              locals;

          (* Keep assertions, properties and main annotations *)
          asserts = asserts;
          props = props;
          assumptions = assumptions;
          guarantees = guarantees;
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
  | ((state_var :: svtl), 
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
              not 
                (List.exists 
                   (function { name } -> name = n)
                   accum)
                
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
                (fun { call_returns; call_observers } -> 
                   IdxTrie.exists
                     (fun _ sv -> StateVar.equal_state_vars state_var sv) 
                     call_returns 
                   ||
                   List.exists 
                     (fun sv ->  StateVar.equal_state_vars state_var sv)
                     call_observers) 
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
                  (IdxTrie.values call_inputs @ svtl)
                  (call_act :: IdxTrie.values call_defaults)
              in

              (* Add called node to sliced node *)
              (call_coi :: node_coi.calls), 
              svtl', 
              (IdxTrie.values call_outputs @
               call_observers @ 
               sv_visited)

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
          let state_var_indexes, state_var_def = 
            List.assoc state_var node_orig.equations 
          in

          (* Add definition of variable *)
          let equations_coi' = 
            (state_var, (state_var_indexes, state_var_def)) ::
            node_coi.equations 
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
      
      (* Find called node *)
      let { outputs = push_node_outputs; 
            observers = push_node_observers } as push_node = 
        try 
          node_of_name push_name nodes 
        with Not_found -> assert false 
      in 

      (* Reduce called node first, then revisit calling node *)
      reduce_to_coi' 
        nodes
        accum
        ((IdxTrie.fold 
            (fun _ v a -> v :: a) 
            push_node_outputs 
            (push_node_observers @ 
             (state_vars_in_asserts push_node)), 
          [], 
          push_node,
          (empty_node push_name)) :: nl)

(* 
  produces the set of all state variables contained in any of the nodes in the
  given list 
*)
let state_vars_of_node (node : t) =

  (* the set of all state variables in this nodes locals, outputs, & inputs *)
  let ret = 
    IdxTrie.fold
      (fun _ v a -> SVS.add v a)
      node.inputs
      (IdxTrie.fold
         (fun _ v a -> SVS.add v a)
         node.outputs
         SVS.empty)
  in

  (* ret with oracles added *)
  List.fold_left
    (fun acc sv -> SVS.add sv acc)
    ret
    (node.locals @ node.oracles @ node.observers)

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


(* Reduce set of nodes to cone of influence of given state variables *)
let reduce_to_coi nodes main_name state_vars = 
  
  (* Compute input output dependencies for all nodes *)
  let nodes' = 
    List.fold_right
      (fun node accum -> compute_output_input_dep accum node :: accum)
      nodes
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

  match props @ observers with
    
    (* No properties, don't reduce *)
    | [] -> reduce_wo_coi nodes main_name
              
    (* Reduce to cone of influence of all properties *)
    | _ -> 
      
      let props' = 
      SVS.elements 
        (SVS.union
           (svs_of_list props)
           (svs_of_list observers))
      in
      
      reduce_to_coi nodes main_name props'
        
      
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
