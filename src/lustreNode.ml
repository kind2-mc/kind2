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

module SVS = StateVar.StateVarSet

module ISet = I.LustreIdentSet

(* A node

   Nodes are normalized for easy translation into a transition system,
   mainly by introducing new variables. A LustreExpr.t does not
   contain node calls, temporal operators or expressions under a pre
   operator. Node equations become a map of identifiers to expressions
   in node_eqs, all node calls are in node_calls as a list of tuples
   containing fresh variables the node output is assigned to and the
   expressions for the node input.

   The node signature as input and output variables as well as its
   local variables is in [node_inputs], [node_outputs] and
   [node_vars], respectively. Local constants are propagated and do
   not need to be stored.

   Assertions, properties to prove and contracts as assumptions and
   guarantees are lists of expressions in [node_asserts], [node_props],
   [node_requires], and [node_ensures].

   The flag [node_is_main] is set if the node has been annotated as
   main, it is not checked if more than one node or no node at all may
   have that annotation.

*)
type t = 

  { 

    (* Name of node *)
    name : LustreIdent.t;

    (* Input variables of node, some flagged as constant

       The order of the list is important, it is the order the
       parameters in the declaration. *)
    inputs : (StateVar.t * bool) list;

    (* Output variables of node 

       The order of the list is important, it is the order the
       parameters in the declaration. *)
    outputs : StateVar.t list;

    (* Local variables of node 

       The order of the list is irrelevant, we are doing dependency
       analysis and cone of influence reduction later. *)
    locals : StateVar.t list; 

    (* Equations for local and output variables *)
    equations : (StateVar.t * LustreExpr.t) list;

    (* Node calls with activation condition: variables capturing the
       outputs, the Boolean activation condition, the name of the
       called node, expressions for input parameters and expression
       for initialization *)
    calls : 
      (StateVar.t list * 
       LustreExpr.t * 
       LustreIdent.t * 
       LustreExpr.t list * 
       LustreExpr.t list) list;

    (* Assertions of node *)
    asserts : LustreExpr.t list;

    (* Proof obligations for node *)
    props : LustreExpr.t list;

    (* Contract for node, assumptions *)
    requires : LustreExpr.t list;

    (* Contract for node, guarantees *)
    ensures : LustreExpr.t list;

    (* Node is annotated as main node *)
    is_main : bool;

    (* Dependencies of the output variables on input variables *)
    output_input_dep : int list list }


(* An empty node *)
let empty_node name = 
  { name = name;
    inputs = [];
    outputs = [];
    locals = [];
    equations = [];
    calls = [];
    asserts = [];
    props = [];
    requires = [];
    ensures = [];
    is_main = false;
    output_input_dep = []}


(* Pretty-print a node input *)
let pp_print_input safe ppf (var, is_const) =

  Format.fprintf ppf
    "%t%a: %a"
    (function ppf -> if is_const then Format.fprintf ppf "const ")
    (E.pp_print_lustre_var safe) var
    Type.pp_print_type (StateVar.type_of_state_var var)


(* Pretty-print a node output *)
let pp_print_output safe ppf var =

  Format.fprintf ppf
    "%a: %a"
    (E.pp_print_lustre_var safe) var
    Type.pp_print_type (StateVar.type_of_state_var var)


(* Pretty-print a node local variable *)
let pp_print_local safe ppf var =

  Format.fprintf ppf
    "%a: %a"
    (E.pp_print_lustre_var safe) var
    Type.pp_print_type (StateVar.type_of_state_var var)


(* Pretty-print a node equation *)
let pp_print_node_equation safe ppf (var, expr) = 

  Format.fprintf ppf
    "@[<hv 2>%a =@ %a;@]"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node call *)
let pp_print_call safe ppf = function 

  (* Node call on the base clock *)
  | (out_vars, act_expr, node, exprs, _) when act_expr = E.t_true -> 

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>%a(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      out_vars
      (I.pp_print_ident safe) node
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") exprs

  (* Node call not on the base clock, a condact *)
  | (out_vars, act_expr, node, exprs, init_exprs) ->
     
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>condact(%a,%a(%a),@ %a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      out_vars
      (E.pp_print_lustre_expr safe) act_expr
      (I.pp_print_ident safe) node
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") exprs
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") init_exprs


(* Pretty-print an assertion *)
let pp_print_assert safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>assert@ %a;@]"
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a property *)
let pp_print_prop safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--%%PROPERTY@ %a;@]"
    (E.pp_print_lustre_expr safe) expr
    

(* Pretty-print an assumption *)
let pp_print_requires safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--@@requires@ %a;@]"
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a guarantee *)
let pp_print_ensures safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--@@ensures %a;@]"
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node *)
let pp_print_node 
    safe
    ppf 
    { name;
      inputs; 
      outputs; 
      locals; 
      equations; 
      calls; 
      asserts; 
      props; 
      requires; 
      ensures;
      is_main } = 

  (* Output a space if list is not empty *)
  let space_if_nonempty = function
    | [] -> (function _ -> ())
    | _ -> (function ppf -> Format.fprintf ppf "@ ")
  in

  Format.fprintf ppf 
    "@[<hv>@[<hv 2>node %a@ @[<hv 1>(%a)@]@;<1 -2>\
     returns@ @[<hv 1>(%a)@];@]@ \
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
    (pp_print_list (pp_print_input safe) ";@ ") inputs
    (pp_print_list (pp_print_output safe) ";@ ") outputs
    (function ppf -> 
      if locals = [] then () else 
        Format.fprintf ppf 
          "@[<hv 2>var@ %a@]" 
          (pp_print_list (pp_print_local safe) "@ ") locals)
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
    (pp_print_list (pp_print_prop safe) "@ ") props
    


(* Calculate dependencies of variables *)
let rec node_var_dependencies init_or_step nodes node accum = 

  (* Return expression either for the initial state or a step state *)
  let init_or_step_of_expr { E.expr_init; E.expr_step } = 
    if init_or_step then expr_init else expr_step 
  in

  function 

    (* Return all calculated dependencies *)
    | [] -> accum

    (* Calculate dependency of variable [ident], which all variables
       in [dep] depend on *)
    | (var, dep) :: tl -> 

(*
      Format.printf 
        "@[<h>node_var_dependencies %a (%a)@]@."
        (I.pp_print_ident false) ident
        (pp_print_list (I.pp_print_ident false) "@ ") dep;
*)

      if 

        (* Variable is an input variable *)
        List.exists 
          (fun (v, _) -> (==) var v)
          node.inputs 

      then 

        (* No dependencies for inputs *)
        node_var_dependencies 
          init_or_step 
          nodes
          node
          ((var, SVS.empty) :: accum) 
          tl

      else

        (* Variables this variable depends on *)
        let vars = 

          try 

            (* Get expression defining variable *)
            let expr = 
              List.assq var node.equations 
            in

            (* Get variables in expression *)
            SVS.elements
              (Term.state_vars_at_offset_of_term
                 (Numeral.zero)
                 (init_or_step_of_expr expr))

          (* Variable is not input or not defined in an equation *)
          with Not_found -> 

            try

              (* Iterate over node calls to find identifier in
                 variables capturing the output *)
              let rec aux ident = function
                | [] -> raise Not_found
                | (o, _, _, _, _) as n :: tl -> 

                  (* Iterate over variables capturing the output to
                     find variable and return the node call and the
                     position of the variable in the output
                     parameters *)
                  let rec aux2 i = function
                    | [] -> raise Not_found 
                    | v :: _ when v == var -> (n, i)
                    | _ :: tl -> aux2 (succ i) tl
                  in

                  try aux2 0 o with Not_found -> aux ident tl

              in

              (* Return node call and position of variable in output
                 parameters *)
              let (_, _, node_ident, call_params, _), input_pos = 
                aux var node.calls 
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
                List.find
                  (function { name = ident } -> node_ident = ident)
                  nodes
              in

              (* Get expressions that output of node depends on *)
              let dep_expr = 
                List.fold_left
                  (fun a d -> 
                     (init_or_step_of_expr (List.nth call_params d)) :: a)
                  []
                  (List.nth output_input_dep input_pos)
              in

              (* Get variables in expression *)
              SVS.elements
                (List.fold_left
                   (fun a e -> 
                      SVS.union
                        (Term.state_vars_at_offset_of_term
                           (Numeral.zero) e) 
                        a)
                   SVS.empty
                   dep_expr)

            (* Variable is not input or defined in an equation or node
               call, it could be in an assertion *)
            with Not_found -> []

        in

        (* Some variables have had their dependencies calculated
           already *)
        let vars_visited, vars_not_visited = 
          List.partition
            (fun ident -> List.mem_assq ident accum)
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

          (* Add variable and its dependencies to accumulator *)
          node_var_dependencies 
            init_or_step 
            nodes
            node 
            ((var, dependent_vars) :: accum)
            tl

        else
          
        if 

          (* Circular dependency: a variable that this variable
             depends on occurs as a dependency *)
          List.exists
            (fun v -> List.memq v dep)
            (var :: vars_not_visited)

        then

          failwith "circular dependency"

        else

          (* First get dependencies of all dependent variables *)
          node_var_dependencies 
            init_or_step 
            nodes 
            node
            accum 
            ((List.map 
                (fun v -> (v, var :: dep)) 
                vars_not_visited) @ 
             ((var, dep) :: tl))

             
(* Calculate dependencies of outputs on inputs *) 
let output_input_dep_of_var_dep node var_deps =

  (* Return a list of positions in inputs for each output *)
  List.map
    (fun o -> 

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
                | (ident, _) :: tl when ident = v -> i
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



(* If x = y and x captures the output of a node, substitute y *)
let solve_eqs_node_calls node = 

  let calls', vars_eliminated =

    (* Iterate over all calls, collect modified calls and eliminated
       variables *)
    List.fold_left 
      (fun (accum_calls, accum_vars_eliminated) (o, c, n, i, s) -> 

         
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

                  (v' :: accum_outputs, v :: accum_vars_eliminated)

                (* Variable not found in a variable alias equation *)
                with Not_found -> 

                    (v :: accum_outputs, accum_vars_eliminated))
             
             o
             ([], accum_vars_eliminated)
         in
         (o', c, n, i, s) :: accum_calls, accum_vars_eliminated')
      ([], [])
      node.calls
  in
  (*  
  Format.printf
    "@[<v>Elminated variables:@,%a@]@."
    (pp_print_list (I.pp_print_ident false) "@,") 
    vars_eliminated;
*)

  let locals' = 
    List.filter
      (fun v -> not (List.memq v vars_eliminated))
      node.locals
  in

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
      (fun accum (_, act_cond, _, args, inits) -> 
         act_cond :: (args @ inits @ accum))
      exprs_equations
      calls
  in

  (* Add expressions in assertions *)
  let exprs_asserts = asserts @ exprs_calls in

  (* Add expressions in assertions *)
  let exprs_props = props @ exprs_asserts in

  (* Add expressions in assumptions *)
  let exprs_requires = requires @ exprs_props in

  (* Add expressions in guarantees *)
  let exprs_ensures = ensures @ exprs_requires in

  (* Return collected expressions *)
  exprs_ensures



(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
