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
module T = LustreType
module E = LustreExpr

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

    (* Input variables of node, some flagged as constant

       The order of the list is important, it is the order the
       parameters in the declaration. *)
    inputs : 
      (LustreIdent.t * (((LustreIdent.index * LustreType.t) list) * bool)) list;

    (* Output variables of node 

       The order of the list is important, it is the order the
       parameters in the declaration. *)
    outputs : 
      (LustreIdent.t * ((LustreIdent.index * LustreType.t) list)) list;

    (* Local variables of node 

       The order of the list is irrelevant, we are doing dependency
       analysis and cone of influence reduction later. *)
    locals :
      (LustreIdent.t * ((LustreIdent.index * LustreType.t) list)) list;

    (* Equations for local and output variables *)
    equations : (LustreIdent.t * LustreExpr.t) list;

    (* Node calls with activation condition: variables capturing the
       outputs, the Boolean activation condition, the name of the
       called node, expressions for input parameters and expression
       for initialization *)
    calls : 
      ((LustreIdent.t * LustreType.t) list * 
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
    is_main : bool }


(* An empty node *)
let empty_node = 
  { inputs = [];
    outputs = [];
    locals = [];
    equations = [];
    calls = [];
    asserts = [];
    props = [];
    requires = [];
    ensures = [];
    is_main = false }


(* Pretty-print a node input *)
let pp_print_input safe ppf (ident, (index_list, is_const)) =

  Format.fprintf ppf
    "%t%a"
    (function ppf -> if is_const then Format.fprintf ppf "const ")
    (pp_print_list 
       (fun ppf (j, t) -> 
         Format.fprintf ppf 
           "%a: %a" 
           (I.pp_print_ident safe) (I.push_index j ident)
           (T.pp_print_lustre_type safe) t)
       ";@ ")
    index_list


(* Pretty-print a node output *)
let pp_print_output safe ppf (ident, index_list) =

  Format.fprintf ppf
    "%a"
    (pp_print_list 
       (fun ppf (j, t) -> 
         Format.fprintf ppf 
           "%a: %a" 
           (I.pp_print_ident safe) (I.push_index j ident)
           (T.pp_print_lustre_type safe) t)
       ";@ ")
    index_list


(* Pretty-print a node local variable *)
let pp_print_local safe ppf (ident, index_list) =

  Format.fprintf ppf
    "%a"
    (pp_print_list 
       (fun ppf (j, t) -> 
         Format.fprintf ppf 
           "%a: %a;" 
           (I.pp_print_ident safe) (I.push_index j ident)
           (T.pp_print_lustre_type safe) t)
       "@ ")
    index_list


(* Pretty-print a node equation *)
let pp_print_node_equation safe ppf (ident, expr) = 

  Format.fprintf ppf
    "@[<hv 2>%a =@ %a;@]"
    (I.pp_print_ident safe) ident
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node call *)
let pp_print_call safe ppf = function 

  (* Node call on the base clock *)
  | (out_vars, act_expr, node, exprs, _) when act_expr = E.t_true -> 

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>%a(%a);@]@]"
      (pp_print_list 
         (fun ppf (i, _) -> I.pp_print_ident safe ppf i)
         ",@ ") 
      out_vars
      (I.pp_print_ident safe) node
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") exprs

  (* Node call not on the base clock, a condact *)
  | (out_vars, act_expr, node, exprs, init_exprs) ->
     
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv>condact(%a,%a(%a),@ %a);@]@]"
      (pp_print_list 
         (fun ppf (i, _) -> I.pp_print_ident safe ppf i)
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
    node_ident 
    ppf 
    { inputs; 
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
     %t\
     %a%t\
     %a%t\
     %a%t\
     %a%t\
     %a@;<1 -2>\
     tel;@]@]"  
    (I.pp_print_ident safe) node_ident
    (pp_print_list (pp_print_input safe) ";@ ") inputs
    (pp_print_list (pp_print_output safe) ";@ ") outputs
    (function ppf -> 
      if locals = [] then () else 
        Format.fprintf ppf 
          "@[<hv 2>var@ %a@]" 
          (pp_print_list (pp_print_local safe) "@ ") locals)
    (space_if_nonempty locals)
    (pp_print_list (pp_print_node_equation safe) "@ ") equations
    (space_if_nonempty equations)
    (function ppf -> if is_main then Format.fprintf ppf "--%%MAIN@,")
    (pp_print_list (pp_print_requires safe) "@ ") requires
    (space_if_nonempty requires)
    (pp_print_list (pp_print_ensures safe) "@ ") ensures
    (space_if_nonempty ensures)
    (pp_print_list (pp_print_prop safe) "@ ") props
    (space_if_nonempty props)
    (pp_print_list (pp_print_assert safe) "@ ") asserts
    (space_if_nonempty asserts)
    (pp_print_list (pp_print_call safe) "@ ") calls
    


(* *)
let rec node_var_dependencies init_or_step node accum = 

  (* Return expression either for the initial state or a step state *)
  let init_or_step_of_expr { E.expr_init; E.expr_step } = 
    if init_or_step then expr_init else expr_step 
  in

  function 
    
    | [] -> accum
      
    | ident :: tl -> 
      
      if 
        
        (* Variable is an input variable *)
        List.exists 
          (fun (ident', (indexes, _)) -> 
             List.exists 
               (fun (index', _) -> ident = I.push_index index' ident')
               indexes)
          node.inputs 
          
      then 
        
        (* No dependencies for inputs *)
        node_var_dependencies 
          init_or_step 
          node
          ((ident, ISet.empty) :: accum) 
          tl
          
      else
        
          let vars = 

            try 
              
              (* Get expression defining variable *)
              let expr = 
                List.assoc ident node.equations 
              in
              
              (* Get variables in expression *)
              E.vars_of_expr (init_or_step_of_expr expr) 

            (* Variable is not input or defined in an equation *)
            with Not_found -> 
              
              try
                
                let rec aux ident = function
                  | [] -> raise Not_found
                  | (o, _, n, _, _ ) :: tl -> 
                    let rec aux2 i = function
                      | [] -> raise Not_found 
                      | (v, _) :: _ when v = ident -> (n, i)
                      | _ :: tl -> aux2 (succ i) tl
                    in
                    try aux2 0 o with Not_found -> aux ident tl
                in
                
                let n, i = aux ident node.calls in
                
                Format.printf 
                  "%a is at position %d in call to node %a@."
                  (I.pp_print_ident false) ident 
                  i
                  (I.pp_print_ident false) n;
                
                []
                
              (* Variable is not input or defined in an equation or node
                 call *)
              with Not_found -> []
                
          in
          
          let vars_visited, vars_not_visited = 
            List.partition
              (fun ident -> List.mem_assoc ident accum)
              vars
          in

          (* All dependent variables visited? *)
          if vars_not_visited = [] then 
            
            let dependent_vars = 
              List.fold_left
                (fun a i -> 
                   ISet.union a (List.assoc i accum))
                ISet.empty
                vars_visited
            in
            
            (* First get dependencies of all dependent variables *)
            node_var_dependencies 
              init_or_step 
              node 
              ((ident, dependent_vars) :: accum)
              tl
              
          else
            
            (* First get dependencies of all dependent variables *)
            node_var_dependencies 
              init_or_step 
              node 
              accum 
              (vars_not_visited @ tl)
              


(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
