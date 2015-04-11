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
module D = LustreIndex
module E = LustreExpr

module SVS = StateVar.StateVarSet
module SVMap = StateVar.StateVarMap


(* Add a list of state variables to a set *)
let add_to_svs set list = 
  List.fold_left (fun a e -> SVS.add e a) set list 
  

(* Bound for index variable, or fixed value for index variable *)
type 'a bound_or_fixed = 
  | Bound of 'a  (* Upper bound for index variable *)
  | Fixed of 'a  (* Fixed value for index variable *)


(* A call of a node *)
type node_call = 

  { 

    (* Position of node call in input file *)
    call_pos : position;

    (* Name of called node *)
    call_node_name : I.t;
    
    (* Boolean activation condition *)
    call_clock : StateVar.t option;

    (* Variables for input parameters *)
    call_inputs : StateVar.t D.t;

    (* Variables providing non-deterministic inputs *)
    call_oracles : StateVar.t list;

    (* Variables capturing the outputs *)
    call_outputs : StateVar.t D.t;

    (* Variables capturing the the observer streams *)
    call_observers : StateVar.t list;

    (* Expression for initial return values *)
    call_defaults : E.t D.t;

  }


(* A contract is a name, a position, a list of observers for the
   requirements, and an observer for the implication between its
   requirements and ensures. *)
type contract =
  { 

    (* Position of the contract in the input *)
    contract_pos: position;

    (* One observer for each requirement *)
    contract_reqs : StateVar.t list;

    (* One observer for each ensures *)
    contract_enss : StateVar.t list;

    (* One observer for the implication between requirements and ensures *)
    contract_impl : StateVar.t }


(* A Lustre node *)
type t = 

  { 

    (* Name of node *)
    name : I.t;

    (* Input variables of node together with their index in the
       original model and a list of expressions for the upper bounds
       of each array dimension *)
    inputs : StateVar.t D.t;

    (* Oracle inputs *)
    oracles : StateVar.t list;

    (* Output variables of node together with their index in the
       original model and a list of expressions for the upper bounds
       of each array dimension *)
    outputs : StateVar.t D.t;

    (* Observer outputs *)
    observers : StateVar.t list;

    (* Local variables of node and a list of expressions for the upper
       bounds of each array dimension *)
    locals : StateVar.t D.t list;

    (* Equations for local and output variables *)
    equations : (StateVar.t * E.expr bound_or_fixed list * E.t) list;

    (* Node calls with activation condition: variables capturing the
       outputs, the Boolean activation condition, the name of the
       called node, expressions for input parameters and expression
       for initialization *)
    calls : node_call list;

    (* Assertions of node *)
    asserts : E.t list;

    (* Proof obligations for node *)
    props : (StateVar.t * TermLib.prop_source) list;

    (* The contracts of the node: an optional global contract and a
       list of named mode contracts *)
    contracts : contract option * (string * contract) list;

    (* Node is annotated as main node *)
    is_main : bool;

    (* Input state variables an each output depends on to detect
       cyclic definitions through node calls *)
    output_input_dep : D.index list D.t;

  }


(* An empty node *)
let empty_node name = 
  { name = name;
    inputs = D.empty;
    oracles = [];
    outputs = D.empty;
    observers = [];
    locals = [];
    equations = [];
    calls = [];
    asserts = [];
    props = [];
    contracts = None, [];
    is_main = false;
    output_input_dep = D.empty }


(* Pretty-print array bounds of index *)
let pp_print_array_dims safe ppf idx = 

  match D.array_bounds_of_index idx with 

    (* Print only if not empty *)
    | [] -> ()

    | bounds -> 

      Format.fprintf 
        ppf
        "^%a"
        (pp_print_list (E.pp_print_expr safe) "^")
        bounds


(* Pretty-print a node input *)
let pp_print_input safe ppf (idx, var) =

  Format.fprintf ppf
    "%t%a: %a%a"
    (function ppf -> 
      if StateVar.is_const var then Format.fprintf ppf "const ")
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)
    (pp_print_array_dims safe) idx


(* Pretty-print a node output *)
let pp_print_output safe ppf (idx, var) =

  Format.fprintf ppf
    "%a: %a%a"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)
    (pp_print_array_dims safe) idx


(* Pretty-print a node local variable *)
let pp_print_local' safe ppf (idx, var) =

  Format.fprintf ppf
    "%a: %a%a"
    (E.pp_print_lustre_var safe) var
    (E.pp_print_lustre_type safe) (StateVar.type_of_state_var var)
    (pp_print_array_dims safe) idx

(* Pretty-print a node local variable *)
let pp_print_local safe ppf l = pp_print_list (pp_print_local' safe) "@," ppf l


(* Pretty-print a node equation *)
let pp_print_node_equation safe ppf (var, bounds, expr) = 

  Format.fprintf ppf
    "@[<hv 2>%a%a =@ %a;@]"
    (E.pp_print_lustre_var safe) var
    (pp_print_listi
       (fun ppf i -> function 
          | Bound e -> 
            Format.fprintf
              ppf
              "[%a(%a)]"
              (I.pp_print_ident false)
              (I.push_index I.index_ident i)
              (E.pp_print_expr safe) e
          | Fixed e -> Format.fprintf ppf "[%a]" (E.pp_print_expr safe) e)
       "") 
    bounds
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node call *)
let pp_print_call safe ppf = function 

  (* Node call on the base clock *)
  | { call_node_name; 
      call_clock = None; 
      call_inputs; 
      call_oracles; 
      call_outputs; 
      call_observers } ->

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>%a@,(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (List.rev_map 
         (fun (_, sv) -> sv)
         (D.bindings call_outputs) @ 
       call_observers)
      (I.pp_print_ident safe) call_node_name
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (List.rev_map 
         (fun (_, sv) -> sv)
         (D.bindings call_inputs) @ 
      call_oracles)

  (* Node call not on the base clock is a condact *)
  |  { call_node_name; 
       call_clock = Some call_clock_var;
       call_inputs; 
       call_oracles; 
       call_outputs; 
       call_observers; 
       call_defaults } ->
     
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>condact(@,%a,@,%a(%a),@,%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (List.rev_map 
         (fun (_, sv) -> sv)
         (D.bindings call_outputs) @ 
       call_observers)
      (E.pp_print_lustre_var safe) call_clock_var
      (I.pp_print_ident safe) call_node_name
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (List.rev_map  
         (fun (_, sv) -> sv)
         (D.bindings call_inputs) @ 
       call_oracles)
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") 
      (List.rev_map snd (D.bindings call_defaults)
       @ (List.map (fun _ -> E.t_true) call_observers))
          

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
let pp_print_require safe ppf sv =
  Format.fprintf ppf
    "@[<hv 2>--@@require@ @[<h>%a@];@]"
    (E.pp_print_lustre_var safe) sv


(* Pretty-print a guarantee *)
let pp_print_ensure safe ppf sv =
  Format.fprintf ppf
    "@[<hv 2>--@@ensure @[<h>%a@];@]"
    (E.pp_print_lustre_var safe) sv


(* Pretty-print a named mode contract. *)
let pp_print_mode_contract safe ppf (name, { contract_reqs; contract_enss }) =
  Format.fprintf
    ppf
    "@[<v>--@@contract %s ;@,%a@,%a@]"
    name
    (pp_print_list (pp_print_require safe) "@ ") contract_reqs
    (pp_print_list (pp_print_ensure safe) "@ ") contract_enss


(* Pretty-print an anonymous global contract. *)
let pp_print_global_contract safe ppf = function

  (* No global contract *)
  | None -> ()

  (* Global contract *)
  | Some { contract_reqs; contract_enss } ->

    Format.fprintf
      ppf
      "@[<v>%a@,%a@]"
      (pp_print_list (pp_print_require safe) "@ ") contract_reqs
      (pp_print_list (pp_print_ensure safe) "@ ") contract_enss


(* Pretty-print the contracts. *)
let pp_print_contracts safe ppf (global_contract, mode_contracts) = 
  Format.fprintf
    ppf
    "@[<v>%a%t%a@]"
    (pp_print_global_contract safe) global_contract
    (fun ppf -> if global_contract <> None then Format.fprintf ppf "@,")
    (pp_print_list (pp_print_mode_contract safe) "@,") mode_contracts
    

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
      contracts;
      is_main } = 

  (* Output a space if list is not empty *)
  let space_if_nonempty = function
    | [] -> (function _ -> ())
    | _ -> (function ppf -> Format.fprintf ppf "@ ")
  in

  Format.fprintf ppf 
    "@[<hv>@[<hv 2>node %a@ @[<hv 1>(%a)@]@;<1 -2>\
     returns@ @[<hv 1>(%a)@];@]@ \
     %a%t\
     @[<v>%t@]\
     @[<hv 2>let@ \
     %a%t\
     %a%t\
     %a%t\
     %t\
     %a@;<1 -2>\
     tel;@]@]"  

    (* %a *)
    (I.pp_print_ident safe) name

    (* %a *)
    (pp_print_list (pp_print_input safe) ";@ ") 
    (List.rev_map
       (* Remove first index of input argument for printing *)
       (function ([], e) -> ([], e) | (_ :: tl, e) -> (tl, e))
       (D.bindings inputs) @
     (List.map (fun sv -> (D.empty_index, sv)) oracles))

    (* %a *)
    (pp_print_list (pp_print_output safe) ";@ ") 
    (List.rev_map
       (* Remove first index of output argument for printing *)
       (function ([], e) -> ([], e) | (_ :: tl, e) -> (tl, e))
       (D.bindings outputs) @
     (List.map (fun sv -> (D.empty_index, sv)) observers))

    (pp_print_contracts safe) contracts
    (space_if_nonempty
       (match fst contracts with 
         | None -> snd contracts
         | Some c -> ("", c) :: snd contracts))

    (* %t *)
    (function ppf -> 
      if locals <> [] then
        Format.fprintf ppf 
          "@[<hv 2>var@ %a;@]@ " 
          (pp_print_list (pp_print_local safe) ";@ ") 
          (List.map D.bindings locals))

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

    (pp_print_list (pp_print_prop safe) "@ ") (List.map fst props)
    


let pp_print_state_var_trie ppf t = 
  D.bindings t |> 
  pp_print_list
    (fun ppf (i, sv) -> 
       if i = D.empty_index then 
         (E.pp_print_lustre_var false) ppf sv
       else
         Format.fprintf 
           ppf
           "%a: %a"
           (D.pp_print_index false) i
           (E.pp_print_lustre_var false) sv)
    ";@ "
    ppf

let pp_print_node_call_debug 
    ppf
    { call_node_name; 
      call_clock; 
      call_inputs; 
      call_oracles; 
      call_outputs; 
      call_observers } =

  Format.fprintf
    ppf
    "call %a { @[<hv>clock    = %a;@ \
                     inputs   = [@[<hv>%a@]];@ \
                     oracles  = [@[<hv>%a@]];@ \
                     outputs  = [@[<hv>%a@]];@ \
                     observers = [@[<hv>%a@]]; }@]"
    (I.pp_print_ident false) call_node_name
    (pp_print_option (E.pp_print_lustre_var false)) call_clock
    pp_print_state_var_trie call_inputs
    (pp_print_list (E.pp_print_lustre_var false) ";@ ") call_oracles
    pp_print_state_var_trie call_outputs
    (pp_print_list (E.pp_print_lustre_var false) ";@ ") call_observers


let pp_print_node_debug
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
      contracts;
      is_main } = 

  let pp_print_equation = pp_print_node_equation false in

  let pp_print_prop ppf (state_var, source) = 

    Format.fprintf
      ppf
      "%a (%a)"
      (E.pp_print_lustre_var false) state_var
      TermLib.pp_print_prop_source source

  in

  let pp_print_contract ppf { contract_reqs; contract_enss } =
    Format.fprintf 
      ppf
      "@[<v>requires = @[<hv>%a@]@,\
            ensures  = @[<hv>%a@]@]"
      (pp_print_list (E.pp_print_lustre_var false) ",@ ") contract_reqs
      (pp_print_list (E.pp_print_lustre_var false) ",@ ") contract_enss
  in

  let pp_print_contracts ppf (global_contract, mode_contracts) = 
    Format.fprintf 
      ppf
      "@[<v>%t%t@]"
      (fun ppf -> match global_contract with
         | None -> ()
         | Some c -> Format.fprintf ppf "global = %a"pp_print_contract c)
      (fun ppf -> match mode_contracts with 
         | [] -> ()
         | _ -> 
           Format.fprintf 
             ppf
             "%t%a"
             (fun ppf -> match global_contract with 
                | None -> () 
                | Some _ -> Format.fprintf ppf "@,")
             (pp_print_list
                (fun ppf (n, c) -> 
                   Format.fprintf 
                     ppf
                     "@[<v 2>%s:@,%a@]" 
                     n
                     pp_print_contract c)
                "@,") 
             mode_contracts)
  in

  Format.fprintf 
    ppf
    "node %a @[<hv 2>{ inputs =    [@[<hv>%a@]];@ \
                       oracles =   [@[<hv>%a@]];@ \
                       outputs =   [@[<hv>%a@]];@ \
                       observers = [@[<hv>%a@]];@ \
                       locals =    [@[<hv>%a@]];@ \
                       equations = [@[<hv>%a@]];@ \
                       calls =     [@[<hv>%a@]];@ \
                       asserts =   [@[<hv>%a@]];@ \
                       props =     [@[<hv>%a@]];@ \
                       contracts = [@[<hv>%a@]];@ \
                       is_main =   @[<hv>%B@]; }@]"

    (I.pp_print_ident false) name
    pp_print_state_var_trie inputs
    (pp_print_list StateVar.pp_print_state_var ";@ ") oracles
    pp_print_state_var_trie outputs
    (pp_print_list StateVar.pp_print_state_var ";@ ") observers
    (pp_print_list pp_print_state_var_trie ";@ ") locals
    (pp_print_list pp_print_equation "@ ") equations
    (pp_print_list pp_print_node_call_debug ";@ ") calls
    (pp_print_list (E.pp_print_lustre_expr false) ";@ ") asserts
    (pp_print_list pp_print_prop ";@ ") props
    pp_print_contracts contracts
    is_main


(* ********************************************************************** *)
(* Find nodes in lists                                                    *)
(* ********************************************************************** *)


(* Return true if a node of the given name exists in the a list of nodes *)
let exists_node_of_name name nodes =

  List.exists
    (function { name = node_name } -> name = node_name)
    nodes


(* Return the node of the given name from a list of nodes *)
let node_of_name name nodes =

  List.find
    (function { name = node_name } -> name = node_name)
    nodes

    
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


(* Return identifier of last node in list *)
let rec ident_of_top = function 
  
  | [] -> raise (Invalid_argument "ident_of_top")

  | [{ name }] -> name 

  | h :: tl -> ident_of_top tl

(* ********************************************************************** *)
(* Stateful variables                                                     *)
(* ********************************************************************** *)


(* Return state variables that occur as previous state variables *)
let stateful_vars_of_expr { E.expr_step } = 

  Term.eval_t
    (function 

      (* Previous state variables have negative offset *)
      | Term.T.Var v when 
          Var.is_state_var_instance v && 
          Numeral.(Var.offset_of_state_var_instance v < E.cur_offset) -> 
        
        (function 
          | [] -> 
            SVS.singleton 
              (Var.state_var_of_state_var_instance v)
          | _ -> assert false)

      | Term.T.Var _
      | Term.T.Const _ -> 

        (function 
          | [] -> SVS.empty
          | _ -> assert false)

      | Term.T.App _ -> 

        (function l -> 
          List.fold_left 
            SVS.union 
            SVS.empty 
            l)

      | Term.T.Attr _ ->
        (function | [s] -> s | _ -> assert false))
    
    (expr_step :> Term.t)


(* Return all stateful variables from expressions in a node *)
let stateful_vars_of_node
    { inputs; 
      oracles; 
      outputs; 
      observers; 
      equations; 
      calls; 
      asserts; 
      props; 
      contracts } =

  (* Input, oracle, output and observer variables are always stateful *)
  let stateful_vars =
    add_to_svs
      SVS.empty
      ((D.values inputs)
       @ (D.values outputs)
       @ oracles 
       @ observers)
  in

  (* Add stateful variables from equations *)
  let stateful_vars = 
    List.fold_left
      (fun  accum (_, _, expr) -> 
         SVS.union accum (stateful_vars_of_expr expr))
      stateful_vars
      equations
  in

  (* Add property variables *)
  let stateful_vars = add_to_svs stateful_vars (List.map fst props) in
(*
  (* Add stateful variables from contracts *)
  let stateful_vars = 
    List.fold_left 
      (fun accum (_, _, requires, ensures) -> 
         
         (* Add stateful variables to accumulator *)
         let aux expr_list accum = 
           List.fold_left 
             (fun accum expr ->
                SVS.union accum (stateful_vars_of_expr expr))
             accum
             expr_list
         in
         
         (* Add stateful variables from requires and ensures clauses *)
         aux requires accum |> aux ensures)

      stateful_vars
      contracts
  in
*)
  (* Add stateful variables from assertions *)
  let stateful_vars = 
    List.fold_left 
      (fun accum expr -> 
         SVS.union accum (stateful_vars_of_expr expr))
      stateful_vars
      asserts
  in

  (* Add variables from node calls *)
  let stateful_vars = 
    List.fold_left
      (fun
        accum
        { call_clock; 
          call_inputs; 
          call_oracles;
          call_outputs; 
          call_observers; 
          call_defaults } -> 

        (SVS.union 

           (* Add stateful variables from initial defaults *)
           (List.fold_left 
              (fun accum expr -> 
                 SVS.union accum (stateful_vars_of_expr expr))
              accum
              (D.values call_defaults))
              
           (* Input and output variables are always stateful *)
           (add_to_svs

              (* Variables in activation condition are always stateful *)
              (match call_clock with
               | Some var -> SVS.singleton var
               | None -> SVS.empty)

              (* Input and output variables are always stateful *)
              ((D.values call_inputs) @ 
               call_oracles @
               call_observers @ 
               (D.values call_outputs)))))
      stateful_vars
      calls
  in

  stateful_vars

(* ********************************************************************** *)
(* State variable sources                                                 *)
(* ********************************************************************** *)

(* Source of a state variable *)
type state_var_source =

  (* Input stream *)
  | Input

  (* Output stream *)
  | Output

  (* Local defined stream *)
  | Local

  (* Local ghost stream *)
  | Ghost

  (* Local abstracted stream *)
  | Abstract

  (* Oracle input stream *)
  | Oracle

  (* Observer output stream *)
  | Observer


(* Pretty-print the source of a state variable *)
let rec pp_print_state_var_source ppf = function
  
  | Input -> Format.fprintf ppf "input"

  | Oracle -> Format.fprintf ppf "oracle"

  | Output -> Format.fprintf ppf "output"

  | Observer -> Format.fprintf ppf "observer"

  | Local -> Format.fprintf ppf "local"

  | Ghost -> Format.fprintf ppf "ghost"

  | Abstract -> Format.fprintf ppf "abstract"


(* Map from a state variable to its source *)
let state_var_source_map : state_var_source StateVar.StateVarHashtbl.t = 
  StateVar.StateVarHashtbl.create 7


(* Set source of state variable *)
let set_state_var_source state_var source = 

  (* Overwrite previous source *)
  StateVar.StateVarHashtbl.replace
    state_var_source_map 
    state_var
    source


(* Get source of state variable *)
let get_state_var_source state_var = 

  StateVar.StateVarHashtbl.find
    state_var_source_map 
    state_var


(* Return true if the state variable should be visible to the user,
    false if it was created internally *)
let state_var_is_visible state_var = 

  match get_state_var_source state_var with

    (* Oracle inputs and abstraced streams are invisible *)
    | Ghost
    | Observer 
    | Oracle
    | Abstract -> false

    (* Inputs, outputs and defined locals are visible *)
    | Input
    | Output
    | Local -> true

    (* Invisible if no source set *)
    | exception Not_found -> false


(* Return true if the state variable is an input *)
let state_var_is_input state_var = 

    match get_state_var_source state_var with
      | Input -> true
      | _ -> false
      | exception Not_found -> false


(* Return true if the state variable is an output *)
let state_var_is_output state_var = 

    match get_state_var_source state_var with
      | Output -> true
      | _ -> false
      | exception Not_found -> false


(* Return true if the state variable is a local variable *)
let state_var_is_local state_var = 

    match get_state_var_source state_var with
      | Local -> true
      | _ -> false
      | exception Not_found -> false

    

(* ********************************************************************** *)
(* State variable maps                                                    *)
(* ********************************************************************** *)


(* Stream is identical to a stream in a node instance at position *)
type state_var_instance = position * I.t * StateVar.t


(* Map from state variables to identical state variables in other
   scopes *)
let state_var_instance_map : state_var_instance list StateVar.StateVarHashtbl.t = 
  StateVar.StateVarHashtbl.create 7


(* Return identical state variable in a node instance if any *)
let get_state_var_instances state_var = 

  try 

    (* Read list of instances from the hash table *)
    StateVar.StateVarHashtbl.find
      state_var_instance_map 
      state_var

  (* Return empty list *)
  with Not_found -> []


(* State variable is identical to a state variable in a node instance *)
let set_state_var_instance state_var pos node state_var' = 

  (* Get instances of state variable, may return the empty list *)
  let instances = get_state_var_instances state_var in

  (* Add to instances of state variable *)
  let instances' =

    (* Check if instance already known *)
    if List.mem (pos, node, state_var') instances then 

      (* Do not create duplicates *)
      instances 

    else 

      (* Add new instance *)
      (pos, node, state_var') :: instances 

  in

  (* Overwrite previous instances with modified list *)
  StateVar.StateVarHashtbl.replace
    state_var_instance_map 
    state_var
    instances'



(*

(* Return all expressions of a node *)
let exprs_of_node { equations; calls; asserts; props; contracts } =

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

  (* Add all the expressions appearing in the contract. *)
  contracts
  |> List.fold_left
       ( fun list (_, _, reqs, ens) ->
         reqs @ ens @ list )
       exprs_asserts

*)



    



      
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
