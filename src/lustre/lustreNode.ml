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
module SVM = StateVar.StateVarMap


(* Add a list of state variables to a set *)
let add_to_svs set list = 
  List.fold_left (fun a e -> SVS.add e a) set list 
  

(* Bound for index variable, or fixed value for index variable *)
type 'a bound_or_fixed = 
  | Bound of 'a  (* Upper bound for index variable *)
  | Fixed of 'a  (* Fixed value for index variable *)

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

  (* Oracle input stream *)
  | Oracle


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

    (* Expression for initial return values 

       This value should be [None] for node calls on the base clock,
        and [Some l] for node calls with a clock. A node call with a
        clock may only have [None] here if it occurs directly under a
        [merge] operator.*)
    call_defaults : E.t D.t option;

  }


(* A call of a function *)
type function_call = 

  { 

    (* Position of function call in input file *)
    call_pos : position;

    (* Name of called function *)
    call_function_name : I.t;
    
    (* Expressions for input parameters *)
    call_inputs : E.t D.t;

    (* Variables capturing the outputs *)
    call_outputs : StateVar.t D.t;

  }


type contract =
  { 

    (* Identifier of contract *)
    contract_name : LustreIdent.t;

    (* Position of the contract in the input *)
    contract_pos: position;

    (* Invariant from requirements of contract *)
    contract_reqs : (position * StateVar.t) list;

    (* Invariants from ensures of contract *)
    contract_enss : (position * StateVar.t) list

  }


(* An equation *)
type equation = (StateVar.t * E.expr bound_or_fixed list * E.t) 


(* A Lustre node *)
type t = 

  { 

    (* Name of node *)
    name : I.t;

    (* Constant state variable uniquely identifying the node instance *)
    instance : StateVar.t;

    (* Distinguished state variable to become true in the first
       instant only *)
    init_flag : StateVar.t;

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

    (* Local variables of node and a list of expressions for the upper
       bounds of each array dimension *)
    locals : StateVar.t D.t list;

    (* Equations for local and output variables *)
    equations : equation list;

    (* Node calls *)
    calls : node_call list;

    (* Function calls

       Needed to share functions calls with the same input
       parameters *)
    function_calls : function_call list;

    (* Assertions of node *)
    asserts : E.t list;

    (* Proof obligations for node *)
    props : (StateVar.t * string * Property.prop_source) list;

    (* Global contracts *)
    global_contracts : contract list;

    (* Mode contracts *)
    mode_contracts :  contract list;

    (* Node is annotated as main node *)
    is_main : bool;

    (* Map from a state variable to its source *)
    state_var_source_map : state_var_source SVM.t 

  }


(* An empty node *)
let empty_node name = 
  { name = name;
    instance = 
      StateVar.mk_state_var
        ~is_const:true
        (I.instance_ident |> I.string_of_ident false)
        (I.to_scope name @ I.reserved_scope)
        Type.t_int;
    init_flag = 
      StateVar.mk_state_var
        (I.init_flag_ident |> I.string_of_ident false)
        (I.to_scope name @ I.reserved_scope)
        Type.t_bool;
    inputs = D.empty;
    oracles = [];
    outputs = D.empty;
    locals = [];
    equations = [];
    calls = [];
    function_calls = [];
    asserts = [];
    props = [];
    global_contracts = [];
    mode_contracts = [];
    is_main = false;
    state_var_source_map = SVM.empty }


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
let pp_print_local safe ppf l = pp_print_list (pp_print_local' safe) ";@ " ppf l


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
      call_outputs } ->

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>%a@,(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (D.values call_outputs)
      (I.pp_print_ident safe) call_node_name
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (D.values call_inputs @ 
       call_oracles)

  (* Node call not on the base clock is a condact *)
  |  { call_node_name; 
       call_clock = Some call_clock_var;
       call_inputs; 
       call_oracles; 
       call_outputs; 
       call_defaults = Some call_defaults } ->
     
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>condact(@,%a,@,%a(%a)%t);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (D.values call_outputs) 
      (E.pp_print_lustre_var safe) call_clock_var
      (I.pp_print_ident safe) call_node_name
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (List.map  
         (fun (_, sv) -> sv)
         (D.bindings call_inputs) @ 
       call_oracles)
      (fun ppf -> 
         match 
           D.values call_defaults
         with 
           | [] -> ()
           | l -> 
             Format.fprintf 
               ppf 
               ",@,%a"
               (pp_print_list (E.pp_print_lustre_expr safe) ",@ ")
               l)
          
  (* Node call not on the base clock without defaults *)
  |  { call_node_name; 
       call_clock = Some call_clock_var;
       call_inputs; 
       call_oracles; 
       call_outputs; 
       call_defaults = None } ->
     
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>(activate@ %a@ every@ %a)@,(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (D.values call_outputs) 
      (I.pp_print_ident safe) call_node_name
      (E.pp_print_lustre_var safe) call_clock_var
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (List.map  
         (fun (_, sv) -> sv)
         (D.bindings call_inputs) @ 
       call_oracles)
          

(* Pretty-print a function call *)
let pp_print_function_call safe ppf = function 

  (* Node call on the base clock *)
  | { call_function_name; 
      call_inputs; 
      call_outputs } ->

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>%a@,(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (D.values call_outputs)
      (I.pp_print_ident safe) call_function_name
      (pp_print_list (E.pp_print_lustre_expr safe) ",@ ") 
      (D.values call_inputs)


(* Pretty-print an assertion *)
let pp_print_assert safe ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>assert@ %a;@]"
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a property *)
let pp_print_prop safe ppf (sv, n, _) = 
  
  let sv_string = 
    Format.asprintf "%a" (E.pp_print_lustre_var safe) sv 
  in

  Format.fprintf ppf
    "@[<hv 2>--%%PROPERTY %s;%t@]"
    sv_string
    (fun ppf -> 
       if sv_string <> n then
         Format.fprintf ppf " -- was: %s" n)

(* Pretty-print an assumption *)
let pp_print_require safe ppf (_,sv) =
  Format.fprintf ppf
    "@[<hv 2>--@@require@ @[<h>%a@];@]"
    (E.pp_print_lustre_var safe) sv


(* Pretty-print a guarantee *)
let pp_print_ensure safe ppf (_,sv) =
  Format.fprintf ppf
    "@[<hv 2>--@@ensure @[<h>%a@];@]"
    (E.pp_print_lustre_var safe) sv


(* Pretty-print a named mode contract. *)
let pp_print_mode_contract safe ppf {
  contract_name; contract_reqs; contract_enss
} =
  Format.fprintf
    ppf
    "@[<v>--@@contract %a;@,%a@,%a@]"
    (I.pp_print_ident false) contract_name
    (pp_print_list (pp_print_require safe) "@ ") contract_reqs
    (pp_print_list (pp_print_ensure safe) "@ ") contract_enss


(* Pretty-print an anonymous global contract. *)
let pp_print_global_contract safe ppf {
  contract_name; contract_reqs; contract_enss
} =

    Format.fprintf
      ppf
      "@[<v>-- %a@,%a@,%a@]"
      (I.pp_print_ident false) contract_name
      (pp_print_list (pp_print_require safe) "@ ") contract_reqs
      (pp_print_list (pp_print_ensure safe) "@ ") contract_enss


(* Pretty-print a named mode contract. *)
let pp_print_mode_contract  safe ppf {
  contract_name; contract_reqs; contract_enss
} =

    Format.fprintf
      ppf
      "@[<v>--@contract %a@,%a@,%a@]"
      (I.pp_print_ident false) contract_name
      (pp_print_list (pp_print_require safe) "@ ") contract_reqs
      (pp_print_list (pp_print_ensure safe) "@ ") contract_enss



(* Pretty-print a node *)
let pp_print_node safe ppf {
  name;
  inputs; 
  oracles; 
  outputs; 
  locals; 
  equations; 
  calls;
  function_calls;
  asserts; 
  props;
  global_contracts;
  mode_contracts;
  is_main
} =

  (* Output a space if list is not empty *)
  let space_if_nonempty = function
    | [] -> (function _ -> ())
    | _ -> (function ppf -> Format.fprintf ppf "@ ")
  in

  Format.fprintf ppf 
    "@[<hv>@[<hv 2>node %a@ @[<hv 1>(%a)@]@;<1 -2>\
     returns@ @[<hv 1>(%a)@];@]@ \
     %a%t\
     %a%t\
     @[<v>%t@]\
     @[<hv 2>let@ \
     %a%t\
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
    (List.map
       (* Remove first index of input argument for printing *)
       (function ([], e) -> ([], e) | (_ :: tl, e) -> (tl, e))
       (D.bindings inputs) @
     (List.map (fun sv -> (D.empty_index, sv)) oracles))

    (* %a *)
    (pp_print_list (pp_print_output safe) ";@ ") 
    (List.map
       (* Remove first index of output argument for printing *)
       (function ([], e) -> ([], e) | (_ :: tl, e) -> (tl, e))
       (D.bindings outputs))

    (pp_print_list (pp_print_global_contract safe) "@,") global_contracts
    (space_if_nonempty global_contracts)

    (pp_print_list (pp_print_mode_contract safe) "@,") mode_contracts
    (space_if_nonempty mode_contracts)

    (* %t *)
    (function ppf -> 
      if locals <> [] then
        Format.fprintf ppf 
          "@[<hv 2>var@ %a;@]@ " 
          (pp_print_list (pp_print_local safe) ";@ ") 
          (List.map D.bindings locals))

    (* %a%t *)
    (pp_print_list (pp_print_call safe) "@ ") calls
    (space_if_nonempty calls)

    (* %a%t *)
    (pp_print_list (pp_print_function_call safe) "@ ") function_calls
    (space_if_nonempty function_calls)

    (* %a%t *)
    (pp_print_list (pp_print_node_equation safe) "@ ") equations
    (space_if_nonempty equations)

    (* %a%t *)
    (pp_print_list (pp_print_assert safe) "@ ") asserts
    (space_if_nonempty asserts)

    (* %t *)
    (function ppf -> if is_main then Format.fprintf ppf "--%%MAIN@,")

    (pp_print_list (pp_print_prop safe) "@ ") props
    


let pp_print_state_var_trie_debug ppf t = 
  D.bindings t |> 
  pp_print_list
    (fun ppf (i, sv) -> 
       if i = D.empty_index then 
         StateVar.pp_print_state_var ppf sv
       else
         Format.fprintf 
           ppf
           "%a: %a"
           (D.pp_print_index false) i
           StateVar.pp_print_state_var sv)
    ";@ "
    ppf

let pp_print_node_call_debug 
    ppf
    { call_node_name; 
      call_clock; 
      call_inputs; 
      call_oracles; 
      call_outputs } =

  Format.fprintf
    ppf
    "call %a { @[<hv>clock    = %a;@ \
                     inputs   = [@[<hv>%a@]];@ \
                     oracles  = [@[<hv>%a@]];@ \
                     outputs  = [@[<hv>%a@]]; }@]"
    (I.pp_print_ident false) call_node_name
    (pp_print_option StateVar.pp_print_state_var) call_clock
    pp_print_state_var_trie_debug call_inputs
    (pp_print_list StateVar.pp_print_state_var ";@ ") call_oracles
    pp_print_state_var_trie_debug call_outputs


let pp_print_node_debug
    ppf 
    { name;
      instance;
      init_flag;
      inputs; 
      oracles; 
      outputs; 
      locals; 
      equations; 
      calls; 
      asserts; 
      props;
      global_contracts;
      mode_contracts;
      is_main;
      state_var_source_map } = 

  let pp_print_equation = pp_print_node_equation false in

  let pp_print_prop ppf (state_var, name, source) = 

    Format.fprintf
      ppf
      "%a (%s, %a)"
      StateVar.pp_print_state_var state_var
      name
      Property.pp_print_prop_source source

  in

  let pp_print_contract
      ppf
      { contract_name;
        contract_reqs;
        contract_enss } =
    let pp_snd_of fmt (_,sv) =
      Format.fprintf fmt "%a" StateVar.pp_print_state_var sv
    in

    Format.fprintf 
      ppf
      "@[<v>name = %a@,\
            requires = @[<hv>%a@]@,\
            ensures =  @[<hv>%a@]@]"
      (I.pp_print_ident false) contract_name
      (pp_print_list pp_snd_of ",@ ") contract_reqs
      (pp_print_list pp_snd_of ",@ ") contract_enss
  in

  let pp_print_state_var_source ppf = 
    let p sv src = Format.fprintf ppf "%a:%s" StateVar.pp_print_state_var sv src in
    function 
      | (sv, Input) -> p sv "in"
      | (sv, Output) -> p sv "out"
      | (sv, Local) -> p sv "loc" 
      | (sv, Ghost) -> p sv "gh" 
      | (sv, Oracle) -> p sv "or" 

  in

  Format.fprintf 
    ppf
    "node %a @[<hv 2>\
       { instance =         %a;@ \
         init_flag =        %a;@ \
         inputs =           [@[<hv>%a@]];@ \
         oracles =          [@[<hv>%a@]];@ \
         outputs =          [@[<hv>%a@]];@ \
         locals =           [@[<hv>%a@]];@ \
         equations =        [@[<hv>%a@]];@ \
         calls =            [@[<hv>%a@]];@ \
         asserts =          [@[<hv>%a@]];@ \
         props =            [@[<hv>%a@]];@ \
         global_contracts = [@[<hv>%a@]];@ \
         mode_contracts =   [@[<hv>%a@]];@ \
         is_main =          @[<hv>%B@];@ \
         source_map =       [@[<hv>%a@]]; }@]"

    StateVar.pp_print_state_var instance
    StateVar.pp_print_state_var init_flag
    (I.pp_print_ident false) name
    pp_print_state_var_trie_debug inputs
    (pp_print_list StateVar.pp_print_state_var ";@ ") oracles
    pp_print_state_var_trie_debug outputs
    (pp_print_list pp_print_state_var_trie_debug ";@ ") locals
    (pp_print_list pp_print_equation "@ ") equations
    (pp_print_list pp_print_node_call_debug ";@ ") calls
    (pp_print_list (E.pp_print_lustre_expr false) ";@ ") asserts
    (pp_print_list pp_print_prop ";@ ") props
    (pp_print_list pp_print_contract ";@ ") global_contracts
    (pp_print_list pp_print_contract ";@ ") mode_contracts
    is_main
    (pp_print_list pp_print_state_var_source ";@ ") 
    (SVM.bindings state_var_source_map)


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


(* Return the name of the node *)
let name_of_node { name } = name

(* Return the scope of the name of the node *)
let scope_of_node { name } = name |> I.to_scope

    
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


(* Node has a contract if it has a global or at least one mode
   contract *)
let has_contract { global_contracts; mode_contracts } = 
  not (global_contracts = [] && mode_contracts = [])


(* Node always has an implementation *)
let has_impl = function 

  (* Only equations without assertions can be implementation-free

     Don't consider node calls here, because the outputs of node calls
     are assigned to state variables in an equation, and we just check
     those equations. *)
  | { equations; asserts = []; state_var_source_map } -> 

    (* Return true if there is an equation of a non-ghost variable *)
    List.exists
      (fun (sv, _, _) -> 
         match SVM.find sv state_var_source_map with
           | Ghost -> false
           | _ -> true
           | exception Not_found -> true)
      equations

  (* Node with an assertion does have an implementation *)
  | _ -> false



(* Return a subsystem from a list of nodes where the top node is at
   the head of the list. *)
let rec subsystem_of_nodes' nodes accum = function

  (* Return subsystems for all nodes *)
  | [] -> accum

  (* Create subsystem for node *)
  | top :: tl -> 

    if

      (* Subsystem for node already created? *)
      List.exists
        (fun (n, _) -> n = top)
        accum

    then

      (* Don't add to accumulator again *)
      subsystem_of_nodes' nodes accum tl

    else

      (* Nodes called by this node *)
      let { calls } as node =

        try 

          (* Get node by name *)
          node_of_name top nodes 

        (* Node must be in the list of nodes *)
        with Not_found -> 

          raise
            (Invalid_argument 
               (Format.asprintf
                  "subsystem_of_nodes: node %a not found"
                  (I.pp_print_ident false) top))

      in

      (* For all called nodes, either add the already created
         subsystem to the [subsystems], or add the name of the called
         node to [tl']. *)
      let subsystems, tl' = 

        List.fold_left 
          (fun (a, tl) { call_node_name } -> 

             try 

               (* Find subsystem for callee *)
               let callee_subsystem = 

                 List.find
                   (fun (n, _) -> n = call_node_name)
                   accum

                 |> snd 

               in

               if 

                 (* Callee already seen as a subsystem of this
                    node? *)
                 List.exists 
                   (fun { SubSystem.scope } -> 
                      scope = [I.string_of_ident false call_node_name])
                   a

               then

                 (* Add node as subsystem only once, not for each
                    call *)
                 (a, tl)

               else

                 (callee_subsystem :: a, tl)

             (* Subsystem for callee not created yet *)
             with Not_found -> 

               (* Must visit callee first *)
               (a, call_node_name :: tl))


          ([], [])
          calls

      in

      (* Subsystem for some callees not created? *)
      if tl' <> [] then 
        
        (* Recurse to create subsystem of callees first *)
        subsystem_of_nodes' nodes accum (tl' @ top :: tl)
          
      else

        (* Scope of the system from node name *)
        let scope = [I.string_of_ident false top] in

        (* Does node have contracts? *)
        let has_contract = has_contract node in 

        (* Does node have an implementation? *)
        let has_impl = has_impl node in

        (* Construct subsystem of node *)
        let subsystem = 

          { SubSystem.scope;
            SubSystem.source = node;
            SubSystem.has_contract;
            SubSystem.has_impl;
            SubSystem.subsystems  }

        in

        (* Add subsystem of node to accumulator and continue *)
        subsystem_of_nodes' 
          nodes 
          ((top, subsystem) :: accum)
          tl


(* Return a subsystem from a list of nodes where the top node is at
   the head of the list. *)
let subsystem_of_nodes = function

  (* Head of list is top system *)
  | { name } :: _ as nodes -> 

    (* Create subsystems for all nodes *)
    let all_subsystems = subsystem_of_nodes' nodes [] [name] in

    (try 

       (* Find subsystem of top node *)
       List.find 
         (fun (n, _) -> n = name)
         all_subsystems 

       |> snd

     (* Subsystem for node must have been created *)
     with Not_found -> assert false)

  (* Cannot have an empty list of nodes *)
  | [] ->

    raise
      (Invalid_argument 
         "subsystem_of_nodes: List of nodes is empty")
          

(* Return list of topologically ordered list of nodes from subsystem.
   The top node is a the head of the list. *)
let nodes_of_subsystem subsystem = 
  
  SubSystem.all_subsystems subsystem
  |> List.map (function { SubSystem.source } -> source) 


(* ********************************************************************** *)
(* Iterators                                                              *)
(* ********************************************************************** *)

(* Stack for zipper in [fold_node_calls_with_trans_sys'] *)
type fold_stack = 
  | FDown of t * TransSys.t * (TransSys.t * TransSys.instance) list
  | FUp of t * TransSys.t * (TransSys.t * TransSys.instance) list

let rec fold_node_calls_with_trans_sys' 
    nodes
    (f : t -> TransSys.t -> (TransSys.t * TransSys.instance) list -> 'a list -> 'a)
    accum = 

  function 

    (* All systems visited, return result *)
    | [] -> 

      (match accum with
        | [[a]] -> a
        | _ -> assert false)

    (* We need to evaluate called nodes first *)
    | FDown (({ calls } as node), trans_sys, instances) :: tl -> 
      
      (* Direct subsystems of transition system *)
      let subsystems = 
        TransSys.get_subsystem_instances trans_sys 
      in

      let tl' = 
        List.fold_left 
          (fun a { call_pos; call_node_name } ->

             (* Find called node by name *)
             let node' = node_of_name call_node_name nodes in

             (* Find subsystem of this node by name *)
             let trans_sys', instances' =
               List.find 
                 (fun (t, _) -> 
                    Scope.equal
                      (TransSys.scope_of_trans_sys t)
                      (I.to_scope call_node_name))
                 subsystems
             in

             (* Find instance of this node call by position *)
             let instance = 
               List.find 
                 (fun { TransSys.pos } -> 
                    pos = call_pos)
                 instances'
             in

             FDown (node', trans_sys', (trans_sys, instance) :: instances) :: a)
          (FUp (node, trans_sys, instances) :: tl)

          calls
      in

      fold_node_calls_with_trans_sys'
        nodes
        f 
        ([] :: accum)
        tl'

    (* Subsytems are in the accumulator, evaluate this system now *)
    | FUp (n, t, i) :: tl -> 

      (match accum with
        | a :: b :: c ->
          
          fold_node_calls_with_trans_sys' 
            nodes
            f
            (((f n t i a) :: b) :: c) 
            tl
            
        | _ -> assert false)



let fold_node_calls_with_trans_sys nodes f node trans_sys =

  fold_node_calls_with_trans_sys' nodes f [[]] [FDown (node, trans_sys, [])]


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


let stateful_vars_of_prop (state_var, _, _) = SVS.singleton state_var 

let stateful_vars_of_contract { contract_reqs; contract_enss } = 
  ( List.map snd contract_reqs ) @ ( List.map snd contract_enss )
  |> SVS.of_list

(* Return all stateful variables from expressions in a node *)
let stateful_vars_of_node
    { inputs; 
      oracles; 
      outputs; 
      locals;
      equations; 
      calls; 
      asserts; 
      props; 
      global_contracts;
      mode_contracts } =

  (* Input, oracle, and output variables are always stateful

     This includes state variables from requires, ensures and
     implications in contracts, because they all become observers. *)
  let stateful_vars =
    add_to_svs
      SVS.empty
      ((D.values inputs)
       @ (D.values outputs)
       @ oracles)
  in

  (* Add stateful variables from properties *)
  let stateful_vars =
    List.fold_left
      (fun accum p -> SVS.union accum (stateful_vars_of_prop p))
      stateful_vars
      props
  in

  (* Add stateful variables from global and mode contracts *)
  let stateful_vars =
    List.fold_left
      (fun accum p -> SVS.union accum (stateful_vars_of_contract p))
      stateful_vars
      (global_contracts @ mode_contracts)
  in

  (* Add stateful variables from equations *)
  let stateful_vars = 
    List.fold_left
      (fun  accum (_, _, expr) -> 
         SVS.union accum (stateful_vars_of_expr expr))
      stateful_vars
      equations
  in

  (* Unconstrained local state variables must be stateful *)
  let stateful_vars = 
    List.fold_left
      (fun a l -> 
         D.fold
           (fun _ sv a -> 
              if 

                (* Local state variable is defined by an equation? *)
                List.exists
                  (fun (sv', _, _) -> StateVar.equal_state_vars sv sv') 
                  equations 
              then 
              
                (* State variable is not necessarily stateful *)
                a

              else 

                (* State variable without equation must be stateful *)
                SVS.add sv a)
           l
           a)
      stateful_vars
      locals
  in

  (* Add property variables *)
  let stateful_vars = 
    add_to_svs
      stateful_vars
      (List.map (fun (sv, _, _) -> sv) props) 
  in

  (* Add stateful variables from assertions *)
  let stateful_vars = 
    List.fold_left 
      (fun accum expr -> 

         (* Add stateful variables of assertion *)
         SVS.union accum (stateful_vars_of_expr expr) |> 
         
         (* Variables in assertion that do not have a definition must
            be stateful *)
         SVS.union
           (E.state_vars_of_expr expr
            |> 
            SVS.filter
              (fun sv -> 
                 not
                   (List.exists
                      (fun (sv', _, _) -> 
                         StateVar.equal_state_vars sv sv') 
                      equations))))
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
          call_defaults } -> 

        (SVS.union 

           (* Add stateful variables from initial defaults *)
           (match call_defaults with 
             | None -> accum
             | Some d ->
               List.fold_left 
                 (fun accum expr -> 
                    SVS.union accum (stateful_vars_of_expr expr))
                 accum
                 (D.values d))
              
           (* Input and output variables are always stateful *)
           (add_to_svs

              (* Variables in activation condition are always stateful *)
              (match call_clock with
               | Some var -> SVS.singleton var
               | None -> SVS.empty)

              (* Input and output variables are always stateful *)
              ((D.values call_inputs) @ 
               call_oracles @
               (D.values call_outputs)))))
      stateful_vars
      calls
  in

  stateful_vars

(* ********************************************************************** *)
(* State variable sources                                                 *)
(* ********************************************************************** *)

(* Pretty-print the source of a state variable *)
let rec pp_print_state_var_source ppf = function
  | Input -> Format.fprintf ppf "input"
  | Oracle -> Format.fprintf ppf "oracle"
  | Output -> Format.fprintf ppf "output"
  | Local -> Format.fprintf ppf "local"
  | Ghost -> Format.fprintf ppf "ghost"


(* Set source of state variable *)
let set_state_var_source ({ state_var_source_map } as node) state_var source = 

  (* Overwrite previous source *)
  let state_var_source_map' =
    SVM.add 
      state_var
      source
      state_var_source_map 
  in

  { node with state_var_source_map = state_var_source_map' }

(* Get source of state variable *)
let get_state_var_source { state_var_source_map } state_var = 

  SVM.find
    state_var
    state_var_source_map 


(* Return true if the state variable should be visible to the user,
    false if it was created internally *)
let state_var_is_visible node state_var = 

  match get_state_var_source node state_var with

    (* Oracle inputs and abstraced streams are invisible *)
    | Ghost
    | Oracle -> false

    (* Inputs, outputs and defined locals are visible *)
    | Input
    | Output
    | Local -> true

    (* Invisible if no source set *)
    | exception Not_found -> false


(* Return true if the state variable is an input *)
let state_var_is_input node state_var = 

    match get_state_var_source node state_var with
      | Input -> true
      | _ -> false
      | exception Not_found -> false


(* Return true if the state variable is an output *)
let state_var_is_output node state_var = 

    match get_state_var_source node state_var with
      | Output -> true
      | _ -> false
      | exception Not_found -> false


(* Return true if the state variable is a local variable *)
let state_var_is_local node state_var = 

    match get_state_var_source node state_var with
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
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
