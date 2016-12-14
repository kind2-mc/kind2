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
module C = LustreContract

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module SVT = StateVar.StateVarHashtbl

module ET = LustreExpr.LustreExprHashtbl
(* Add a list of state variables to a set *)
let add_to_svs set list = 
  List.fold_left (fun a e -> SVS.add e a) set list 


(* Source of a state variable *)
type state_var_source =

  (* Input stream *)
  | Input

  (* Output stream *)
  | Output

  (* Local defined stream *)
  | Local

  (* Tied to a node call. *)
  | Call

  (* Local ghost stream *)
  | Ghost

  (* Oracle input stream *)
  | Oracle

  (* Alias for another state variable. *)
  | Alias of
    StateVar.t * state_var_source option

type call_cond =
  | CActivate of StateVar.t
  | CRestart of StateVar.t

(* A call of a node *)
type node_call = {

  (* Position of node call in input file *)
  call_pos : position;

  (* Name of called node *)
  call_node_name : I.t;
    
  (* Boolean activation and/or restart conditions if any *)
  call_cond : call_cond list;
 
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


(* Left hand side of an equation *)
type equation_lhs = StateVar.t * E.expr E.bound_or_fixed list


(* An equation *)
type equation = equation_lhs * E.t

(* A contract. *)
type contract = C.t

(* A Lustre node *)
type t = { 

  (* Name of node *)
  name : I.t;

  (* Is the node extern? *)
  is_extern: bool;

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

  (* Assertions of node *)
  asserts : E.t list;

  (* Proof obligations for node *)
  props : (StateVar.t * string * Property.prop_source) list;

  (* Contract. *)
  contract : contract option ;

  (* Node is annotated as main node *)
  is_main : bool ;

  (* Node is actually a function. *)
  is_function: bool ;

  (* Map from a state variable to its source *)
  state_var_source_map : state_var_source SVM.t;

  oracle_state_var_map : StateVar.t SVT.t;

  state_var_expr_map : LustreExpr.t SVT.t;

}


(* An empty node *)
let empty_node name is_extern = {
  name ;
  is_extern ;
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
  asserts = [];
  props = [];
  contract = None ;
  is_main = false;
  is_function = false ;
  state_var_source_map = SVM.empty;
  oracle_state_var_map = SVT.create 17;
  state_var_expr_map = SVT.create 17;
}


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
let pp_print_local safe ppf l =
  pp_print_list (pp_print_local' safe) ";@ " ppf l


(* Pretty-print a node equation *)
let pp_print_node_equation safe ppf ((var, bounds), expr) = 

  Format.fprintf ppf
    "@[<hv 2>%a%a =@ %a;@]"
    (E.pp_print_lustre_var safe) var
    (pp_print_listi
       (fun ppf i -> function 
          | E.Bound e -> 
            Format.fprintf
              ppf
              "[%a(%a)]"
              (I.pp_print_ident false)
              (I.push_index I.index_ident i)
              (E.pp_print_expr safe) e
          | E.Fixed e -> Format.fprintf ppf "[%a]" (E.pp_print_expr safe) e
          | E.Unbound e -> Format.fprintf ppf "[%a]" (E.pp_print_expr safe) e)
       "") 
    bounds
    (E.pp_print_lustre_expr safe) expr


(* Pretty-print a node call *)
let pp_print_call safe ppf = function 

  (* Node call on the base clock *)
  | { call_node_name; 
      call_cond = [];
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

  (* Node call on the base clock with restart *)
  | { call_node_name; 
      call_cond = [CRestart restart_var];
      call_inputs; 
      call_oracles; 
      call_outputs } ->

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>restart %a@,(%a)@ every@ %a;@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (D.values call_outputs)
      (I.pp_print_ident safe) call_node_name
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ") 
      (D.values call_inputs @ 
       call_oracles)
      (E.pp_print_lustre_var safe) restart_var

  (* Node call not on the base clock is a condact *)
  | { call_node_name; 
      call_cond = [CActivate call_clock_var];
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
  | { call_node_name; 
      call_cond = [CActivate call_clock_var];
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

  (* Node call not on the base clock is a condact with restart *)
  | { call_node_name; 
      call_cond =
        ([CActivate call_clock_var; CRestart restart_var] |
         [CRestart restart_var; CActivate call_clock_var]) ;
      call_inputs; 
      call_oracles; 
      call_outputs; 
      call_defaults = Some call_defaults } ->
    
    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>condact(@,%a,@,(restart %a every %a)(%a)%t);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (D.values call_outputs) 
      (E.pp_print_lustre_var safe) call_clock_var
      (I.pp_print_ident safe) call_node_name
      (E.pp_print_lustre_var safe) restart_var
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
      
  (* Node call not on the base clock without defaults with restart  *)
  | { call_node_name; 
      call_cond =
        ([CActivate call_clock_var; CRestart restart_var] |
         [CRestart restart_var; CActivate call_clock_var]) ;
      call_inputs; 
      call_oracles; 
      call_outputs; 
      call_defaults = None } ->

    Format.fprintf ppf
      "@[<hv 2>@[<hv 1>(%a)@] =@ @[<hv 1>(activate (restart@ %a@ every@ %a) every %a)@,(%a);@]@]"
      (pp_print_list 
         (E.pp_print_lustre_var safe)
         ",@ ") 
      (D.values call_outputs) 
      (I.pp_print_ident safe) call_node_name
      (E.pp_print_lustre_var safe) restart_var
      (E.pp_print_lustre_var safe) call_clock_var
      (pp_print_list (E.pp_print_lustre_var safe) ",@ ")
      (List.map  
         (fun (_, sv) -> sv)
         (D.bindings call_inputs) @ 
       call_oracles)
    
  | _ -> assert false


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


let pp_print_node_signature fmt { inputs ; outputs } =
  Format.fprintf fmt
    "\
      (@   \
        @[<hov>%a@]@ \
      ) returns (@   \
        @[<hov>%a@]@ \
      ) ;\
    "

    (* %a *)
    (pp_print_list (pp_print_input false) ";@ ")
    (List.map
       (* Remove first index of input argument for printing *)
       (function ([], e) -> ([], e) | (_ :: tl, e) -> (tl, e))
       (D.bindings inputs))

    (* %a *)
    (pp_print_list (pp_print_output false) ";@ ")
    (List.map
       (* Remove first index of output argument for printing *)
       (function ([], e) -> ([], e) | (_ :: tl, e) -> (tl, e))
       (D.bindings outputs))



(* Pretty-print a node *)
let pp_print_node safe ppf {
  name;
  inputs; 
  oracles; 
  outputs; 
  locals; 
  equations; 
  calls;
  asserts; 
  props;
  contract;
  is_main ;
  is_function ;
} =

  (* Output a space if list is not empty *)
  let space_if_nonempty = function
    | [] -> (function _ -> ())
    | _ -> (function ppf -> Format.fprintf ppf "@ ")
  in

  Format.fprintf ppf 
    "@[<v>@[<hv 2>%s %a@ @[<hv 1>(%a)@]@;<1 -2>\
     returns@ @[<hv 1>(%a)@];@]@ \
     %a\
     @[<v>%t@]\
     @[<hv 2>let@ \
     %a%t\
     %a%t\
     %a%t\
     %t\
     %a@;<1 -2>\
     tel;@]@]@?"  

    (* %s *)
    (if is_function then "function" else "node")

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

    (fun fmt -> function
      | None -> ()
      | Some contract ->
        Format.fprintf fmt "%a@ " (C.pp_print_contract safe) contract)
    contract

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

let pp_print_cond ppf = function
  (* | CNone -> Format.pp_print_string ppf "None" *)
  | CActivate c ->
    Format.fprintf ppf "activate on %a" StateVar.pp_print_state_var c
  | CRestart r ->
    Format.fprintf ppf "restart on %a" StateVar.pp_print_state_var r


let pp_print_conds ppf = pp_print_list pp_print_cond ",@ " ppf 


let pp_print_node_call_debug 
    ppf
    { call_node_name; 
      call_cond; 
      call_inputs; 
      call_oracles; 
      call_outputs } =

  Format.fprintf
    ppf
    "call %a { @[<hv>cond     = %a;@ \
                     inputs   = [@[<hv>%a@]];@ \
                     oracles  = [@[<hv>%a@]];@ \
                     outputs  = [@[<hv>%a@]]; }@]"
    (I.pp_print_ident false) call_node_name
    pp_print_conds call_cond
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
      contract;
      is_main;
      is_function;
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

  let pp_print_state_var_source ppf = 
    let p sv src = Format.fprintf ppf "%a:%s" StateVar.pp_print_state_var sv src in
    function 
      | (sv, Input) -> p sv "in"
      | (sv, Output) -> p sv "out"
      | (sv, Local) -> p sv "loc"
      | (sv, Call) -> p sv "cl"
      | (sv, Ghost) -> p sv "gh"
      | (sv, Oracle) -> p sv "or"
      | (sv, Alias (sub, _)) -> p sv (
        Format.asprintf "al(%a)"
          StateVar.pp_print_state_var sub
      )

  in

  Format.fprintf 
    ppf
    "node %a @[<hv 2>\
       { instance =  %a;@ \
         init_flag = %a;@ \
         inputs =     [@[<hv>%a@]];@ \
         oracles =    [@[<hv>%a@]];@ \
         outputs =    [@[<hv>%a@]];@ \
         locals =     [@[<hv>%a@]];@ \
         equations =  [@[<hv>%a@]];@ \
         calls =      [@[<hv>%a@]];@ \
         asserts =    [@[<hv>%a@]];@ \
         props =      [@[<hv>%a@]];@ \
         contract =   [@[<hv>%a@]];@ \
         is_main =    @[<hv>%B@];@ \
         is_function =    @[<hv>%B@];@ \
         source_map = [@[<hv>%a@]]; }@]"

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
    (fun fmt -> function
      | None -> ()
      | Some contract ->
        Format.fprintf fmt "%a@ "
          (C.pp_print_contract false) contract) contract
    is_main
    is_function
    (pp_print_list pp_print_state_var_source ";@ ") 
    (SVM.bindings state_var_source_map)


(* ********************************************************************** *)
(* Find nodes in lists                                                    *)
(* ********************************************************************** *)


(* Return true if a node of the given name exists in the a list of nodes *)
let exists_node_of_name name nodes =

  List.exists
    (function { name = node_name } -> I.equal name node_name)
    nodes


(* Return the node of the given name from a list of nodes *)
let node_of_name name nodes =

  List.find
    (function { name = node_name } -> I.equal name node_name)
    nodes


(* Return the name of the node *)
let name_of_node { name } = name


(** [ordered_equations_of_node n stateful init]
    Returns the equations of [n], topologically sorted by their base (step)
    expression if [init] ([not init]). *)
let ordered_equations_of_node { equations } stateful init =
  let svars_of ((_, _), expr) =
    expr |> if init
      then E.base_state_vars_of_init_expr
      else E.cur_state_vars_of_step_expr
  in

  let is_known eqs svar =
    List.exists (StateVar.equal_state_vars svar) stateful ||
    List.exists (fun ((sv, _), _) -> StateVar.equal_state_vars svar sv) eqs
  in

  let rec loop postponed ordered = function
    | eq :: tail ->
      if svars_of eq |> SVS.for_all (is_known ordered) then
        (* We have ordered all the state vars the lhs of the equation mentions.
           Prepending to ordered. *)
        loop postponed (eq :: ordered) tail
      else
        (* We are missing some equations, postponing the ordering of this
           equation. *)
        loop (eq :: postponed) ordered tail
    | [] -> (
      match postponed with
      | [] -> List.rev ordered
      | _ -> loop [] ordered postponed
    )
  in

  loop [] [] equations

(** Returns the equation for a state variable if any. *)
let equation_of_svar { equations } svar =
  try Some (
    equations |> List.find (fun ((svar',_),_) -> svar == svar')
  ) with Not_found -> None

(** Returns the source of a state variable if any. *)
let source_of_svar { state_var_source_map } svar =
  try Some (
    SVM.find svar state_var_source_map
  ) with Not_found -> None

(** Returns the node call the svar is the output of, if any. *)
let node_call_of_svar { calls } svar =
  let rec loop: node_call list -> node_call option = function
    | ({ call_outputs } as call) :: _ when D.exists (
      fun _ svar' -> svar == svar'
    ) call_outputs -> Some call
    | _ :: tail -> loop tail
    | [] -> None
  in
  loop calls

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


(* Node has a contract if it has a global or at least one mode contract *)
let has_contract { contract } = contract != None

let has_modes = function
| { contract = None } -> false
| { contract = Some { C.modes } } -> modes != []



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
        (fun (n, _) -> I.equal n top)
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
                   (fun (n, _) -> I.equal n call_node_name)
                   accum

                 |> snd 

               in

               if 

                 (* Callee already seen as a subsystem of this
                    node? *)
                 let call_node_name_string =
                   I.string_of_ident false call_node_name in
                 List.exists 
                   (function
                     | { SubSystem.scope = [i] } ->
                       String.equal i call_node_name_string
                     | _ -> false)
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

        (* Does node have modes? *)
        let has_modes = has_modes node in

        (* Does node have an implementation? *)
        let has_impl = not node.is_extern in

        (* Construct subsystem of node *)
        let subsystem = 

          { SubSystem.scope;
            SubSystem.source = node;
            SubSystem.has_contract;
            SubSystem.has_modes;
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
         (fun (n, _) -> I.equal n name)
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
  | FDown of t * TransSys.t *
             (TransSys.t * TransSys.instance * call_cond list) list
  | FUp of t * TransSys.t *
           (TransSys.t * TransSys.instance * call_cond list) list

let rec fold_node_calls_with_trans_sys' 
    nodes
    (f : t -> TransSys.t ->
     (TransSys.t * TransSys.instance * call_cond list) list -> 'a list -> 'a)
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
          (fun a { call_pos; call_node_name; call_cond; call_defaults } ->

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
                    Lib.compare_pos pos call_pos = 0)
                 instances'
             in

             (* Only keep call conditions that effectively sample the node
                call, i.e. not the ones where default initial values are
                provided (e.g. for interpolating condacts) *)
             let call_cond = match call_defaults with
               | None -> call_cond
               | Some _ ->
                 List.filter (function CActivate _ -> false | _ -> true)
                   call_cond
             in
             
             FDown (node', trans_sys',
                    (trans_sys, instance, call_cond) :: instances) :: a)
          (FUp (node, trans_sys, instances) :: tl)

          calls
      in

      fold_node_calls_with_trans_sys'
        nodes
        f 
        ([] :: accum)
        tl'

    (* Subsytems are in the accumulator, evaluate this system now *)
    | FUp (n, t, i) :: tl -> (

      match accum with
        | a :: b :: c ->
          
          fold_node_calls_with_trans_sys' 
            nodes
            f
            (((f n t i a) :: b) :: c) 
            tl
            
        | _ -> assert false

    )



let fold_node_calls_with_trans_sys nodes f node trans_sys =

  fold_node_calls_with_trans_sys' nodes f [[]] [FDown (node, trans_sys, [])]


(* ********************************************************************** *)
(* Stateful variables                                                     *)
(* ********************************************************************** *)


(* Return state variables that occur as previous state variables *)
let stateful_vars_of_expr { E.expr_step } = 

  Term.eval_t ~fail_on_quantifiers:false
    (function 

      (* Previous state variables have negative offset *)
      | Term.T.Var v when 
          Var.is_state_var_instance v && 
          (Numeral.(Var.offset_of_state_var_instance v < E.cur_offset)
           || Flags.Certif.certif ()) -> 

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

(* Return all stateful variables from expressions in a node *)
let stateful_vars_of_node
    { name;
      inputs; 
      oracles; 
      outputs; 
      locals;
      equations; 
      calls; 
      asserts; 
      props; 
      contract } =

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
  let stateful_vars = match contract with
    | None -> stateful_vars
    | Some contract -> C.svars_of contract |> SVS.union stateful_vars 
  in

  (* Add stateful variables from equations *)
  let stateful_vars = 
    List.fold_left
      (fun  accum (_, expr) -> 
         SVS.union accum (stateful_vars_of_expr expr))
      stateful_vars
      equations
  in

  (* TODO: this can be removed if we forbid undefined local variables.
     Unconstrained local state variables must be stateful *)
  let stateful_vars = 
    List.fold_left
      (fun a l -> 
         D.fold
           (fun _ sv a ->
              if 
                (* Arrays are global TODO maybe this is not necessary *)
                not (Type.is_array (StateVar.type_of_state_var sv)) &&
                (* Local state variable is defined by an equation? *)
                List.exists
                  (fun ((sv', _), _) -> StateVar.equal_state_vars sv sv') 
                  equations 
              then a
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
                      (fun ((sv', _), _) -> 
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
        { call_cond;
          call_inputs; 
          call_oracles;
          call_outputs; 
          call_defaults } -> 

        (* Input and output variables are always stateful *)
        ((D.values call_inputs) @ 
         call_oracles @
         (D.values call_outputs))
        
        |> SVS.of_list
        
        (* Add stateful variables from initial defaults *)
        |> SVS.union 
           (match call_defaults with 
             | None -> accum
             | Some d ->
               List.fold_left 
                 (fun accum expr -> 
                    SVS.union accum (stateful_vars_of_expr expr))
                 accum
                 (D.values d))

        (* Variables in activation and restart conditions are always
           stateful *)
        |> SVS.union
          (List.map (function | CActivate v | CRestart v -> v) call_cond
           |> SVS.of_list)
       
      ) stateful_vars calls
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
  | Call -> Format.fprintf ppf "call"
  | Ghost -> Format.fprintf ppf "ghost"
  | Alias (sv, _) ->
    Format.fprintf ppf "alias(%a)" StateVar.pp_print_state_var sv


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

(* Sets a state variable as alias for another one. *)
let set_state_var_alias node alias svar =
  Alias (
    svar,
    try Some (get_state_var_source node alias) with Not_found -> None
  ) |> set_state_var_source node alias

(* Set source of state variable if not already defined. *)
let set_state_var_source_if_undef node svar source =
  try (
    get_state_var_source node svar |> ignore ;
    node
  ) with Not_found -> set_state_var_source node svar source


let set_oracle_state_var { oracle_state_var_map } = SVT.add oracle_state_var_map

let get_oracle_state_var_map { oracle_state_var_map } = oracle_state_var_map

let set_state_var_expr { state_var_expr_map } = SVT.add state_var_expr_map

let get_state_var_expr_map { state_var_expr_map } = state_var_expr_map


(* Return true if the state variable should be visible to the user,
    false if it was created internally *)
let state_var_is_visible node state_var =
  let open Lib.ReservedIds in

  let rec visible_of_src = function
    (* Oracle inputs and abstracted streams are invisible *)
    | Call
    | Ghost
    | Oracle -> false

    (* Inputs, outputs and defined locals are visible *)
    | Input
    | Output
    | Local -> true

    (* Alias depends on source of alias. *)
    | Alias (_, None) -> false
    | Alias (_, Some src) -> visible_of_src src
  in
  
  (match get_state_var_source node state_var with
   | src -> visible_of_src src
   (* Invisible if no source set *)
   | exception Not_found -> false)
  &&
  let s = StateVar.name_of_state_var state_var in
  let r = Format.sprintf ".*\\(%s\\|%s\\|%s\\|%s\\|%s\\..*\\)$"
      state_selected_string restart_selected_string
      state_selected_next_string restart_selected_next_string "last"
  in
  let r = Str.regexp r in
  not (Str.string_match r s 0)  


let is_automaton_state_var sv =
  let open Lib.ReservedIds in
  let s = StateVar.name_of_state_var sv in
  let r = Format.sprintf "\\([^\\.]*\\)\\.\\(%s\\|%s\\)$"
      state_string restart_string
  in
  let r = Str.regexp r in
  if Str.string_match r s 0 then
    try Some (Str.matched_group 1 s, Str.matched_group 2 s)
    with Not_found -> None
  else None
    

let node_is_visible node =
  let open Lib.ReservedIds in
  let r = Format.sprintf ".*\\.\\(%s\\)\\." unless_string in
  let r = Str.regexp r in
  not (Str.string_match r (I.string_of_ident false node.name) 0)


let node_is_state_handler node =
  let open Lib.ReservedIds in
  let r = Format.sprintf ".*\\.\\(%s\\)\\.\\(.*\\)$" handler_string in
  let r = Str.regexp r in
  let s = I.string_of_ident false node.name in
  if Str.string_match r s 0 then
    try Some (Str.matched_group 2 s)
    with Not_found -> None
  else None
  

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


(* Register state var as tied to a node call if not already registered. *)
let set_state_var_node_call (
  { state_var_source_map } as node
) state_var =
  set_state_var_source_if_undef node state_var Call

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
    if List.exists (fun (p, n, sv) ->
        Lib.compare_pos p pos = 0
        && I.equal n node
        && StateVar.equal_state_vars sv state_var'
      ) instances then 

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
  
