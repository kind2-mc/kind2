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

open Lib
open LustreReporting
   
module A = LustreAst

module I = LustreIdent
module IT = LustreIdent.Hashtbl

module D = LustreIndex

module E = LustreExpr
module ET = E.LustreExprHashtbl

module C = LustreContract
module N = LustreNode

module SVM = StateVar.StateVarMap
module SVT = StateVar.StateVarHashtbl
module SVS = StateVar.StateVarSet

module VS = Var.VarSet

module Deps = LustreDependencies


(* Node not found, possible forward reference 

   This is just failing at the moment, we'd need some dependency
   analysis to recognize cycles to fully support forward
   referencing. *)
exception Node_not_found of I.t * position

exception Type_not_found of I.t * position

exception Contract_not_found of I.t * position


(* Context for typing, flattening of indexed types and constant
   propagation *)
type t = { 

  (* Previous context *)
  prev : t;
  
  (* Scope of context *)
  scope : string list ;

  (* Contract scope of the context. *)
  contract_scope: string list ;

  (* Definitions for node so far *)
  node : N.t option;

  (* Visible nodes *)
  nodes : N.t list;

  (* Node and function dependencies. *)
  (* deps : I.Set.t I.Map.t ; *)

  (* Dependencies. *)
  deps' : Deps.t ;

  (* Visible contract nodes *)
  contract_nodes : (position * A.contract_node_decl) list;

  (* Type identifiers and their types and bounds of their indexes *)
  ident_type_map : (Type.t D.t) IT.t;

    (* register bounds of state variables for later use *)
    state_var_bounds : (E.expr E.bound_or_fixed list) SVT.t;
    
  (* Identifiers and the expresssions they are bound to

     Contains a term of a variable if the identifier denotes a
     stream, and a term of an expression if the identifier denotes a
     constant. Equational definitions are not stored here, this is
     for constant propagation only. *)
  ident_expr_map : (E.t D.t) IT.t list;

  (* Map from expressions to state variables abstracting them

     This map may contain for the same expression several state
     variables with different properties (is_const, is_input,
     for_inv_gen). 

     The most recent binding shadows earlier ones, use ET.find_all
     instead of ET.find. A ET.fold will return all bindings to an
     expression. (Thus turning an annoyance of OCaml into our
     advantage.) *)
  expr_abs_map : N.equation_lhs ET.t;

  (* Map from state variables to state variables providing a
     non-deterministic pre-initial value *)
  state_var_oracle_map : StateVar.t SVT.t;

  (* Index to use for next fresh state variable *)
  fresh_local_index : int ref;

  (* Index to use for next fresh oracle state variable *)
  fresh_oracle_index : int ref;

  (* [None] if definitions are allowed, otherwise a pair of a
     message and a position to raise an error with. *)
  definitions_allowed : (Lib.position * string) option;

  (* saving inputs variables positions and their luster identifiers for error
     reporting and creation of subrange checking properties *)
  inputs_info : (StateVar.t * I.t * Lib.position) list;

  (* saving local variables positions and their luster identifiers for error
     reporting and creation of subrange checking properties *)
  locals_info : (StateVar.t * I.t * Lib.position) list;

  (* saving output variables positions and their luster identifiers for error
     reporting and creation of subrange checking properties *)
  outputs_info : (StateVar.t * I.t * Lib.position) list;

  (* Indicates there are unguarded pre's in the lustre code and we need to
  guard them. *)
  guard_pre : bool;

  free_constants : (Var.t D.t) IT.t;

  (* Map from state variables whose type has changed
     to its original integer type *)
  original_int_type : Type.t SVM.t;
}

(* Create an initial empty context 

   This must be a function, because it contains a hash table, which is
   modified in place. *)
let mk_empty_context () = 

  let rec c =
    { scope = [];
      prev = c;
      contract_scope = [];
      node = None;
      nodes = [];
      (* deps = I.Map.empty; *)
      deps' = Deps.empty;
      contract_nodes = [];
      ident_type_map = IT.create 7;
      ident_expr_map = [IT.create 7];
      expr_abs_map = ET.create 7;
      state_var_oracle_map = SVT.create 7;
      state_var_bounds = SVT.create 7;
      fresh_local_index = ref 0;
      fresh_oracle_index = ref 0;
      definitions_allowed = None;
      inputs_info = [];
      locals_info = [];
      outputs_info = [];
      guard_pre = false;
      free_constants = IT.create 7;
      original_int_type = SVM.empty;
    }
  in
  c


let set_guard_flag ctx b = { ctx with guard_pre = b }

let reset_guard_flag ctx = { ctx with guard_pre = false }

let guard_flag ctx = ctx.guard_pre


(* ********************************************************************** *)
(*                                                                        *)
(* ********************************************************************** *)

(* Set flag context to raise an error when defining an expression. *)
let fail_on_new_definition ctx pos msg = 
  { ctx with definitions_allowed = Some (pos, msg) }


(* Raise exception if no new definitions allowed *)
let raise_no_new_definition_exc = function

  (* Raise exception *)
  | { definitions_allowed = Some (pos, msg) } -> 
    fail_at_position pos msg

  (* Must not allow new definitions *)
  | _ -> assert false

  

(* Return the scope of the current node *)
let scope_of_node = function 

  (* Within a node: add node name to scope *)
  | { node = Some node } -> N.scope_of_node node

  (* Outside a node: return empty scope *)
  | { node = None } -> []



(* Return the scope of the current context *)
let scope_of_context ({ scope } as ctx) = 

  (* Start with scope of node *)
  scope_of_node ctx @ List.rev scope


(* Add scope to context *)
let push_scope ({
  scope ; ident_expr_map
} as ctx) ident = { ctx with 
  scope = ident :: scope ;
  ident_expr_map = IT.create 7 :: ident_expr_map ;
}

(* Add contract scope to context *)
let push_contract_scope ({
  contract_scope ; ident_expr_map
} as ctx) ident = { ctx with 
  contract_scope = ident :: contract_scope;
  ident_expr_map = IT.create 7 :: ident_expr_map;
}


(* Remove scope from context *)
let pop_scope = function
(* fail if at top scope *)
| { scope = [] } 
| { ident_expr_map = [] } -> raise (Invalid_argument "pop_scope")
(* Return context with first scope removed *)
| { scope = _ :: scope; ident_expr_map = _ :: ident_expr_map } as ctx -> {
  ctx with scope ; ident_expr_map
}

(* Remove contract scope from context *)
let pop_contract_scope = function
(* fail if at top scope *)
| { contract_scope = [] } 
| { ident_expr_map = [] } -> raise (Invalid_argument "pop_scope")
(* Return context with first scope removed *)
| {
  contract_scope = _ :: contract_scope ;
  ident_expr_map = _ :: ident_expr_map ;
} as ctx -> { ctx with
  contract_scope ; ident_expr_map
}

(* Contract scope of a context. *)
let contract_scope_of { contract_scope } = contract_scope


let bounds_of_index index =
  List.fold_left (fun acc -> function
      | D.ArrayVarIndex b -> E.Bound b :: acc
      | D.ArrayIntIndex i ->
        E.Fixed (E.mk_int_expr (Numeral.of_int i)) :: acc
      | _ -> acc
    ) [] index



(* Create an empty node in the context *)
let create_node = function 

  (* Already in a node or function *)
  | { node = Some _ } ->

    (* Fail *)
    (function _ -> raise (Invalid_argument "create_node"))

  (* Not in a node or function *)
  | { ident_type_map; ident_expr_map; expr_abs_map } as ctx -> 

    (fun ident is_extern ->

      (* Add empty node to context *)
      { ctx with
        prev = ctx;
        (* Make deep copies of hash tables *)
        ident_type_map = IT.copy ident_type_map;
        ident_expr_map = List.map IT.copy ident_expr_map;
        expr_abs_map = ET.copy expr_abs_map;
        fresh_local_index = ref !(ctx.fresh_local_index);
        fresh_oracle_index = ref !(ctx.fresh_oracle_index);
        node = Some (N.empty_node (ident, None, None) is_extern) } )

(** Maps something to the current node. *)
let current_node_map = function
  | { node = Some node } as ctx -> (
    fun f -> { ctx with node = Some (f node) }
  )
  | ctx -> (fun _ -> ctx)


(** Returns the modes of the current node. *)
let current_node_modes = function
| { node = None } -> None
| { node = Some { N.contract } } -> Some (
  match contract with
  | None -> None
  | Some { C.modes } -> Some modes
)

(* Returns the name of the current node, if any. *)
let current_node_name = function
| { node = Some { N.name = (name, _, _) } } -> Some name
| { node = None } -> None

(** Returns the calls made by the current node, if any. *)
let current_node_calls = function
| { node = Some { N.calls } } -> calls
| { node = None } -> raise (Invalid_argument "current_node_calls")


(* Create an empty function in the context *)
let create_function = function 

  (* Already in a node or function *)
  | { node = Some _ } ->

    (* Fail *)
    (function _ -> raise (Invalid_argument "create_function"))

  (* Not in a node or function *)
  | { ident_type_map; ident_expr_map; expr_abs_map } as ctx -> 

    (function _ (* ident *) -> 

      (* Add empty function to context *)
      { ctx with 

          (* Make deep copies of hash tables *)
          ident_type_map = IT.copy ident_type_map;
          ident_expr_map = List.map IT.copy ident_expr_map;
          fresh_local_index = ref !(ctx.fresh_local_index);
          fresh_oracle_index = ref !(ctx.fresh_oracle_index);
          expr_abs_map = ET.copy expr_abs_map } )


let add_free_constant ctx ident vt =
  IT.add ctx.free_constants ident vt 


let get_free_constants ctx =
  IT.fold (fun i vt acc -> (i, vt) :: acc) ctx.free_constants []


let free_constant_expr_of_ident ctx ident =
  IT.find ctx.free_constants ident |>
  D.map E.mk_free_var

(* Add a binding of an identifier to an expression to context *)
let add_expr_for_ident ?(shadow = false) ({ident_expr_map} as ctx) ident expr = 

  (* Must have at least a map for the top level *)
  assert (ident_expr_map <> []);

  (* TODO: This is a temporary fix *)
  if  IT.mem (List.hd ident_expr_map) ident then IT.remove (List.hd ident_expr_map) ident ;

  (* Fail if hash table for the current scope already contains a
     binding to the identifier, and if the binding should not shadow,
     then also if some of the lower scopes contains a binding to the
     identifier. *)
  if 
    (* TODO check this *)
    IT.mem (List.hd ident_expr_map) ident ||  
    (not shadow &&
     List.exists (fun m -> IT.mem m ident) (List.tl ident_expr_map))

  then

    raise (Invalid_argument
             ("add_expr_for_ident: "^I.string_of_ident false ident))

  else
    
    (* Modify hash table in place *)
    IT.add (List.hd ident_expr_map) ident expr; 
  
  (* Return context *)
  ctx


(* Add a binding of an identifier to an expression to context *)
let [@ocaml.warning "-27"] add_expr_for_indexed_ident
    ?(shadow = false)
    ({ ident_expr_map } as ctx) 
    ident 
    index 
    expr = 

  try 

    (* Must have at least a map for the top level *)
    assert (ident_expr_map <> []);

    (* Get trie for expression *)
    let t = IT.find (List.hd ident_expr_map) ident in

    (* Disable temporarily this check because it is very restrictive
    if 

      (* Fail if trie for the idnetifier in the current scope already
         contains a binding to the index, and if the binding should
         not shadow, then also if some of the lower scopes contains a
         binding to the index in the trie for the identifier. *)
      (D.mem index t)
      || 
      (not shadow
       &&
       (List.exists 
          (fun m -> 
             try IT.find m ident |> D.mem index with Not_found -> false)
          (List.tl ident_expr_map)))

    then
      raise (Invalid_argument "add_expr_for_ident")    

    else*)

      (* Add expression for index to trie *)
      let t' = D.add index expr t in

      (* Add modified trie in-place to the hash table *)
      IT.add (List.hd ident_expr_map) ident t';

      (* Return context *)
      ctx

  with Not_found -> 

    (* Add expression with index to empty trie and add to hash table
       in-place *)
    IT.add (List.hd ident_expr_map) ident (D.singleton index expr);

    (* Return context *)
    ctx


(* Add a binding of an identifier to an expression to context *)
let remove_expr_for_ident ({ ident_expr_map } as ctx) ident = 

  (* Ensure the hash table does not already contain the expression *)
  if not (List.exists (fun m -> IT.mem m ident) ident_expr_map) then 

    raise (Invalid_argument "remove_expr_for_ident")

  else (

      (* Must have at least a map for the top level *)
      assert (ident_expr_map <> []);

      (* Modify hash table in place *)
      IT.remove (List.hd ident_expr_map) ident; 
      
      (* Return context *)
      ctx
  )


(* Add a binding of an identifier to a type to context *)
let add_type_for_ident ({ ident_type_map } as ctx) ident l_type = 

  (* Modify hash table in place *)
  IT.add ident_type_map ident l_type; 

  (* Return context *)
  ctx


(* Return nodes defined in all contexts *)
let rec get_nodes ({ prev; nodes } as ctx) =
  if ctx == prev then nodes
  else nodes @ get_nodes prev

(* Return the current node in context. *)
let get_node { node } = node


let prev { prev } = prev

(* Return state vars indexes hash  table  *)
let get_state_var_bounds { state_var_bounds } = state_var_bounds
(* Return a contract node by its identifier *)
let contract_node_decl_of_ident { contract_nodes } ident = 

  try 
    
    (* Return contract node by name *)
    List.find
      (function (_, (i, _, _, _, _)) -> i = ident)
      contract_nodes

  (* Raise error again for more precise backtrace *)
  with Not_found -> raise Not_found


(** The contract nodes in the context. *)
let contract_nodes { contract_nodes } = List.map snd contract_nodes

(* Add a contract node to the context for inlining later *)
let add_contract_node_decl_to_context
    ({ contract_nodes } as ctx)
    (pos, ((ident, _, _, _, _) as contract_node_decl)) =

  if 

    (* Check if contract of with the same identifier exists *)
    List.exists
      (function (_, (i, _, _, _, _)) -> i = ident)
      contract_nodes

  then

    fail_at_position
      pos
      "Contract node already defined"
      
  else

    (* Add contract node to context *)
    { ctx with contract_nodes = (pos, contract_node_decl) :: contract_nodes }


(* Set source of state variable in a context *)
let set_state_var_source = function 

  (* Must be in a node *)
  | { node = Some n } as ctx -> 

    (fun state_var state_var_source -> 

       (* Update sources of state variables in node *)
       let n' = N.set_state_var_source n state_var state_var_source in

       (* Return modified context *)
       { ctx with node = Some n'})
        
  (* Fail if not in a node *)
  | { node = None } -> 

    function _ -> function _ -> 
      raise (Invalid_argument "set_state_var_source")


(* Create a state variable for from an indexed state variable in a
   scope *)
let mk_state_var
    ?is_input
    ?is_const
    ?for_inv_gen 
    ?(shadow = false)
    ctx
    scope
    ident 
    index 
    state_var_type
    state_var_source = 

  (* Concatenate identifier and indexes *)
  let state_var_name = 
    Format.asprintf "%a%a"
      (I.pp_print_ident true) ident
      (D.pp_print_index true) 

      (* Filter out array indexes *)
      (List.filter
         (function 
           | D.ArrayVarIndex _ 
           | D.ArrayIntIndex _ -> false
           | D.RecordIndex _
           | D.TupleIndex _
           | D.ListIndex _
           | D.AbstractTypeIndex _ -> true)
         index)
  in

  (* For each index add a scope to the identifier to distinguish the
     flattened indexed identifier from unindexed identifiers

     The scopes indicate the positions from the back of the string in
     the flattened identifier where a new index begins.

     The following indexed identifiers are all flattened to x_y_z, but
     we can distinguish them by their scopes:

     x_y_z  [] 
     x.y.z  [2;2]
     x.y_z  [4]
     x_y.z  [2]

  *)
  let flatten_scopes = D.mk_scope_for_index index in

  (* Create or retrieve state variable *)
  let state_var =
  (* TODO check this *)
    try
      StateVar.state_var_of_string
        (state_var_name,
         (List.map Ident.to_string (scope @ flatten_scopes)))
    with Not_found ->
      StateVar.mk_state_var
        ?is_input
        ?is_const
        ?for_inv_gen 
        state_var_name
        (scope @ flatten_scopes)
        state_var_type 
  in

  (* Register bounds for indexes *)
  if index <> [] then
    SVT.add ctx.state_var_bounds state_var (bounds_of_index index);

  (* Set source of state variable *)
  let ctx = match state_var_source with 
    | Some s -> set_state_var_source ctx state_var s 
    | None -> ctx
  in

  (* Create expression from state variable *)
  let expr = E.mk_var state_var in

  (* Bind state variable to identifier *)
  let ctx = 

    (* State variable without index? *)
    (if index = D.empty_index then

       (* Create singleton trie for identifier *)
       D.singleton D.empty_index expr
       |> add_expr_for_ident ~shadow ctx ident 

     else

       (* Add to exisiting trie or create new trie for identifier*)
       add_expr_for_indexed_ident ~shadow ctx ident index expr)
    
  in

  (* Return state variable and changed context *)
  state_var, ctx


(* Exception because can't iterate manually over bindings in hash
   tables. *)
exception FoundIt of E.t

(* Resolve an svar to an expression *)
let expr_of_svar { expr_abs_map } svar =
  try
    expr_abs_map |> ET.iter (
      fun expr (svar', _) ->
        (* Format.printf "  - %a@." StateVar.pp_print_state_var svar ; *)
        if svar == svar' then raise (FoundIt expr) else ()
    ) ;
    None
  with FoundIt expr -> Some expr



(* Resolve an indentifier to an expression in all scopes *)
let rec expr_of_ident' ident = function 

  | [] -> raise Not_found

  | m :: tl ->
    try IT.find m ident with Not_found -> expr_of_ident' ident tl


(* Resolve an indentifier to an expression *)
let expr_of_ident { ident_expr_map } ident =
  expr_of_ident' ident ident_expr_map


(* Return true if the identifier denotes an output or local variable *)
let assignable_state_var_of_ident = function 

  (* No node in context *)
  | { node = None } -> 

    (function _ -> 
      raise (Invalid_argument "assignable_state_var_of_ident"))

  (* Get locals and outputs from node in context *)
  | { node = Some { N.locals; N.outputs } } as ctx ->

    (function ident -> 

      try 

        (* Get expression from identifier *)
        let expr = expr_of_ident ctx ident in 

        D.map 
          (fun e -> 
        
             (* Expression is a variable *)
             if E.is_var e then 
               
               (* Get state variable of expression *)
               let state_var = E.state_var_of_expr e in 

               if 

                 (* Find state variable in outputs *)
                 D.exists 
                   (fun _ sv -> StateVar.equal_state_vars state_var sv)
                   outputs
                   
                 || 
                 
                 (* Find state variable in locals *)
                 List.exists 
                   (D.exists 
                      (fun _ sv -> StateVar.equal_state_vars state_var sv))
                   locals
                   
               then 
                 
                 (* Return state variable *)
                 state_var
                   
               (* State variable is not a local variable or output *)
               else
                 
                 raise (Invalid_argument "assignable_state_var_of_ident")

            (* Expression is not a variable *)
            else 

              raise (Invalid_argument "assignable_state_var_of_ident"))

          expr
     
              
      (* Identifier does not denote an expression *)
      with Not_found -> raise Not_found)


(* Resolve an indentifier to an expression *)
let type_of_ident { ident_type_map } ident = IT.find ident_type_map ident 


(* Return true if identifier has been declared, raise an exception if
   the identifier is reserved. *)
let expr_in_context { ident_expr_map } ident = 

  (* Return if identifier is in context *)
  (List.exists (fun m -> IT.mem m ident) ident_expr_map) 


(* Return true if identifier has been declared, raise an exception if
   the identifier is reserved. *)
let type_in_context { ident_type_map } ident = 

  (* Return if identifier is in context *)
  (IT.mem ident_type_map ident) 


(* Return true if node has been declared in the context *)
let node_in_context ctx ident = 
  
  (* Return if identifier is in context or previous contexts *)
  N.exists_node_of_name (ident, None, None) (get_nodes ctx)
    

(* Return true if property name has been declared in the context *)
let prop_name_in_context ctx ident =
  match ctx with
  | { node = None } -> false
  | { node = Some ({ N.props }) } ->
    List.exists (fun (_, name, _, _) -> name = ident) props

let original_int_type { original_int_type } svar =
  SVM.find_opt svar original_int_type

(* Add newly created variable to locals *)
let add_state_var_to_locals = function 
  | { node = None } -> (function _ -> assert false)
  | { node = Some ({ N.locals } as node) } as ctx ->

    (function state_var -> 

      { ctx with 
          node = Some { node with 
                          N.locals = 
                            D.singleton D.empty_index state_var :: locals} })

let add_node_oracle = function
  | { node = None } -> (fun _ -> assert false)
  | { node = Some node } as ctx ->
    fun state_var ->
      ctx.fresh_oracle_index := succ !(ctx.fresh_oracle_index) ;
      { ctx with node = Some { node with 
                      N.oracles = state_var :: node.N.oracles} }


(* Create a fresh state variable as an oracle input *)
let mk_fresh_oracle 
    ?is_input
    ?is_const
    ?for_inv_gen
    ?(bounds = [])
    ({ node; definitions_allowed; fresh_oracle_index } as ctx) 
    state_var_type =

  let state_var_type = Type.generalize state_var_type in
  
  match definitions_allowed with 

    (* Fail with error if no new definitions allowed *)
    | Some (pos, msg) -> fail_at_position pos msg

    (* Continue if definitions allowed *)
    | _ -> 

      (* Are we in a node? *)
      match node with 

        (* Fail if not inside a node *)
        | None -> raise (Invalid_argument "mk_fresh_oracle")

        (* Add to oracles *)
        | Some _ ->

          (* Create state variable for abstraction *)
          let state_var, ctx = 
            mk_state_var 
              ?is_input:is_input
              ?is_const:is_const
              ?for_inv_gen:for_inv_gen
              ctx
              (scope_of_node ctx @ I.reserved_scope)
              (I.push_index I.oracle_ident !fresh_oracle_index)
              D.empty_index
              state_var_type
              (Some N.Oracle)
          in

          (* Register bounds *)
          SVT.add ctx.state_var_bounds state_var bounds;
          
          (* Increment index of fresh oracle *)
          let ctx = add_node_oracle ctx state_var in

          (* Return variable and changed context *)
          (state_var, ctx)


(* Associate oracle with state variable *)
let set_state_var_oracle ctx state_var oracle =
  SVT.add ctx.state_var_oracle_map state_var oracle;
  match ctx with
  | { node = Some n } ->
    (* Register inverse binding in node *)
    N.set_oracle_state_var n oracle state_var
  | _ -> ()


(* Create a fresh state variable as an oracle input for the state variable *)
let mk_fresh_oracle_for_state_var
    ?bounds
    ctx 
    state_var =

  (* Create fresh oracle *)
  let state_var', ctx = 
    mk_fresh_oracle
      ~is_const:true 
        (* ?bounds *)
        ~bounds:(let b =
                  try SVT.find ctx.state_var_bounds state_var
                  with Not_found -> [] in
                match bounds with None | Some [] -> b | Some b' -> b @ b')
      ctx
      (StateVar.type_of_state_var state_var)
  in

  (* Associate oracle with state variable *)
  set_state_var_oracle ctx state_var state_var';
  (* SVT.add state_var_oracle_map state_var state_var'; *)

  (* Return changed context

     The hash table of state variables to their oracles has been
     modfied in place. *)
  state_var', ctx


(* Guard unguarded pre expression with a fresh oracle constant

   An unguarded pre is a previous state variable occuring in the
   initial state expression, since the arrow operator has been lifted
   to the top of the expression. *)
let [@ocaml.warning "-27"] close_expr ?(bounds=[]) ?original pos ({ E.expr_init } as expr, ctx) =     

  (* Get variables in initial state term *)
  let init_vars = Term.vars_of_term (expr_init :> Term.t) in

  let unguarded =
    VS.exists 
      (fun var -> 
         Var.is_state_var_instance var &&
         Numeral.(Var.offset_of_state_var_instance var < E.base_offset))
      init_vars
  in
  
  (* Filter for variables before the base instant *)
  (* let init_pre_vars =  *)
  (*   VS.filter  *)
  (*     (fun var ->  *)
  (*        Var.is_state_var_instance var && *)
  (*        Numeral.(Var.offset_of_state_var_instance var < E.base_offset)) *)
  (*     init_vars *)
  (* in *)

  
  (* No unguarded pres in initial state term? *)
  if not unguarded then (expr, ctx )
  else

    let rctx = ref ctx in
    let expr_init = E.map_vars_expr (fun var ->
        if Var.is_state_var_instance var &&
           Numeral.(Var.offset_of_state_var_instance var < E.base_offset) then
          let state_var = Var.state_var_of_state_var_instance var in
          let state_var', ctx = mk_fresh_oracle_for_state_var !rctx state_var in
          rctx := ctx;
          E.base_var_of_state_var E.base_offset state_var'
        else var
      ) expr_init
    in

    E.mk_arrow (E.mk_of_expr ~as_type:expr.E.expr_type expr_init) expr, !rctx

    (* (\* New oracle for each state variable *\) *)
    (* let oracle_substs, ctx = VS.fold (fun var (accum, ctx) ->  *)

    (*     (\* We only expect state variable instances *\) *)
    (*     assert (Var.is_state_var_instance var); *)

    (*     (\* State variable of state variable instance *\) *)
    (*     let state_var = Var.state_var_of_state_var_instance var in *)

    (*     (\* Create a new oracle variable or re-use previously created oracle *\) *)
    (*     let state_var', ctx = mk_fresh_oracle_for_state_var ctx state_var in *)

    (*     (\* Substitute oracle variable for variable *\) *)
    (*     (state_var, E.mk_var state_var') :: accum, ctx *)

    (*   ) init_pre_vars ([], ctx) *)
    (* in *)

    (* (\* Return expression with all previous state variables in the init *)
    (*    expression substituted by fresh constants *\) *)
    (* E.mk_arrow (E.mk_let_pre oracle_substs expr) expr, ctx (\* {ctx with guard_pre = true}  *\) *)

(* Record mapping of expression to state variable

   This will shadow but not replace a previous definition. Use
   [find_all] to retrieve the definitions, and the usual
   [fold] to iterate over all definitions. *)
let set_expr_state_var ctx expr (state_var, bounds) =
  ET.add ctx.expr_abs_map expr (state_var, bounds);
  match ctx with
  | { node = Some n } ->
    (* register inverse binding in node *)
    N.set_state_var_expr n state_var expr
  | _ -> ()

let has_var_index_t vi t =
  Var.VarSet.mem vi (Term.vars_of_term t)

let has_var_index vi expr =
  Var.VarSet.mem vi (E.vars_of_expr expr)

let bounds_of_expr bounds ctx expr =
  let sel_terms =
    Term.TermSet.union
      (Term.select_terms (E.unsafe_term_of_expr expr.E.expr_init))
      (Term.select_terms (E.unsafe_term_of_expr expr.E.expr_step))
  in
  let i = ref (-1) in
  List.map (fun bnd -> incr i; match bnd with
      | E.Bound _ | E.Fixed _ | E.Unbound _ ->
        let vi = match bnd with
          | E.Unbound e -> E.mk_of_expr e |> E.var_of_expr
          | _ -> E.mk_index_var !i |> E.var_of_expr
        in
        try
          let t = Term.TermSet.filter (has_var_index_t vi) sel_terms
                  |> Term.TermSet.choose in
          let v, tind = Term.indexes_and_var_of_select t in
          let sv = Var.state_var_of_state_var_instance v in
          let bnds_sv = SVT.find ctx.state_var_bounds sv in
          List.fold_left2 (fun acc b ti -> 
              if has_var_index_t vi ti then (vi, b) else acc
            ) (vi, bnd) bnds_sv tind
        with Not_found | Invalid_argument _ -> (vi, bnd)
          (* if has_var_index vi expr then bnd :: acc else acc *)
    ) bounds
  


let fresh_state_var_for_expr
    ?(is_input = false)
    ?(is_const = false)
    ?(for_inv_gen = true)
    ?(reuse = true)
    bounds
    present_bounds
    present_bounds'
    ({ fresh_local_index } as ctx)
    after_mk
    expr
    expr_type
  = 

  (* Don't abstract simple state variables *)
  if reuse && (E.is_var expr || E.is_const_var expr) then
  
      let v = E.var_of_expr expr in
      let sv = Var.state_var_of_state_var_instance v in
      (sv, bounds), ctx

  else if reuse && E.is_select_array_var expr && present_bounds <> [] then

      let (v, ixes) = E.indexes_and_var_of_array_select expr in
      let sv = Var.state_var_of_state_var_instance v in
      let ixes' = List.map (fun i -> E.Unbound i) ixes in
      (sv, ixes'), ctx

  else

    (* Create state variable for abstraction *)
    let state_var, ctx = 
      mk_state_var 
        ~is_input:is_input
        ~is_const:is_const
        ~for_inv_gen:for_inv_gen
        ctx
        (scope_of_node ctx @ I.reserved_scope)
        (I.push_index I.abs_ident !fresh_local_index)
        D.empty_index
        expr_type
        None
    in

    (* Register bounds *)
    SVT.add ctx.state_var_bounds state_var bounds;

    (* Add bounds from array definition if necessary *)
    let abs = state_var, present_bounds in
    let abs' = state_var, present_bounds' in

    (* Record mapping of expression to state variable (or term)

       This will shadow but not replace a previous definition. Use
       [find_all] to retrieve the definitions, and the usual
       [fold] to iterate over all definitions. *)
    set_expr_state_var ctx expr abs';
    
    (* Evaluate continuation after creating new variable *)
    let ctx = after_mk ctx state_var in

    (* Hash table is modified in place, increment index of fresh state
       variable *)
    ctx.fresh_local_index := succ !fresh_local_index ;

    (* Return variable and changed context *)
    (abs, ctx)
    
    
    
(* Define the expression with a state variable *)
let mk_abs_for_expr
    ?(is_input = false)
    ?(is_const = false)
    ?(for_inv_gen = true)
    ?(bounds = [])
    ?(reuse = true)
    ({ expr_abs_map } as ctx)
    after_mk
    ({ E.expr_type } as expr) = 

  let bounds' = bounds_of_expr bounds ctx expr in

  (* new array if there are bound variables *)
  let expr_type, expr, present_bounds, present_bounds', _ =
    List.fold_left2 (fun (ty, expr, bounds_acc, bounds_acc', i) ->
        let vi = E.mk_index_var i |> E.var_of_expr in
        fun b1 bp -> match b1 with
          | ev, ((E.Bound b | E.Fixed b) as bnd)
            when Var.equal_vars ev vi ->
            if not (has_var_index vi expr) then
              ty, expr, bounds_acc, bounds_acc', i
            else
              Type.mk_array ty
                (if E.is_numeral b then
                   Type.mk_int_range (Some Numeral.zero) (Some (E.numeral_of_expr b))
                 else Type.t_int),
              expr,
              bp :: bounds_acc,
              bnd :: bounds_acc',
              succ i
          | ev, (E.Unbound b | E.Bound b | E.Fixed b as bnd) ->
            if not (has_var_index ev expr) then
              ty, expr, bounds_acc, bounds_acc', i
            else
              let it = vi |> Term.mk_var |> E.unsafe_expr_of_term in
              Type.mk_array ty (E.type_of_expr b),
              E.apply_subst [ev, it] expr,
              bp :: bounds_acc,
              (bnd) :: bounds_acc',
              succ i
      ) (expr_type, expr, [], [], 0)
      (List.rev bounds') (List.rev bounds) in

  let present_bounds = List.rev present_bounds in
  let present_bounds' = List.rev present_bounds' in
  
  if not reuse then
    
    fresh_state_var_for_expr ~is_input ~is_const ~for_inv_gen ~reuse
      bounds present_bounds present_bounds' ctx after_mk expr expr_type
      
  else
    try 

    (* Format.eprintf "mk_abs_for_expr %a %a@." (E.pp_print_lustre_expr false) expr *)
    (* (pp_print_listi *)
    (*    (fun ppf i -> function *)
    (*       | E.Bound e -> *)
    (*         Format.fprintf *)
    (*           ppf *)
    (*           "[%a(%a)]" *)
    (*           (I.pp_print_ident false) *)
    (*           (I.push_index I.index_ident i) *)
    (*           (E.pp_print_expr false) e *)
    (*       | E.Fixed e -> Format.fprintf ppf "[%a]" (E.pp_print_expr false) e *)
    (*       | E.Unbound e -> Format.fprintf ppf "[%a]" (E.pp_print_expr false) e) *)
    (*    "") present_bounds'; *)

    
    (* Find previous definition of expression

       Use [find_all] to get all state variables that define the
       expression. *)
    let lhs_list = ET.find_all expr_abs_map expr in
    
    (* Find state variable with same properties *)
    let abs_sv, _ = 
      List.find
        (fun (sv, b) ->
           b = present_bounds' &&
           StateVar.is_input sv = is_input && 
           StateVar.is_const sv = is_const && 
           StateVar.for_inv_gen sv = for_inv_gen)
        lhs_list
    in


    (* Return state variable used before *)
    ((abs_sv, present_bounds), ctx)

  (* Expresssion has not been abstracted before *)
  with Not_found ->

    (* If it's not there already, create a new state variable *)
    fresh_state_var_for_expr ~is_input ~is_const ~for_inv_gen ~reuse
      bounds present_bounds present_bounds' ctx after_mk expr expr_type
  


(* Define the expression with a state variable *)
let mk_local_for_expr
    ?is_input
    ?is_const
    ?for_inv_gen
    ?bounds
    ?(reuse=true)
    ?(is_ghost=false)
    ?original
    pos
    ({ node; 
       definitions_allowed } as ctx)
    expr =

  match definitions_allowed with 

    (* Fail with error if no new definitions allowed *)
    | Some (pos, msg) -> fail_at_position pos msg

    (* Continue if definitions allowed *)
    | _ -> 

      (* Are we in a node? *)
      match node with 

        (* Fail if not inside a node *)
        | None -> raise (Invalid_argument "mk_local_for_expr")

        (* Add to locals *)
        | Some _ ->

          (* Guard unguarded pres before adding definition *)
          let expr', ctx = close_expr ?bounds ?original pos (expr, ctx) in

          (* Define the expression with a fresh abstraction *)
          let ((state_var, _) as abs), ctx = 
            mk_abs_for_expr
              ?is_input
              ?is_const
              ?for_inv_gen
              ?bounds
              ~reuse
              (* ~reuse:(not ctx.guard_pre) *)
              ctx add_state_var_to_locals expr'
          in

          let ctx =
            (* Get most updated version of node *)
            let node = get (get_node ctx) in
            if is_ghost then (
              (* Don't change source of svar if already there. *)
              try
                N.get_state_var_source node state_var |> ignore ;
                ctx
              with Not_found -> {
                ctx with node = Some (
                  N.set_state_var_source node state_var N.Generated
                )
              }
            ) else ctx
          in

          (* Return variable and changed context *)
          (abs, ctx)


(* Create a fresh abstraction as an oracle input *)
let mk_fresh_local
    ?is_input
    ?is_const
    ?for_inv_gen
    ?(bounds=[])
    ({ node; fresh_local_index } as ctx) 
    state_var_type =

  (* Are we in a node? *)
  match node with 

    (* Fail if not inside a node *)
    | None -> raise (Invalid_argument "mk_fresh_local")

    (* Add to locals *)
    | Some { N.locals } ->

      (* Create state variable for abstraction *)
      let state_var, ctx = 
        mk_state_var 
          ?is_input:is_input
          ?is_const:is_const
          ?for_inv_gen:for_inv_gen
          ctx
          (scope_of_node ctx @ I.reserved_scope)
          (I.push_index I.abs_ident !fresh_local_index)
          D.empty_index
          state_var_type
          None
      in

      (* Register bounds *)
      SVT.add ctx.state_var_bounds state_var bounds;


      (* Increment index of fresh oracle *)
      ctx.fresh_local_index := succ !fresh_local_index ;
      let ctx = 
        match ctx with
          | { node = None } -> assert false
          | { node = Some node } ->
            { ctx with 
                node = Some { node with 
                   N.locals = D.singleton D.empty_index state_var :: locals } }
      in

      (* Return variable and changed context *)
      (state_var, ctx)

(* Return the node of the given name from the context*)
let rec node_of_name ({ prev; nodes } as ctx) ident =
  try N.node_of_name (ident, None, None) nodes
  with Not_found ->
    if ctx == prev then raise Not_found
    else node_of_name prev ident


(* Return the output variables of a node call in the context with the
   same parameters *)
let call_outputs_of_node_call 
    { node } 
    ident
    cond_var
    input_state_vars 
    defaults = 

  (* Are we in a node? *)
  match node with 

    (* Fail if not inside a node *)
    | None -> raise (Invalid_argument "call_outputs_of_node_call")

    (* Add to node calls *)
    | Some { N.calls } ->

      try 

        (* Find a call to the same node on the same clock with the same
           inputs in this node *)
        let { N.call_outputs } = 

          List.find
            (fun { N.call_cond = call_cond;
                   N.call_defaults = call_defaults;
                   N.call_node_name = (call_ident, _, _);
                   N.call_inputs = call_inputs } -> 

              (* Call must be to the same node, and ... *)
              (I.equal ident call_ident) &&

              (* ... activation and restart conditions must be equal, and ... *)
              (try List.for_all2 (fun c c' -> match c, c' with

                (* Both calls are with an activation condition *)
                | N.CActivate v, N.CActivate v' -> 
                  (* Same activation condition *)
                  StateVar.equal_state_vars v v' &&
                  (* Same defaults *)
                  (match defaults, call_defaults with
                    | None, None -> true
                    | Some d1, Some d2 -> 
                      D.for_all2
                        (fun _ sv1 sv2 -> E.equal sv1 sv2)
                        d1 
                        d2
                    | None, Some _ 
                    | Some _, None -> false)

                (* Both calls are with a restart condition *)
                | N.CRestart v, N.CRestart v' ->
                  StateVar.equal_state_vars v v' 

                (* (\* Both calls without activation condtion *\) *)
                (* | N.CNone, N.CNone -> true *)

                (* One call with and the other without condition *)
                | _ -> false)
                   cond_var call_cond
               with Invalid_argument _ -> false)
              &&
                            
              (* ... inputs must be the same up to oracles *)
              D.for_all2 
                (fun _ sv1 sv2 -> StateVar.equal_state_vars sv1 sv2)
                input_state_vars
                call_inputs)

            calls

        in

        (* Return output variables from node call to re-use *)
        Some call_outputs

      (* No node call found *)
      with Not_found -> None

(* Add node input to context *)
let add_node_input ?is_const ctx ident pos index_types =

  match ctx with 

    | { node = None } -> raise (Invalid_argument "add_node_input")

    | { node = Some { N.inputs } } -> 

      (* Get next index at root of trie *)
      let next_top_idx = D.top_max_index inputs |> succ in

      (* Add state variables for all indexes of input *)
      let inputs', ctx = 
        D.fold
          (fun index index_type (accum, ctx) ->
         
             (* Create state variable as input and contant *)
             let state_var, ctx = 
               mk_state_var
                 ~is_input:true
                 ?is_const
                 ctx
                 (scope_of_node ctx @ I.user_scope)
                 ident
                 index
                 index_type
                 (Some N.Input)
             in
             
             (* Register input declarations positions for later *)
             let ctx  =
               { ctx with
                 inputs_info = (state_var, ident, pos) :: ctx.inputs_info }
             in

             (* Add expression to trie of identifier *)
             (D.add (D.ListIndex next_top_idx :: index) state_var accum, ctx))
             
          index_types
          (inputs, ctx)
      in

      (* Return node with input added *)
      match ctx with
        | { node = None } -> assert false
        | { node = Some node } ->
          { ctx with node = Some { node with N.inputs = inputs' } }


(* Add node output to context *)
let add_node_output ?(is_single = false) ctx ident pos index_types = 

  match ctx with 

    | { node = None } -> raise (Invalid_argument "add_node_output")

    | { node = Some { N.outputs } } -> 

      (* Get next index at root of trie *)
      let next_top_idx = D.top_max_index outputs |> succ in

      let outputs', ctx = 
        D.fold
          (fun index index_type (accum, ctx) ->
         
             (* Create state variable as input and contant *)
             let state_var, ctx = 
               mk_state_var
                 ~is_input:false
                 ctx
                 (scope_of_node ctx @ I.user_scope)
                 ident
                 index
                 index_type
                 (Some N.Output)
             in
             
             let index' = 
               if is_single then index else 
                 D.ListIndex next_top_idx :: index
             in

             (* Register local declarations positions for later *)
             let ctx  =
               { ctx with
                 outputs_info = (state_var, ident, pos) :: ctx.outputs_info }
             in

             (* Add expression to trie of identifier *)
             (D.add index' state_var accum, ctx))
             
          index_types
          (outputs, ctx)
      in

      (* Return node with outputs added *)
      match ctx with
        | { node = None } -> assert false
        | { node = Some node } ->
          { ctx with node = Some { node with N.outputs = outputs' } }

(* The output state variables of the current node. *)
let outputs_of_current_node = function
| { node = None } -> raise (Invalid_argument "outputs_of_current_node")
| { node = Some { N.outputs } } -> outputs


(* Add node local to context *)
let add_node_local ?(ghost = false) ctx ident pos index_types = 

  match ctx with 

    | { node = None } -> raise (Invalid_argument "add_node_local")

    | { node = Some { N.locals } } -> 

      (* Create state variable for each stream *)
      let local, ctx = 
        D.fold
          (fun index index_type (accum, ctx) ->
             
             (* Create state variable as input and contant *)
             let state_var, ctx = 
               mk_state_var
                 ~is_input:false
                 ~shadow:ghost
                 ctx
                 (scope_of_context ctx @ I.user_scope)
                 ident
                 index
                 index_type
                 (if ghost then Some N.Ghost else Some N.Local)
             in

             (* Register local declarations positions for later *)
             let ctx  =
               { ctx with
                 locals_info = (state_var, ident, pos) :: ctx.locals_info }
             in
             
             (* Add expression to trie of identifier *)
             (D.add index state_var accum, ctx))
             
          index_types
          (D.empty, ctx)
      in

      (* Return node with local variable added *)
      match ctx with
        | { node = None } -> assert false
        | { node = Some node } ->
          { ctx with node = Some { node with N.locals = local :: locals } }

(** The svars in the COI of the input expression, in the current node.

Returns [None] if there's no current node.
Raises [Not_found] if some svars in the COI do not have an equation and are
not outputs of node calls.

Used to check that the assumes and requires of a contract do not mention
the outputs. *)
let trace_svars_of ctx expr = match ctx with
| { node = None } -> None | { node = (Some node) } -> (

  (* Svars of an expression. *)
  let svars_of e =
    E.base_state_vars_of_init_expr e
    |> SVS.union (E.cur_state_vars_of_step_expr e)
  in
  (* Set of an index. *)
  let to_set idx = D.fold ( fun _ elm set -> SVS.add elm set ) idx SVS.empty in
  (* $(a \setminus b) \cup c$ *)
  let diff_union a b c = SVS.diff a b |> SVS.union c in

  let rec loop (mem, to_do) =
    if SVS.is_empty to_do then mem else (
      (mem, SVS.empty) |> SVS.fold (
        fun svar (mem, to_do) ->
          let mem = SVS.add svar mem in
          match (
            (* Fresh vars do not have a source, catching that here. *)
            try N.get_state_var_source node svar with Not_found -> N.Local
          ) with
          | N.Oracle
          | N.Input
          | N.Output -> mem, to_do
          | N.Local
          | N.Ghost
          | N.Generated
          (* | N.Alias (_,_) *)
          | N.Call -> (
            let svars =
              (* Do we have an equation for svar? *)
              match N.equation_of_svar node svar with
              | Some (_, expr) -> svars_of expr
              | None -> (
                (* Is it the output of a node call? *)
                match N.node_call_of_svar node svar with
                | Some { N.call_inputs } -> to_set call_inputs
                | None -> (
                  (* Is it purely contextual?. *)
                  match expr_of_svar ctx svar with
                  | Some expr -> svars_of expr
                  | None -> raise Not_found
                )
              )
            in
            mem, diff_union svars mem to_do
          )
      ) to_do
      |> loop
    )
  in
  Some (
    (SVS.empty, svars_of expr) |> loop
  )
)


(* Add node assumes to context *)
let add_node_ass ctx assumes = 

  match ctx with

    | { node = None } -> raise (Invalid_argument "add_node_global_contract")

    | { node = Some ({ N.contract } as node) } ->
      let contract, ctx = match contract with
        | None -> (
          let svar, ctx = mk_fresh_local ctx Type.t_bool in
          C.mk assumes svar [] [], ctx
        )
        | Some contract -> C.add_ass contract assumes, ctx
      in
      (* Return node with contract added *)
      { ctx with node = Some { node with N.contract = Some contract } }

(* Add guarantees to context *)
let add_node_gua ctx guarantees = 

  match ctx with

    | { node = None } -> raise (Invalid_argument "add_node_global_contract")

    | { node = Some ({ N.contract } as node) } ->
      let contract, ctx = match contract with
        | None -> (
          let svar, ctx = mk_fresh_local ctx Type.t_bool in
          C.mk [] svar guarantees [], ctx
        )
        | Some contract -> C.add_gua contract guarantees, ctx
      in
      (* Return node with contract added *)
      { ctx with node = Some { node with N.contract = Some contract } }


(* Add node mode to context *)
let add_node_mode ctx mode = 

  match ctx with 

    | { node = None } -> raise (Invalid_argument "add_node_mode_contract")

    | { node = Some ({ N.contract } as node) } ->
      let contract, ctx = match contract with
        | None -> (
          let svar, ctx = mk_fresh_local ctx Type.t_bool in
          C.mk [] svar [] [ mode ], ctx
        )
        | Some contract -> C.add_modes contract [ mode ], ctx
      in
      (* Return node with contract added *)
      { ctx with node = Some { node with N.contract = Some contract } }


(* Add node assert to context *)
let add_node_assert ctx pos sv = 

  match ctx with 

    | { node = None } -> raise (Invalid_argument "add_node_assert")

    | { node = Some ({ N.asserts } as node) } -> 

      (* Return node with assertion added *)
      { ctx with node = Some { node with N.asserts = (pos, sv) :: asserts } }


(* Add node sofar(assumption) to context *)
let add_node_sofar_assumption ctx =

   match ctx with

    | { node = None } -> raise (Invalid_argument "add_node_sofar_assumption")

    | { node = Some ({ N.locals ; N.equations; N.contract } as n) } ->

      match contract with

       | None -> ctx

       | Some contract -> (

         let sofar_svar = contract.C.sofar_assump in

         let conj_of_assumes = contract.C.assumes |>
           List.map (fun { C.svar } -> E.mk_var svar) |> E.mk_and_n
         in

         let pre_sofar, _ = (* Context should not be modified *)
           assert (not (guard_flag ctx));
           E.mk_pre_with_context
             (* No abstraction should be necessary, see [mk_pre] *)
             (fun _ _ -> assert false) (fun _ -> assert false)
             ctx false (E.mk_var sofar_svar)
         in

         let expr =
           E.mk_arrow conj_of_assumes (E.mk_and conj_of_assumes pre_sofar)
         in

         let equations' = ((sofar_svar, []), expr) :: equations in

         (* Return node with equation and local variable added *)
         { ctx with
             node = Some { n with
               N.equations = equations' ;
               N.locals = D.singleton D.empty_index sofar_svar :: locals
             }
         }

       )


(* Add node assert to context *)
let add_node_property ctx source name expr = 

  match ctx with 

    | { node = None } -> raise (Invalid_argument "add_node_property")

    | { node = Some _ } -> 

      (* State variable for property and changed environment *)
      let state_var, ctx =

        if 

          (* Property is a state variable at current offset? *)
          E.is_var expr

        then 

          (* State variable of expression *)
          let state_var = E.state_var_of_expr expr in

          (state_var, ctx)

        else

          (* State variable of abstraction variable *)
          let abs, ctx = 
            mk_abs_for_expr ctx add_state_var_to_locals expr in

          let state_var = match abs with
            | sv, [] -> sv
            | _ -> assert false
          in
          
          (* Return changed context and new state variable *)
          (state_var, ctx)

      in

      match ctx with 
        | { node = None } -> assert false
        | { node = Some ({ N.equations; N.props } as n) } -> 

          (* May need to add an alias for the property if it already
             exists *)
          let equations', prop', ctx = 

            if 

              (* A property with the same state variables exists? *)
              List.exists 
                (fun (sv, _, _, _) -> StateVar.equal_state_vars state_var sv)
                props
                
            then

              (* Create a fresh local variable as an alias *)
              let state_var', ctx = 
                mk_fresh_local ctx Type.t_bool
              in

              (* Add an equation for the alias *)
              ((state_var', []), E.mk_var state_var) :: equations, 

              (* Use alias as property *)
              (state_var', name, source, Property.Invariant), 

              (* Context with new declaration *)
              ctx
              
            else

              (* Change nothing *)
              equations, (state_var, name, source, Property.Invariant), ctx

          in
          (* Return node with property and possibly alias equation
             added *)
          { ctx with 
              node = Some { n with
                              N.equations = equations';
                              N.props = prop' :: props } }


(* Add node equation to context *)
let add_node_equation ctx pos state_var bounds indexes expr = 

  match ctx with 

    | { node = None } -> raise (Invalid_argument "add_node_equation")

    | { node = Some { N.equations; N.calls } } ->
      (* TODO: This was a temporary fix. It does not seem to be necessary anymore *)
      (*let equations = List.filter
          (fun ((sv, b), _) -> 
             (StateVar.equal_state_vars state_var sv &&
             List.for_all2 
               (fun b1 b2 -> match b1, b2 with
                  | E.Fixed e1, E.Fixed e2 -> E.equal_expr e1 e2
                  | E.Bound _, E.Bound _ -> true
                  | _ -> false)
               b bounds) |> not)
          equations
      in*)

      if  
        (* State variable already defined by equation? *)
        List.exists
          (fun ((sv, b), _) -> 
             StateVar.equal_state_vars state_var sv &&
             List.for_all2 
               (fun b1 b2 -> match b1, b2 with
                  | E.Fixed e1, E.Fixed e2 -> E.equal_expr e1 e2
                  | E.Bound _, E.Bound _ -> true
                  | _ -> false)
               b 
               bounds)
          equations

        ||

        (* State variable defined by a node call? *)
        List.exists
          (fun { N.call_outputs } -> 
             D.exists 
               (fun _ sv -> StateVar.equal_state_vars state_var sv)
               call_outputs)
          calls

      then

        fail_at_position
          pos
          (Format.asprintf 
             "Duplicate definition for %a"
             (E.pp_print_lustre_var false) state_var);

      
      (* (* Wrap type of expression in arrays for the number of not fixed
         bounds *)
      let rec aux accum i = if i <= 0 then accum else
          aux (Type.mk_array Type.t_int accum) (pred i)
      in *)

      (* let expr_type = aux (E.type_of_lustre_expr expr) indexes in *)

      let expr_type = E.type_of_lustre_expr expr in

      (* let rec keep_same acc l1 l2 = match l1, l2 with *)
      (*   | x :: r1, _ :: r2 -> keep_same (x :: acc) r1 r2 *)
      (*   | _, [] -> List.rev acc *)
      (*   | [], _ -> assert false *)
      (* in *)

      let expr, expr_type, bounds, _ (* indexes *) =
        if Type.is_array expr_type then

          (* When expression is of type array, add select operator around to
             fall back in a supported fragment *)
          let elty = Type.last_elem_type_of_array expr_type in
          let eitys = Type.all_index_types_of_array expr_type in
          let expr, _ = List.fold_left (fun (e, i) _ ->
              E.mk_select e (E.mk_index_var i), succ i
            ) (expr, indexes) eitys in

          expr, elty, bounds, indexes
          
          (* let ear, _ = expr *)
          (*           |> E.cur_term_of_t E.base_offset *)
          (*           |> Term.array_and_indexes_of_select in *)

          (* (\* maybe we're doing a select over a store *\) *)
          (* if not (Term.is_free_var ear) then expr, elty, bounds, indexes *)
          (* else *)
          (*   let earv = Term.free_var_of_term ear in *)

          (*   let bnds_earv = try *)
          (*       SVT.find ctx.state_var_bounds *)
          (*         (Var.state_var_of_state_var_instance earv) *)
          (*     with Not_found -> [] in *)
          (*   (\* We only add select (and their bounds) for array indexes which do *)
          (*      not yet appear on the left hand side *\) *)
          (*   let extra_bnds = keep_same [] bnds_earv eitys in *)
          (*   Format.printf "extra %d@." (List.length extra_bnds); *)
          (*   expr, elty, List.rev_append extra_bnds bounds, i *)

        else
          expr, expr_type, bounds, indexes
      in
      (* Type of state variable *)
      let state_var_type =
        if bounds = [] then (
          let t = StateVar.type_of_state_var state_var in
          if Type.is_array t then (Type.last_elem_type_of_array t) else t
        )
        else (
          List.fold_left
            (fun t -> function
               | E.Bound _
               | E.Fixed _
               | E.Unbound _ ->
                 if Type.is_array t then Type.elem_type_of_array t
                 else
                   fail_at_position
                     pos
                     (Format.asprintf
                        "Type mismatch in equation: %a and %a"
                        (E.pp_print_lustre_type false) t
                        (E.pp_print_lustre_type false) expr_type))
            (StateVar.type_of_state_var state_var)
            bounds
         )
      in

      let ctx = 

        if 
          (* Type must be a subtype of declared type *)
          Type.check_type 
            expr_type
            state_var_type

        then

          (* Nothing to add *)
          ctx

        else

          (* Type of expression may not be subtype of declared type *)
          match state_var_type, expr_type with 

            (* Declared type is an actual integer range, expression is of type
               integer *)
            | t, s 
              when Type.is_int_range t &&
                   (Type.is_int s || Type.is_int_range s) -> 

              ctx

              (* Local analysis based on types misses cases.
                 We introduce appropiate checks in lustreDeclarations.

              let (lbound, ubound) = Type.bounds_of_int_range t in

              (* Value of expression is in range of declared type: 
                 lbound <= expr and expr <= ubound *)
              let range_expr = 
                (E.mk_and 
                   (E.mk_lte (E.mk_int lbound) expr) 
                   (E.mk_lte expr (E.mk_int ubound)))
              in

              let msg =
                Format.sprintf
                  "Cannot determine correctness of subrange type, \
                   adding constraint as property and reverting to type int for \
                   variable %s." 
                  (StateVar.string_of_state_var state_var) in

              note_at_position pos msg;

              (* Expanding type of state variable to int *)
              StateVar.change_type_of_state_var state_var (Type.mk_int ());

              (* Add property to node *)
              add_node_property
                ctx
                (Property.Generated (None, [state_var]))
                (Format.asprintf
                   "%a.bound" 
                   (E.pp_print_lustre_var false) 
                   state_var)
                range_expr*)

            | t, s -> 

              fail_at_position
                pos
                (Format.asprintf 
                   "Type mismatch in equation: %a and %a"
                   (E.pp_print_lustre_type false) t
                   (E.pp_print_lustre_type false) s)

      in

      let state_var_type = StateVar.type_of_state_var state_var in

      let convert_type =

        (* State variable declared as integer, but type of expression
           inferred as integer range? *)
        state_var_type |> Type.is_int && Type.is_int_range expr_type

        (* TODO: accept this conversion and create the appropiate checks
           in lustreDeclarations.
        ||

        (* State variable declared as integer range, but type of
           expression inferred as stricter integer range? *)
        state_var_type |> Type.is_int_range &&
        Type.is_int_range expr_type &&
        (let l1, u1 = 
           state_var_type |> Type.bounds_of_int_range
         in
         let l2, u2 = Type.bounds_of_int_range expr_type in
         Numeral.(l1 < l2) && Numeral.(u1 > u2)) *)
      in

      if convert_type then

        (* Change type of state variable to the stricter type of the
           expression to get a constraint on the values later

           This is just a heuristic to make at least some use of the
           type inference on the expression. In particular, it and
           will not infer types transitively. For that we would need
           to re-type all expressions the contain the variable, and
           then continue recursively. *)
        StateVar.change_type_of_state_var state_var expr_type;

      (* Return node with equation added *)
      match ctx with 
      | { node = None } -> assert false 
      | { node = Some node; original_int_type } ->
        { ctx with

          original_int_type =
            if convert_type then
              SVM.add state_var state_var_type original_int_type
            else
              original_int_type;

          node = Some { node with
                        N.equations = 
                          ((state_var, bounds), expr) :: equations } }


(* Add node call to context *)
let add_node_call ctx pos ({ N.call_outputs } as node_call) =
  match ctx with 
    | { node = None } -> raise (Invalid_argument "add_node_call")

    | { node = Some ({ N.equations; N.calls } as node) } -> 

      (* TODO: This was a temporary fix. It does not seem to be necessary anymore *)
      (*let calls =
        D.fold (fun _ state_var calls ->
          List.filter
            (fun { N.call_node_name; N.call_outputs } -> 
              D.exists 
                (fun _ sv -> StateVar.equal_state_vars state_var sv)
                call_outputs |> not)
            calls )
          call_outputs calls
      in*)

      if D.exists (
        fun _ state_var -> 

          (* State variable already defined by equation? *)
          List.exists
            (fun ((sv, _), _) -> StateVar.equal_state_vars state_var sv)
            equations
           
          ||

          (* State variable defined by a node call? *)
          List.exists (
            fun { N.call_outputs } -> D.exists (
              fun _ sv -> StateVar.equal_state_vars state_var sv
            ) call_outputs
          ) calls

      ) call_outputs

      then
        fail_at_position pos
          "Duplicate definition for output of node call";

      (* Add node call to context *)
      { ctx with node = Some { node with N.calls = node_call :: calls } }


(* Create a node from the context *)
let node_of_context = function

  (* Fail if not in a node *)
  | { node = None } -> 
    raise (Invalid_argument "node_of_context")

  (* Add abstractions to node and return *)
  | { expr_abs_map; node = Some _ } as ctx -> 
    match
      (* Add equations from definitions to equations *)
      ET.fold
        (fun e (sv, b) ctx -> add_node_equation ctx dummy_pos sv b (List.length b) e)
        expr_abs_map ctx
      with
        | { node = Some n } -> n
        | _ -> assert false


(* Add node from second context to nodes of first *)
let add_node_to_context ctx node_ctx =
  let n = node_of_context node_ctx in
  (* let rec aux ctx = *)
  (*   { ctx with *)
  (*     prev = if ctx.prev == ctx then ctx.prev else aux ctx.prev; *)
  (*     nodes = n :: ctx.nodes } *)
  (* in *)
  (* { ctx with prev = aux node_ctx.prev } *)
  { ctx with prev = { node_ctx.prev with nodes = n :: node_ctx.prev.nodes } }


let add_assumption_variable = function

(* No node in context *)
| { node = None } ->

  (function _ ->
    raise (Invalid_argument "add_assumption_variable"))

(* Get inputs and outputs from node in context *)
| { node = Some ({ N.inputs; N.outputs; N.assumption_svars } as node) } as ctx ->

  (function (pos, ident) ->

    try

      let expr = expr_of_ident ctx ident in

      D.fold
        (fun _ e ctx ->

           (* Expression is a variable *)
           if E.is_var e || E.is_const_var e then

             (* Get state variable of expression *)
             let state_var =
               let v = E.var_of_expr e in (* Works for constant inputs too *)
               Var.state_var_of_state_var_instance v
             in

             if

               (* Find state variable in inputs *)
               D.exists
                 (fun _ sv -> StateVar.equal_state_vars state_var sv)
                 inputs

               ||

               (* Find state variable in outputs *)
               D.exists
                 (fun _ sv -> StateVar.equal_state_vars state_var sv)
                 outputs

             then

               let assumption_svars' =
                 SVS.add state_var assumption_svars
               in

               { ctx with
                 node = Some { node with N.assumption_svars = assumption_svars' } 
               }

             (* State variable is not a input or output variable *)
             else

              fail_at_position pos
                (Format.asprintf "State variable '%a' is not an input or an output."
                   (I.pp_print_ident false) ident)

          (* Expression is not a variable *)
          else

            fail_at_position pos
                (Format.asprintf "Identifier '%a' is not a variable."
                   (I.pp_print_ident false) ident) )

        expr
        ctx


    (* Identifier does not denote an expression *)
    with Not_found ->

      fail_at_position pos
        (Format.asprintf "Identifier '%a' does not denote an expression."
          (I.pp_print_ident false) ident)

    )


(* Mark node as main node *)
let set_node_main ctx = match ctx with
| { node = None } -> raise (Invalid_argument "set_node_main")
| { node = Some node } ->
  { ctx with node = Some { node with N.is_main = true } }


(* Mark node as function *)
let set_node_function ctx = match ctx with
| { node = None } -> raise (Invalid_argument "set_node_function")
| { node = Some node } ->
  { ctx with node = Some { node with N.is_function = true } }

(** Checks if the current node, if any, is a function. *)
let get_node_function_flag ctx = match ctx with
| { node = None } -> raise (Invalid_argument "get_node_function_flag")
| { node = Some { N.is_function } } -> is_function



(* Resolve a forward reference, fails if a circular dependency is detected. *)
let solve_fref { deps' } decl (f_type, f_ident, f_pos) decls =
  (* Retrieve info of current declaration. *)
  let pos, ident, typ = Deps.info_of_decl decl in
  (* Does the declaration forward ref-ed depend on current declaration? *)
  if Deps.mem deps' (f_type, f_ident) (typ, ident) then (
    Format.asprintf
      "circular dependency between %a '%a' and %a '%a'"
      Deps.pp_print_decl f_type (I.pp_print_ident false) f_ident
      Deps.pp_print_decl typ (I.pp_print_ident false) ident
    |> fail_at_position pos
  ) else (
    (* Add dependency between current declaration and forward one. *)
    Deps.add deps' (typ, ident) (f_type, f_ident) ;
    try
      Deps.insert_decl decl (f_type, f_ident) decls
    with Not_found ->
      (* Forward reference to unknown declaration. *)
      Format.asprintf
        "unknown %a '%a' referenced in %a '%a'"
        ( fun ppf -> function
          (* If it's an unknown constant, it's more generally an unknown
          identifier. *)
          | Deps.Const -> Format.fprintf ppf "identifier"
          | typ -> Deps.pp_print_decl ppf typ
        ) f_type (I.pp_print_ident false) f_ident
        Deps.pp_print_decl typ (I.pp_print_ident false) ident
      |> fail_at_position f_pos
  )

(* Returns true if new definitions are allowed in the context *)
let are_definitions_allowed ctx = ctx.definitions_allowed = None

(* Check that the node being defined has no undefined local variables *)
let check_local_vars_defined ctx =
  match ctx.node with
  | Some { N.equations; N.is_extern = false } ->
    (* Look for localss definitions *)
    List.iter (fun (sv, id, pos) ->
        if not (List.exists
                  (fun ((sv', _), _) -> StateVar.equal_state_vars sv sv') 
                  equations )
        then
          (* Always fail *)
          fail_at_position pos
            (Format.asprintf "Local variable %a has no definition."
               (I.pp_print_ident false) id)
      ) ctx.locals_info
  | _ -> ()

(*
let check_output_defined ctx =
  match ctx.node with
  | Some { N.equations; N.is_extern = false } ->
    (* Look for outputs definitions *)
    List.iter (fun (sv, id, pos) ->
        if not (List.exists
                  (fun ((sv', _), _) -> StateVar.equal_state_vars sv sv') 
                  equations )
        then
          (* Always fail *)
          fail_at_position pos
            (Format.asprintf "Output variable %a has no definition."
               (I.pp_print_ident false) id)
      ) ctx.outputs_info
  | _ -> ()
*)

let check_vars_defined ctx =
  (* check_outputs_defined ctx; *)
  check_local_vars_defined ctx
  
let position_of_state_variable ctx svar =
  let eq (sv,_,_) =
    StateVar.equal_state_vars sv svar
  in
  let { inputs_info } = ctx in
  match List.find_opt eq inputs_info with
  | Some (_,_,pos) -> Some pos
  | None -> (
    let { outputs_info } = ctx in
    match List.find_opt eq outputs_info with
    | Some (_,_,pos) -> Some pos
    | None -> (
      let { locals_info } = ctx in
      match List.find_opt eq locals_info with
      | Some (_,_,pos) -> Some pos
      | None -> None
    )
  )

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
