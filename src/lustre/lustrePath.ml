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

(* Abbreviations *)
module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module N = LustreNode
module S = SubSystem
module T = TransSys
module C = LustreContract

module SVT = StateVar.StateVarHashtbl
module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet

module MS = Map.Make (String)

(* Model for a node and its subnodes *)
type t =
  Node of
    N.t *
    Model.path *
    C.mode list list option *
    N.call_cond list *
    ((I.t * position) list * t) list


(* ********************************************************************** *)
(* Reconstruct a model for a node hierarchy                               *)
(* ********************************************************************** *)

(* Map a state variable to its instance in the top system *)
let map_top instances state_var =

  List.fold_left 
    (fun state_var (_, { T.map_up }, _) -> SVM.find state_var map_up)
    state_var
    instances


(* Map all state variables in the term to their instances in the top
   system *)
let map_term_top instances term = 

  Term.map
    (fun _ t -> 

       (* Only map free variables *)
       if Term.is_free_var t then 

         (* Get free variable of term *)
         let v = Term.free_var_of_term t in

         (* Is variable an instance of a state variable? *)
         (if Var.is_state_var_instance v then

            (* Get state variable of variable instace *)
            let sv = Var.state_var_of_state_var_instance v in

            (* Get offset of variable instace *)
            let o = Var.offset_of_state_var_instance v in

            (* Map variable to the top system *)
            let sv' = map_top instances sv in

            (* Return variable instance at the same offset *)
            Var.mk_state_var_instance sv' o 

          (* Variable is not a state variable instance *)
          else 

            (* Variable must be a constant state variable *)
            (assert (Var.is_const_state_var v);

             (* Get state variable of constant variable *)
             let sv = Var.state_var_of_state_var_instance v in

             (* Map variable to the top system *)
             let sv' = map_top instances sv in

             (* Return constant variable *)
             Var.mk_const_state_var sv')
         )
         
         (* Return term of variable *)
         |> Term.mk_var

       (* Return other terms unchanged *)
       else t)

    term


(* Map the state variable [state_var] to its instance in the top
   system using the instantiation path [instances], get the sequence
   of values of this state variable from [model] and add this sequence
   to [model'] for [state_var]. Fail with exception [Not_found] if
   there is no instance of the state variable, or if there are no
   values for the state variable in the top system.

   Use the function as the iterator in LustreIndex.iter *)
let rec map_top_and_add instances model model' i state_var = 

  if SVT.length model == 0 then

    SVT.add model' state_var []

  else

    try

      (* Find state variable instance in top node *)
      let state_var' = map_top instances state_var in

      (* Get path of top node state variable *)
      SVT.find model state_var'

      (* Add as path of subnode state variable *)
      |> SVT.add model' state_var

    (* Go one level up if the state variable could not be found *)
    with Not_found ->
    match instances with
    | _ :: up_instances ->
      map_top_and_add up_instances model model' i state_var
    | [] -> raise Not_found


let safe_map_top_and_add instances model model' i state_var =
  try
    map_top_and_add instances model model' i state_var
  with Not_found -> () (* No state variable is added to model' *)


let find_and_move_to_head f =
  let rec loop pref = function
  | hd :: tl when fst hd |> f -> hd :: (List.rev_append pref tl)
  | hd :: tl -> loop (hd :: pref) tl
  | [] -> raise Not_found
  in
  loop []

(* Compute substitutions for each state variable in the last arguments
   to either its instance in the top system, or its definition in
   [equations] and recursively for each state variable in a
   definition.

   /!\ [equations] must be topologically sorted. /!\

   We separate the substitutions for state vars [sv_subst] and those coming
   from equations [subst]. The latter needs to be reordered at the end. *)
let rec substitute_definitions'
  stateful_vars equations sv_subst subst
= function 

  (* All state variables are in the top system, reorder substitutions to make
     sure they respect the topological order of the equations. *)
  | [] ->
    let subst =
      equations |> List.fold_left (fun subst ((sv, _), _) ->
        try
          find_and_move_to_head
            (StateVar.equal_state_vars sv)
            subst
        with Not_found -> subst
      ) subst
    in
    subst @ sv_subst

  (* Substitution for state variable already computed? *)
  | state_var :: tl 
    when
        List.exists
          (fun (sv, _) -> StateVar.equal_state_vars sv state_var)
          subst
    ||  
        List.exists
          (fun (sv, _) -> StateVar.equal_state_vars sv state_var)
          sv_subst
  ->
    (* Do nothing, we reorder before returning anyways. *)
    substitute_definitions' stateful_vars equations sv_subst subst tl

  (* Variable is stateful? *)
  | state_var :: tl 
    when
      List.exists
        (StateVar.equal_state_vars state_var) 
        stateful_vars ->

    (* Add substitution for state variable and continue *)
    substitute_definitions'
      stateful_vars
      equations
      ((state_var, E.mk_var state_var) :: sv_subst)
      subst
      tl

  (* Get variable in this system to be instantiated *)
  | state_var :: tl -> 

    try 

      (* Find equation for the variable *)
      let expr =
        List.find (fun ((sv, _), _) -> 
            (* Equation is for state variable? *)
            StateVar.equal_state_vars sv state_var
          ) equations
          
        (* Return expression on right-hand side of equation *)
        |> (function (_, e) -> e)
      in

      (* Add substitution for state variable and continue *)
      substitute_definitions'
        stateful_vars 
        equations
        sv_subst
        ((state_var, expr) :: subst)
        ((E.state_vars_of_expr expr |> SVS.elements) @ tl)

    (* No equation for state variable 

       This should not happen, but just make sure not to fail. *)
    with Not_found -> 

      (* Add substitution for state variable and continue *)
      substitute_definitions'
        stateful_vars 
        equations
        sv_subst
        subst
        tl



(* Recursively substitute the state variable with either its instance
   in the top system, or with its definition in [equations] *)
let substitute_definitions instances equations state_var =
  substitute_definitions' instances equations [] [] [state_var]
  (* Stateless variables do not occur under a pre, therefore it is
     enough to substitute it at the current instant *)
  |> List.fold_left (
    fun a b -> E.mk_let_cur [b] a
  ) (E.mk_var state_var)

(* Recursively substitute the state variables in an expression with its
   definition in [equations]. *)
let substitute_definitions_in_expr equations expr =
  E.state_vars_of_expr expr |> SVS.elements
  |> substitute_definitions' [] equations [] []
  |> fun bindings -> E.mk_let_cur bindings expr

(* Get the sequence of values of the state variable in the top system
   and add for this state variables as with [map_top_and_add] if
   possible. Otherwise, reconstruct the sequence of values from its
   definitions.
   
   Use as the iterator function in LustreIndex.iter *)
let map_top_reconstruct_and_add
    first_is_init
    trans_sys
    instances
    equations_of_init
    model 
    model'
    index
    state_var =
  try

    (* Format.printf "map_top_reconstruct_and_add@.@." ;
    Format.printf "  state_var %a@.@."
      StateVar.pp_print_state_var state_var ; *)

    (* Return the model for the instance *)
    map_top_and_add instances model model' index state_var

  (* No instance, or no model *)
  with Not_found ->

    (* Format.printf "not found@.@." ; *)
    
    (* Get stateful variables of transition system *)
    let stateful_vars = TransSys.state_vars trans_sys in

    (* Format.printf "stateful:@.  @[<v>%a@]@.@."
      (pp_print_list StateVar.pp_print_state_var "@ ") stateful_vars ; *)

    (* Get definition in terms of state variables of the top node *)
    let expr init =
      let equations = equations_of_init init in
(*       Format.printf "equations (%b):@.  @[<v>%a@]@.@."
        init
        (pp_print_list (fun fmt (sv,_,e) ->
          Format.fprintf fmt "%a = %a"
            StateVar.pp_print_state_var sv
            (LustreExpr.pp_print_lustre_expr true) e)
         "@ ")
        equations ; *)
      substitute_definitions
        stateful_vars
        equations
        state_var
    in

    (* Format.printf "%a = %a -> %a@.@."
      StateVar.pp_print_state_var state_var
      (LustreExpr.pp_print_lustre_expr true) (expr true)
      (LustreExpr.pp_print_lustre_expr true) (expr false) ; *)

    (* Evaluate expression with reversed list of models *)
    let rec aux expr_not_init accum = function 
      (* The order of the pattern matching below should not be changed.
        In the last case, the step case, it is assume that the list contains
        at least two elements to retrieve the previous values of the state
        variables.

        This holds because of how the pattern matching is ordered, so do not
        change the order. *)

      (* All steps in path evaluated, return *)
      | [] -> accum

      (* At last step of path, is this the initial state? *)
      | [m] when first_is_init ->

        (* Value for state variable at step *)
        let v =

          (* Get expression for initial state *)
          E.base_term_of_t Model.path_offset (expr true)

          (* Map variables in term to top system *)
          |> (map_term_top instances)

          (* Evaluate term in model *)
          |> Eval.eval_term
            (TransSys.uf_defs trans_sys) 
            m

          (* Return term *)
          |> Eval.term_of_value

        in

        (* Add term to accumulator as first value and return *)
        Model.Term v :: accum

      (* If this is the last step but not an initial state *)
      | [m] ->

        let expr_not_init = match expr_not_init with
          | None -> expr false
          | Some eni -> eni
        in

        (* Value for state variable at step *)
        let v =

          (* Get expression for step state *)
          E.cur_term_of_t Model.path_offset expr_not_init

          (* Map variables in term to top system *)
          |> (map_term_top instances)

          (* Evaluate expression for step state *)
          |> Eval.eval_term
            (TransSys.uf_defs trans_sys)
            (* We do not know the state of the variables at the previous step,
               so we evaluate this term with only the current state *)
            m

          (* Return term *)
          |> Eval.term_of_value

        in

        (* Add term to accumulator and continue *)
        (Model.Term v :: accum)

      (* Model for step of path *)
      | m :: tl ->

        let expr_not_init = match expr_not_init with
          | None -> expr false
          | Some eni -> eni
        in

        (* Value for state variable at step *)
        let v =

          (* Get expression for step state *)
          E.cur_term_of_t Model.path_offset expr_not_init

          (* Map variables in term to top system *)
          |> (map_term_top instances)

          (* Evaluate expression for step state *)
          |> Eval.eval_term
            (TransSys.uf_defs trans_sys)
            (* The `List.hd` below CANNOT FAIL because there is at least two
              elements in this list, since `[]` and `[m]` are catched above. *)
            (List.hd tl |> Model.bump_and_merge Numeral.(~- one) m)

          (* Return term *)
          |> Eval.term_of_value

        in

        (* Add term to accumulator and continue *)
        aux (Some expr_not_init) (Model.Term v :: accum) tl

    in

    (* Evaluate expression at each step of path *)
    aux None [] (Model.models_of_path model |> List.rev)

    (* Add as path of subnode state variable *)
    |> SVT.add model' state_var

let active_modes_of_instances model_top instances = function
(* No contract. *)
| None | Some { C.modes = [] } -> None
(* Contract with some modes. *)
| Some { C.modes } -> (
  (* Retrieves the trace of value of a requirement from a top model. *)
  let trace_of_req { C.svar } =
    map_top instances svar
    |> SVT.find model_top
    |> List.map (
      function
      | Model.Term t -> t == Term.t_true
      | _ -> failwith "\
        evaluating mode requirement: value should be a term"
    )
  in

  (* Trace of active modes has the same length as the model. Originally
  empty. *)
  let empty_trace =
    let rec loop acc n =
      if n <= 0 then acc else loop ([] :: acc) (n - 1)
    in
    Model.path_length model_top |> loop []
  in

  (* Merges two traces of requirement values. *)
  let merge_req_traces t1 t2 =
    let rec loop acc = function
      | ([],[]) -> List.rev acc
      | (v1 :: t1, v2 :: t2) -> loop ( (v1 && v2) :: acc ) (t1, t2)
      | _ -> failwith "\
        while constructing the trace of active modes:@ \
        tried to merge two traces of inconsistent length\
      "
    in
    loop [] (t1, t2)
  in

  (* Adds a mode [m] to the steps of a trace of active modes where [m] is
  active. *)
  let add_mode_to_trace mode_trace = function
    | { C.requires = [] } as m ->
      (* No requires, always active. *)
      mode_trace |> List.map (fun active -> m :: active)
    | { C.requires = head :: tail } as m ->
      let head = trace_of_req head in
      let reqs_val =
        tail |> List.fold_left (
          fun acc req -> trace_of_req req |> merge_req_traces acc
        ) head
      in

      let rec loop pref = function
        | ([], []) -> List.rev pref
        | (act :: act_tail, reqs_val :: reqs_val_tail) ->
          loop
            ( (if reqs_val then m :: act else act) :: pref )
            (act_tail, reqs_val_tail)
        | _ -> failwith "\
          while adding mode to trace of active modes:@ \
          tried to merge two traces of inconsistent length\
        "
      in

      loop [] (mode_trace, reqs_val)
  in

  Some (
    if empty_trace = [] then []
    else
      modes
      |> List.fold_left (
        fun acc mode -> add_mode_to_trace acc mode
      ) empty_trace
  )
)

let active_modes_to_strings =
  let rec loop acc current rest width = function
    | [] :: tail ->
      loop acc ("" :: current) ([] :: rest) width tail
    | ( mode :: mode_tail ) :: tail ->
      let str = Format.asprintf "%a" (I.pp_print_ident false) mode.C.name in
      loop
        acc (str :: current) (mode_tail :: rest)
        ( max width (String.length str) ) tail
    | [] -> (
      if rest |> List.for_all (fun l -> l = []) then
        (List.rev current) :: acc, width
      else
        loop ( (List.rev current) :: acc ) [] [] width (List.rev rest)
    )
  in
  loop [] [] []


let get_constants const_map scope =
  match Scope.Map.find_opt scope const_map with
  | None -> []
  | Some l -> l

  
(* Reconstruct model for the instance given the models for the subnodes 

   Use with [TransSys.fold_subsystem_instances]. *)
let node_path_of_instance
    const_map
    first_is_init
    model_top
    ({
      N.inputs; N.outputs; N.locals; N.contract
    } as node)
    trans_sys
    instances
    subnodes =

  (* Format.printf "node_path_of_instance@.@." ; *)

  (* Record trace of node calls *)
  let trace = 
    List.map
      (fun (t, { T.pos }, _) -> 
         (TransSys.scope_of_trans_sys t |> I.of_scope, pos))
      instances
  in

  (* Record activation conditions *)
  let call_conds =
    List.fold_left 
      (fun acc (_, _, call_cond) ->
         List.rev_append call_cond acc
      ) [] instances
    |> List.rev
  in

  (* Format.printf "subnodes@.@." ; *)

  (* Create a path for the state variables of the node *)
  let model = 
    Model.create_path
      (D.cardinal inputs + 
       D.cardinal outputs +
       List.length call_conds +
       List.fold_left (fun a d -> D.cardinal d + a) 0 locals)
  in

  (* Format.printf "model@.@." ; *)

  (* Map all input state variables to the top instances and add their
     path to the model

     Inputs are always stateful, therefore there is exactly one state
     variable of the top system each input is an instance of.

     There is only one exception. The input is a global constant
     without a definition. We use safe_* version of map_top_and_add
     to allow this case.
  *)
  D.iter (safe_map_top_and_add instances model_top model) inputs;

  (* Map all output state variables to the top instances and add their
     path to the model

     Ouputs are always stateful, therefore there is exactly one state
     variable of the top system each output is an instance of.
  *)
  D.iter (safe_map_top_and_add instances model_top model) outputs;

  (* Map all activation conditions and add their path to the model, but start
     from one level up in the instance hierarchy *)
  List.iter (function N.CActivate c | N.CRestart c ->
    try map_top_and_add (List.tl instances) model_top model D.empty_index c
    with Not_found -> assert false
    ) call_conds;

  let equations_of_init init =
    N.ordered_equations_of_node
      node (TransSys.state_vars trans_sys) init
  in

  (* Map all local state variables to the top instances or
     reconstruct and add their path to the model

     A local variable is either stateful in which case there is
     exactly one state variable of the top system it is an instance
     of. Otherwise, there is an equation of the node that can be
     substituted for the state variable. *)
  List.iter
    (D.iter
       (map_top_reconstruct_and_add
          first_is_init
          trans_sys
          instances
          equations_of_init
          model_top
          model))
    ((D.singleton D.empty_index node.N.init_flag) :: locals);

  let active_modes = active_modes_of_instances model_top instances contract in
(*   ( match active_modes with
    | None -> ()
    | Some active_modes ->
      Format.printf "active modes: @[<v>%a@]@.@."
        (pp_print_list
          (pp_print_list
            (fun fmt { C.name } -> LustreIdent.pp_print_ident false fmt name) ", "
          )
          "@ "
        ) active_modes
  ) ; *)

  let constants =
    (* Node constants + Global constants *)
    List.rev_append
      (get_constants const_map (N.scope_of_node node))
      (get_constants const_map [])
    |> List.map snd
  in

  if SVT.length model_top = 0 then (
    List.iter (fun sv -> SVT.add model sv []) constants
  )
  else (
    List.iter (fun sv -> SVT.add model sv (SVT.find model_top sv)) constants
  ) ;

  (* Return path for subnode and its call trace *)
  (trace, Node (node, model, active_modes, call_conds, subnodes))


(* Return a hierarchical model for the nodes from a flat model by
   mapping the model of the top node to model of the subnode instances,
   reconstructing the streams in the original input. *)
let node_path_of_subsystems
    globals
    first_is_init
    trans_sys
    model
    ({ S.scope } as subsystems) =

  (* Format.printf "trans_sys@.@." ; *)

  (* Get transition system of top scope of subsystems *)
  let trans_sys' = 
    TransSys.find_subsystem_of_scope trans_sys scope 
  in

  (* Format.printf "nodes@.@." ; *)

  let nodes = N.nodes_of_subsystem subsystems in

  (* Format.printf "folding@.@." ; *)
  (*Printexc.record_backtrace true ;*)

  (* Map from scopes to constants (empty scope = global scope) *)
  let const_map =
    let constants =
      List.fold_left (fun acc (_, vt) ->
        let l =
          (D.bindings vt)
          |> List.map (fun (i,v) -> (i, Var.state_var_of_state_var_instance v))
        in
        List.rev_append l acc
      ) [] globals.LustreGlobals.free_constants
      |> List.rev
    in
    List.fold_left
      (fun acc (i, sv) ->
        let scope =
          let scope_sv = StateVar.scope_of_state_var sv in
          match scope_sv with
          | [_] -> []
            (* Use empty scope for global scope (scope with one id) *)
          | _ -> [scope_sv |> List.hd]
            (* Retrieve name of node from scope (first id) *)
        in
        Scope.Map.update
          scope
          (function
          | None -> Some [(i,sv)]
          | Some l -> Some ((i,sv) :: l)
          )
          acc
      )
      Scope.Map.empty
      constants
  in

  try
    let r =
      (* Create models for all subnodes *)
      N.fold_node_calls_with_trans_sys
        nodes
        (node_path_of_instance const_map first_is_init model)
        (N.node_of_name (I.of_scope scope) nodes)
        trans_sys'
    in
    (r, const_map)
  with
  | TimeoutWall -> raise TimeoutWall
  | e ->
    (* Get backtrace now, Printf changes it *)
    (*let backtrace = Printexc.get_backtrace () in

    Format.printf "Caught %s.@ Backtrace:@\n%s@.@."
      (Printexc.to_string e)
      backtrace ;*)
    raise e


(* *************************************************************** *)
(* Plain-text output                                               *)
(* *************************************************************** *)

(*
(* Pretty-print a value *)
let pp_print_term ty ppf term =

  (* We expect values to be constants *)
  if Term.is_numeral term then 
    let n = Term.numeral_of_term term in
    if Type.is_enum ty then
      Type.get_constr_of_num n |> Format.pp_print_string ppf
    else
    (* Pretty-print as a numeral *)
      Numeral.pp_print_numeral ppf n

  (* Constant is a decimal? *)
  else if Term.is_decimal term then 
    
    (* Pretty-print as a decimal *)
    Decimal.pp_print_decimal 
      ppf
      (Term.decimal_of_term term)
      
  (* Constant is a Boolean? *)
  else if Term.is_bool term then 
    
    (* Get Boolean value of constant *)
    if Term.bool_of_term term then 
      
      (* Pretty-print as Boolean value *)
      Format.fprintf ppf "true"
        
    else
      
      (* Pretty-print as Boolean value *)
      Format.fprintf ppf "false"

  (* Constant is a signed bitvector? *)
  else if Type.is_bitvector (Term.type_of_term term) then

    let bv = Term.bitvector_of_term term in
      let size = Bitvector.length_of_bitvector bv in
        let num = (match size with
          | 8 -> Bitvector.bv8_to_num bv
          | 16 -> Bitvector.bv16_to_num bv
          | 32 -> Bitvector.bv32_to_num bv
          | 64 -> Bitvector.bv64_to_num bv
          | _ -> raise E.Type_mismatch) in
        Numeral.pp_print_numeral ppf num

  (* Constant is an unsigned bitvector? *)
  else if Type.is_ubitvector (Term.type_of_term term) then

    let ubv = Term.bitvector_of_term term in
      let size = Bitvector.length_of_bitvector ubv in
        let num = (match size with
          | 8 -> Bitvector.ubv8_to_num ubv
          | 16 -> Bitvector.ubv16_to_num ubv
          | 32 -> Bitvector.ubv32_to_num ubv
          | 64 -> Bitvector.ubv64_to_num ubv
          | _ -> raise E.Type_mismatch) in
        Numeral.pp_print_numeral ppf num

  else

    (* Fall back to pretty-print as lustre expression *)
    (LustreExpr.pp_print_expr false) ppf
      (LustreExpr.unsafe_expr_of_term term)
*)

let pp_print_value = Model.pp_print_value


(* Output a single value of a stream at an instant

   Give [val_width] as the maximum expected width of the string
   representation of the values for correct alignment. *)
let pp_print_stream_value_pt ty val_width ppf = function
  | None ->
    Format.fprintf ppf "%*s" val_width "_"
  | Some v ->
    let value_string = string_of_t (pp_print_value ~as_type:ty) v in
    let padding = val_width - (width_of_string value_string) in
    Format.fprintf ppf "%*s%a" padding "" (pp_print_value ~as_type:ty) v


let pp_print_stream_string_pt val_width ppf v =
  Format.fprintf ppf "%*s" val_width v

(* Output a position *)
let pp_print_pos_pt ppf pos = 

  (* Do not print anything for a dummy position *)
  if is_dummy_pos pos then () else 

    Lib.pp_print_line_and_column ppf pos


(* Output the name of the lustre variable and remove the automaton prefixes *)
let pp_print_lustre_var ppf state_var =
  match N.is_automaton_state_var state_var with
  | Some (_, name) -> Format.pp_print_string ppf name
  | None -> E.pp_print_lustre_var false ppf state_var


(* Output the identifier of an indexed stream *)
let pp_print_stream_ident_pt ppf (index, state_var) =

  Format.fprintf
    ppf
    "%a%a"
    pp_print_lustre_var state_var
    (D.pp_print_index false) index


(* Output the the calling node and the position of the call *)
let pp_print_call_pt ppf (name, pos) = 
 
  Format.fprintf
    ppf
    "%a%a"
    (I.pp_print_ident false) name
    pp_print_pos_pt pos


(* Convert values to strings and update maximal lengths *)
let rec values_width val_width ty = function

  (* All values consumed, return in original order *)
  | [] -> val_width

  (* Output a term as a value *)
  | v :: tl -> 

    (* Convert value to string *)
    let value_string = string_of_t (pp_print_value ~as_type:ty) v in
    
    (* Keep track of maximum width of values *)
    let val_width = max val_width (width_of_string value_string) in
    
    (* Add string representation of value and continue with remaining
       values *)
    values_width val_width ty tl 


(* activation condition stream *)
let rec act_to_bool acc = function
  | [] -> List.rev acc
  | Model.Term t :: tl ->
    act_to_bool (Term.bool_of_term t :: acc) tl
  | _ :: _ -> assert false

(* point wise and over multiple Boolean lists *)
let rec and_lists acc ls =
  let cur, rs, one_empty =
    List.fold_left (fun (cur, rs, one_empty) l ->
        match l, one_empty with
        | _, true -> cur, rs, true
        | b :: r, false -> cur && b, r :: rs, false
        | [], _ -> cur, rs, true
      ) (true, [], false) ls
  in
  if one_empty then List.rev acc
  else and_lists (cur :: acc) rs
  
(* activation condition stream as boolean list if any *)
let act_stream path l =
  let streams =
    List.fold_left (fun acc -> function
        | N.CActivate c ->
          (SVT.find path c |> act_to_bool []) :: acc
        | _ -> acc
      ) [] l in
  match streams with
  | [] -> None
  | _ -> Some (and_lists [] streams)


(* Sample a stream of values (as strings) on a Boolean clock *)
let sample_stream_on_clock =
  List.map2 (fun s b -> match s, b with
      | Some _, true -> s
      | _ -> None
    )

(* Sample a set of streams *)
let sample_streams_on_clock clock streams =
  List.map
    (fun (name, ty, stream) ->
       (name, ty, sample_stream_on_clock stream clock))
    streams


(* Convert identifiers and values of streams to strings and update
   maximal lenght of the strings *)
let rec streams_to_values path ident_width val_width streams = 

  function

    (* All streams consumed, return in original order and with maximum
       width of identifiers and values *)
    | [] -> (ident_width, val_width, List.rev streams)

    (* Take first stream *)
    | (index, state_var) :: tl ->

      try 

        (* Identifier and index of stream *)
        let stream_name = 
          string_of_t pp_print_stream_ident_pt (index, state_var)
        in

        let ty = StateVar.type_of_state_var state_var in
        
        (* Get values of stream and convert to strings, keep track of
           maximum width of values *)
        let stream_values = SVT.find path state_var in
        let val_width = values_width val_width ty stream_values in

        let stream_values = List.map (fun v -> Some v) stream_values in
        
        (* Keep track of maximum width of identifiers *)
        let ident_width = 
          max ident_width (String.length stream_name)
        in

        (* Add string representation of stream and continue with
           remaining streams *)
        streams_to_values 
          path
          ident_width
          val_width 
          ((stream_name, ty, stream_values) :: streams)
          tl

      (* State variable must be in the model *)
      with Not_found ->
        (* Format.eprintf "Where is %a ?@." *)
        (*   StateVar.pp_print_state_var state_var; *)
        (* We ignore the state variable and continue converting.
           There is only one case in the current implementation where
           this may happen and it is not because a bug. The model contains
           a global constant without a definition.
           TODO: check that if we are here, the above is really the case.
        *)
        streams_to_values
          path
          ident_width
          val_width
          streams
          tl



(* Output a stream value with given width for the identifier and
   values *)
let pp_print_stream_pt
    ident_width val_width ppf (stream_name, ty, stream_values) = 
  (* Break lines if necessary and indent correctly *)
  Format.fprintf
    ppf
    "@[<hov %d>@{<blue_b>%-*s@} %a@]"
    (ident_width + 1)
    ident_width
    stream_name
    (pp_print_list (pp_print_stream_value_pt ty val_width) "@ ")
    stream_values


(* Output a stream value with given width for the identifier and
   values *)
let pp_print_stream_string_pt
    ident_width val_width stream_name ppf stream_string_values = 
  (* Break lines if necessary and indent correctly *)
  Format.fprintf
    ppf
    "@[<hov %d>@{<blue_b>%-*s@} %a@]"
    (ident_width + 1)
    ident_width
    stream_name
    (pp_print_list (pp_print_stream_string_pt val_width) "@ ")
    stream_string_values


(* Output state variables and their sequences of values under a
   header, or output nothing if the list is empty *)
let pp_print_stream_section_pt ident_width val_width sect ppf = function 
  | [] -> ()
  | l -> 
    Format.fprintf
      ppf
      "== @{<b>%s@} ==@,\
       %a@,"
      sect
      (pp_print_list (pp_print_stream_pt ident_width val_width) "@,") 
      l


(* For modes *)
let pp_print_modes_section_pt ident_width val_width mode_ident ppf = function 
  | None -> ()
  | Some vals -> 
    Format.fprintf
      ppf
      "== @{<b>%s@} ==@,\
       %a@,"
      mode_ident
      (pp_print_list (pp_print_stream_string_pt ident_width val_width "") "@,") 
      vals



(* Output state variables and their sequences of values under a
   header, or output nothing if the list is empty *)
let pp_print_stream_automaton_pt ident_width val_width auto ppf = function 
  | [] -> ()
  | l -> 
    Format.fprintf
      ppf
      "== @{<b>Automaton@} @{<blue>%s@} ==@,\
       %a@,"
      auto
      (pp_print_list (pp_print_stream_pt ident_width val_width) "@,") 
      l

let pp_print_stream_automata_pt ident_width val_width ppf auto_map =
  MS.iter (fun auto streams ->
      pp_print_stream_automaton_pt ident_width val_width auto ppf streams
    ) auto_map


(* Partition variables depending on their belonging to an automaton *)
let partition_locals_automaton is_visible locals =
  let locals = List.map D.bindings locals |> List.flatten in
  List.fold_left (fun (auto_map, others) (i, sv) ->
      match N.is_automaton_state_var sv with
      | Some (auto, _) ->
        let l = try MS.find auto auto_map with Not_found -> [] in
        MS.add auto ((i, sv) :: l) auto_map, others
      | None when is_visible sv -> auto_map, (i, sv) :: others
      | None -> auto_map, others
    ) (MS.empty, []) locals



(* Output sequences of values for each stream of the nodes in the list
   and for all its called nodes *)
let rec pp_print_lustre_path_pt' is_top const_map ppf = function

(* All nodes printed *)
| [] -> ()

(* Take first node to print *)
| (
  trace, Node (
    { N.name; N.inputs; N.outputs; N.locals;
      N.is_function; } as node,
    model, active_modes, call_conds, subnodes
  )
) :: tl when N.node_is_visible node ->

  let is_visible = N.state_var_is_visible node in

  let is_state, name =
    match N.node_is_state_handler node with
    | None -> false, name
    | Some state -> true, I.mk_string_ident state
  in
  
  let title =
    if is_function then "Function"
    else if is_state then "State"
    else "Node"
  in
  
  (* Remove first dimension from index *)
  let pop_head_index = function 
    | ([], sv) -> ([], sv)
    | (_ :: tl, sv) -> (tl, sv)
  in

  (* Boolean clock that indicates if the node is active for this particular
     call *)
  let clock = act_stream model call_conds in
  
  (* Reset maximum widths for this node *)
  let ident_width, val_width = 0, 0 in

  (* Remove index of position in input for printing *)
  let ident_width, val_width, inputs' = 
    D.bindings inputs
    |> List.map pop_head_index
    |> List.filter (fun (_, sv) -> is_visible sv)
    |> streams_to_values model ident_width val_width []
  in

  (* Remove index of position in output for printing *)
  let ident_width, val_width, outputs' = 
    D.bindings outputs
    |> List.map pop_head_index
    |> List.filter (fun (_, sv) -> is_visible sv)
    |> streams_to_values model ident_width val_width []
  in

  let mode_ident = "Mode(s)" in
  let _ (* ident_witdth *), val_width, modes = match active_modes with
    | None -> ident_width, val_width, None
    | Some modes ->
      let ident_width = max ident_width (String.length mode_ident) in
      let modes, val_width = active_modes_to_strings val_width modes in
      (* Format.printf "modes:@." ;
      modes |> List.iter (
        fun line -> Format.printf "  %a@." (pp_print_list Format.pp_print_string ", ") line
      ) ;
      Format.printf "@." ; *)
      ident_width, val_width, Some modes
  in

  (* Filter locals to for visible state variables only and return
     as a list 

     The list of locals is the reversed from the original input in the node,
     with fold_left in partition_locals_automaton here we get it in the
     original order again. *)
  let locals_auto, locals = partition_locals_automaton is_visible locals in
  
  let ghosts, locals =
    locals
    |> List.partition
      (fun (_, sv) ->
        try
          match N.get_state_var_source node sv with
          | N.Ghost -> true
          | _ -> false
        with Not_found -> false
      )
  in

  let _ (* ident_witdth *), val_width, ghosts' =
    ghosts |> streams_to_values model ident_width val_width []
  in

  let ident_width, val_width, locals' = 
    locals |> streams_to_values model ident_width val_width []
  in

  let ident_width, val_width, locals_auto' =
    MS.fold (fun auto streams (w, v, ls) ->
        let w, v, s = streams_to_values model w v [] streams in
        w, v, MS.add auto s ls
      ) locals_auto (ident_width, val_width, MS.empty)
  in

  let globals = if is_top then get_constants const_map [] else [] in

  let constants =
    let scope = LustreNode.scope_of_node node in
    get_constants const_map scope
  in

  let ident_width, val_width, globals' =
    globals |> streams_to_values model ident_width val_width []
  in

  let ident_width, val_width, constants' =
    constants |> streams_to_values model ident_width val_width []
  in

  (* Sample inputs, outputs and locals on clock *)
  let globals', constants', inputs', outputs', ghosts', locals', locals_auto'  = match clock with
    | None -> globals', constants', inputs', outputs', ghosts', locals', locals_auto'
    | Some c ->
      sample_streams_on_clock c globals',
      sample_streams_on_clock c constants',
      sample_streams_on_clock c inputs',
      sample_streams_on_clock c outputs',
      sample_streams_on_clock c ghosts',
      sample_streams_on_clock c locals',
      MS.map (sample_streams_on_clock c) locals_auto'
  in
  
  (* Pretty-print this node or function. *)
  Format.fprintf ppf "@[<v>\
      @{<b>%s@} @{<blue>%a@} (%a)@,  @[<v>\
        %a\
        %a\
        %a\
        %a\
        %a\
        %a\
        %a\
        %a\
      @]\
    @,@]"
    title
    (I.pp_print_ident false) 
    name
    (pp_print_list pp_print_call_pt " / ") 
    (List.rev trace)
    (pp_print_modes_section_pt ident_width val_width mode_ident) modes
    (pp_print_stream_section_pt ident_width val_width "Global Constants") globals'
    (pp_print_stream_section_pt ident_width val_width "Constants") constants'
    (pp_print_stream_section_pt ident_width val_width "Inputs") inputs'
    (pp_print_stream_section_pt ident_width val_width "Outputs") outputs'
    (pp_print_stream_section_pt ident_width val_width "Ghosts") ghosts'
    (pp_print_stream_section_pt ident_width val_width "Locals") locals'
    (pp_print_stream_automata_pt ident_width val_width) locals_auto';

  (* Recurse depth-first to print subnodes *)
  pp_print_lustre_path_pt'
    false
    const_map
    ppf
    (subnodes @ tl)

| _ :: tl ->
  
  pp_print_lustre_path_pt' false const_map ppf tl

  

(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_pt ppf (lustre_path, const_map) = 

  (* Delegate to recursive function *)
  pp_print_lustre_path_pt' true const_map ppf [lustre_path]


(* Output a hierarchical model as plain text *)
let pp_print_path_pt
  trans_sys globals subsystems first_is_init ppf model
  =
  (* Create the hierarchical model *)
  node_path_of_subsystems
    globals first_is_init trans_sys model subsystems
  (* Output as plain text *)
  |> pp_print_lustre_path_pt ppf


(* ********************************************************************** *)
(* XML output                                                             *)
(* ********************************************************************** *)


(* Output a file *)
let pp_print_file_xml ppf pos_file = 

  if pos_file = "" then () else
    Format.fprintf ppf "@ file=\"%s\"" pos_file


(* Output a position as XML attributes *)
let pp_print_pos_xml ppf pos = 

  (* Do not print anything for a dummy position *)
  if is_dummy_pos pos then () else 

    (* Get file, line and column of position *)
    let pos_file, pos_lnum, pos_cnum = 
      file_row_col_of_pos pos
    in
    
    (* Print attributes *)
    Format.fprintf 
      ppf
      "%a@ line=\"%d\"@ column=\"%d\""
      pp_print_file_xml pos_file
      pos_lnum
      pos_cnum


(* Output a call trace *)
let pp_print_call_xml ppf = function 

  (* Nothing to output for the top node *)
  | [] -> ()

  (* Output only the position of the last call *)
  | (_, pos) :: _ -> 
    Format.fprintf ppf "%a" pp_print_pos_xml pos


(* Output the identifier of an indexed stream *)
let pp_print_stream_ident_xml = pp_print_stream_ident_pt


(* Pretty-print a property of a stream as XML attributes *)
let pp_print_stream_prop_xml node ppf state_var =

  match N.get_state_var_source node state_var with

  | N.Input -> Format.fprintf ppf "@ class=\"input\""

  | N.Output -> Format.fprintf ppf "@ class=\"output\""

  | N.Local -> Format.fprintf ppf "@ class=\"local\""

  | N.Ghost -> Format.fprintf ppf "@ class=\"ghost\""

  (*| N.Alias (_, Some src) -> pp_print_stream_prop_xml ppf src*)

  | exception Not_found when StateVar.is_const state_var ->

    Format.fprintf ppf "@ class=\"constant\""

  (* Any other streams should have been culled out *)
  | _ -> assert false 



(* Pretty-print a single value of a stream at an instant *)
let pp_print_stream_value ty ppf i show v =
  if show then
    Format.fprintf ppf
      "@,@[<hv 2><Value instant=\"%d\">@,@[<hv 2>%a@]@,@]</Value>"
      i (Model.pp_print_value_xml ~as_type:ty) v

(*
(* Print type of a stream in the current model *)
let pp_print_type_of_svar model ppf state_var =
  (* Get type of identifier *)
  let stream_type = StateVar.type_of_state_var state_var in
  match SVT.find model state_var |> List.hd with
  | Model.Map m ->
    Format.fprintf ppf "%a ^ %a"
      (E.pp_print_lustre_type false) (Type.last_elem_type_of_array stream_type)
      (pp_print_list Format.pp_print_int " ^ ")
      (Model.dimension_of_map m |> List.rev)
  | _ -> E.pp_print_lustre_type false ppf stream_type
*)  
  
let pp_print_stream_values clock ty ppf l =
  match clock with
  | None ->
    (* Show all values if no clock *)
    pp_print_listi (fun ppf i -> pp_print_stream_value ty ppf i true) "" ppf l
  | Some c ->
    (* Show values sampled on the clock *)
    pp_print_list2i (pp_print_stream_value ty) "" ppf c l


(* Pretty-print a single stream *)
let pp_print_stream_xml node model clock ppf (index, state_var) =

  let pp_print_type ppf stream_type =
    match (Type.node_of_type stream_type) with
    | Type.Bool ->
      Format.pp_print_string ppf "type=\"bool\""
    | Type.Int ->
      Format.pp_print_string ppf "type=\"int\""              
    | Type.UBV i ->
      begin match i with
      | 8 -> Format.pp_print_string ppf "type=\"uint8\""
      | 16 -> Format.pp_print_string ppf "type=\"uint16\""
      | 32 -> Format.pp_print_string ppf "type=\"uint32\""
      | 64 -> Format.pp_print_string ppf "type=\"uint64\""
      | _ -> raise 
      (Invalid_argument "pp_print_type: BV size not allowed")
      end
    | Type.BV i ->
      begin match i with
      | 8 -> Format.pp_print_string ppf "type=\"int8\""
      | 16 -> Format.pp_print_string ppf "type=\"int16\""
      | 32 -> Format.pp_print_string ppf "type=\"int32\""
      | 64 -> Format.pp_print_string ppf "type=\"int64\""
      | _ -> raise 
      (Invalid_argument "pp_print_type: BV size not allowed")
      end
    | Type.IntRange (i, j, Type.Range) ->
      Format.fprintf ppf "type=\"subrange\" min=\"%a\" max=\"%a\""
      Numeral.pp_print_numeral i Numeral.pp_print_numeral j
    | Type.Real ->
      Format.pp_print_string ppf "type=\"real\""
    | Type.Abstr s ->
      Format.pp_print_string ppf s
    | Type.IntRange (_, _, Type.Enum) ->
      let pp_print_enum_name ppf =
          Format.fprintf ppf "enumName=\"%s\" " (Type.name_of_enum stream_type)
      in
      Format.fprintf ppf "type=\"enum\"@ %tvalues=\"%a\""
        pp_print_enum_name (pp_print_list Format.pp_print_string ", ")
        (Type.constructors_of_enum stream_type)
    | Type.Array (_, _) ->
      Format.pp_print_string ppf "type=\"array\""
  in

  try 
    let stream_values = SVT.find model state_var in
    let stream_type = StateVar.type_of_state_var state_var in
    Format.fprintf 
      ppf
      "@,@[<hv 2>@[<hv 1><Stream@ name=\"%a\" %a%a>@]\
       %a@]@,</Stream>"
      pp_print_stream_ident_xml (index, state_var)
      pp_print_type stream_type
      (pp_print_stream_prop_xml node) state_var
      (pp_print_stream_values clock stream_type) stream_values

  with Not_found -> assert false


let pp_print_automaton_xml node model clock ppf name streams  =
  Format.fprintf ppf "@,@[<hv 2>@[<hv 1><Automaton@ name=\"%s\">@]" name;
  List.iter (pp_print_stream_xml node model clock ppf) streams;
  Format.fprintf ppf"@]@,</Automaton>"
    

let pp_print_automata_xml node model clock ppf auto_map =
  MS.iter (pp_print_automaton_xml node model clock ppf) auto_map



let pp_print_active_modes_xml ppf = function
| None | Some [] -> ()
| Some mode_trace ->
  Format.fprintf ppf
    "@,@[<v>%a@]"
    (pp_print_list
      ( fun _ (k, tree) ->
        Format.fprintf ppf
          "\
            <ActiveModes instant=\"%d\">@   \
              %a\
            </ActiveModes>\
          "
          k
          C.ModeTrace.fmt_as_cex_step_xml tree
          (* (List.length scoped)
          (pp_print_list
            (fun fmt ->
              Format.fprintf fmt
                "<Mode name=\"%a\">"
                (I.pp_print_ident false)
            )
            "@ "
          ) active
          (pp_print_list pp_print_mode_scoped_xml "@ ") scoped
          (fun ppf ->
            if scoped <> [[]] || active <> [] then Format.fprintf ppf "@ ") *)
      )
      "@ "
    ) (
      mode_trace |> List.fold_left (
        fun (acc, count) mode ->
          (count, C.ModeTrace.mode_paths_to_tree mode) :: acc, count + 1
      ) ([], 0)
      |> fst |> List.rev
    )

(* Output a list of node models. *)
let rec pp_print_lustre_path_xml' is_top const_map ppf = function 

  | [] -> ()

  | (
    trace, Node (
      { N.name; N.inputs; N.outputs; N.locals; N.is_function } as node,
      model, active_modes, call_conds, subnodes
    )
  ) :: tl when N.node_is_visible node ->

    let is_visible = N.state_var_is_visible node in
  
    let is_state, name =
      match N.node_is_state_handler node with
      | None -> false, name
      | Some state -> true, I.mk_string_ident state
    in

    let title =
      if is_function then "Function"
      else if is_state then "State"
      else "Node"
    in

    (* Boolean clock that indicates if the node is active for this particular
       call *)
    let clock = act_stream model call_conds in

    (* Remove first dimension from index *)
    let pop_head_index = function 
      | ([], sv) -> ([], sv)
      | (_ :: tl, sv) -> (tl, sv)
    in

    (* Remove index of position in input for printing *)
    let inputs' = 
      D.bindings inputs
      |> List.filter (fun (_, sv) -> is_visible sv)
      |> List.map pop_head_index
    in

    (* Remove index of position in output for printing *)
    let outputs' = 
      D.bindings outputs
      |> List.filter (fun (_, sv) -> is_visible sv)
      |> List.map pop_head_index
    in
    
    (* Filter locals to for visible state variables only and return
       as a list 

       The list of locals is the reversed from the original input in the node,
       with fold_left in partition_locals_automaton here we get it in the
       original order again. *)
    let locals_auto', locals' = partition_locals_automaton is_visible locals in

    let ghosts', locals' =
      locals'
      |> List.partition
        (fun (_, sv) ->
          try
            match N.get_state_var_source node sv with
            | N.Ghost -> true
            | _ -> false
          with Not_found -> false
        )
    in

    let globals' = if is_top then get_constants const_map [] else [] in

    let constants' =
      let scope = LustreNode.scope_of_node node in
      get_constants const_map scope
    in

    (* Pretty-print this node *)
    Format.fprintf ppf "@,@[<hv 2>@[<hv 1><%s@ name=\"%a\"%a>@]"
      title
      (I.pp_print_ident false) name
      pp_print_call_xml trace;

    pp_print_active_modes_xml ppf active_modes;
    List.iter (pp_print_stream_xml node model clock ppf) globals';
    List.iter (pp_print_stream_xml node model clock ppf) constants';
    List.iter (pp_print_stream_xml node model clock ppf) inputs';
    List.iter (pp_print_stream_xml node model clock ppf) outputs';
    List.iter (pp_print_stream_xml node model clock ppf) ghosts';
    List.iter (pp_print_stream_xml node model clock ppf) locals';
    pp_print_automata_xml node model clock ppf locals_auto';
    pp_print_lustre_path_xml' false const_map ppf subnodes;
    Format.fprintf ppf "@]@,</%s>" title;

    (* Continue *)
    pp_print_lustre_path_xml' false const_map ppf tl

  | _ :: tl ->
    
    (* Continue *)
    pp_print_lustre_path_xml' false const_map ppf tl


(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_xml ppf (path, const_map) = 

  (* Delegate to recursive function *)
  pp_print_lustre_path_xml' true const_map ppf [path]


(* Ouptut a hierarchical model as XML *)
let pp_print_path_xml
  trans_sys globals subsystems first_is_init ppf model
=
  (* Create the hierarchical model *)
  node_path_of_subsystems
    globals first_is_init trans_sys model subsystems
  (* Output as XML *)
  |> pp_print_lustre_path_xml ppf


(* ********************************************************************** *)
(* JSON output                                                             *)
(* ********************************************************************** *)


(* Output a call trace *)
let pp_print_call_json ppf = function

  (* Nothing to output for the top node *)
  | [] -> ()

  (* Output only the position of the last call *)
  | (_, pos) :: _ ->

    let pp_print_file_json ppf pos_file =
      if pos_file = "" then () else
        Format.fprintf ppf ",@,\"file\" : \"%s\"" pos_file
    in

    (* Do not print anything for a dummy position *)
    if is_dummy_pos pos then () else

      (* Get file, line and column of position *)
      let pos_file, pos_lnum, pos_cnum =
        file_row_col_of_pos pos
      in

      (* Print attributes *)
      Format.fprintf ppf
        "%a,@,\"line\" : %d,@,\"column\" : %d"
        pp_print_file_json pos_file
        pos_lnum
        pos_cnum


(* Output the identifier of an indexed stream *)
let pp_print_stream_ident_json = pp_print_stream_ident_pt


(* Pretty-print a property of a stream as JSON attributes *)
let pp_print_stream_prop_json node ppf state_var =

  match N.get_state_var_source node state_var with

  | N.Input -> Format.fprintf ppf "\"class\" : \"input\",@,"

  | N.Output -> Format.fprintf ppf "\"class\" : \"output\",@,"

  | N.Local -> Format.fprintf ppf "\"class\" : \"local\",@,"

  | N.Ghost -> Format.fprintf ppf "\"class\" : \"ghost\",@,"

  (* | N.Alias (_, Some src) -> pp_print_stream_prop_json ppf src *)

  | exception Not_found when StateVar.is_const state_var ->

    Format.fprintf ppf "\"class\" : \"constant\",@,"

  (* Any other streams should have been culled out *)
  | _ -> assert false


(* Pretty-print a single value of a stream at an instant *)
let pp_print_stream_value_json ty ppf i v =
  Format.fprintf ppf
    "@,[%d, %a]"
    i (Model.pp_print_value_json ~as_type:ty) v


let pp_print_stream_values_json clock ty ppf l =
  match clock with
  | None ->
    (* Show all values if no clock *)
    pp_print_listi (fun ppf i -> pp_print_stream_value_json ty ppf i) "," ppf l
  | Some c ->
    (* Pair each value with its index and clock, and then filter out undefined ones.
     * This must be done before printing, because otherwise we print commas in-between
     * filtered elements, which is invalid json. *)
    let values_on_clock =
      List.mapi (fun i c -> (i, c)) c
      |> List.map2 (fun v (i, c) -> (i, v, c)) l
      |> List.filter (fun (_, _, c) -> c)
    in
      pp_print_list (fun ppf (i, v, _c) -> pp_print_stream_value_json ty ppf i v) "," ppf values_on_clock


let rec pp_print_type_json field ppf stream_type =
  match (Type.node_of_type stream_type) with
  | Type.Bool
  | Type.Int
  | Type.UBV _
  | Type.BV _
  | Type.Real -> (
    Format.fprintf ppf "\"%s\" : \"%a\",@,"
        field (E.pp_print_lustre_type false) stream_type
  )
  | Type.Abstr s -> (
    Format.fprintf ppf
        "\"%s\" : \"abstr\",@,\
         \"%sInfo\" :@,{@[<v 1>@,\
         \"name\" : %s\
         @]@,},@,\
        "
        field field s
  )
  | Type.IntRange (i, j, Type.Range) -> (
    Format.fprintf ppf
        "\"%s\" : \"subrange\",@,\
         \"%sInfo\" :@,{@[<v 1>@,\
         \"min\" : %a,@,\
         \"max\" : %a\
         @]@,},@,\
        "
        field field
        Numeral.pp_print_numeral i Numeral.pp_print_numeral j
  )
  | Type.IntRange (_, _, Type.Enum) -> (
    let pp_print_qstring ppf s =
      Format.fprintf ppf "\"%s\"" s
    in
    let pp_print_enum_name ppf =
        Format.fprintf ppf "\"name\" : \"%s\",@," (Type.name_of_enum stream_type)
    in
    Format.fprintf ppf
        "\"%s\" : \"enum\",@,\
         \"%sInfo\" :@,{@[<v 1>@,\
         %t\
         \"values\" : [%a]\
         @]@,},@,\
        "
        field field
        pp_print_enum_name
        (pp_print_list pp_print_qstring ", ")
        (Type.constructors_of_enum stream_type)
  )
  | Type.Array _ -> (
    let base_type = Type.last_elem_type_of_array stream_type in
    let sizes =
      Type.all_index_types_of_array stream_type |>
      List.map Type.node_of_type |>
      List.map (function
        | Type.IntRange (_, j, Type.Range) ->
          Numeral.string_of_numeral j
        | _ -> "null"
      )
    in
    Format.fprintf ppf
        "\"type\" : \"array\",@,\
         \"typeInfo\" :@,{@[<v 1>@,\
         %a\
         \"sizes\" : [%a]\
         @]@,},@,\
        "
        (pp_print_type_json "baseType") base_type
        (pp_print_list Format.pp_print_string ", ") sizes
  )

(* Pretty-print a single stream *)
let pp_print_stream_json node model clock ppf (index, state_var) =
  try
    let stream_values = SVT.find model state_var in
    let stream_type = StateVar.type_of_state_var state_var in
    Format.fprintf ppf
      "@,{@[<v 1>@,\
        \"name\" : \"%a\",@,\
        %a\
        %a\
        \"instantValues\" :%t\
       @]@,}\
      "
      pp_print_stream_ident_json (index, state_var)
      (pp_print_type_json "type") stream_type
      (pp_print_stream_prop_json node) state_var
      (function ppf ->
         if stream_values = [] then
           Format.fprintf ppf " []"
         else
           Format.fprintf ppf "@,[@[<v 1>%a@]@,]"
           (pp_print_stream_values_json clock stream_type)
           stream_values
      )

  with Not_found -> assert false


let pp_print_active_modes_json ppf = function
  | None | Some [] -> ()
  | Some mode_trace ->
      Format.fprintf ppf ",@,\"activeModes\" :@,[@[<v 1>%a@]@,]"
        (pp_print_list (fun _ (k, tree) ->
          Format.fprintf ppf
            "@,{@[<v 1>@,\
              \"instant\" : %d,@,\
              %a\
             @]@,}\
            "
            k
            C.ModeTrace.fmt_as_cex_step_json tree
        ) ",")
        (
          mode_trace |> List.fold_left (
          fun (acc, count) mode ->
            (count, C.ModeTrace.mode_paths_to_tree mode) :: acc, count + 1
          ) ([], 0)
          |> fst |> List.rev
        )


let pp_print_streams_json node model clock ppf = function
  | [] -> ()
  | streams ->
      Format.fprintf ppf ",@,\"streams\" :@,[@[<v 1>%a@]@,]"
        (pp_print_list
          (pp_print_stream_json node model clock) ",")
        streams


let pp_print_automaton_json node model clock ppf (name, streams) =

  Format.fprintf ppf
    "@,{@[<v 1>@,\
      \"name\" : \"%s\"\
      %a\
     @]@,}\
    "
    name (pp_print_streams_json node model clock) streams


let pp_print_automata_json node model clock ppf auto_map =

  if MS.is_empty auto_map then () else
    Format.fprintf ppf ",@,\"automata\" :@,[@[<v 1>%a@]@,]"
      (pp_print_list
        (pp_print_automaton_json node model clock) ",")
      (MS.bindings auto_map)


let pp_print_streams_and_automata_json is_top const_map ppf
  ({N.inputs; N.outputs; N.locals} as node, model, call_conds) =

  let is_visible = N.state_var_is_visible node in

  (* Boolean clock that indicates if the node is active for this particular
     call *)
  let clock = act_stream model call_conds in

  (* Remove first dimension from index *)
  let pop_head_index = function
    | ([], sv) -> ([], sv)
    | (_ :: tl, sv) -> (tl, sv)
  in

  (* Remove index of position in input for printing *)
  let inputs' =
    D.bindings inputs
    |> List.filter (fun (_, sv) -> is_visible sv)
    |> List.map pop_head_index
  in

  (* Remove index of position in output for printing *)
  let outputs' =
    D.bindings outputs
    |> List.filter (fun (_, sv) -> is_visible sv)
    |> List.map pop_head_index
  in

  (* Filter locals to for visible state variables only and return
     as a list

     The list of locals is the reversed from the original input in the node,
     with fold_left in partition_locals_automaton here we get it in the
     original order again. *)
  let locals_auto', locals' = partition_locals_automaton is_visible locals in

  let ghosts', locals' =
    locals'
    |> List.partition
      (fun (_, sv) ->
        try
          match N.get_state_var_source node sv with
          | N.Ghost -> true
          | _ -> false
        with Not_found -> false
      )
  in

  let globals' = if is_top then get_constants const_map [] else [] in

  let constants' =
    let scope = LustreNode.scope_of_node node in
    get_constants const_map scope
  in

  let streams = []
    |> List.rev_append globals'
    |> List.rev_append constants'
    |> List.rev_append inputs'
    |> List.rev_append outputs'
    |> List.rev_append ghosts'
    |> List.rev_append locals'
    |> List.rev
  in

  Format.fprintf ppf "%a%a"
    (pp_print_streams_json node model clock) streams
    (pp_print_automata_json node model clock) locals_auto'


(* Output a list of node models. *)
let rec pp_print_lustre_path_json' is_top const_map ppf = function

  | [] -> ()

  | (
    trace, Node ({ N.name; N.is_function } as node,
      model, active_modes, call_conds, subnodes
    )
  ) :: tl when N.node_is_visible node ->

    let is_state, name =
      match N.node_is_state_handler node with
      | None -> false, name
      | Some state -> true, I.mk_string_ident state
    in

    let title =
      if is_function then "function"
      else if is_state then "state"
      else "node"
    in

    let pp_print_subnodes_json ppf = function
      | [] -> ()
      | subnodes ->
          Format.fprintf ppf ",@,\"subnodes\" :@,[@[<v 1>%a@]@,]"
            (pp_print_lustre_path_json' false const_map) subnodes
    in

    let comma = if tl <> [] then "," else "" in

    (* Pretty-print this node *)
    Format.fprintf ppf
       "@,{@[<v 1>@,\
        \"blockType\" : \"%s\",@,\
        \"name\" : \"%a\"\
        %a%a%a%a\
        @]@,}%s\
       "
       title (I.pp_print_ident false) name
       pp_print_call_json trace
       pp_print_active_modes_json active_modes
       (pp_print_streams_and_automata_json is_top const_map) (node, model, call_conds)
       pp_print_subnodes_json subnodes
       comma;

    (* Continue *)
    pp_print_lustre_path_json' false const_map ppf tl

  | _ :: tl ->

    (* Continue *)
    pp_print_lustre_path_json' false const_map ppf tl


(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_json ppf (path, const_map) =

  (* Delegate to recursive function *)
  Format.fprintf ppf "@,[@[<v 1>%a@]@,]"
    (pp_print_lustre_path_json' true const_map) [path]


(* Ouptut a hierarchical model as JSON *)
let pp_print_path_json
  trans_sys globals subsystems first_is_init ppf model
=
  (* Create the hierarchical model *)
  node_path_of_subsystems
    globals first_is_init trans_sys model subsystems
  (* Output as JSON *)
  |> pp_print_lustre_path_json ppf


(* ********************************************************************** *)
(* CSV output                                                             *)
(* ********************************************************************** *)

(* Pretty-prints a single stream in CSV. *)
let pp_print_stream_csv model ppf (index, sv) =
  try
    let typ3 = StateVar.type_of_state_var sv in
    let values = SVT.find model sv in
    Format.fprintf ppf "%a,%a,%a"
      pp_print_stream_ident_xml (index, sv)
      (E.pp_print_lustre_type false) typ3
      (pp_print_list Model.pp_print_value ",")
      values
  with Not_found ->
    Format.asprintf
      "[LustrePath.pp_print_stream_csv] could not find state var %a"
      pp_print_stream_ident_xml (index, sv)
    |> failwith


(* Outputs a sequence of values for the inputs of a node. *)
let pp_print_lustre_path_in_csv ppf = function
| (_, Node ( { N.inputs }, model, _, _, _ )), _ ->

  (* Remove first dimension from index. *)
  let pop_head_index = function
    | [], sv -> [], sv
    | _ :: tl, sv -> tl, sv
  in

  (* Remove index of position in input for printing. *)
  let inputs = D.bindings inputs |> List.map pop_head_index in

  (* Print inputs in CSV. *)
  Format.fprintf ppf "@[<v>%a@]"
    (pp_print_list (pp_print_stream_csv model) "@ ") inputs

(* Outputs a model for the inputs of a system in CSV. *)
let pp_print_path_in_csv
  trans_sys globals subsystems first_is_init ppf model
=
  (* Create the hierarchical model. *)
  node_path_of_subsystems 
    globals first_is_init trans_sys model subsystems
  (* Output as CSV. *)
  |> pp_print_lustre_path_in_csv ppf



(***************************************************)
(* Reconstruct Lustre streams from state variables *)
(***************************************************)

let same_args abstr_map (inputs, defs) (inputs', defs') =
  D.equal (fun a1 a2 ->
      StateVar.equal_state_vars a1 a2 ||
      (* can be abstractions *)
      try
        let e1 = SVM.find a1 abstr_map in
        let e2 = SVM.find a2 abstr_map in
        LustreExpr.equal e1 e2
      with Not_found -> false)
    inputs inputs' &&
  match defs, defs' with
  | Some d1, Some d2 -> D.equal LustreExpr.equal d1 d2
  | None, None -> true
  | _ -> false


let rec add_to_callpos abstr_map acc pos cond args calls =
  match calls with
  | ((pos', nb', _, args') as x) :: r ->
    let c_pos = Lib.compare_pos pos pos' in

    if c_pos = 0 then raise Exit; (* already in there, abort *)
    
    if same_args abstr_map args args' then
      (* calls with same arguments but at different positions *)
      (* insert in between with the same number, don't shift anything *)
      if c_pos > 0 then
        List.rev_append acc (x :: (pos, nb', cond, args) :: r)
      else
        List.rev_append acc ((pos, nb', cond, args) :: calls)
          
    else if c_pos > 0 then
      (* continue to look *)
      add_to_callpos abstr_map (x :: acc) pos cond args r

    else (* c_pos < 0 *)
      (* insert in between and shift the ones on the right *)
      List.rev_append acc
        ((pos, nb', cond, args) ::
         (List.map (fun (p, n, c, a) -> (p, n+1, c, a)) calls))

  | [] ->
    (* last one or only one *)
    let nb = match acc with [] -> 0 | (_, n, _, _) :: _ -> n+1 in
    List.rev ((pos, nb, cond, args) :: acc)



let register_callpos_for_nb abstr_map hc lid parents pos cond args =
  let is_condact = match cond with | N.CActivate _ :: _ -> true | _ -> false in
  let cat =
    try Hashtbl.find hc (lid, is_condact)
    with Not_found ->
      let c = Hashtbl.create 7 in
      Hashtbl.add hc (lid, is_condact) c;
      c
  in
  let calls = try Hashtbl.find cat parents with Not_found -> [] in
  try
    let new_calls = add_to_callpos abstr_map [] pos cond args calls in
    Hashtbl.replace cat parents new_calls
  with Exit -> () (* already in there *)

  
let pos_to_numbers abstr_map nodes =
  let hc = Hashtbl.create 43 in

  (* let main_node = List.find (fun n -> n.LustreNode.is_main) nodes in *)
  let main_node = List.hd nodes in

  let node_by_lid lid =
    List.find (fun n -> I.equal n.N.name lid) nodes in

  let rec fold parents node =

    List.iter
      (fun ({ N.call_node_name = lid;
             call_pos = pos; call_cond = cond;
             call_inputs = inputs; call_defaults = defs } as call) -> 

        (* Format.eprintf "register : %a at %a %s \n ARgs: (%a)@." *)
        (*   (LustreIdent.pp_print_ident false) lid Lib.pp_print_position pos *)
        (*   (match clock with *)
        (*    | None -> "" *)
        (*    | Some c -> "ON "^ (StateVar.string_of_state_var c)) *)
        (*   (pp_print_list StateVar.pp_print_state_var ", ") inputs *)
        (* ; *)
        
        register_callpos_for_nb
          abstr_map hc lid parents pos cond (inputs, defs);

        fold (call :: parents) (node_by_lid lid)

      ) node.LustreNode.calls
  in

  fold [] main_node;
  
  hc

exception Found of int * N.call_cond list

let get_pos_number hc lid pos =
  (* Format.eprintf "getpos : %a at %a@." (LustreIdent.pp_print_ident false) lid *)
  (* Lib.pp_print_position pos; *)

  let find_in_cat cat =
    Hashtbl.iter (fun _ l ->
        List.iter (fun (p, n, c, _) ->
            if Lib.equal_pos p pos then raise (Found (n, c)))
          l
      ) cat;
    raise Not_found
  in

  (* look for both condact and non condact calls *)
  try
    (try Hashtbl.find hc (lid, false) |> find_in_cat
     with Not_found -> Hashtbl.find hc (lid, true)  |> find_in_cat);
  with Found (n,c) -> n, c


let rec get_instances acc hc parents sv =
  (* Format.eprintf "get_instances : %a@." StateVar.pp_print_state_var sv; *)
  match N.get_state_var_instances sv with
  | [] ->
    (sv, List.rev parents) :: acc
  | insts ->
    List.fold_left (fun acc (pos, lid, lsv) ->
        try
          let nb, cond = get_pos_number hc lid pos in
          get_instances acc hc ((lid, nb, cond) :: parents) lsv
        with Not_found ->
          (* was removed by slicing, ingore this instance *)
          acc
      ) acc insts


let get_lustre_streams hc sv = get_instances [] hc [] sv
  

let inverse_oracle_map nodes =
  List.fold_left (fun acc node ->
      SVT.fold (fun oracle sv acc ->
          let l = try SVM.find oracle acc with Not_found -> [] in
          Debug.fec
             "inverse oracle: %a ->>> %a"
             StateVar.pp_print_state_var oracle
             StateVar.pp_print_state_var sv;
          SVM.add oracle (sv :: l) acc 
        ) (N.get_oracle_state_var_map node) acc
    ) SVM.empty nodes

let inverse_expr_map nodes =
  List.fold_left (fun acc node ->
      SVT.fold (fun sv e acc ->
        Debug.fec
           "inverse expr: %a ->>> %a" StateVar.pp_print_state_var sv
           (LustreExpr.pp_print_lustre_expr false) e;
          SVM.add sv e acc
        ) (N.get_state_var_expr_map node) acc
  ) SVM.empty nodes


let orig_of_oracle oracle_map sv =
  try SVM.find sv oracle_map with Not_found -> [sv]
  (* try *)
  (*   let l = SVMap.find sv oracle_map in *)
  (*   List.fold_left *)
  (*     (fun acc sv -> List.rev_append (orig_of_oracle oracle_map sv) acc) [] l *)
  (* with Not_found -> [sv] *)


let reconstruct_lustre_streams subsystems state_vars =

  let nodes = SubSystem.all_subsystems_of_list subsystems
              |> List.map (fun {SubSystem.source} -> source) in
  
  (* mapback from abstract state variables to expressions *)
  let abstr_map = inverse_expr_map nodes in

  (* convert position to call numbers *)
  let hc = pos_to_numbers abstr_map nodes in
  
  (* mapback from oracles to state vars *)
  let oracle_map = inverse_oracle_map nodes in

  List.fold_left (fun acc sv ->

      (* if it's an oracle get the original variables otherwise just keep the
         variable *)
      let l = orig_of_oracle oracle_map sv in

      (* get streams *)
      let streams = List.flatten (List.map (get_lustre_streams hc) l) in

      (* get original variables of oracles in node call parameters *)
      let streams =
        List.fold_left (fun acc (sv, p) ->
            List.fold_left
              (fun acc s -> (s, p) :: acc)
              acc (orig_of_oracle oracle_map sv)
          ) [] streams
        |> List.rev in
      
      (* append to others *)
      let others = try SVM.find sv acc with Not_found -> [] in
      SVM.add sv (streams @ others) acc
        
    ) SVM.empty state_vars


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
