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
module NI = NodeId

module SVT = StateVar.StateVarHashtbl
module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet
module G = LustreGlobals

(* Model for a node and its subnodes *)
type t =
  Node of
    N.t *
    Model.path *
    (string * Type.t * Model.value list) list * (* Required modes: conjunction of all the requires clauses of a mode *)
    (string * Type.t * Model.value list) list * (* Ensured modes: conjunction of all the ensures  clauses of a mode *)
    (string * Type.t * Model.value list) list * (* Assumptions *)
    (string * Type.t * Model.value list) list * (* Guarantees *)
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
let map_term_top ?(no_fail=false) instances term = 

  Term.map
    (fun _ t -> 

       (* Only map free variables *)
       if Term.is_free_var t then 

       try
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

       with Not_found -> if no_fail then t else raise Not_found

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


let add_init_values
  equations_of_init
  trans_sys
  instances
  model'
  first_model
  to_reconstruct
=
  equations_of_init |> List.iter (fun ((sv, _), def) ->
  if SVS.mem sv to_reconstruct then
    (* Value for state variable at step *)
    let v =
      (* Get expression for initial state *)
      E.base_term_of_t Model.path_offset def
      (* Map variables in term to top system, but
          not fail if they are not available *)
      |> (map_term_top ~no_fail:true instances)
      (* Evaluate term in model *)
      |> Eval.eval_term
        (TransSys.uf_defs trans_sys)
        first_model
      (* Return term *)
      |> Eval.term_of_value
    in
    let var =
      Var.mk_state_var_instance sv Model.path_offset
    in
    (* Add value to [first_model] so that it is available when
        evaluating the definition of the next variable *)
    Var.VarHashtbl.add first_model var (Model.Term v) ;
    match SVT.find_opt model' sv with
    | None -> SVT.add model' sv [Model.Term v]
    | Some l -> SVT.replace model' sv ((Model.Term v) :: l)
  )

let add_step_values
  equations_of_step
  trans_sys
  instances
  model'
  curr_model
  prev_model
  to_reconstruct
=
  equations_of_step |> List.iter (fun ((sv, _), def) ->
  if SVS.mem sv to_reconstruct then
    (* Value for state variable at step *)
    let v =
      (* Get expression for step state *)
      E.cur_term_of_t Model.path_offset def
      (* Map variables in term to top system, but
         not fail if they are not available *)
      |> (map_term_top ~no_fail:true instances)
      (* Evaluate expression for step state *)
      |> Eval.eval_term
        (TransSys.uf_defs trans_sys)
        (Model.bump_and_merge Numeral.(~- one) curr_model prev_model)
      (* Return term *)
      |> Eval.term_of_value
    in
    let var =
      Var.mk_state_var_instance sv Model.path_offset
    in
    (* Add value to [m] so that it is available when
       evaluating the definition of the next variable *)
    Var.VarHashtbl.add curr_model var (Model.Term v) ;
    match SVT.find_opt model' sv with
    | None -> SVT.add model' sv [Model.Term v]
    | Some l -> SVT.replace model' sv ((Model.Term v) :: l)
  )

let reconstruct_and_add
  first_is_init
  node
  trans_sys
  instances
  model'
  step_models
  to_reconstruct
=
  let equations_of_init =
    (* Equations must be topologically sorted *)
    N.ordered_equations_of_node
      node (TransSys.state_vars trans_sys) true
  in
  let equations_of_step =
    match step_models with
    | [] ->
      (* Unreachable; [map_top_and_add] handles the case where the path is empty *)
      assert false
    | [_] when first_is_init -> [] (* We don't use equations_of_step later *)
    | _ ->
      (* Equations must be topologically sorted *)
      N.ordered_equations_of_node
        node (TransSys.state_vars trans_sys) false
  in
  let rec aux = function
  | [] ->
    (* Unreachable; [map_top_and_add] handles the case where the path is empty *)
    assert false

  | [first_model] when first_is_init -> (
    (* The first model is encoding the initial state *)

    (* Reconstruct the values for the variables at the initial step
       from their (initial) Lustre expressions *)
    add_init_values
      equations_of_init trans_sys
      instances
      model'
      first_model
      to_reconstruct
  )

  | [curr_model] -> (
    (* The first model represents an arbitrary state *)
    let prev_model =
      (* We do not know the value of the variables at the previous state, so
         we use an empty model *)
      Model.create 0
    in
    add_step_values
      equations_of_step
      trans_sys
      instances
      model'
      curr_model
      prev_model
      to_reconstruct
  )

  | curr_model :: tl ->

    (* Reconstruct the rest of values for the variables
       from their (step) Lustre expressions *)
    add_step_values
      equations_of_step
      trans_sys
      instances
      model'
      curr_model
      (List.hd tl)
      to_reconstruct ;

    (* Continue reconstruction *)
    aux tl
  in
  aux (List.rev step_models)


(* Get the sequence of values in the top system of each local state variable 
   (if exists) and add it to [model']. Otherwise, reconstruct the sequence of
   values from its definition. *)
let map_top_or_reconstruct_and_add
  first_is_init
  node
  trans_sys
  instances
  model
  model'
  locals
=
  (* Set of local variable to reconstruct *)
  let to_reconstruct =
    List.fold_left
      (fun acc l ->
        D.fold
          (fun i state_var acc' ->
            try
              (* Get the sequence of values of the state variable in
                 the top system and add it to [model'] *)
              map_top_and_add instances model model' i state_var;
              acc'
            with Not_found ->
              (* Mark the state variable as pending to reconstruct *)
              SVS.add state_var acc'
          )
          l
          acc
      )
      SVS.empty
      locals
  in
  if not (SVS.is_empty to_reconstruct) then (

    let step_models =
      (* Create fresh list of models, one for each step on the path,
         that can be modified locally for reconstructing values
         of local varibles *)
      Model.models_of_path model
    in

    reconstruct_and_add
      first_is_init
      node
      trans_sys
      instances
      model'
      step_models
      to_reconstruct
  )

let trace_of_contract_item model_top instances sv =
  let model_values = try map_top instances sv |> SVT.find model_top with Not_found -> [] in
  List.map (function
    | Model.Term t -> t == Term.t_true
    | _ -> failwith "evaluating mode requirement: value should be a term") model_values

let mk_term_t_or_f b = if b then Term.mk_true () else Term.mk_false ()

let guarantees_of_instances model_top instances = function
  (* No contract. *)
  | None | Some { C.guarantees = [] } -> []
  (* Contract with some modes. *)
  | Some { C.guarantees } -> 
    let trace_of_req = trace_of_contract_item model_top instances in
   
    let name_normalize name pos = 
      match name with 
      | None ->  Format.asprintf "guarantee%a" Lib.pp_print_line_and_column pos
      | Some s -> s
    in 
    let svar_tform ({C.svar; name; pos}, _) = 
      ( name_normalize name pos
      , Type.mk_bool ()
      , List.map (function bool -> Model.Term (mk_term_t_or_f bool)) (trace_of_req svar))
    in
    List.map svar_tform guarantees
    

let assumptions_of_instances model_top instances = function
  (* No contract. *)
  | None | Some { C.assumes = [] } -> []
  (* Contract with some modes. *)
  | Some { C.assumes } -> 
    let trace_of_req = trace_of_contract_item model_top instances in
   
    let name_normalize name pos = match name with 
      | None -> Format.asprintf "assume%a" Lib.pp_print_line_and_column pos
      | Some s -> s
    in 
    let svar_tform {C.svar; name; pos} = 
      ( name_normalize name pos
      , Type.mk_bool ()
      , List.map (function bool -> Model.Term (mk_term_t_or_f bool)) (trace_of_req svar))
    in
    List.map svar_tform assumes

let merge_req_traces t1 t2 =
  let rec loop acc = function
    | ([], []) -> List.rev acc
    | (v1 :: t1, v2 :: t2) -> loop ((v1 && v2) :: acc) (t1, t2)
    | _ -> failwith "while constructing the trace of active modes: tried to merge two traces of inconsistent length"
  in
  loop [] (t1, t2)

let mode_requires_of_instances model_top instances = function
  (* No contract. *)
  | None | Some { C.modes = [] } -> ([], 0)
  (* Contract with some modes. *)
  | Some { C.modes } ->
    let trace_of_req { C.svar } = trace_of_contract_item model_top instances svar in
    let add_mode_to_trace (mode_trace, max_len) = function
      | { C.requires = head :: tail } as m ->
        let head = trace_of_req head in
        let reqs_val =
          List.fold_left
            (fun acc req -> trace_of_req req |> merge_req_traces acc)
            head tail
        in
        let entry =
          ( I.string_of_ident true m.name ^ ".requires"
          , Type.mk_bool ()
          , List.map (fun req_val -> Model.Term (mk_term_t_or_f req_val)) reqs_val )
        in
        (entry :: mode_trace, max max_len (List.length reqs_val))
      | { C.requires = [] } as m ->
        let entry =
          ( I.string_of_ident true m.name ^ ".requires"
          , Type.mk_bool ()
          , [] )
        in
        (entry :: mode_trace, max_len)
    in

    List.fold_left add_mode_to_trace ([], 0) modes



let mode_ensures_of_instances model_top instances = function
  (* No contract. *)
  | None | Some { C.modes = [] } -> ([], 0)
  (* Contract with some modes. *)
  | Some { C.modes } ->
    let trace_of_req { C.svar } = trace_of_contract_item model_top instances svar in

    let add_mode_to_trace (mode_trace, max_len) = function
      | { C.ensures = head :: tail } as m ->
        let head = trace_of_req head in
        let reqs_val =
          List.fold_left
            (fun acc req -> trace_of_req req |> merge_req_traces acc)
            head tail
        in
        let entry =
          ( I.string_of_ident true m.name ^ ".ensures"
          , Type.mk_bool ()
          , List.map (fun req_val -> Model.Term (mk_term_t_or_f req_val)) reqs_val )
        in
        (entry :: mode_trace, max max_len (List.length reqs_val))
      | { C.ensures = [] } as m ->
        let entry =
          ( I.string_of_ident true m.name ^ ".ensures"
          , Type.mk_bool ()
          , [] )
        in
        (entry :: mode_trace, max_len)
    in

    List.fold_left add_mode_to_trace ([], 0) modes

let rec transpose = function
    | [] | [] :: _ -> []
    | rows -> List.map List.hd rows :: transpose (List.map List.tl rows)

let get_constants const_map scope =
  match Scope.Map.find_opt scope const_map with
  | None -> []
  | Some l -> l

let fill_empty_modes t_max modes =
  let fill_out_mode = function
    | (name, type_bool, []) ->
        let init_vals = List.init t_max (fun _ ->  Model.Term (mk_term_t_or_f true)) in
        (name, type_bool, init_vals)
    | (name, type_bool, vals) ->
        (name, type_bool, vals)
  in
  List.map fill_out_mode modes
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
         (* For a recursive function, the subsystem scope is prefixed with a
            recursion tag that distinguishes unrollings (e.g. [rec_5; name]);
            the node name is the last element. This ident is only used to
            display the call trace, where the internal tag should not appear,
            so we keep just the node name. [of_scope] also only accepts a flat
            (single-id) scope. For a non-recursive node the scope already is
            [name], so this is a no-op. *)
         let ident =
           TransSys.scope_of_trans_sys t |> List.rev |> List.hd
         in
         ([ident] |> I.of_scope, pos))
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

  (* Map all local state variables to the top instances or
     reconstruct and add their path to the model

     A local variable is either stateful in which case there is
     exactly one state variable of the top system it is an instance
     of. Otherwise, there is an equation of the node that can be
     substituted for the state variable. *)
  map_top_or_reconstruct_and_add
    first_is_init
    node
    trans_sys
    instances
    model_top
    model
    ((D.singleton D.empty_index node.N.init_flag) :: locals)
  ;

  let required_modes, max_length = mode_requires_of_instances (*active_modes_of_instances*) model_top instances contract in
  let required_modes = fill_empty_modes max_length required_modes in
  let ensured_modes, max_length = mode_ensures_of_instances model_top instances contract in
  let ensured_modes = fill_empty_modes max_length ensured_modes in
  let contract_assumptions = assumptions_of_instances model_top instances contract in
  let contract_guarantees = guarantees_of_instances model_top instances contract in

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
  (trace, Node (node, model, required_modes, ensured_modes, contract_assumptions, contract_guarantees, call_conds, subnodes))


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
  (* List.iter (fun node -> Format.printf "Node is subsystem: %a,\n" N.pp_print_node_debug node) nodes; *)
  (* Format.printf "folding@.@." ; *)
  (*Printexc.record_backtrace true ;*)

  (* Map from scopes to constants (empty scope = global scope) *)
  let const_map =
    let constants =
      List.fold_left (fun acc (_, vt, is_generated) ->
        if is_generated then acc
        else
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
        (N.node_of_scope (I.of_scope scope) nodes)
        trans_sys'
    in
    (r, const_map)
  with
  | TimeoutWall -> raise TimeoutWall
  | e ->
    (* Get backtrace now, Printf changes it *)
    let backtrace = Printexc.get_backtrace () in

    Format.printf "Caught %s.@ Backtrace:@\n%s@.@."
      (Printexc.to_string e)
      backtrace ;
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


(* Output the name of the lustre variable *)
let pp_print_lustre_var ppf state_var =
  E.pp_print_lustre_var false ppf state_var


(* Output the identifier of an indexed stream *)
let pp_print_stream_ident_pt ppf (index, state_var) =

  Format.fprintf
    ppf
    "%a%a"
    pp_print_lustre_var state_var
    (D.pp_print_index false) index


(* Output the calling node and the position of the call *)
let pp_print_call_pt ppf (name, pos) = 
  let name = string_of_t (I.pp_print_ident true) name in
  Format.fprintf ppf "%s%a"
    name
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
let rec interleave = function 
  | (l, []) | ([], l) -> l 
  | (x::xs, y::ys) -> x::y::(interleave (xs,ys))
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

let req_modes_to_stream_strings
    (modes : (string * Type.t * Model.value list) list)
  : string list list =
  let strip_requires = function 
  | s ->
    let len = String.length s in
    String.sub s 0 (len - 9) 
  in
 let list_with_none = List.map 
 (fun (name, _, trace) -> List.map
 (fun v -> if Model.equal_value
   (Model.Term (Term.mk_true ())) v then Some (strip_requires name) else None) trace) modes in

 List.map (List.filter_map Fun.id) (transpose list_with_none) |> transpose

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
let pp_print_modes_section_pt full_contract ident_width val_width mode_ident ppf = function 
| (req_modes, ensured_modes, assumed, guaranteed) ->
  if full_contract then

  let transform_to_valid_format = function 
    | trace -> (List.map 
      (function (name, stream_type, mode_trace) -> 
        (name, stream_type, List.map (function (tr_val) -> 
          (Some tr_val)) mode_trace) ) trace) 
  in
  let modes = interleave (req_modes,ensured_modes) in
  Format.fprintf 
    ppf 
    "%a%a%a"
    (pp_print_stream_section_pt ident_width val_width "Assumptions") (transform_to_valid_format assumed)
    (pp_print_stream_section_pt ident_width val_width "Guarantees") (transform_to_valid_format guaranteed)
    (pp_print_stream_section_pt ident_width val_width "Modes") (transform_to_valid_format modes)
  else 
    let active_modes = req_modes_to_stream_strings req_modes in
    Format.fprintf
      ppf
      "== @{<b>%s@} ==@,\
       %a@,"
      mode_ident
      (* (List.length active_modes) *)
      (pp_print_list (pp_print_stream_string_pt ident_width val_width "") "@,") 
      active_modes

(* Filter local variables on visibility *)
let filter_locals is_visible locals =
  let locals = List.map D.bindings locals |> List.flatten in
  List.fold_left (fun acc (i, sv) ->
      match is_visible sv with
      | true -> (i, sv) :: acc
      | false -> acc
    ) [] locals

let rec get_widths_for_contract ident_width values_width contract_trace = match contract_trace with
  | (a,_,_) :: trace_tail -> get_widths_for_contract (max ident_width (String.length a)) (max values_width (5)) trace_tail
  | [] -> (ident_width, values_width)

(* Strip a list prefix from an index; returns None if prefix doesn't match. *)
let strip_index_prefix prefix index =
  let rec go = function
    | [], rest -> Some rest
    | _ :: _, [] -> None
    | p :: ps, h :: hs when p = h -> go (ps, hs)
    | _ -> None
  in
  go (prefix, index)


(* Reconstruct a plain ADT payload field value from a flat list of
   (remaining_index, state_var) pairs, where the common field prefix has already been
   stripped.  Handles scalars and arrays (reusing pp_print_value for array formatting).
   Records and tuples are not natively printed and return "_" since those types are
   flattened in the Kind 2 model. *)
let reconstruct_compound_at_step model sub_bindings step =
  match sub_bindings with
  | [] -> "_"
  | [([], sv)] ->
    (match SVT.find_opt model sv with
    | None -> "_"
    | Some vals ->
      match List.nth_opt vals step with
      | None -> "_"
      | Some v ->
        let ty = StateVar.type_of_state_var sv in
        string_of_t (pp_print_value ~as_type:ty) v)
  | ([D.ArrayVarIndex _], sv) :: _ | ([D.ArrayIntIndex _], sv) :: _ ->
    (* Array stored as a single sv; reuse existing pp_print_value which dispatches
       to pp_print_map_as_array for Map-valued (array) state variables. *)
    (match SVT.find_opt model sv with
    | None -> "_"
    | Some vals ->
      match List.nth_opt vals step with
      | None -> "_"
      | Some v ->
        let ty = StateVar.type_of_state_var sv in
        string_of_t (pp_print_value ~as_type:ty) v)
  | _ -> "_"

(* Reconstruct the ADT value string for a known disc_sv at a given step.
   root_index is [] for top-level variables and [AdtPayloadIndex ...] for nested ADT fields.
   For nested ADT fields, the nested disc sv is located via bindings using the
   field_index prefix, which makes lookups unambiguous within a single variable's D.t. *)
let rec reconstruct_adt_at_step model bindings adt_map step root_index type_name disc_sv =
  match G.HStringMap.find_opt type_name adt_map with
  | None -> assert false
  | Some adt_info ->
    let disc_type = StateVar.type_of_state_var disc_sv in
    let disc_vals = try SVT.find model disc_sv with Not_found -> assert false in
    (match List.nth_opt disc_vals step with
    | None -> assert false
    | Some (Model.Term t) when Type.is_enum disc_type ->
      let ctor_name = Term.numeral_of_term t |> Type.get_constr_of_num in
      let ctor_hs = HString.mk_hstring ctor_name in
      let fields =
        match G.HStringMap.find_opt ctor_hs adt_info.G.ctor_fields with
        | None -> assert false | Some fs -> fs
      in
      if fields = [] then ctor_name
      else
        let field_strs = List.mapi (fun j (_fname, field_kind) ->
          let field_index =
            root_index @ [D.AdtPayloadIndex (ctor_name, j)]
          in
          match field_kind with
          | G.AdtFieldNested nested_type ->
            (* For nested ADT, look up disc sv by index; the field_index prefix
               makes this unambiguous even in a flat bindings list. *)
            let nested_disc_index =
              field_index @ [D.AdtTagIndex (HString.string_of_hstring nested_type)]
            in
            (match List.assoc_opt nested_disc_index bindings with
            | None -> assert false
            | Some nested_disc_sv ->
              reconstruct_adt_at_step model bindings adt_map step
                field_index nested_type nested_disc_sv)
          | G.AdtFieldPlain ->
            (match List.assoc_opt field_index bindings with
            | Some psv ->
              (match SVT.find_opt model psv with
              | None -> "_"
              | Some pvals ->
                match List.nth_opt pvals step with
                | None -> "_"
                | Some pv ->
                  let pty = StateVar.type_of_state_var psv in
                  string_of_t (pp_print_value ~as_type:pty) pv)
            | None ->
              (* Compound field: look for sub-bindings with field_index as prefix *)
              let sub_bindings = List.filter_map (fun (idx, sv) ->
                match strip_index_prefix field_index idx with
                | Some (_ :: _ as rest) -> Some (rest, sv)
                | _ -> None
              ) bindings in
              reconstruct_compound_at_step model sub_bindings step)
        ) fields in
        ctor_name ^ "(" ^ String.concat ", " field_strs ^ ")"
    | _ -> assert false)

(* Reconstruct original ADT constructor values from hidden disc+payload fields.
   Returns one adt_stream per top-level ADT variable; nested ADT fields are
   embedded in the parent's value string rather than returned separately. *)
let adt_streams_from_bindings (adt_map : G.adt_map) model node bindings =
  if G.HStringMap.is_empty adt_map then []
  else
    (* Collect top-level disc svs: Generated (Discriminant type_name) whose root_index
       contains no AdtPayloadIndex/AdtTagIndex (i.e., not nested inside a payload). *)
    let disc_entries = List.filter_map (fun (index, sv) ->
      match N.get_state_var_source node sv with
      | N.Generated (N.Discriminant type_name) ->
        let root_index = match List.rev index with _ :: rest -> List.rev rest | [] -> [] in
        let is_top_level = not (List.exists (function
          | D.AdtPayloadIndex _ | D.AdtTagIndex _ -> true | _ -> false) root_index)
        in
        if is_top_level then Some (index, sv, type_name, root_index)
        else None
      | _ -> None
      (* A state var with no recorded source is not a discriminant; skip it. *)
      | exception Not_found -> None
    ) bindings in
    List.filter_map (fun (_disc_index, disc_sv, type_name, root_index) ->
      (* Derive the user-visible stream name by stripping ".disc_field" from
         the state var name (which bakes the full index path into its name). *)
      let sv_name = StateVar.name_of_state_var disc_sv in
      let root_name =
        match G.HStringMap.find_opt type_name adt_map with
        | None -> assert false
        | Some adt_info ->
          let disc_suffix = "." ^ HString.string_of_hstring adt_info.G.disc_field in
          let n = String.length sv_name and m = String.length disc_suffix in
          if n > m && String.sub sv_name (n - m) m = disc_suffix
          then String.sub sv_name 0 (n - m)
          else assert false
      in
      let disc_sv_values =
        try SVT.find model disc_sv with Not_found -> []
      in
      let n_steps = List.length disc_sv_values in
      let step_strings = List.init n_steps (fun step ->
        reconstruct_adt_at_step model bindings adt_map step root_index type_name disc_sv
      ) in
      if step_strings = [] then None
      else Some (root_name, step_strings)
    ) disc_entries

(* Print a section combining regular streams and ADT-reconstructed string streams.
   Both kinds are printed together under a single section header. *)
let pp_print_mixed_section_pt ident_width val_width sect ppf (streams, adt_streams) =
  let val_width = List.fold_left (fun w (_, vals) ->
    List.fold_left (fun w s -> max w (String.length s)) w vals
  ) val_width adt_streams in
  let pp_adt_stream ppf (name, vals) =
    Format.fprintf ppf "@[<hov %d>@{<blue_b>%-*s@} %a@]"
      (ident_width + 1) ident_width name
      (pp_print_list (fun ppf s -> Format.fprintf ppf "%*s" val_width s) "@ ") vals
  in
  match streams, adt_streams with
  | [], [] -> ()
  | _ ->
    Format.fprintf ppf "== @{<b>%s@} ==@," sect;
    (match streams with [] -> ()
    | _ -> Format.fprintf ppf "%a@," (pp_print_list (pp_print_stream_pt ident_width val_width) "@,") streams);
    (match adt_streams with [] -> ()
    | _ -> Format.fprintf ppf "%a@," (pp_print_list pp_adt_stream "@,") adt_streams)

  (* Output sequences of values for each stream of the nodes in the list
   and for all its called nodes *)
let rec pp_print_lustre_path_pt' ?(full_contract=false) is_top const_map const_funcs globals ppf = function

(* All nodes printed *)
| [] -> ()

(* Take first node to print *)
| (
   trace, Node (
    { N.node_id; N.inputs; N.outputs; N.locals } as node,
    model, required_modes, ensured_modes, contract_assumptions, contract_guarantees, call_conds, subnodes
  )
) :: tl when N.node_is_visible node ->

  (* Functions derived from constants are printed along with the global constants. 
     Type ascriptions not shown. *)
  if NI.get_node_type node_id = FreeConstant || NI.get_node_type node_id = TypeAscription || NI.get_node_type node_id = ClockedExpr then
    pp_print_lustre_path_pt' false const_map const_funcs globals ppf tl
  else 

  let is_visible = N.state_var_is_visible node in

  let node_name = NI.get_user_name node_id |> HString.string_of_hstring in
  let title =
    if N.is_function node then "Function"
    else match (NI.get_node_type node_id) with 
    | Environment -> "Environment of"
    | Contract -> "Contract of"
    | Type -> "Type"
    | Component -> "Node"
    | Any -> "'Any' operator"
    | DefinedConstant -> "Global constant"
    | FreeConstant -> "Global constant"
    | Choose -> "'Choose' operator"
    | ClockedExpr -> "clocked expression"
    | TypeAscription -> "Type ascription operator"
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
  (* let _ (* ident_witdth *), val_width, modes = match active_modes with
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
  in *)

  (* Filter locals to for visible state variables only and return
     as a list 

     The list of locals is the reversed from the original input in the node,
     with fold_left in filter_locals here we get it in the
     original order again. *)
  let locals = filter_locals is_visible locals in
  
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

  let global_const_svs = if is_top then get_constants const_map [] else [] in

  let scope = LustreNode.scope_of_node node in
  let constants = get_constants const_map scope in

  let ident_width, val_width, globals' =
    global_const_svs |> streams_to_values model ident_width val_width []
  in

  let ident_width, val_width, constants' =
    constants |> streams_to_values model ident_width val_width []
  in

  (* Compute ADT-reconstructed streams from hidden disc/payload fields *)
  let adt_map = globals.G.adt_map in
  let all_input_bindings = D.bindings inputs in
  let all_output_bindings = D.bindings outputs in
  let adt_inputs = adt_streams_from_bindings adt_map model node all_input_bindings in
  let adt_outputs = adt_streams_from_bindings adt_map model node all_output_bindings in
  (* Each local is its own D.t with unqualified indices: process per-variable to avoid
     index collisions when multiple locals share the same ADT type. *)
  let adt_locals =
    List.concat_map (fun local_var ->
      adt_streams_from_bindings adt_map model node (D.bindings local_var)
    ) node.N.locals
  in

  (* Sample inputs, outputs and locals on clock *)
  let globals', constants', inputs', outputs', ghosts', locals'  = match clock with
    | None -> 
      (if is_top then globals' @ const_funcs else []), 
      constants', inputs', outputs', ghosts', locals'
    | Some c ->
      (if is_top then (sample_streams_on_clock c globals') @ (sample_streams_on_clock c const_funcs) else []),
      sample_streams_on_clock c constants',
      sample_streams_on_clock c inputs',
      sample_streams_on_clock c outputs',
      sample_streams_on_clock c ghosts',
      sample_streams_on_clock c locals'
  in
  let modes_stream = interleave (required_modes, ensured_modes) in
  let contract_info =  (required_modes, ensured_modes ,contract_assumptions, contract_guarantees) in
  let ident_width, val_width = if full_contract then 
    get_widths_for_contract ident_width val_width (modes_stream @ contract_assumptions @ contract_guarantees) 
    else ident_width, val_width in
  (* Pretty-print this node or function. *)
  Format.fprintf ppf "@[<v>\
      @{<b>%s@} @{<blue>%s@} (%a)@,  @[<v>\
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
    node_name
    (pp_print_list pp_print_call_pt " / ") 
    (List.rev trace)
    (pp_print_modes_section_pt full_contract ident_width val_width mode_ident) contract_info
    (pp_print_stream_section_pt ident_width val_width "Global Constants") globals'
    (pp_print_stream_section_pt ident_width val_width "Constants") constants'
    (pp_print_mixed_section_pt ident_width val_width "Inputs") (inputs', adt_inputs)
    (pp_print_mixed_section_pt ident_width val_width "Outputs") (outputs', adt_outputs)
    (pp_print_stream_section_pt ident_width val_width "Ghosts") ghosts'
    (pp_print_mixed_section_pt ident_width val_width "Locals") (locals', adt_locals);

  (* Recurse depth-first to print subnodes *)
  pp_print_lustre_path_pt'
    false
    const_map
    const_funcs
    globals
    ppf
    (subnodes @ tl)

| _ :: tl ->

  pp_print_lustre_path_pt' false const_map const_funcs globals ppf tl

let get_const_func_info n = 
  let rec get_const_funcs (Node (top, path, _, _, _, _, _, subnodes)) = 
    let recursive_results = List.concat_map get_const_funcs (List.map snd subnodes) in
    if NI.get_node_type top.LustreNode.node_id = FreeConstant then 
      (top, path) :: recursive_results 
    else 
      recursive_results 
  in
  let const_funcs = get_const_funcs n in 
  let const_funcs = List.map (fun ({ LustreNode.node_id; outputs; }, path) -> 
    let str_name = node_id |> NI.get_name |> HString.string_of_hstring in 
    let output = List.hd (D.values outputs) in
    let () = StateVar.set_const true output in
    let vals = SVT.find path output |> List.map Option.some in
    let ty = StateVar.type_of_state_var output in
    str_name, ty, vals, output
  ) const_funcs in
  (* Filter duplicates *)
  List.fold_left (fun acc ((id, _, _, _) as info) -> 
    if List.exists (fun (id2, _, _, _) -> String.equal id id2) acc then 
      acc 
    else 
      info :: acc
  ) [] const_funcs



(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_pt ?(full_contract = false) globals ppf (lustre_path, const_map) =
  (* Collect information on functions derived from global constants *)
  let const_funcs = get_const_func_info (snd lustre_path) in
  let const_funcs = List.map (fun (id, ty, vals, _) -> id, ty, vals) const_funcs in

  (* Delegate to recursive function *)
  pp_print_lustre_path_pt' ~full_contract true const_map const_funcs globals ppf [lustre_path]


(* Output a hierarchical model as plain text *)
let pp_print_path_pt
  ?(full_contract = false) trans_sys globals subsystems first_is_init ppf model
  =
  (* Create the hierarchical model *)
  node_path_of_subsystems
    globals first_is_init trans_sys model subsystems
  (* Output as plain text *)
  |> pp_print_lustre_path_pt ~full_contract:full_contract globals ppf


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
    | Type.IntRange (i, j) ->
      let pp_print_bound_opt attr bound ppf =
        match bound with
        | None -> ()
        | Some x ->
          Format.fprintf ppf " %s=\"%a\""
            attr Numeral.pp_print_numeral x
      in
      Format.fprintf ppf "type=\"subrange\"%t%t"
        (pp_print_bound_opt "min" i) (pp_print_bound_opt "max" j)
    | Type.Real ->
      Format.pp_print_string ppf "type=\"real\""
    | Type.Abstr s ->
      Format.pp_print_string ppf s
    | Type.Enum _ ->
      let pp_print_enum_name ppf =
          Format.fprintf ppf "enumName=\"%s\" " (Type.name_of_enum stream_type)
      in
      Format.fprintf ppf "type=\"enum\"@ %tvalues=\"%a\""
        pp_print_enum_name (pp_print_list Format.pp_print_string ", ")
        (Type.constructors_of_enum stream_type)
    | Type.Array (_, _) ->
      Format.pp_print_string ppf "type=\"array\""
  in

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

let pp_print_contract_var ppf (vname, ty, values) =
  Format.fprintf 
    ppf
    "@,@[<hv 2>@[<hv 1><Stream@ name=\"%s\" type=\"bool\" class=\"ghost\">@]\
     %a@]@,</Stream>"
    vname
    (pp_print_stream_values None ty) values  


let pp_print_contract_section_xml ctype ppf items =
  match items with 
  | [] -> ()
  | _ -> 
    Format.fprintf ppf
      "@,@[<hv 0>@[<hv 1><Contract@ name=\"%s\">@]@,\
        @[<hv 3>%a@]@,</Contract>@]"
      ctype
      (pp_print_list pp_print_contract_var "") items

(* Output a list of node models. *)
let rec pp_print_lustre_path_xml' is_top const_map const_funcs ppf = function 

  | [] -> ()

  | (
    trace, Node (
      { N.node_id; N.inputs; N.outputs; N.locals } as node,
      model, required_modes, ensured_modes, contract_assumptions, contract_guarantees , call_conds, subnodes
    )
  ) :: tl when N.node_is_visible node ->

    (* Functions derived from constants are printed along with the global constants. 
       Type ascriptions not shown. *)
    if NI.get_node_type node_id = FreeConstant || NI.get_node_type node_id = TypeAscription || NI.get_node_type node_id = ClockedExpr then 
      pp_print_lustre_path_xml' false const_map const_funcs ppf tl 
    else

    let is_visible = N.state_var_is_visible node in
  
    let name = NI.get_user_name node_id |> HString.string_of_hstring in

    let title =
      if N.is_function node then "Function"
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
       with fold_left in filter_locals here we get it in the
       original order again. *)
    let locals' = filter_locals is_visible locals in

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

    let globals' = 
      if is_top then (get_constants const_map [] @ const_funcs) else [] 
    in

    let contract_modes = interleave (required_modes, ensured_modes) in
    let constants' =
      let scope = LustreNode.scope_of_node node in
      get_constants const_map scope
    in

    (* Pretty-print this node *)
    Format.fprintf ppf "@,@[<hv 2>@[<hv 1><%s@ name=\"%s\"%a>@]"
      title
      name
      pp_print_call_xml trace;
    (pp_print_contract_section_xml "Assumptions" ppf contract_assumptions) ;
    (pp_print_contract_section_xml "Guarantees" ppf contract_guarantees) ;
    (pp_print_contract_section_xml "Modes" ppf contract_modes) ;
    List.iter (pp_print_stream_xml node model clock ppf) globals';
    List.iter (pp_print_stream_xml node model clock ppf) constants';
    List.iter (pp_print_stream_xml node model clock ppf) inputs';
    List.iter (pp_print_stream_xml node model clock ppf) outputs';
    List.iter (pp_print_stream_xml node model clock ppf) ghosts';
    List.iter (pp_print_stream_xml node model clock ppf) locals';
    pp_print_lustre_path_xml' false const_map const_funcs ppf subnodes;
    Format.fprintf ppf "@]@,</%s>" title;

    (* Continue *)
    pp_print_lustre_path_xml' false const_map const_funcs ppf tl

  | _ :: tl ->
    
    (* Continue *)
    pp_print_lustre_path_xml' false const_map const_funcs ppf tl

(* const_funcs need extra processing for xml and json *)
let process_const_funcs const_funcs path = 
(* Need to update model in path to include the constant. *)
  let _, Node (_, model, _, _, _, _, _, _) = path in
  List.iter (fun (_, _, vals, sv) -> 
    SVT.add model sv (List.map Option.get vals)
  ) const_funcs;  
  List.map (fun (_, _, _, sv) -> [], sv) const_funcs 

(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_xml ppf (path, const_map) = 
  let const_funcs = get_const_func_info (snd path) in
  let const_funcs = process_const_funcs const_funcs path in

  (* Delegate to recursive function *)
  pp_print_lustre_path_xml' true const_map const_funcs ppf [path]


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
  
  (* | N.Generated -> Format.fprintf ppf "\"class\" : \"kind_2_generated_WIP\",@," *)
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


(* Pair each value with its step index, filtering to clock-active steps only.
   When clock is None all steps are included. *)
let clock_filter clock values =
  match clock with
  | None -> List.mapi (fun i v -> (i, v)) values
  | Some c ->
    List.combine values c
    |> List.mapi (fun i (v, ck) -> (i, v, ck))
    |> List.filter_map (fun (i, v, ck) -> if ck then Some (i, v) else None)

let pp_print_stream_values_json clock ty ppf l =
  match clock_filter clock l with
  | [] -> pp_print_listi (fun ppf i -> pp_print_stream_value_json ty ppf i) "," ppf []
  | values_on_clock ->
    pp_print_list (fun ppf (i, v) -> pp_print_stream_value_json ty ppf i v) "," ppf values_on_clock


let rec pp_print_type_json ?state_var ?model field ppf stream_type =
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
  | Type.IntRange (i, j) -> (
    Format.fprintf ppf
        "\"%s\" : \"subrange\",@,\
         \"%sInfo\" :@,{@[<v 1>@,\
         %t\
         @]@,},@,\
        "
        field field
        (fun ppf ->
          match i, j with
          | Some i, Some j ->
            Format.fprintf ppf "\"min\" : %a,@,\"max\" : %a"
              Numeral.pp_print_numeral i Numeral.pp_print_numeral j
          | Some i, None ->
            Format.fprintf ppf "\"min\" : %a"
              Numeral.pp_print_numeral i
          | None, Some j ->
            Format.fprintf ppf "\"max\" : %a"
              Numeral.pp_print_numeral j
          | None, None -> ()
        )
  )
  | Type.Enum (_, _) -> (
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
      match state_var, model with
      | Some sv, Some m when SVT.mem m sv ->
        let stream_values = SVT.find m sv in
        (match stream_values with
        | Model.Map map :: _ ->
          Model.dimension_of_map map |> List.map string_of_int
        | _ -> 
          Type.all_index_types_of_array stream_type |>
          List.map Type.node_of_type |>
          List.map (function
            | Type.IntRange (_, Some j) ->
              Numeral.string_of_numeral j
            | _ -> assert false
          )
        )
      | _ ->
        Type.all_index_types_of_array stream_type |>
        List.map Type.node_of_type |>
        List.map (function
          | Type.IntRange (_, Some j) ->
            Numeral.string_of_numeral j
          | _ -> assert false
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

let pp_print_section_json sect ppf mode_traces  =
  match mode_traces with 
  | [] -> ()
  | _ -> 
    Format.fprintf ppf ",@,\"%s\" :@,[@[<v 1>%a@]@,]"
      sect
      (pp_print_list
        (fun ppf (name, stream_type, values) ->
            Format.fprintf ppf
              "@,{@[<v 1>@,\
                \"name\" : \"%s\",@,\
                %a\
                \"instantValues\" :%t\
              @]@,}"
              name
              (pp_print_type_json "type") stream_type
              (fun ppf ->
                if values = [] then
                  Format.fprintf ppf " []"
                else
                  Format.fprintf ppf "@,[@[<v 1>%a@]@,]"
                    (pp_print_stream_values_json None stream_type) values
              )
        )
        ",")
      mode_traces
    
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
      (pp_print_type_json ~state_var ~model "type") stream_type
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

(* Print one reconstructed ADT stream as a JSON stream object. *)
let pp_adt_stream_json clock class_str ppf (name, step_strings) =
  let values = clock_filter clock step_strings in
  Format.fprintf ppf
    "@,{@[<v 1>@,\"name\" : \"%s\",@,\"type\" : \"adt\",@,\"class\" : \"%s\",@,\
     \"instantValues\" :%t@]@,}"
    name class_str
    (fun ppf ->
      if values = [] then Format.fprintf ppf " []"
      else
        Format.fprintf ppf "@,[@[<v 1>%a@]@,]"
          (pp_print_list (fun ppf (step, s) ->
            Format.fprintf ppf "@,[%d, \"%s\"]" step s) ",") values)

let pp_print_streams_json node model clock adt_tagged ppf regular =
  let all_printers =
    List.map (fun s ppf -> pp_print_stream_json node model clock ppf s) regular
    @ List.map (fun (class_str, adt_s) ppf -> pp_adt_stream_json clock class_str ppf adt_s) adt_tagged
  in
  match all_printers with
  | [] -> ()
  | _ ->
    Format.fprintf ppf ",@,\"streams\" :@,[@[<v 1>%a@]@,]"
      (pp_print_list (fun ppf f -> f ppf) ",") all_printers

let pp_print_streams_json is_top const_map const_funcs globals ppf
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
     with fold_left in partition_locals here we get it in the
     original order again. *)
  let locals' = filter_locals is_visible locals in

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

  let globals' = 
    if is_top then (get_constants const_map [] @ const_funcs) else [] 
  in

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

  let adt_map = globals.G.adt_map in
  let adt_inputs = adt_streams_from_bindings adt_map model node (D.bindings inputs) in
  let adt_outputs = adt_streams_from_bindings adt_map model node (D.bindings outputs) in
  let adt_locals =
    List.concat_map (fun local_var ->
      adt_streams_from_bindings adt_map model node (D.bindings local_var)
    ) node.N.locals
  in
  let adt_tagged =
    List.map (fun s -> ("input", s)) adt_inputs
    @ List.map (fun s -> ("output", s)) adt_outputs
    @ List.map (fun s -> ("local", s)) adt_locals
  in

  Format.fprintf ppf "%a"
    (pp_print_streams_json node model clock adt_tagged) streams


let pp_print_var_json_testgen ppf ((name, var_type), value) =
  Format.fprintf ppf
    "@[<h>\"%s\": %a@]"
    name
    (Model.pp_print_value_json ~as_type:var_type) value


let pp_print_instance_testgen names_types ppf values =
  (* values is one time-step worth of values, i.e. a list of Model.value *)
  Format.fprintf ppf
    "@[<v 1>{@,%a@,}@]"
    (pp_print_list (pp_print_var_json_testgen) ",@,")
    (List.combine names_types values)


let pp_print_streams_json_testgen ppf
  ({N.inputs} as node, model, _) =

  let is_visible = N.state_var_is_visible node in

  let pop_head_index = function
    | ([], sv) -> ([], sv)
    | (_ :: tl, sv) -> (tl, sv)
  in

  let inputs' =
    D.bindings inputs
    |> List.filter (fun (_, sv) -> is_visible sv)
    |> List.map pop_head_index
  in

  let streams =
    []
    |> List.rev_append inputs'
    |> List.rev
  in

  

  let streams_with_values =
    streams
    |> List.map (fun (_, sv) -> SVT.find model sv)
    |> transpose
  in

  let stream_names_types =
    streams
    |> List.map (fun (_, sv) ->
          (StateVar.name_of_state_var sv, StateVar.type_of_state_var sv))
  in

  Format.fprintf ppf
    "@[<v 1>%a@]"
    (pp_print_list (pp_print_instance_testgen stream_names_types) ",@,")
    streams_with_values

(* Output a list of node models. *)
let rec pp_print_lustre_path_json' is_top const_map const_funcs globals ppf = function

  | [] -> ()

  | (
    trace, Node ({ N.node_id } as node,
      model, required_modes, ensured_modes, contract_assumptions, contract_guarantees, call_conds, subnodes
    )
  ) :: tl when N.node_is_visible node ->

    (* Functions derived from constants are printed along with the global constants. 
       Type ascriptions not shown. *)
    if NI.get_node_type node_id = FreeConstant || NI.get_node_type node_id = TypeAscription || NI.get_node_type node_id = ClockedExpr then
      pp_print_lustre_path_json' false const_map const_funcs globals ppf tl
    else

    let name = NI.get_user_name node_id |> HString.string_of_hstring in

    let title =
      if N.is_function node then "function"
      else "node"
    in

    let pp_print_subnodes_json ppf = function
      | [] -> ()
      | subnodes ->
          Format.fprintf ppf ",@,\"subnodes\" :@,[@[<v 1>%a@]@,]"
            (pp_print_lustre_path_json' false const_map const_funcs globals) subnodes
    in

    let comma = if tl <> [] then "," else "" in

    (* Pretty-print this node *)
    (* Format.fprintf ppf
       "@,{@[<v 1>@,\
        \"blockType\" : \"%s\",@,\
        \"name\" : \"%s\"\
        %a%a%a%a%a\
        @]@,}%s\
       " *)
         Format.fprintf ppf
       "@,{@[<v 1>@,\
        \"blockType\" : \"%s\",@,\
        \"name\" : \"%s\"\
        %a%a%a%a%a%a\
        @]@,}%s\
       "
       title 
       name
       pp_print_call_json trace
       (pp_print_section_json "assumptionsTrace") contract_assumptions
       (pp_print_section_json "guaranteesTrace") contract_guarantees
       (pp_print_section_json "modesTrace") (interleave (required_modes,ensured_modes))
       (pp_print_streams_json is_top const_map const_funcs globals) (node, model, call_conds)
       pp_print_subnodes_json subnodes
       comma;

    (* Continue *)
    pp_print_lustre_path_json' false const_map const_funcs globals ppf tl

  | _ :: tl ->

    (* Continue *)
    pp_print_lustre_path_json' false const_map const_funcs globals ppf tl


(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_json globals ppf (path, const_map) =
  let const_funcs = get_const_func_info (snd path) in
  let const_funcs = process_const_funcs const_funcs path in

  (* Delegate to recursive function *)
  Format.fprintf ppf "@,[@[<v 1>%a@]@,]"
    (pp_print_lustre_path_json' true const_map const_funcs globals) [path]


(* Output a hierarchical model as JSON *)
let pp_print_path_json
  trans_sys globals subsystems first_is_init ppf model
=
  (* Create the hierarchical model *)
  node_path_of_subsystems
    globals first_is_init trans_sys model subsystems
  (* Output as JSON *)
  |> pp_print_lustre_path_json globals ppf



let rec pp_print_lustre_path_json_testgen' const_map const_funcs ppf = function
  | [] -> ()
  | (
    _, Node (node,
      model, _, _, _, _, call_conds, _
    )
  ) :: tl when N.node_is_visible node ->
      Format.fprintf ppf
       "@[<v 1>@,\
        %a\
        @]@,\
       "
       (pp_print_streams_json_testgen) (node, model, call_conds)
       ;

    (* Continue *)
    pp_print_lustre_path_json_testgen' const_map const_funcs ppf tl

  | _ :: tl ->
    (* Continue *)
    pp_print_lustre_path_json_testgen' const_map const_funcs ppf tl


let pp_print_lustre_path_json_testgen ppf (path, const_map) =
  let const_funcs = get_const_func_info (snd path) in
  let const_funcs = process_const_funcs const_funcs path in

  (* Delegate to recursive function *)
  Format.fprintf ppf "[@[<v 1>%a@]]"
    (pp_print_lustre_path_json_testgen' const_map const_funcs) [path]

let pp_print_path_json_testgen
  trans_sys globals subsystems first_is_init ppf model
=

  (* Create the hierarchical model *)
  node_path_of_subsystems
    globals first_is_init trans_sys model subsystems
  (* Output as JSON *)
  |> pp_print_lustre_path_json_testgen ppf

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
| (_, Node ( { N.inputs }, model,_,_,_,_, _, _ )), _ ->

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

  let main_nodes = LustreNode.get_main_annotated_nodes nodes in

  let rec fold parents node =

    List.iter
      (fun ({ N.call_node_id = node_id;
             call_pos = pos; call_cond = cond;
             call_inputs = inputs; call_defaults = defs } as call) -> 

        (* Format.eprintf "register : %a at %a %s \n ARgs: (%a)@." *)
        (*   (LustreIdent.pp_print_ident false) name Lib.pp_print_position pos *)
        (*   (match clock with *)
        (*    | None -> "" *)
        (*    | Some c -> "ON "^ (StateVar.string_of_state_var c)) *)
        (*   (pp_print_list StateVar.pp_print_state_var ", ") inputs *)
        (* ; *)
        
        let name = NI.get_internal_name node_id |> I.of_hstring in
        register_callpos_for_nb
          abstr_map hc name parents pos cond (inputs, defs);

        fold (call :: parents) (LustreNode.node_of_node_id node_id nodes)

      ) node.LustreNode.calls
  in

  List.iter (fun main_node_id -> 
      let main_node = LustreNode.node_of_node_id main_node_id nodes in
      fold [] main_node)
    main_nodes;

  hc

exception Found of int * N.call_cond list

let get_pos_number hc lid pos =

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
