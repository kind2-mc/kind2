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
module A = LustreAst
module E = LustreExpr
module N = LustreNode
module F = LustreFunction
module S = SubSystem
module T = TransSys
module C = LustreContract

module SVT = StateVar.StateVarHashtbl
module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet


(* Model for a node and its subnodes *)
type t =
  | Function of F.t * Model.path
  | Node of
    N.t * Model.path * C.mode list list option * ((I.t * position) list * t) list


(* ********************************************************************** *)
(* Reconstruct a model for a node hierarchy                               *)
(* ********************************************************************** *)

(* Map a state variable to its instance in the top system *)
let map_top instances state_var =

  List.fold_left 
    (fun state_var (_, { T.map_up }) -> SVM.find state_var map_up)
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
let map_top_and_add instances model model' _ state_var = 

  try 

    (* Find state variable instance in top node *)
    let state_var' = map_top instances state_var in

    (* Get path of top node state variable *)
    SVT.find model state_var'

    (* Add as path of subnode state variable *)
    |> SVT.add model' state_var

  (* Fail if state variable is not in the top node *)
  with Not_found ->

    raise Not_found


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
      equations |> List.fold_left (fun subst (sv, _, _) ->
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

        List.find
          (function 

            (* Equation is for state variable? *)
            | (sv, [], def) -> StateVar.equal_state_vars sv state_var

            (* Fail if state variable has indexes *)
            | _ -> assert false)
          equations

        (* Return expression on right-hand side of equation *)
        |> (function (_, _, e) -> e)

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
            m

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


(* Reconstruct a model for a function call given the models for the
   subnodes. *)
let function_path_of_instance
  first_is_init
  trace
  globals
  model_top
  ({ N.name } as node)
  { N.call_pos; N.call_function_name; N.call_inputs; N.call_outputs }
  trans_sys
  instances
  subnodes
=

  (* Format.printf "function_path_of_instance@.@." ; *)

  let model = Model.create_path (
      D.cardinal call_inputs + D.cardinal call_outputs
    )
  in

  (* Format.printf "model@.@." ; *)

  let { F.inputs; F.outputs } as fun_def =
    try F.function_of_name call_function_name globals.LustreGlobals.functions
    with Not_found -> assert false
  in

  (* Format.printf "fun_def@.@." ; *)

  let call_outputs = call_outputs |> D.map E.mk_var in

  (* Format.printf "call_outputs@.@." ; *)

  let zip formal actual =
    D.fold2 (fun _ f a l ->
      (f, [], a) :: l
    ) formal actual
  in

  let equations_of_init init =
    (zip inputs call_inputs [] |> zip outputs call_outputs) @ (
      N.ordered_equations_of_node
        node (TransSys.state_vars trans_sys) init
    )
  in



  inputs |> D.iter (
    map_top_reconstruct_and_add
      first_is_init
      trans_sys
      instances
      equations_of_init
      model_top
      model
  ) ;

  (* Format.printf "inputs@.@." ; *)

  outputs |> D.iter (
    map_top_reconstruct_and_add
      first_is_init
      trans_sys
      instances
      equations_of_init
      model_top
      model
  ) ;

  (* Format.printf "outputs@.@." ; *)

  (name, call_pos) :: trace, Function(fun_def, model)

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
      | Model.Lambda _ -> failwith "\
        evaluating mode requirement: value should be a term, not a lambda\
      "
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
    | { C.name ; C.requires = head :: tail } as m ->
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


(* Reconstruct model for the instance given the models for the subnodes 

   Use with [TransSys.fold_subsystem_instances]. *)
let node_path_of_instance 
    first_is_init
    globals
    model_top
    ({
      N.inputs; N.outputs; N.locals; N.equations; N.function_calls; N.contract
    } as node)
    trans_sys
    instances
    subnodes =

  (* Format.printf "node_path_of_instance@.@." ; *)

  (* Record trace of node calls *)
  let trace = 
    List.map
      (fun (t, { T.pos }) -> 
         (TransSys.scope_of_trans_sys t |> I.of_scope, pos))
      instances
  in

  (* Format.printf "trace@.@." ; *)

  let subnodes =
    function_calls |> List.fold_left (
      fun l fc -> (
        function_path_of_instance
          first_is_init
          trace
          globals
          model_top
          node
          fc
          trans_sys
          instances
          subnodes
      ) :: l
    ) subnodes
  in

  (* Format.printf "subnodes@.@." ; *)

  (* Create a path for the state variables of the node *)
  let model = 
    Model.create_path
      (D.cardinal inputs + 
       D.cardinal outputs +
       List.fold_left (fun a d -> D.cardinal d + a) 0 locals)
  in

  (* Format.printf "model@.@." ; *)

  (* Map all input state variables to the top instances and add their
     path to the model

     Inputs are always stateful, therefore there is exactly one state
     variable of the top system each input is an instance of. *)
  D.iter (map_top_and_add instances model_top model) inputs;

  (* Map all output state variables to the top instances and add their
     path to the model

     Ouputs are always stateful, therefore there is exactly one state
     variable of the top system each output is an instance of. *)
  D.iter (map_top_and_add instances model_top model) outputs;

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

  (* Return path for subnode and its call trace *)
  (trace, Node(node, model, active_modes, subnodes))


(* Return a hierarchical model for the nodes from a flat model by
   mapping the model of the top node to model of the subnode instances,
   reconstructing the streams in the original input. *)
let node_path_of_subsystems
    first_is_init
    trans_sys
    instances
    model
    ({ S.scope } as subsystems)
    globals =

  (* Format.printf "trans_sys@.@." ; *)

  (* Get transition system of top scope of subsystems *)
  let trans_sys' = 
    TransSys.find_subsystem_of_scope trans_sys scope 
  in

  (* Format.printf "nodes@.@." ; *)

  let nodes = N.nodes_of_subsystem subsystems in

  (* Format.printf "folding@.@." ; *)
  Printexc.record_backtrace true ;

  try
    (* Create models for all subnodes *)
    N.fold_node_calls_with_trans_sys
      nodes
      (node_path_of_instance first_is_init globals model)
      (N.node_of_name (I.of_scope scope) nodes)
      trans_sys'
  with e ->
    (* Get backtrace now, Printf changes it *)
    let backtrace = Printexc.get_backtrace () in

    Format.printf "Caught %s.@ Backtrace:@\n%s@.@."
      (Printexc.to_string e)
      backtrace ;
    raise e


(* *************************************************************** *)
(* Plain-text output                                               *)
(* *************************************************************** *)

(* Pretty-print a value *)
let rec pp_print_value ppf term =

  (* We expect values to be constants *)
  if Term.is_numeral term then 

    (* Pretty-print as a numeral *)
    Numeral.pp_print_numeral 
      ppf
      (Term.numeral_of_term term)

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
        
  else
    
    (* Fall back to pretty-print as a term *)
    Term.pp_print_term ppf term 


(* Output a single value of a stream at an instant

   Give [val_width] as the maximum expected width of the string
   representation of the values for correct alignment. *)
let pp_print_stream_value_pt val_width ppf = function

  (* Output a term as a value *)
  | Model.Term t -> 

    Format.fprintf 
      ppf
      "%-*s"
      val_width
      (string_of_t pp_print_value t)    

  (* TODO: output an array *)
  | Model.Lambda _ -> assert false


(* Output a file position *)
let pp_print_file_pt ppf pos_file = 

  if pos_file = "" then () else
    Format.fprintf ppf "(%s)" pos_file


(* Output a position *)
let pp_print_pos_pt ppf pos = 

  (* Do not print anything for a dummy position *)
  if is_dummy_pos pos then () else 

    (* Get file, line and column of position *)
    let pos_file, pos_lnum, pos_cnum = 
      file_row_col_of_pos pos
    in
    
    (* Print attributes *)
    Format.fprintf 
      ppf
      "[%al%dc%d]"
      pp_print_file_pt pos_file
      pos_lnum
      pos_cnum


(* Output the identifier of an indexed stream *)
let pp_print_stream_ident_pt ppf (index, state_var) =

  Format.fprintf
    ppf
    "%a%a"
    (E.pp_print_lustre_var false) state_var
    (D.pp_print_index false) index


(* Output the the calling node and the position of the call *)
let pp_print_call_pt ppf (name, pos) = 
 
  Format.fprintf
    ppf
    "%a%a"
    (I.pp_print_ident false) name
    pp_print_pos_pt pos


(* Convert values to strings and update maximal lengths *)
let rec values_to_strings val_width values = function

  (* All values consumed, return in original order *)
  | [] -> (val_width, List.rev values)

  (* Output a term as a value *)
  | Model.Term t :: tl -> 

    (* Convert value to string *)
    let value_string = string_of_t pp_print_value t in

    (* Keep track of maximum width of values *)
    let val_width = 
      max val_width (String.length value_string)
    in

    (* Add string representation of value and continue with remaining
       values *)
    values_to_strings 
      val_width
      (value_string :: values)
      tl 

  (* TODO: output an array *)
  | Model.Lambda _ :: _ -> assert false

  
(* Convert identifiers and values of streams to strings and update
   maximal lenght of the strings *)
let rec streams_to_strings path ident_width val_width streams = 

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

        (* Get values of stream and convert to strings, keep track of
           maximum width of values *)
        let val_width, stream_values = 
          SVT.find path state_var  
          |> values_to_strings val_width []
        in

        (* Keep track of maximum width of identifiers *)
        let ident_width = 
          max ident_width (String.length stream_name)
        in

        (* Add string representation of stream and continue with
           remaining streams *)
        streams_to_strings 
          path
          ident_width
          val_width 
          ((stream_name, stream_values) :: streams)
          tl

      (* State variable must be in the model *)
      with Not_found -> assert false


(* Output a stream value with the given width *)
let pp_print_stream_value_pt val_width ppf v =
  if not (Flags.color ()) then
    Format.fprintf ppf "%*s" val_width v
  else
    match v with
    | "false" -> Format.fprintf ppf "@{<black_b>%*s@}" val_width v
    | _ ->
      Format.fprintf ppf "%*s" val_width v
      (* maybe too crazy *)
      (* try Scanf.sscanf v "%d" (fun x -> *)
      (*     let f = Scanf.format_from_string *)
      (*         ("@{<c:" ^ string_of_int (x mod 35 + 57) ^ ">%*s@}") *)
      (*         "%*s" in *)
      (*     Format.fprintf ppf f val_width v *)
      (*   ) *)
      (* with _ -> Format.fprintf ppf "%*s" val_width v *)



(* Output a stream value with given width for the identifier and
   values *)
let pp_print_stream_pt ident_width val_width ppf (stream_name, stream_values) = 

  (* Break lines if necessary and indent correctly *)
  Format.fprintf
    ppf
    "@[<hov %d>@{<blue_b>%-*s@} %a@]"
    (ident_width + 1)
    ident_width
    stream_name
    (pp_print_list (pp_print_stream_value_pt val_width) "@ ")
    stream_values


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


(* Output sequences of values for each stream of the nodes in the list
   and for all its called nodes *)
let rec pp_print_lustre_path_pt' ppf = function

(* All nodes printed *)
| [] -> ()

(* Take first node to print *)
| (trace, t) :: tl ->

  let (
    name, inputs, outputs, locals, is_visible,
    model, active_modes, subnodes, title
  ) =
    match t with
    | Node (
      { N.name; N.inputs; N.outputs; N.locals } as node,
      model, active_modes, subnodes
    ) ->
      name, inputs, outputs, locals,
      N.state_var_is_visible node, model, active_modes, subnodes,
      "Node"
    | Function ( { F.name; F.inputs; F.outputs }, model ) ->
      name, inputs, outputs, [], (fun _ -> true), model, None, [], "Function"
  in

  (* Remove first dimension from index *)
  let pop_head_index = function 
    | ([], sv) -> ([], sv)
    | (h :: tl, sv) -> (tl, sv)
  in

  (* Reset maximum widths for this node *)
  let ident_width, val_width = 0, 0 in

  (* Remove index of position in input for printing *)
  let ident_width, val_width, inputs' = 
    D.bindings inputs
    |> List.map pop_head_index
    |> streams_to_strings model ident_width val_width []
  in

  (* Remove index of position in output for printing *)
  let ident_width, val_width, outputs' = 
    D.bindings outputs
    |> List.map pop_head_index
    |> streams_to_strings model ident_width val_width []
  in

  let mode_ident = "Mode(s)" in
  let ident_witdth, val_width, modes = match active_modes with
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

     The list of locals is the reversed from the original input in
     the node, with fold_left here we get it in the original order
     again. *)
  let ident_width, val_width, locals' = 
    locals |> List.fold_left (
      fun a d ->
        (D.filter (fun _ sv -> is_visible sv) d |> D.bindings) @ a
    ) []
    |> streams_to_strings model ident_width val_width []
  in

  (* Pretty-print this node or function. *)
  Format.fprintf ppf "@[<v>\
      @{<b>%s@} @{<blue>%a@} (%a)@,  @[<v>\
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
    (fun fmt -> function
      | None -> ()
      | Some modes ->
        modes
        |> List.map (fun vals -> ("", vals))
        |> pp_print_stream_section_pt ident_width val_width mode_ident fmt
    ) modes
    (pp_print_stream_section_pt ident_width val_width "Inputs") inputs'
    (pp_print_stream_section_pt ident_width val_width "Outputs") outputs'
    (pp_print_stream_section_pt ident_width val_width "Locals") locals';

  (* Recurse depth-first to print subnodes *)
  pp_print_lustre_path_pt' 
    ppf
    (subnodes @ tl)


(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_pt ppf lustre_path = 

  (* Delegate to recursive function *)
  pp_print_lustre_path_pt' ppf [lustre_path]


(* Output a hierarchical model as plain text *)
let pp_print_path_pt
  trans_sys instances subsystems globals first_is_init ppf model
=
  (* Create the hierarchical model *)
  node_path_of_subsystems
    first_is_init trans_sys instances model subsystems globals
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
let pp_print_stream_ident_xml ppf (index, state_var) = 

  Format.fprintf
    ppf
    "%a%a"
    (E.pp_print_lustre_var false) state_var
    (D.pp_print_index false) index



(* Pretty-print a property of a stream as XML attributes *)
let pp_print_stream_prop_xml ppf = function 

  | N.Input -> Format.fprintf ppf "@ class=\"input\""

  | N.Output -> Format.fprintf ppf "@ class=\"output\""

  | N.Local -> Format.fprintf ppf "@ class=\"local\""

  (* Any other streams should have been culled out *)
  | _ -> assert false 


(* Pretty-print a single value of a stream at an instant *)
let pp_print_stream_value ppf i = function

  | Model.Term t -> 

    Format.fprintf 
      ppf
      "@[<hv 2><Value instant=\"%d\">@,@[<hv 2>%a@]@;<0 -2></Value>@]" 
      i
      pp_print_value t    

  | Model.Lambda _ -> 

    (* TODO: output an array *)
    assert false


(* Pretty-print a single stream *)
let pp_print_stream_xml get_source model ppf (index, state_var) =

  try 

    (* Get type of identifier *)
    let stream_type = StateVar.type_of_state_var state_var in

    let stream_values = SVT.find model state_var in

    Format.fprintf 
      ppf
      "@[<hv 2>@[<hv 1><Stream@ name=\"%a\" type=\"%a\"%a>@]@,\
       %a@;<0 -2></Stream>@]"
      pp_print_stream_ident_xml (index, state_var)
      (E.pp_print_lustre_type false) stream_type
      pp_print_stream_prop_xml (get_source state_var)
      (pp_print_listi pp_print_stream_value "@,") stream_values

  with Not_found -> assert false


let pp_print_active_modes_xml ppf = function
| None | Some [] -> ()
| Some mode_trace ->
  Format.fprintf ppf
    "@[<v>%a@]@,"
    (pp_print_list
      ( fun fmt (k, tree) ->
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
let rec pp_print_lustre_path_xml' ppf = function 

  | [] -> ()

  | (trace, t) :: tl ->

    let
      name, inputs, outputs, locals, is_visible, get_source,
      model, active_modes, subnodes, title
    =
      match t with
      | Node (
        { N.name; N.inputs; N.outputs; N.locals } as node,
        model, active_modes, subnodes
      ) ->
        name, inputs, outputs, locals,
        N.state_var_is_visible node, N.get_state_var_source node,
        model, active_modes, subnodes, "Node"
      | Function ( { F.name; F.inputs; F.outputs } as f, model ) ->
        name, inputs, outputs, [],
        (fun _ -> true), F.get_state_var_source f,
        model, None, [], "Function"
    in

    (* Remove first dimension from index *)
    let pop_head_index = function 
      | ([], sv) -> ([], sv)
      | (h :: tl, sv) -> (tl, sv)
    in

    (* Remove index of position in input for printing *)
    let inputs' = 
      D.bindings inputs
      |> List.map pop_head_index
    in

    (* Remove index of position in output for printing *)
    let outputs' = 
      D.bindings outputs
      |> List.map pop_head_index
    in

    (* Filter locals to for visible state variables only and return
       as a list 

       The list of locals is the reversed from the original input in
       the node, with fold_left here we get it in the original order
       again. *)
    let locals' = 
      List.fold_left
        (fun a d -> 
           (D.filter 
              (fun _ sv -> is_visible sv)
              d
            |> D.bindings) 
           @ a)
        []
        locals
    in

    (* Pretty-print this node *)
    Format.fprintf 
      ppf
      "@[<hv 2>@[<hv 1><%s@ name=\"%a\"%a>@]@,%a%a%t%a%t%a%t%a@;<0 -2></%s>@]%t"
      title
      (I.pp_print_ident false) 
      name
      pp_print_call_xml
      trace
      pp_print_active_modes_xml active_modes
      (pp_print_list (pp_print_stream_xml get_source model) "@,") inputs'
      (fun ppf -> 
         if
           inputs' <> [] && 
           (outputs' <> [] || locals' <> [] || subnodes <> []) 
         then
           Format.fprintf ppf "@,")
      (pp_print_list (pp_print_stream_xml get_source model) "@,") outputs'
      (fun ppf -> 
         if outputs' <> [] && (locals' <> [] || subnodes <> []) then
           Format.fprintf ppf "@,")
      (pp_print_list (pp_print_stream_xml get_source model) "@,") locals'
      (fun ppf -> if locals' <> [] && subnodes <> [] 
        then Format.fprintf ppf "@,")
      pp_print_lustre_path_xml' subnodes
      title
      (fun ppf -> if tl <> [] then Format.fprintf ppf "@,");

    (* Continue *)
    pp_print_lustre_path_xml' ppf tl


(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_xml ppf path = 

  (* Delegate to recursive function *)
  pp_print_lustre_path_xml' ppf [path]


(* Ouptut a hierarchical model as XML *)
let pp_print_path_xml
  trans_sys instances subsystems globals first_is_init ppf model
=
  (* Create the hierarchical model *)
  node_path_of_subsystems
    first_is_init trans_sys instances model subsystems globals
  (* Output as XML *)
  |> pp_print_lustre_path_xml ppf


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
      (pp_print_list
        (fun fmt -> function
          | Model.Term v ->
            Format.fprintf fmt "%a" pp_print_value v
          | Model.Lambda _ ->
            failwith "error: found lambda in model value"
        ) ","
      )
      values
  with Not_found ->
    Format.asprintf
      "[LustrePath.pp_print_stream_csv] could not find state var %a"
      pp_print_stream_ident_xml (index, sv)
    |> failwith


(* Outputs a sequence of values for the inputs of a node. *)
let pp_print_lustre_path_in_csv ppf = function
| _, Function _ -> ()
| trace, Node( { N.inputs }, model, _, _ ) ->

  (* Remove first dimension from index. *)
  let pop_head_index = function
    | [], sv -> [], sv
    | h :: tl, sv -> tl, sv
  in

  (* Remove index of position in input for printing. *)
  let inputs = D.bindings inputs |> List.map pop_head_index in

  (* Print inputs in CSV. *)
  Format.fprintf ppf "@[<v>%a@]"
    (pp_print_list (pp_print_stream_csv model) "@ ") inputs

(* Outputs a model for the inputs of a system in CSV. *)
let pp_print_path_in_csv
  trans_sys instances subsystems globals first_is_init ppf model
=
  (* Create the hierarchical model. *)
  node_path_of_subsystems 
    first_is_init trans_sys instances model subsystems globals
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


let rec add_to_callpos abstr_map acc pos clock args calls =
  match calls with
  | ((pos', nb', clock', args') as x) :: r ->
    let c_pos = Lib.compare_pos pos pos' in

    if c_pos = 0 then raise Exit; (* already in there, abort *)
    
    if same_args abstr_map args args' then
      (* calls with same arguments but at different positions *)
      (* insert in between with the same number, don't shift anything *)
      if c_pos > 0 then
        List.rev_append acc (x :: (pos, nb', clock, args) :: r)
      else
        List.rev_append acc ((pos, nb', clock, args) :: calls)
          
    else if c_pos > 0 then
      (* continue to look *)
      add_to_callpos abstr_map (x :: acc) pos clock args r

    else (* c_pos < 0 *)
      (* insert in between and shift the ones on the right *)
      List.rev_append acc
        ((pos, nb', clock, args) ::
         (List.map (fun (p, n, c, a) -> (p, n+1, c, a)) calls))

  | [] ->
    (* last one or only one *)
    let nb = match acc with [] -> 0 | (_, n, _, _) :: _ -> n+1 in
    List.rev ((pos, nb, clock, args) :: acc)



let register_callpos_for_nb abstr_map hc lid parents pos clock args =
  let is_condact = clock <> None in
  let cat =
    try Hashtbl.find hc (lid, is_condact)
    with Not_found ->
      let c = Hashtbl.create 7 in
      Hashtbl.add hc (lid, is_condact) c;
      c
  in
  let calls = try Hashtbl.find cat parents with Not_found -> [] in
  try
    let new_calls = add_to_callpos abstr_map [] pos clock args calls in
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
             call_pos = pos; call_clock = clock;
             call_inputs = inputs; call_defaults = defs } as call) -> 

        (* Format.eprintf "register : %a at %a %s \n ARgs: (%a)@." *)
        (*   (LustreIdent.pp_print_ident false) lid Lib.pp_print_position pos *)
        (*   (match clock with *)
        (*    | None -> "" *)
        (*    | Some c -> "ON "^ (StateVar.string_of_state_var c)) *)
        (*   (pp_print_list StateVar.pp_print_state_var ", ") inputs *)
        (* ; *)
        
        register_callpos_for_nb
          abstr_map hc lid parents pos clock (inputs, defs);

        fold (call :: parents) (node_by_lid lid)

      ) node.LustreNode.calls
  in

  fold [] main_node;
  
  hc

exception Found of int * StateVar.t option

let get_pos_number hc lid pos =
  (* Format.eprintf "getpos : %a at %a@." (LustreIdent.pp_print_ident false) lid *)
  (* Lib.pp_print_position pos; *)

  let find_in_cat cat =
    Hashtbl.iter (fun _ l ->
        List.iter (fun (p, n, c, _) ->
            if Lib.compare_pos p pos = 0 then raise (Found (n, c)))
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
          let nb, clock = get_pos_number hc lid pos in
          get_instances acc hc ((lid, nb, clock) :: parents) lsv
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


let rec orig_of_oracle oracle_map sv =
  try SVM.find sv oracle_map with Not_found -> [sv]
  (* try *)
  (*   let l = SVMap.find sv oracle_map in *)
  (*   List.fold_left *)
  (*     (fun acc sv -> List.rev_append (orig_of_oracle oracle_map sv) acc) [] l *)
  (* with Not_found -> [sv] *)


let reconstruct_lustre_streams node state_vars =

  let nodes = SubSystem.all_subsystems node
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
