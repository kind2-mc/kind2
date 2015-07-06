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
module S = SubSystem
module T = TransSys

module SVT = StateVar.StateVarHashtbl
module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet


(* Model for a node and its subnodes *)
type t = 
  { 

    (* Node *)
    node : N.t;

    (* Assignments to state variables of node *)
    model : Model.path;

    (* Subnodes and position of their calls *)
    subnodes : ((I.t * position) list * t) list

  }


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

    Format.printf "Instance for %a not found@." StateVar.pp_print_state_var state_var;
      
    raise Not_found


(* Compute substitutions for each state variable in the last arguments
   to either its instance in the top system, or its definition in
   [equations] and recursively for each state variable in a
   definition *)
let rec substitute_definitions' stateful_vars equations subst = function 

  (* All state variables are in the top system, return substitutions *)
  | [] -> subst

  (* Substitution for state variable already computed? *)
  | state_var :: tl 
    when 
      List.exists
        (fun (sv, _) -> 
           StateVar.equal_state_vars sv state_var) 
        subst -> 
    
    (* Skip state variable and continue *)
    substitute_definitions' stateful_vars equations subst tl

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
      ((state_var, E.mk_var state_var) :: subst)
      tl

  (* Get variable in this system to be instantiated *)
  | state_var :: tl -> 

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
      ((state_var, expr) :: subst)
      ((E.state_vars_of_expr expr |> SVS.elements) @ tl)


(* Recursively substitute the state variable with either its instance
   in the top system, or with its definition in [equations] *)
let substitute_definitions instances equations state_var =

  let defs = 
    substitute_definitions' instances equations [] [state_var] 
  in

  (* Stateless variables do not occur under a pre, therefore it is
     enough to substitute it at the current instant *)
  List.fold_left
    (fun a b -> E.mk_let_cur [b] a)
    (E.mk_var state_var)
    (List.rev defs)



(* Get the sequence of values of the state variable in the top system
   and add for this state variables as with [map_top_and_add] if
   possible. Otherwise, reconstruct the sequence of values from its
   definitions.
   
   Use as the iterator function in LustreIndex.iter *)
let map_top_reconstruct_and_add
    first_is_init
    trans_sys
    instances 
    model 
    model'
    equations
    index
    state_var =

  try 

    (* Return the model for the instance *)
    map_top_and_add instances model model' index state_var

  (* No instance, or no model *)
  with Not_found -> 
    
    (* Get stateful variables of transition system *)
    let stateful_vars = TransSys.state_vars trans_sys in

    (* Get definition in terms of state variables of the top node *)
    let expr = substitute_definitions stateful_vars equations state_var in

    (* Evaluate expression with reversed list of models *)
    let rec aux accum = function 

      (* All steps in path evaluated, return *)
      | [] -> accum

      (* At last step of path, is this the initial state? *)
      | [m] when first_is_init -> 

        (* Value for state variable at step *)
        let v = 

          (* Get expression for initial state *)
          E.base_term_of_t TransSys.init_base expr

          |>

          (* Map variables in term to top system *)
          (map_term_top instances)

          |> 

          (* Evaluate term in model *)
          Eval.eval_term
            (TransSys.uf_defs trans_sys) 
            m

          (* Return term *)
          |> Eval.term_of_value

        in

        (* Add term to accumulator as first value and return *)
        Model.Term v :: accum

      (* Model for step of path *)
      | m :: tl -> 

        (* Value for state variable at step *)
        let v = 

          (* Get expression for step state *)
          E.cur_term_of_t TransSys.trans_base expr

          |>

          (* Map variables in term to top system *)
          (map_term_top instances)

          |> 

          (* Evaluate expression for step state *)
          Eval.eval_term
            (TransSys.uf_defs trans_sys) 
            m

          (* Return term *)
          |> Eval.term_of_value

        in

        (* Add term to accumulator and continue *)
        aux (Model.Term v :: accum) tl

    in

    (* Evaluate expression at each step of path *)
    aux [] (Model.models_of_path model |> List.rev)

    (* Add as path of subnode state variable *)
    |> SVT.add model' state_var


(* Reconstruct model for the instance given the models for the subnodes 

   Use with [TransSys.fold_subsystem_instances]. *)
let node_path_of_instance 
    first_is_init
    model_top
    nodes
    trans_sys
    instances
    subnodes =

  (* Convert scope of transition system to a node identifier *)
  let ident = 
    TransSys.scope_of_trans_sys trans_sys
    |> LustreIdent.of_scope 
  in

  (* Source node of transition system *)
  let { N.inputs; N.outputs; N.locals; N.equations } as node = 

    try 

      (* Get node by name *)
      N.node_of_name ident nodes 

    (* Node must be in the subsystems *)
    with Not_found -> assert false

  in

  (* Create a path for the state variables of the node *)
  let model = 
    Model.create_path
      (D.cardinal inputs + 
       D.cardinal outputs + 
       List.fold_left (fun a d -> D.cardinal d + a) 0 locals)
  in

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

  (* Map all local state variables to the top instances or
     reconstructand add their path to the model

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
          model_top
          model
          equations))
    locals;

  (* Record trace of node calls *)
  let trace = 
    List.map
      (fun (t, { T.pos }) -> 
         (TransSys.scope_of_trans_sys t |> I.of_scope, pos))
      instances
  in

  (* Return path for subnode and its call trace *)
  (trace, { node; model; subnodes })


(* Return a hierarchical model for the nodes from a flat model by
   mapping the model of the top node to model of the subnoe instances,
   reconstructing the streams in the original input. *)
let node_path_of_subsystems first_is_init trans_sys model subsystems = 

  (* Create models for all subnodes *)
  TransSys.fold_subsystem_instances 
    (node_path_of_instance first_is_init model (N.nodes_of_subsystem subsystems))
    trans_sys


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
  Format.fprintf
    ppf 
    "%*s"
    val_width
    v


(* Output a stream value with given width for the identifier and
   values *)
let pp_print_stream_pt ident_width val_width ppf (stream_name, stream_values) = 

  (* Break lines if necessary and indent correctly *)
  Format.fprintf
    ppf
    "@[<hov %d>%-*s %a@]"
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
      "== %s ==@,\
       %a@,"
      sect
      (pp_print_list (pp_print_stream_pt ident_width val_width) "@,") 
      l


(* Output sequences of values for each stream of the nodes in the list
   and for all its called nodes *)
let rec pp_print_lustre_path_pt' ppf = 

  function 

    (* All nodes printed *)
    | [] -> ()

    (* Take first node to print *)
    | (trace,
       { node = { N.name; N.inputs; N.outputs; N.locals } as node; 
         model; 
         subnodes }) :: tl ->

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

      (* Filter locals to for visible state variables only and return
         as a list 

         The list of locals is the reversed from the original input in
         the node, with fold_left here we get it in the original order
         again. *)
      let ident_width, val_width, locals' = 
        List.fold_left
          (fun a d -> 
             (D.filter 
                (fun _ sv -> N.state_var_is_visible node sv)
                d
              |> D.bindings) 
             @ a)
          []
          locals
        |> streams_to_strings model ident_width val_width []
      in

      (* Pretty-print this node *)
      Format.fprintf 
        ppf
        "@[<v>Node %a (%a)@,\
         %a\
         %a\
         %a@]@,@,"
        (I.pp_print_ident false) 
        name
        (pp_print_list pp_print_call_pt " / ") 
        (List.rev trace)
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


(* Ouptut a hierarchical model as plan text *)
let pp_print_path_pt trans_sys subsystems first_is_init ppf model = 

  (* Create the hierarchical model *)
  node_path_of_subsystems first_is_init trans_sys model subsystems

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
let pp_print_stream_xml node model ppf (index, state_var) =

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
      pp_print_stream_prop_xml (N.get_state_var_source node state_var)
      (pp_print_listi pp_print_stream_value "@,") stream_values

  with Not_found -> assert false
    

(* Output a list of node models *)
let rec pp_print_lustre_path_xml' ppf = function 

  | [] -> ()

  | (trace,
     { node = { N.name; N.inputs; N.outputs; N.locals } as node; 
       model; 
       subnodes }) :: tl ->

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
              (fun _ sv -> N.state_var_is_visible node sv)
              d
            |> D.bindings) 
           @ a)
        []
        locals
    in

    (* Pretty-print this node *)
    Format.fprintf 
      ppf
      "@[<hv 2>@[<hv 1><Node@ name=\"%a\"%a>@]@,%a%t%a%t%a%t%a@;<0 -2></Node>@]%t"
      (I.pp_print_ident false) 
      name
      pp_print_call_xml
      trace
      (pp_print_list (pp_print_stream_xml node model) "@,") inputs'
      (fun ppf -> 
         if
           inputs' <> [] && 
           (outputs' <> [] || locals' <> [] || subnodes <> []) 
         then
           Format.fprintf ppf "@,")
      (pp_print_list (pp_print_stream_xml node model) "@,") outputs'
      (fun ppf -> 
         if outputs' <> [] && (locals' <> [] || subnodes <> []) then
           Format.fprintf ppf "@,")
      (pp_print_list (pp_print_stream_xml node model) "@,") locals'
      (fun ppf -> if locals' <> [] && subnodes <> [] 
        then Format.fprintf ppf "@,")
      pp_print_lustre_path_xml' subnodes
      (fun ppf -> if tl <> [] then Format.fprintf ppf "@,");

    (* Continue *)
    pp_print_lustre_path_xml' ppf tl


(* Output sequences of values for each stream of the node and for all
   its called nodes *)
let pp_print_lustre_path_xml ppf path = 

  (* Delegate to recursive function *)
  pp_print_lustre_path_xml' ppf [path]


(* Ouptut a hierarchical model as XML *)
let pp_print_path_xml trans_sys subsystems first_is_init ppf model = 

  (* Create the hierarchical model *)
  node_path_of_subsystems first_is_init trans_sys model subsystems

  (* Output as XML *)
  |> pp_print_lustre_path_xml ppf 


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
