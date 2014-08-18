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
module A = LustreAst
module E = LustreExpr
module N = LustreNode

module CallId = struct
  type t = I.t * A.position       
  let compare = Pervasives.compare
end

module CallMap = Map.Make(CallId)
module SVMap = StateVar.StateVarMap

(* (state var source, model terms) *)
type stream = E.state_var_source * Term.t array

(* A nested representation of a model *)
type tree_path =
    (* Node(node identifier, call position, streams, subnodes)
       model of an instantiation of a lustre node *)
  | Node of I.t * A.position * stream SVMap.t * tree_path CallMap.t 

(* ********************************************************************** *)
(* Conversion of model to execution path                                  *)
(* ********************************************************************** *)

(* Create a tree path of a model *)
let rec tree_path_components model =
  let fold_state_var (stream_map, call_map) (state_var,terms) =
    let src = E.get_state_var_source state_var in
    match src with
    | E.Input
    | E.Output  
    | E.Local
    | E.Oracle
    | E.Abstract ->
       let stream_map' = 
         SVMap.add 
           state_var
           (src, Array.of_list terms)
           stream_map
       in
       (stream_map',call_map)
    | E.Instance (call_pos, call_node_id, call_state_var) ->
       let call_key = (call_node_id,call_pos) in
       let node_model = 
         if CallMap.mem call_key call_map then
           CallMap.find call_key call_map 
         else
           []
       in
       let node_model' = (call_state_var, terms) :: node_model in
       let call_map' = CallMap.add call_key node_model' call_map in
       (stream_map,call_map')
  in
  let node_of_model (call_node_id,call_pos) model =
    let stream_map, call_map = tree_path_components model in
    Node(call_node_id,call_pos,stream_map,call_map)
  in
  let stream_map,node_map = List.fold_left fold_state_var (SVMap.empty,CallMap.empty) model in
  let node_map' = CallMap.mapi node_of_model node_map in
  stream_map,node_map'

(* reconstructs a stateless variable

   [start_at_init] Is a boolean which is true iff we element 0 of 
   each of the streams is the initial instance.

   [expr] is the expression on the right-hand-side of a stateless variable
   definition
   
   [stream_map] is the stream map for the call containing the variable 
   whose definition is [expr] 

   [ancestors_stream_map] is the combined stream maps of all ancestors of
   the call containing the variable whose definition is [expr]
*)
let reconstruct_single_var start_at_init ancestors_stream_map stream_map expr =
  (* Given that [var_model] contains the first [i] values of the stream 
     we are reconstructing (in reverse order) prepends the next value onto
     the front of [var_model] *)
  let fold_ind var_model i =
    (* prepend the var*term binding(s) for [sv] at cur instance [i]
       (and pre instance [i]-1 when [i]>0) onto substitutions *)
    let fold_stream sv stream substitutions =
      if i = 0 then
        let var = 
          if start_at_init then 
            Var.mk_state_var_instance sv E.base_offset
          else
            Var.mk_state_var_instance sv E.cur_offset
        in
        let stream_terms = snd stream in
        (var, stream_terms.(0)) :: substitutions                                   
      else
        let curr_var = Var.mk_state_var_instance sv E.cur_offset in
        let prev_var = Var.mk_state_var_instance sv E.pre_offset in
        let stream_terms = snd stream in
        let curr_binding = (curr_var, stream_terms.(i)) in
        let prev_binding = (prev_var, stream_terms.(i-1)) in
        curr_binding :: prev_binding :: substitutions
    in
    let substitutions = SVMap.fold fold_stream stream_map [] in
    let substitutions' = SVMap.fold fold_stream ancestors_stream_map substitutions in
    let src_expr = 
      if i = 0 && start_at_init then 
        expr.E.expr_init 
      else 
        expr.E.expr_step 
    in
    let value = Eval.eval_term [] substitutions' (src_expr :> Term.t) in
    (Eval.term_of_value value) :: var_model
  in
  let stream_len = Array.length (snd (snd (SVMap.choose stream_map))) in
  let indices = list_init (fun i -> i) stream_len in
  Array.of_list (List.rev (List.fold_left fold_ind [] indices))

(* reconstructs stateless variables of subtree rooted at [path].
   
   [nodes] is a list of all nodes in the program being processed and
   
   [calls] is a list of all calls made from the parent of [path],
   or empty if [path] has no parent.

   [stream_map] is a map containing reconstructed streams of all 
   ancestors of [path] 
   *)    
let rec reconstruct_stateless_variables nodes start_at_init calls ancestors_stream_map path =
  (* add reconstructed state variable [sv] to [stream_map] 
     if it is not already there *)
  let fold_eqn ancestors_stream_map stream_map (sv,expr) =
    let prop = E.get_state_var_source sv in
    match prop with
    | E.Instance(_,_,_) ->
       assert false
    | E.Abstract      
    | E.Oracle
    | E.Input
    | E.Output
    | E.Local ->
       if SVMap.mem sv stream_map then
         stream_map
       else
           let stream_terms = 
             reconstruct_single_var
               start_at_init
               ancestors_stream_map 
               stream_map 
               expr 
           in 
           SVMap.add sv (prop,stream_terms) stream_map
  in
  match path with
  | Node(ident,pos,stream_map,call_map) ->
     let node = N.node_of_name ident nodes in
     (* [inputs] is a list of (formal,actual) pairs for all inputs to this node,
        or an empty list if this is the main node. 

       [outputs] is a list of (parent state var, current state var) pairs
       for all of the outputs of this node, or an empty list if this
       is the main node.
     *)
     let inputs, outputs =
       try
         let call = List.find (fun call -> call.N.call_pos = pos) calls in
         let inputs =
         List.combine 
           ((List.map fst node.N.inputs) @ node.N.oracles)      
           call.N.call_inputs 
         in
         let outputs = 
           List.combine
             call.N.call_returns
             (List.map fst node.N.outputs)
         in
         inputs,outputs
       with
       | Not_found ->
          (* this must be the main node - we expect that all of its inputs
             are already contained in the model *)
          let in_model (sv,ind) = SVMap.mem sv stream_map in
          if not (List.for_all in_model node.N.inputs) then
            (let sv, _ = List.find (fun sv -> not (in_model sv)) node.N.inputs in
             debug lustrePath
               "State variable %a not in model"
               StateVar.pp_print_state_var sv
             in
             assert false);
          (* assert (List.for_all in_model node.N.inputs); *)
          [],[]
     in

     (* Use the model for the caller's return variables
        as the model for the callee's output variables *)
     let fold_output stream_map (parent_sv,current_sv) =
       let current_prop = E.get_state_var_source current_sv in
       let parent_terms = snd (SVMap.find parent_sv ancestors_stream_map) in
       SVMap.add 
         current_sv
         (current_prop,parent_terms)
         stream_map 
     in

     (* Add models for all outputs of this node. *)
     let stream_map' = 
       List.fold_left fold_output stream_map outputs
     in

     (* Reconstruct the stateless variables of this node *) 
     let stream_map'' = 
       List.fold_left 
         (fold_eqn ancestors_stream_map) 
         stream_map'
         (inputs @ (N.equations_order_by_dep nodes node).N.equations) 
     in

     let merge_stream_maps sv t0 t1 =
       match (t0,t1) with
       | Some(term),None ->
          Some(term)
       | None, Some(term) ->
          Some(term)
       | Some(_),Some(_)
       | None, None ->
          assert false;
     in
     (* Merge this node's models with all ancestor node models to 
        compute the ancestors_stream_map for all children of this node *)
     let merged_stream_map = 
       SVMap.merge merge_stream_maps ancestors_stream_map stream_map''
     in

     let reconstruct_child path = 
       reconstruct_stateless_variables 
         nodes 
         start_at_init
         node.N.calls 
         merged_stream_map 
         path
     in
     let call_map' = CallMap.map reconstruct_child call_map in
     Node(ident,pos,stream_map'',call_map')

(* removes all oracle and abstract streams from [path] and all paths reachable
   from it *)
let rec cull_intermediate_streams path =
  match path with
  | Node(ident,pos,stream_map,call_map) ->
     let not_intermediate sv (prop,terms) =
       match prop with
       | E.Local
       | E.Input
       | E.Output ->
          true
       | E.Oracle
       | E.Abstract ->
          false
       | E.Instance(_,_,_) ->
          assert false
     in
     let stream_map' = SVMap.filter not_intermediate stream_map in
     let call_map' = CallMap.map cull_intermediate_streams call_map in 
     Node(ident,pos,stream_map',call_map')

(* removes all streams from the tree rooted at [path] which are not
   contained in the cone of influence [coi]. *)
let rec cull_with_coi coi nodes path =
  match path with
  | Node(ident,pos,stream_map,call_map) ->
     let node = N.node_of_name ident nodes in
     let calls = node.N.calls in
     let filter_call (id,pos) path =
       let call = List.find (fun call -> call.N.call_pos = pos) calls in
       List.exists 
         (fun sv -> StateVar.StateVarSet.mem sv coi)
         call.N.call_returns
     in
     let stream_map' = 
       SVMap.filter (fun sv _ -> StateVar.StateVarSet.mem sv coi) stream_map
     in
     let call_map' = CallMap.filter filter_call call_map in
     let call_map'' = CallMap.map (cull_with_coi coi nodes) call_map' in
     Node(ident,pos,stream_map',call_map'')

(* ********************************************************************** *)
(* XML output                                                             *)
(* ********************************************************************** *)


(* Pretty-print a position as XML attributes *)
let pp_print_pos_xml ppf pos = 

  (* Do not print anything for a dummy position *)
  if A.is_dummy_pos pos then () else 

    (* Get file, line and column of position *)
    let pos_file, pos_lnum, pos_cnum = 
      A.file_row_col_of_pos pos
    in
    
    (* Print attributes *)
    Format.fprintf 
      ppf
      "file=\"%s\"@ line=\"%d\"@ column=\"%d\""
      pos_file
      pos_lnum
      pos_cnum

(* Pretty-print a property of a stream as XML attributes *)
let pp_print_stream_prop_xml ppf = function 

  | E.Input -> Format.fprintf ppf "@ class=\"input\""

  | E.Output -> Format.fprintf ppf "@ class=\"output\""

  | E.Local -> Format.fprintf ppf "@ class=\"local\""

  (* these types of streams should have been culled out *)
  | E.Abstract | E.Oracle | E.Instance(_,_,_) -> assert false 

let pp_print_stream_xml ppf (sv, (stream_prop, stream_values)) =
  let stream_ident = fst (E.ident_of_state_var sv) in
  let stream_type = StateVar.type_of_state_var sv in

  let print_stream_value ppf i t =
    Format.fprintf 
      ppf
      "@[<hv 2><value state=\"%d\">@,@[<hv 2>%a@]@;<0 -2></value>@]" 
      i
      Term.pp_print_term t    
  in

  Format.fprintf 
    ppf
    "@[<hv 2>@[<hv 1><stream@ name=\"%a\" type=\"%a\"%a>@]@,\
     %a@;<0 -2></stream>@]"
    (I.pp_print_ident false) stream_ident
    (E.pp_print_lustre_type false) stream_type
    pp_print_stream_prop_xml stream_prop
    (pp_print_arrayi print_stream_value "@,") stream_values

(* Pretty-print a tree path as <stream> and <node> tags *)
let rec pp_print_tree_path_xml ppf = function 
  | Node (node_ident, node_pos, stream_map, call_map) ->

     let streams = (SVMap.bindings stream_map) in
     let inputs = List.filter (fun (sv,(prop,_)) -> prop = E.Input) streams in
     let outputs = List.filter (fun (sv,(prop,_)) -> prop = E.Output) streams in
     let locals = List.filter (fun (sv,(prop,_)) -> prop = E.Local) streams in    
     let calls = List.map snd (CallMap.bindings call_map) in
     
     Format.fprintf
       ppf
       "@[<hv 2>@[<hv 1><node@ name=\"%a\"@ %a>@]%a@;<0 -2></node>@]"
       (I.pp_print_ident false) node_ident
       pp_print_pos_xml node_pos
       pp_print_components (inputs,outputs,locals,calls)

(* print the inputs, ouputs, locals, and nodes, making sure not to place break 
   hints before empty components *)
and pp_print_components ppf (inputs,outputs,locals,calls) =
  if List.length inputs > 0 then
    Format.fprintf ppf "@,%a" (pp_print_list pp_print_stream_xml "@,") inputs;

  if List.length outputs > 0 then
    Format.fprintf ppf "@,%a" (pp_print_list pp_print_stream_xml "@,") outputs;

  if List.length locals > 0 then
    Format.fprintf ppf "@,%a" (pp_print_list pp_print_stream_xml "@,") locals;

  if List.length calls > 0 then
    Format.fprintf ppf "@,%a" (pp_print_list pp_print_tree_path_xml "@,") calls

(* prett_print a path in <path> tags, with stateless variables reconstructed *)
let pp_print_path_xml (* nodes *) coi start_at_init ppf model =
  assert (List.length model > 0);
  let stream_map,call_map = tree_path_components model in

  assert (SVMap.cardinal stream_map = 0);
  assert (CallMap.cardinal call_map = 1);

  match CallMap.choose call_map with
  | _, main_node ->     
     let reconstructed  = 
       reconstruct_stateless_variables 
         (* nodes *) coi
         start_at_init
         [] 
         SVMap.empty 
         main_node 
     in
     let coi_svs = LustreNode.extract_state_vars coi in
     let reconstructed' = cull_with_coi coi_svs (* nodes *) coi reconstructed in
     let reconstructed'' = cull_intermediate_streams reconstructed' in
     pp_print_tree_path_xml ppf reconstructed''
  
(* ********************************************************************** *)
(* Plain text output                                                      *)
(* ********************************************************************** *)

(* pretty prints a stream as its identifier followed by its values at each 
  instance. gives [ident_width] space to its identifier column and [val_width]
  space to each of its value columns. *)
let pp_print_stream_pt 
      ident_width 
      val_width 
      ppf 
      sv
      (_,stream_values) =

   let stream_ident = fst (LustreExpr.ident_of_state_var sv) in

   let print_stream_value ppf i t =
     Format.fprintf 
       ppf
       "%-*s"
       val_width
       (string_of_t Term.pp_print_term t)    
   in
   
   Format.fprintf
     ppf
     "%-*s %a@."
     ident_width
     (string_of_t (LustreIdent.pp_print_ident false) stream_ident)
     (pp_print_arrayi print_stream_value " ") stream_values

(* pretty prints a tree_path, giving width [ident_width] to the stream 
   identifier column, width [val_width] to each value column, and
   displaying its ordered list of tree ancestor identifiers [ancestor_idents] 
   in a header. *)
let rec pp_print_tree_path_pt 
  ident_width 
  val_width
  ancestor_idents
  ppf 
  = 
  function
  | Node(node_ident,node_pos,stream_map,call_map) ->
     Format.fprintf
       ppf 
       "@,Node %a (%a)@."
       (I.pp_print_ident false) node_ident
       (pp_print_list (I.pp_print_ident false) " / ")
       (List.rev ancestor_idents);
     
     let children = snd (List.split (CallMap.bindings call_map)) in 
     let ident_path = node_ident :: ancestor_idents in
     let print_child child =
       pp_print_tree_path_pt ident_width val_width ident_path ppf child
     in
     SVMap.iter (pp_print_stream_pt ident_width val_width ppf) stream_map;
     List.iter print_child children

(* Return width of widest identifier and widest value *)
let rec widths_of_model = function 

  | Node (node_ident,node_pos,stream_map,call_map) ->
     
     (* Get the identifier width an maximum value width of a stream *)
     let widths_from_stream (sv, (_, stream_values)) =
       let ident = fst (E.ident_of_state_var sv) in
       let ident_width =         
         (String.length 
           (string_of_t (LustreIdent.pp_print_ident false) ident))
       in
       
       let val_width t =
         let formatted_val = (string_of_t Term.pp_print_term t) in
         (String.length formatted_val)
       in
       
       let max_val_width =
         if Array.length stream_values = 0 then
           0
         else
           array_max (Array.map val_width stream_values)
       in
       ident_width,max_val_width
     in
     
     (* max identifier and value widths over all streams in this node *)
     let max_stream_ident_width, max_stream_val_width =
       if SVMap.cardinal stream_map > 0 then
         let widths = List.map widths_from_stream (SVMap.bindings stream_map) in
         let ident_widths, stream_widths = List.split widths in
         list_max ident_widths, list_max stream_widths
       else
         0,0
     in

     (* results of recursive calls to subnodes *)
     let call_ident_results = 
       List.map (fun (_,call) -> widths_of_model call) (CallMap.bindings call_map) 
     in

     (* max identifier and value widths over all subnodes of this node *) 
     let max_call_ident_width, max_call_val_width = 
       if CallMap.cardinal call_map > 0 then
         let ident_widths, call_widths = List.split call_ident_results in
         list_max ident_widths, list_max call_widths
       else
         0,0
     in

     (max max_stream_ident_width max_call_ident_width,
     max max_stream_val_width max_call_val_width)
     
(* Pretty-print a path in plain text, with stateless variables reconstructed *)
let pp_print_path_pt (* nodes *) coi start_at_init ppf model =
  let stream_map,call_map = tree_path_components model in
  assert (SVMap.cardinal stream_map = 0);
  assert (CallMap.cardinal call_map = 1);
  let reconstructed = 
    reconstruct_stateless_variables 
      coi (* nodes *)
      start_at_init
      []
      SVMap.empty
      (snd (CallMap.choose call_map))
  in
  let coi_svs = LustreNode.extract_state_vars coi in
  let reconstructed' = cull_with_coi coi_svs coi (* nodes *) reconstructed in
  let reconstructed'' = cull_intermediate_streams reconstructed' in
  let ident_width, val_width = widths_of_model reconstructed'' in
  pp_print_tree_path_pt ident_width val_width [] ppf reconstructed''


(* ********************************************************************** *)
(* Plain-text output                                                      *)
(* ********************************************************************** *)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
