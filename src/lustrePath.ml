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

(* Abbreviations *)
module I = LustreIdent
module A = LustreAst
module E = LustreExpr
module N = LustreNode


(* Identifier of a call with total ordering *)
module CallId = 
struct
  type t = I.t * position       
  let compare = compare_pairs I.compare compare_pos
end


(* Map of node instances *)
module CallMap = Map.Make (CallId)


(* Map of state variables *)
module SVMap = StateVar.StateVarMap


(* A nested representation of a model

   Need to have a single constructor, otherwise the type would be
   cylic *)
type tree_path = 
  | N of I.t * position * Term.t array SVMap.t * tree_path CallMap.t 


(* ********************************************************************** *)
(* Printing helpers                                                       *)
(* ********************************************************************** *)


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


(* ********************************************************************** *)
(* Plain text output                                                      *)
(* ********************************************************************** *)

(* Pretty-print a file position *)
let pp_print_file_pt ppf pos_file = 

  if pos_file = "" then () else
    Format.fprintf ppf "(%s)" pos_file


(* Pretty-print a position as XML attributes *)
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


(* Pretty-print a single value of a stream at an instant *)
let pp_print_stream_value val_width ppf i t =
  Format.fprintf 
    ppf
    "%-*s"
    val_width
    (string_of_t pp_print_value t)    


(* pretty prints a stream as its identifier followed by its values at each 
  instance. gives [ident_width] space to its identifier column and [val_width]
  space to each of its value columns. *)
let pp_print_stream_pt 
    ident_width 
    val_width 
    ppf 
    (sv, stream_values) =

  (* Get identifier without scope *)
  let stream_ident, ident_scope = LustreExpr.ident_of_state_var sv in

  Format.fprintf
    ppf
    "%-*s %a"
    ident_width
    (string_of_t (LustreIdent.pp_print_ident false) stream_ident)
    (pp_print_arrayi (pp_print_stream_value val_width) " ") stream_values


(* pretty prints a tree_path, giving width [ident_width] to the stream 
   identifier column, width [val_width] to each value column, and
   displaying its ordered list of tree ancestor identifiers [ancestor_idents] 
   in a header. *)
let rec pp_print_tree_path_pt 
    ident_width 
    val_width
    ancestor_idents
    ppf 
  = function N (node_ident, node_pos, stream_map, call_map) ->

    (* Get all streams in the node *)
    let streams = SVMap.bindings stream_map in

    (* Filter for inputs *)
    let inputs = 
      List.filter (fun (sv, _) -> E.state_var_is_input sv) streams 
    in

    (* Filter for outputs *)
    let outputs = 
      List.filter (fun (sv, _) -> E.state_var_is_output sv) streams 
    in

    (* Filter for local variables *)
    let locals = 
      List.filter (fun (sv, _) -> E.state_var_is_local sv) streams 
    in    

    Format.fprintf
      ppf 
      "Node %a (%a)@,"
      (I.pp_print_ident false) node_ident
      (pp_print_list 
         (function ppf -> function (n, p) -> 
           Format.fprintf ppf 
             "%a%a"
               (I.pp_print_ident false) n
               pp_print_pos_pt p)
         " / ")
      (List.rev ancestor_idents);

    let children = snd (List.split (CallMap.bindings call_map)) in 

    let children = CallMap.bindings call_map in 

    let ident_path = (node_ident, node_pos) :: ancestor_idents in

    let print_child ((_, pos), child) =
      pp_print_tree_path_pt
        ident_width
        val_width
        ((node_ident, pos) :: ancestor_idents)
        ppf 
        child
    in

    (* Pretty-print input streams if any *)
    (match inputs with 
      | [] -> ()
      | _ -> 
        Format.fprintf
          ppf
          "== Inputs ==@,%a@,"
          (pp_print_list 
             (pp_print_stream_pt ident_width val_width)
             "@,")
          inputs);

    (* Pretty-print output streams if any *)
    (match outputs with 
      | [] -> ()
      | _ -> 
        Format.fprintf
          ppf
          "== Outputs ==@,%a@,"
          (pp_print_list 
             (pp_print_stream_pt ident_width val_width)
             "@,")
          outputs);

    (* Pretty-print local streams if any *)
    (match locals with 
      | [] -> ()
      | _ -> 
        Format.fprintf
          ppf
          "== Locals ==@,%a@,"
          (pp_print_list 
             (pp_print_stream_pt ident_width val_width)
             "@,")
          locals);

    (* Empty line at end of node *)
    Format.fprintf ppf "@,";
    
    (* Pretty-print called nodes *)
    List.iter print_child children


(* ********************************************************************** *)
(* Conversion of model to a hierarchical model                            *)
(* ********************************************************************** *)

(* Create a hierarchical model of a flat model *)
let rec tree_path_of_model model =

  (* Add state variables to node or to node calls *)
  let fold_state_var (stream_map, call_map) (state_var, terms) =

    (* Get source of state variable *)
    let src = E.get_state_var_source state_var in

    (* Add variable to streams *)
    let stream_map' = 
      SVMap.add state_var 
        (Array.of_list terms) 
        stream_map
    in

    (* Add all instances to nodes *)
    let call_map' =

      List.fold_left
        (fun call_map (call_pos, call_node_id, call_state_var) ->

           (* Identify node instance by name and position *)
           let call_key = (call_node_id, call_pos) in

           (* Find content of node instance or initialize as empty *)
           let node_model = 
             try CallMap.find call_key call_map with Not_found -> []
           in

           (* Add instantiated variable to node *)
           let node_model' = (call_state_var, terms) :: node_model in

           (* Add modified node content to map, replaces previous entry *)
           let call_map' = CallMap.add call_key node_model' call_map in

           (* Continue with modified node calls *)
           call_map')
        call_map
        (E.get_state_var_instances state_var)

    in

    (stream_map', call_map')

  in

  (* Create a hierarchical model for variables of node *)
  let node_of_model (call_node_id, call_pos) model =

    (* Streams of this node and stream in called nodes  *)
    let stream_map, call_map = tree_path_of_model model in

    (* Create node with its streams and its called nodes *)
    N (call_node_id, call_pos, stream_map, call_map)

  in

  (* Add each state variable to node or to node calls *)
  let stream_map, node_map = 
    List.fold_left fold_state_var (SVMap.empty, CallMap.empty) model 
  in

  (* Recursively create hierarchical model in all called nodes *)
  let node_map' = CallMap.mapi node_of_model node_map in

  (* Return streams of node and called nodes *)
  stream_map, node_map'


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

        let stream_terms = stream in

        (var, stream_terms.(0)) :: substitutions                                   
      else

        let curr_var = Var.mk_state_var_instance sv E.cur_offset in

        let prev_var = Var.mk_state_var_instance sv E.pre_offset in

        let stream_terms = stream in

        let curr_binding = (curr_var, stream_terms.(i)) in

        let prev_binding = (prev_var, stream_terms.(i-1)) in

        curr_binding :: prev_binding :: substitutions

    in

    let substitutions = SVMap.fold fold_stream stream_map [] in

    let substitutions' = 
      SVMap.fold fold_stream ancestors_stream_map substitutions 
    in

    let src_expr = 

      if i = 0 && start_at_init then 

        expr.E.expr_init 

      else 

        expr.E.expr_step 

    in

    let value = Eval.eval_term [] substitutions' (src_expr :> Term.t) in

    (Eval.term_of_value value) :: var_model

  in

  let stream_len = 

    if SVMap.is_empty stream_map then 

      if SVMap.is_empty ancestors_stream_map then 

        assert false
          
      else

        Array.length (snd (SVMap.choose ancestors_stream_map)) 

    else
      
      Array.length (snd (SVMap.choose stream_map)) 

  in

  let indices = list_init (fun i -> i) stream_len in

  Array.of_list (List.rev (List.fold_left fold_ind [] indices))


(* Given a node and a hierarchical model for the node, add those
   streams of the node to the second tree hierarchical model that were
   present in the input, eliminating introduced streams and
   reconstructing defined streams. *)
let rec tree_path_of_nodes 
    start_at_init
    nodes
    { N.inputs; N.outputs; N.locals; N.calls; N.props; N.equations } 
    tree_path_in
    tree_path = 

  (* Sort state variables by their occurence in the equations, put
     state variables without equation at the head of the list *)
  let rec sort_defined_vars accum equations state_vars = 

    match equations, state_vars with 

      (* No more equations, put unconstrained variables first *)
      | [], _ -> state_vars @ List.rev accum

      (* No more variables, return sorted *)
      | _, [] -> List.rev accum

      (* Take first equation *)
      | (sv, _) :: tl, _ -> 

        (* Find state variable equal to state variable of first equation *)
        match List.partition (StateVar.equal_state_vars sv) state_vars with

          (* List does not contain state variable *)
          | [], state_vars' -> 

            (* Continue with remaining equations *)
            sort_defined_vars accum tl state_vars

          (* List contains state variable *)
          | _, state_vars' -> 

            (* Add state variable to accumulator and continue with
               remaining equations and state variables *)
            sort_defined_vars (sv :: accum) tl state_vars'
             
  in
 
  (* Show only inputs, outputs and local variables *)
  let visible_vars = 
    props @
    (List.map fst inputs) @ 
    (sort_defined_vars 
       []
       equations
       ((List.map fst outputs) @ 
        (List.filter 
           (fun sv -> E.get_state_var_source sv = E.Local) 
           (List.map fst locals))))
  in
  
  (* Add streams in node to hierarchic model *)
  let tree_path' = 
    List.fold_left
      (tree_path_of_streams start_at_init equations tree_path_in)
      tree_path
      visible_vars 
  in

  (* Add called nodes to hierarchic model *)
  let tree_path'' =
    List.fold_left
      (tree_path_of_calls start_at_init nodes tree_path_in)
      tree_path'
      calls
  in
    
  (* Return modified tree path *)
  tree_path''

(* Add a stream to the hierarchical model, reconstructing it from its
   definition if it is not present *)
and tree_path_of_streams 
    start_at_init
    equations
    (N (_, _, stream_map, _)) 
    (N (node_name, node_pos, stream_map', call_map')) 
    state_var =

  let terms = 

    try 

      (* Return values of stream from the model *)
      SVMap.find state_var stream_map 

    (* Stream is not in the model *)
    with Not_found -> 

      (* Get defining equation for stream *)
      let expr = 
        try List.assq state_var equations with Not_found -> 

          debug lustrePath 
            "State variable %a not found in %a"
            StateVar.pp_print_state_var state_var 
            (LustreIdent.pp_print_ident false) node_name
          in

          assert false 
      in 

      (* Need to get the source of the variable *)
      let src = E.get_state_var_source state_var in 

      (* Reconstruct values of stream from mode and definition *)
      let terms = 
        reconstruct_single_var start_at_init stream_map stream_map' expr
      in

      (* Return source and values of variable *)
      terms

  in

  (* Add stream to resulting hierarchical model *)
  let stream_map'' = SVMap.add state_var terms stream_map' in 

  (* Continue with hierarchical model with stream addee *)
  N (node_name, node_pos, stream_map'', call_map')
  

(* Add streams in called node to the hierarchical model *)
and tree_path_of_calls
    start_at_init
    nodes
    ((N (_, _, _, call_map)) as tree_path)
    ((N (node_name, node_pos, stream_map', call_map')) as tree_path') 
    { N.call_node_name; N.call_pos } =

  (* Get hierarchical model rooted at the node call *)
  let tree_path_call = 
      CallMap.find (call_node_name, call_pos) call_map 
  in

  (* Add streams of the node to the hierarchical model *)
  let tree_path_call' = 
    tree_path_of_nodes 
      start_at_init 
      nodes 
      (LustreNode.node_of_name call_node_name nodes)
      tree_path_call
      (N (call_node_name, call_pos, SVMap.empty, CallMap.empty))
  in

  (* Add modifed hierarchical model of the called node to the input model *)
  let call_map'' =  
    CallMap.add (call_node_name, call_pos) tree_path_call' call_map' 
  in

  (* Continue with hierarchical model with streams of node added *)
  N (node_name, node_pos, stream_map', call_map'')
  

(* Return a hierarchical model with exactly the streams that ware
   defined in the model *)
let reduced_tree_path_of_model start_at_init nodes model =
  
  (* Convert flat model to a hierarchical model *)
  let stream_map, call_map = tree_path_of_model model in

  (*
  (* Get the single element of the map *)
  let N (node_name, node_pos, _, _) as orig_tree_path = 
    snd (CallMap.choose call_map)
  in
*)

  let main_node = List.hd nodes in

  let node_name = main_node.N.name in

  let node_pos = dummy_pos in
  
  let orig_tree_path = N (node_name, node_pos, stream_map, call_map) in
    
    debug lustrePath
    "%a" (pp_print_tree_path_pt 8 8 [])  orig_tree_path
    in
  

  (* Return hierarchical model corresponding to original definition of
     node *)
  tree_path_of_nodes 
    start_at_init 
    nodes
    (List.hd (List.rev nodes)) 
    orig_tree_path
    (N (node_name, node_pos, SVMap.empty, CallMap.empty))


(* ********************************************************************** *)
(* XML output                                                             *)
(* ********************************************************************** *)


(* Pretty-print a file position *)
let pp_print_file_xml ppf pos_file = 

  if pos_file = "" then () else
    Format.fprintf ppf "file=\"%s\"@ " pos_file


(* Pretty-print a position as XML attributes *)
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
      "%aline=\"%d\"@ column=\"%d\""
      pp_print_file_xml pos_file
      pos_lnum
      pos_cnum


(* Pretty-print a property of a stream as XML attributes *)
let pp_print_stream_prop_xml ppf = function 

  | E.Input -> Format.fprintf ppf "@ class=\"input\""

  | E.Output -> Format.fprintf ppf "@ class=\"output\""

  | E.Local -> Format.fprintf ppf "@ class=\"local\""

  (* these types of streams should have been culled out *)
  | E.Observer | E.Abstract | E.Oracle -> assert false 


(* Pretty-print a single value of a stream at an instant *)
let pp_print_stream_value ppf i t =
  Format.fprintf 
    ppf
    "@[<hv 2><Value instant=\"%d\">@,@[<hv 2>%a@]@;<0 -2></Value>@]" 
    i
    pp_print_value t    


(* Pretty-print a single stream *)
let pp_print_stream_xml ppf (sv, stream_values) =

  (* Get identifier without scope *)
  let stream_ident, _ = E.ident_of_state_var sv in

  (* Get type of identifier *)
  let stream_type = StateVar.type_of_state_var sv in

  Format.fprintf 
    ppf
    "@[<hv 2>@[<hv 1><Stream@ name=\"%a\" type=\"%a\"%a>@]@,\
     %a@;<0 -2></Stream>@]"
    (I.pp_print_ident false) stream_ident
    (E.pp_print_lustre_type false) stream_type
    pp_print_stream_prop_xml (E.get_state_var_source sv)
    (pp_print_arrayi pp_print_stream_value "@,") stream_values


(* Pretty-print a tree path as <Stream> and <Node> tags *)
let rec pp_print_tree_path_xml ppf = 
  function N (node_ident, node_pos, stream_map, call_map) ->

    (* Get all streams in the node *)
    let streams = SVMap.bindings stream_map in

    (* Filter for inputs *)
    let inputs = 
      List.filter (fun (sv, _) -> E.state_var_is_input sv) streams 
    in

    (* Filter for outputs *)
    let outputs = 
      List.filter (fun (sv, _) -> E.state_var_is_output sv) streams 
    in

    (* Filter for local variables *)
    let locals = 
      List.filter (fun (sv, _) -> E.state_var_is_local sv) streams 
    in    

    (* Filter for node calls *)
    let calls = List.map snd (CallMap.bindings call_map) in

    (* Output a node with its streams and calls *)
    Format.fprintf
      ppf
      "@[<hv 2>@[<hv 1><Node@ name=\"%a\"@ %a>@]%a@;<0 -2></Node>@]"
      (I.pp_print_ident false) node_ident
      pp_print_pos_xml node_pos
      pp_print_components (inputs, outputs, locals, calls)

(* Print the inputs, ouputs, locals, and nodes, making sure not to place break 
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
let pp_print_path_xml nodes start_at_init ppf model =

  let reconstructed = reduced_tree_path_of_model start_at_init nodes model in

  pp_print_tree_path_xml ppf reconstructed




(* Return width of widest identifier and widest value *)
let rec widths_of_model = function 

  | N (node_ident, node_pos, stream_map, call_map) ->
     
     (* Get the identifier width an maximum value width of a stream *)
     let widths_from_stream (sv, stream_values) =
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
     
(* Pretty-print a path in plain text, with stateless variables
   reconstructed *)
let pp_print_path_pt nodes start_at_init ppf model =

  let reconstructed =
    reduced_tree_path_of_model start_at_init nodes model
  in

  (* Get maximum widths of identifiers and values *)
  let ident_width, val_width = widths_of_model reconstructed in

  pp_print_tree_path_pt ident_width val_width [] ppf reconstructed


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
