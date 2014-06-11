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
module IdMap = Map.Make (LustreIdent)

module CallId = struct
  type t = I.t * A.position       
  let compare = Pervasives.compare
end
module CallMap = Map.Make(CallId)

type stream_prop = 
  | Input
  | Output
  | Local

type stream = I.t * Type.t * stream_prop * Term.t list

type tree_path =
    (* input/output/local streams, call nodes *)
  | Node of stream IdMap.t * tree_path CallMap.t 

let stream_prop_of_source var_source =
  match var_source with
  | E.Input ->
     Input
  | E.Output ->
     Output
  | E.Local ->
     Local
  | _ ->
     assert false

(* ********************************************************************** *)
(* Conversion of model to execution path                                  *)
(* ********************************************************************** *)


(* [accoc_add k v l] add the element [v] to the list mapped to the key
   [k] in the association list [l]

   If the association list does not contain the key [k], add a new
   entry for [k] with the singleton list of the element. If the key
   exists in the association list, possibly multiple times, add the
   element to the list of the first entry only. The order of the
   entries of the [k] is preserved, but not necessarily the order of
   the whole list. *)
let rec assoc_add key elem list =

  let rec assoc_add' accum key elem = function 
    
    (* At the end of the list, key not found *)
    | [] -> 
      
      (* Add key and singleton list to association list *)
      (key, [elem]) :: accum
      
    (* Key found at the current element *)
    | (k, l) :: tl when k = key -> 
      
      (* Add value to list associated with key, append tail of list and
         return. Ensure that first key occurs before possible duplicat
         keys in the list *)
      ((k, (elem :: l)) :: accum) @ tl
      
    (* Key not found at the current element *)
    | h :: tl -> 
      
      (* Add to accumulator and continue *)
      assoc_add' (h :: accum) key elem tl
        
  in

  (* Call recursive function with empty accumulator *)
  assoc_add' [] key elem list 


(* Partition state variables of a model by their source *)
let partition_model_by_sources 
    ((inputs, outputs, locals, calls) as accum) 
    (state_var, terms) =

  (* Get the type of variable *)
  match LustreExpr.get_state_var_source state_var with 

    (* Add input variable to list *)
    | E.Input -> ((state_var, terms) :: inputs, outputs, locals, calls) 

    (* Add output variable to list *)
    | E.Output -> (inputs, (state_var, terms) :: outputs, locals, calls)  

    (* Add defined local variable to list *)
    | E.Local -> (inputs, outputs, (state_var, terms) :: locals, calls)   

    (* Add variable of node call to list *)
    | E.Instance (call_pos, call_node, call_state_var) -> 

      (inputs, 
       outputs, 
       locals, 
       assoc_add (call_node, call_pos) (call_state_var, terms) calls)

    (* Skip oracle inputs and abstracted variables *)
    | E.Oracle | E.Abstract -> accum


(* Create a Stream value of a state variable assignments *)
let stream_of_model stream_prop (state_var, terms) : stream = 
  
  Format.printf "stream: %a@." StateVar.pp_print_state_var state_var;

  (fst (E.ident_of_state_var state_var),
   StateVar.type_of_state_var state_var,
   stream_prop,
   terms)

(* Create a tree path of a model *)
let rec tree_path_of_model model =
  
  Format.printf
    "node: @[<hv>%a@]@."
    (pp_print_list
       (fun ppf (sv, _) -> StateVar.pp_print_state_var ppf sv)
       "@ ") 
    model;

  let fold_state_var (stream_map, call_map) (state_var,terms) =
    let src = E.get_state_var_source state_var in
    match src with
    | E.Input
    | E.Output  
    | E.Local ->
       let stream_map' = 
         IdMap.add 
           (fst (E.ident_of_state_var state_var)) 
           (stream_of_model (stream_prop_of_source src) (state_var, terms))
           stream_map
       in
       (stream_map',call_map)
    | E.Instance (call_pos, call_node, call_state_var) -> 
       let call_id = (call_node,call_pos) in
       let node_model = 
         try 
           CallMap.find call_id call_map 
         with
         | Not_found ->
            []
       in
       let node_model' = (call_state_var, terms) :: model in
       let call_map' = CallMap.add call_id node_model' call_map in
       (stream_map,call_map')
    | E.Oracle | E.Abstract -> (stream_map,call_map)
  in

  let stream_map,node_map = List.fold_left fold_state_var (IdMap.empty,CallMap.empty) model in
  let node_map' = CallMap.map tree_path_of_model node_map in

  Node(stream_map,node_map')

let rec reconstruct_stateless_variables nodes curr_node model  =

  let fold_eqn stream_map (sv,expr) =
    match E.get_state_var_source sv with
    | E.Abstract
    | E.Instance(_,_,_)
    | E.Oracle ->
       stream_map
    | E.Input
    | E.Output
    | E.Local ->
       stream_map
  in

  let map_call (call_ident,call_pos) path =
    let node = 

  match model with
  | Node(ident,pos,stream_map,call_map) ->
     let node = LustreNode.node_of_name ident nodes in
     let eqs = node.N.equations in
     let stream_map' = List.fold_left fold_eqn stream_map eqs in
     let call_map' = 
       CallMap.map 
         (fun _ path -> reconstruct_stateless_variables nodes path) 
         call_map 
     in
     Node(ident,pos,stream_map',call_map')
(*
  let map_node node =
    
    let relevant (s,_) =
      match E.get_state_var_source s with
      | Abstract
      | Instance
      | Oracle ->
         false
      | _ ->
         true
    in
    
    let eqs = List.filter relevant node.equations in
    
 *)

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

  | Input -> Format.fprintf ppf "@ input"

  | Output -> Format.fprintf ppf "@ output"

  | Local -> ()


(* Pretty-print a list of stream values as <value> tags *)
let rec pp_print_stream_values_xml i ppf = function

  | [] -> ()

  | t :: [] -> 

    Format.fprintf 
      ppf
      "@[<hv 2><value state=\"%d\">@,@[<hv 2>%a@]@;<0 -2></value>@]" 
      i
      Term.pp_print_term t
      
  | t :: tl -> 

    Format.fprintf 
      ppf
      "%a@,%a"
      (pp_print_stream_values_xml i) [t]
      (pp_print_stream_values_xml (succ i)) tl


let pp_print_stream ppf (stream_ident, stream_type, stream_prop, stream_values) =
  Format.fprintf 
    ppf
    "@[<hv 2>@[<hv 1><stream@ name=\"%a\" type=\"%a\"%a>@]@,\
     %a@;<0 -2>\
     </stream>@]"
    (I.pp_print_ident false) stream_ident
    (E.pp_print_lustre_type false) stream_type
    pp_print_stream_prop_xml stream_prop
    (pp_print_stream_values_xml 0) stream_values

(* Pretty-print a tree path as <stream> and <node> tags *)
let rec pp_print_tree_path_xml ppf = function 
  
  | Node (node_ident, node_pos, stream_map, call_map) ->

     let streams = List.map snd (IdMap.bindings stream_map) in
     let inputs = List.filter (fun (_,_,prop,_) -> prop = Input) streams in
     let outputs = List.filter (fun (_,_,prop,_) -> prop = Output) streams in
     let locals = List.filter (fun (_,_,prop,_) -> prop = Local) streams in    
     let calls = List.map snd (CallMap.bindings call_map) in
     
     List.iter (pp_print_stream ppf) inputs;
     List.iter (pp_print_stream ppf) outputs;
     List.iter (pp_print_stream ppf) locals;

     Format.fprintf
       ppf
       "@[<hv 2>@[<hv 1><node@ name=\"%a\"@ %a>@]@,%a@;<0 -2></node>@]"
       (I.pp_print_ident false) node_ident
       pp_print_pos_xml node_pos
       (pp_print_list pp_print_tree_path_xml "@,") calls


(* Pretty-print a path in <path> tags *)
let pp_print_path_xml ppf model =

  let stream_map, call_map = tree_path_of_model model in
 
  let streams = List.map snd (IdMap.bindings stream_map) in
  let inputs = List.filter (fun (_,_,prop,_) -> prop = Input) streams in
  let outputs = List.filter (fun (_,_,prop,_) -> prop = Output) streams in
  let locals = List.filter (fun (_,_,prop,_) -> prop = Local) streams in    
  let calls = List.map snd (CallMap.bindings call_map) in  

  Format.fprintf 
    ppf
    "@[<hv 2><path>@,%a@,%a@,%a@,%a@;<0 -2></path>@]"
    (pp_print_list pp_print_stream "@,") inputs
    (pp_print_list pp_print_stream "@,") outputs
    (pp_print_list pp_print_stream "@,") locals
    (pp_print_list pp_print_tree_path_xml "@,") calls

let pp_print_path_xml_orig nodes ppf model =
  let model' = tree_path_of_model model in
  let main_node = LustreNode.node_of_name "main" nodes in
  let model'' = reconstruct_stateless_variables nodes main_node model' in
  ()
  

(* ********************************************************************** *)
(* Plain-text output                                                      *)
(* ********************************************************************** *)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
