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

type stream_prop = 
  | Input
  | Output
  | Local

type tree_path =
  | Node of I.t * A.position * tree_path list
  | Stream of I.t * Type.t * stream_prop * Term.t list


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
let stream_of_model stream_prop (state_var, terms) = 
  
  Stream
    (fst (E.ident_of_state_var state_var),
     StateVar.type_of_state_var state_var,
     stream_prop,
     terms)


(* Create a tree path of a model *)
let rec tree_path_of_model model =

  let model_input, model_output, model_local, model_calls =
    List.fold_left
      partition_model_by_sources
      ([], [], [], [])
      model
  in

  (List.map (stream_of_model Input) model_input) 
  @ (List.map (stream_of_model Output) model_output) 
  @ (List.map (stream_of_model Local) model_local) 
  @ (List.map node_of_model model_calls)

(* Create a Node value of assignments to variables in a node instance *)
and node_of_model ((call_node, call_pos), model) = 

  Node (call_node, call_pos, tree_path_of_model model)
  


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


(* Pretty-print a tree path as <stream> and <node> tags *)
let rec pp_print_tree_path_xml ppf = function 
  
  | Node (node_ident, node_pos, elements) ->

    Format.fprintf 
      ppf
      "@[<hv 2>@[<hv 1><node@ name=\"%a\"@ %a>@]@,%a@;<0 -2></node>@]"
      (I.pp_print_ident false) node_ident
      pp_print_pos_xml node_pos
      (pp_print_list pp_print_tree_path_xml "@,") elements

  | Stream (stream_ident, stream_type, stream_prop, stream_values) ->

    Format.fprintf 
      ppf
      "@[<hv 2>@[<hv 1><stream@ name=\"%a\" type=\"%a\"%a>@]@,\
       %a@;<0 -2>\
       </stream>@]"
      (I.pp_print_ident false) stream_ident
      (E.pp_print_lustre_type false) stream_type
      pp_print_stream_prop_xml stream_prop
      (pp_print_stream_values_xml 0) stream_values


(* Pretty-print a path in <path> tags *)
let pp_print_path_xml ppf model =

  let model' = tree_path_of_model model in

  Format.fprintf 
    ppf
    "@[<hv 2><path>@,%a@;<0 -2></path>@]"
    (pp_print_list pp_print_tree_path_xml "@,") model'


let pp_print_path_orig_xml _ _ _ = ()


(* ********************************************************************** *)
(* Plain-text output                                                      *)
(* ********************************************************************** *)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
