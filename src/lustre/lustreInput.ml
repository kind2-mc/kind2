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

module A = LustreAst
module I = LustreIdent
module N = LustreNode
module C = LustreContext
module D = LustreDeclarations
module S = SubSystem



(* Parse from input channel *)
let of_channel in_ch = 

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init 
    in_ch
    (try Filename.dirname (Flags.input_file ())
     with Failure _ -> Sys.getcwd ());

  (* Lustre file is a list of declarations *)
  let declarations = 

    try 

      (* Parse file to list of declarations *)
      LustreParser.main LustreLexer.token lexbuf 

    with 

      | LustreParser.Error ->

        let lexer_pos = 
          Lexing.lexeme_start_p lexbuf 
        in

        C.fail_at_position
          (position_of_lexing lexer_pos)
          "Syntax error"

  in

  (* Simplify declarations to a list of nodes *)
  let nodes = D.declarations_to_nodes declarations in

  (* Name of main node *)
  let main_node = 

    (* Command-line flag for main node given? *)
    match Flags.lustre_main () with 
      
      (* Use given identifier to choose main node *)
      | Some s -> LustreIdent.mk_string_ident s
                    
      (* No main node name given on command-line *)
      | None -> 

        (try 

           (* Find main node by annotation, or take last node as
              main *)
           LustreNode.find_main nodes 
             
         (* No main node found

            This only happens when there are no nodes in the input. *)
         with Not_found -> 

           raise (Invalid_argument "No main node defined in input"))

  in

  (* Put main node at the head of the list of nodes *)
  let nodes' = 

    try 

      (* Get main node by name and copy it at the head of the list of
         nodes *)
      N.node_of_name main_node nodes :: nodes

    with Not_found -> 

      (* Node with name of main not found 

         This can only happens when the name is passed as command-line
         argument *)
      raise (Invalid_argument "Main node not found")

  in

  (* Return a subsystem tree from the list of nodes *)
  N.subsystem_of_nodes nodes'
  

(* Open and parse from file *)
let of_file filename = 

    (* Open the given file for reading *)
    let use_file = open_in filename in
    let in_ch = use_file in

    of_channel in_ch

;;

of_file Sys.argv.(1)



(*
let rec input_system_of_declarations' accum nodes = function 

  | [] -> 

    (* Return system at the head of the accumulator *)
    (match accum with | [] -> assert false | (_, s) :: _ -> s)


  | node_name :: tl -> 

    (try 

       (* System for node has been created and added to accumulator
          meanwhile? *)
       let input_sys = List.assoc node_name accum in

       (* Continue with next node *)
       input_system_of_declarations' accum nodes tl

     (* System for node has not been created *)
     with Not_found -> 

       try 

         (* Get node of name *)
         let { N.calls } as node = 
           N.node_of_name node_name nodes 
         in

         (* Subnodes for which we have not created a system *)
         let tl' = 

           List.fold_left 
             (fun a { N.call_node_name } -> 

                if 

                  (* Transition system for node created? *)
                  List.mem_assoc call_node_name accum || 

                  (* Node already pushed to stack? *)
                  List.mem call_node_name a

                then 

                  (* Continue with stack unchanged *)
                  a

                else

                  (* Push node to top of stack *)
                  call_node_name :: a)

             []
             calls

         in

         (* Are there subnodes for which a transition system needs to be
            created first? *)
         match tl' with

           (* Some transitions systems of called nodes have not been
              created *)
           | _ :: _ -> 

             (* TODO: Check here that the call graph does not have
                cycles *)

             (* Recurse to create transition system for subnode, then
                return to this node *)
             input_system_of_declarations'
               accum
               nodes
               (tl' @ node_name :: tl)

           (* All transitions systems of called nodes have been
              created *)
           | [] ->

             let input_system = 
               { S.scope = [I.string_of_ident false node_name];
                 S.source = node; 
                 S.has_contract = N.has_contract node;
                 S.has_impl = N.has_impl node;
                 S.subsystems = 
                   List.map 
                     (fun { N.call_node_name } ->
                        try List.assoc call_node_name accum 
                        with Not_found -> assert false)
                     calls }
             in

             (* Recurse to create transition system for subnode, then
                return to this node *)
             input_system_of_declarations'
               ((node_name, input_system) :: accum)
               nodes
               tl

       (* All subnodes must be on the list, otherwise parsing has
          already failed *)
       with Not_found -> assert false)







  Format.printf 
    "@[<v>Before slicing@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes;

  let nodes_impl = LustreSlicing.slice_to_impl nodes in

  Format.printf 
    "@[<v>After slicing to implementation@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_impl;

  let nodes_contract = LustreSlicing.slice_to_contract nodes in

  Format.printf 
    "@[<v>After slicing to contract@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_contract;

  LustreTransSys.trans_sys_of_nodes nodes_contract nodes_impl;
  ()
*)


(*

  (* Consider only nodes called by main node *)
  let nodes_coi = 
    if keep_all_coi then 
      LustreSlicing.reduce_wo_coi (List.rev nodes) main_node
    else
      LustreNode.reduce_to_props_coi (List.rev nodes) main_node
  in

  debug lustreInput
    "@[<v>After slicing@,%a@]"
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_coi
  in
*)
(*
  (* Create transition system of Lustre nodes *)
  let fun_defs_init, fun_defs_trans, state_vars, init, trans, props = 
    LustreTransSys.trans_sys_of_nodes main_node nodes_coi
  in

  (* Extract properties from nodes *)
  let props = 
    LustreTransSys.props_of_nodes main_node nodes_coi
  in

  let trans_sys = 
 (* Create Kind transition system *)
    TransSys.mk_trans_sys 
      (List.combine fun_defs_init fun_defs_trans)
      state_vars
      init
      trans
      props
      (TransSys.Lustre nodes_coi)
  in
  *)
(*
  let trans_sys =
    LustreTransSys.trans_sys_of_nodes nodes_coi
  in

  (debug lustreInput 
      "%a"
      TransSys.pp_print_trans_sys trans_sys
   in

   Event.log
     L_info
     "Lustre main node is %a"
     (I.pp_print_ident false) main_node;
*)
(*
  Format.printf 
    "%a@."
    (pp_print_list 
       (fun ppf state_var -> 
          Format.fprintf ppf "%a=%a"
            StateVar.pp_print_state_var state_var
            LustreExpr.pp_print_state_var_source 
            (LustreExpr.get_state_var_source state_var))
       ",@ ")
    state_vars);
  trans_sys)

*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
