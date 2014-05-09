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



(* Parse from input channel *)
let of_channel in_ch = 

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init in_ch (Filename.dirname (Flags.input_file ()));

  (* Lustre file is a list of declarations *)
  let declarations = 

    try 

      (* Parse file to list of declarations *)
      LustreParser.main LustreLexer.token lexbuf 

    with 

      | LustreParser.Error ->

        let 
          { Lexing.pos_fname; 
            Lexing.pos_lnum; 
            Lexing.pos_bol; 
            Lexing.pos_cnum } = 
          Lexing.lexeme_start_p lexbuf 
        in

        Format.printf 
          "Syntax error in line %d at column %d in %s: %s@." 
          pos_lnum
          (pos_cnum - pos_bol)
          pos_fname
          (Lexing.lexeme lexbuf);

        exit 1

  in

  (* Simplify declarations to a list of nodes *)
  let nodes = LustreSimplify.declarations_to_nodes declarations in
  
  (* Find main node by annotation *)
  let main_node = 

    match Flags.lustre_main () with 

      | None -> 

        (try 
          
          LustreNode.find_main nodes 
            
        with Not_found -> 
          
          raise (Invalid_argument "No main node defined in input"))

      | Some s -> LustreIdent.mk_string_ident s

  in

  debug lustreInput
    "@[<v>Before slicing@,%a@]"
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes
  in

  (* Consider only nodes called by main node

     TODO: ordering the equations by dependency may be redundant here,
     if the COI reduction preserves the order *)
  let nodes_coi = 
    List.map
      (LustreNode.equations_order_by_dep nodes)
      (LustreNode.reduce_to_property_coi nodes main_node) 
  in

  debug lustreInput
    "@[<v>After slicing@,%a@]"
    (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_coi
  in

  (* Create transition system of Lustre nodes

     TODO: Split definitions into init and trans part *)
  let fun_defs, state_vars, init, trans = 
    LustreTransSys.trans_sys_of_nodes nodes_coi
  in

  (* Extract properties from nodes *)
  let props = 
    LustreTransSys.props_of_nodes main_node nodes_coi
  in
    

  (* Create Kind transition system *)
  let trans_sys = 
    TransSys.mk_trans_sys 
      fun_defs
      state_vars
      init
      trans
      props
  in

  debug lustreInput 
      "%a"
      TransSys.pp_print_trans_sys trans_sys
  in

  trans_sys


(* Open and parse from file *)
let of_file filename = 

    (* Open the given file for reading *)
    let use_file = open_in filename in
    let in_ch = use_file in

    of_channel in_ch


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
