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

module A = LustreAst
module I = LustreIdent
module N = LustreNode
module C = LustreContext
module D = LustreDeclarations
module S = SubSystem


(* Constructs an AST from an input channel. *)
let ast_of_channel in_ch =

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init 
    in_ch
    (try Filename.dirname (Flags.input_file ())
     with Failure _ -> Sys.getcwd ());

  try
    (* Parse file to list of declarations *)
    LustreParser.main LustreLexer.token lexbuf 
  with
  | LustreParser.Error ->
    let lexer_pos = Lexing.lexeme_start_p lexbuf in
    C.fail_at_position (position_of_lexing lexer_pos) "Syntax error"
  | LustreLexer.Lexer_error msg ->
    let lexer_pos = Lexing.lexeme_start_p lexbuf in
    C.fail_at_position (position_of_lexing lexer_pos) msg


(* Parse from input channel *)
let of_channel in_ch =

  (* Get declarations from channel. *)
  let declarations = ast_of_channel in_ch in

  (* Format.printf "Parsed :\n=========\n\n%a\n@." *)
  (*   LustreAst.pp_print_program declarations ; *)
  (* failwith "stop" ; *)

  (* Simplify declarations to a list of nodes *)
  let nodes, globals = D.declarations_to_nodes declarations in

  (* Name of main node *)
  let main_node = 

    (* Command-line flag for main node given? *)
    match Flags.lus_main () with 
      
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
  N.subsystem_of_nodes nodes', globals


(* Returns the AST from a file. *)
let ast_of_file filename =

  (* Open the given file for reading *)
  let in_ch = match filename with
    | "" -> stdin
    | _ -> open_in filename
  in

  ast_of_channel in_ch


(* Open and parse from file *)
let of_file filename =

  (* Open the given file for reading *)
  let in_ch = match filename with
    | "" -> stdin
    | _ -> open_in filename
  in

  of_channel in_ch


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
