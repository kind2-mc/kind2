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
open Lexing
open MenhirLib.General
   
module LA = LustreAst
module LI = LustreIdent
module LN = LustreNode
module LC = LustreContext
module LD = LustreDeclarations
module SS = SubSystem

module LPI = LustreParser.Incremental
module LL = LustreLexer          
module LPMI = LustreParser.MenhirInterpreter
module LPE = LustreParserErrors


let success (v : LustreAst.t): LustreAst.t =
  (* The parser has succeeded and produced a semantic value. Print it. *)
  (* TODO: Find a good way of logging switch to be enabled if asked for. something like kind2 --debug *)
  (* Format.printf "Parsed :\n=========\n\n%a\n@." LustreAst.pp_print_program v ; *)
  v

let get_lexing_position lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

  
let get_parse_error env =
    match LPMI.stack env with
    | lazy Nil -> "Invalid syntax"
    | lazy (Cons (LPMI.Element (state, _, _, _), _)) ->
        try (LPE.message (LPMI.number state)) with
        | Not_found -> "invalid syntax (no specific message for this eror)"

                     
let fail env lexbuf =
  let line, pos = get_lexing_position lexbuf in
  let err = get_parse_error env in
  (* Format.printf "At (line %d, columm %d), Syntax error: %s"
   *   line pos err *)
    raise (LA.Parser_error {position=Some (line, pos);err=err})
  
let rec parse lexbuf (chkpnt : LA.t LPMI.checkpoint) =
  match chkpnt with
  | LPMI.InputNeeded _ ->
     let token = LL.token lexbuf in
     let startp = lexbuf.lex_start_p
     and endp = lexbuf.lex_curr_p in
     let chkpnt = LPMI.offer chkpnt (token, startp, endp) in
     parse lexbuf chkpnt
  | LPMI.Shifting _
  | LPMI.AboutToReduce _ ->
     let chkpnt = LPMI.resume chkpnt in
     parse lexbuf chkpnt
  | LPMI.HandlingError env ->
     fail env lexbuf
  | LPMI.Accepted v -> success v
  | LPMI.Rejected ->
     raise (LA.Parser_error {position=None; err="invalid syntax (parser rejected the input)"})
  

(* Parses input channel to generate an AST *)
let ast_of_channel(in_ch: in_channel): LustreAst.t =
  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in
  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init 
    in_ch
    (try Filename.dirname (Flags.input_file ())
     with Failure _ -> Sys.getcwd ());

  (* Create lexing buffer *)
  parse lexbuf (LPI.main lexbuf.lex_curr_p)
         
(* Parse from input channel *)
let of_channel in_ch =
  (* Get declarations from channel. *)
  let declarations = ast_of_channel in_ch in
  (* Format.printf "Parsed :\n=========\n\n%a\n@."
   *   LustreAst.pp_print_program declarations ; *)
  (* Simplify declarations to a list of nodes *)
  let nodes, globals = LD.declarations_to_nodes declarations in

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
      LN.node_of_name main_node nodes :: nodes
    with Not_found -> 
      (* Node with name of main not found 
         This can only happens when the name is passed as command-line
         argument *)
      raise (Invalid_argument "Main node not found")
  in

  (* Return a subsystem tree from the list of nodes *)
  LN.subsystem_of_nodes nodes', globals, declarations


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
