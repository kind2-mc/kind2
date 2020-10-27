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
module LH = LustreAstHelpers
module LN = LustreNode
module LC = LustreContext
module LD = LustreDeclarations

module LPI = LustreParser.Incremental
module LL = LustreLexer          
module LPMI = LustreParser.MenhirInterpreter
module LPE = LustreParserErrors
module TC = LustreTypeChecker
module IC = LustreAstInlineConstants
module AD = LustreAstDependencies

let (>>=) = Res.(>>=)
let (>>) = Res.(>>)
          
exception NoMainNode of string

(* The parser has succeeded and produced a semantic value.*)
let success (v : LustreAst.t): LustreAst.t =
  Log.log L_trace "Parsed :\n=========\n\n%a\n@." LA.pp_print_program v;
  v

(* Generates the appropriate parser error message *)
let build_parse_error_msg env =
    match LPMI.stack env with
    | lazy Nil -> "Syntax Error"
    | lazy (Cons (LPMI.Element (state, _, _, _), _)) ->
       let pstate = LPMI.number state in
       let error_msg = try (LPE.message pstate) with
                       | Not_found -> "Syntax Error! " 
                                      ^ "Please report this issue with a minimum working example." in
       Log.log L_debug "(Parser Error State: %d)" pstate;
       error_msg
                                     

(* Raises the [Parser_error] exception with appropriate position and error message *)
let fail env lexbuf =
  let emsg = build_parse_error_msg env in
  let pos = position_of_lexing lexbuf.lex_curr_p in
  LC.fail_at_position pos emsg

(* Incremental Parsing *)
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
     LC.fail_no_position "Parser Error: Parser rejected the input."
  

(* Parses input channel to generate an AST *)
let ast_of_channel(in_ch: in_channel): LustreAst.t =

  let input_source = Flags.input_file () in
  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init 
    in_ch
    (try Filename.dirname (input_source)
     with Failure _ -> Sys.getcwd ());

  (* Set the relative file name in lex buffer *)
  (* Lib.set_lexer_filename lexbuf (input_source); *)
  (* Setting the name in the lexer buffer causes issues with the way we display properties.
   * For the time being we would not want to change this behaviour *)

  (* Create lexing buffer and incrementally parse it*)
  try
    (parse lexbuf (LPI.main lexbuf.lex_curr_p))
  with
  | LustreLexer.Lexer_error err -> LC.fail_at_position (Lib.position_of_lexing lexbuf.lex_curr_p) err  

(* Parse from input channel *)
let of_channel in_ch =
  (* Get declarations from channel. *)
  let declarations = ast_of_channel in_ch in

  let declarations': LA.t =
    (* optional type checking and reordering with dependency analysis pass*) 
    if Flags.no_tc ()
     then declarations
     else 
       let tc_res =  
         (Log.log L_note "(Experimental) Typechecking enabled."

         (* Step 0. Split program into top level const and type delcs, and node/contract decls *)
         ; let (const_type_decls, node_contract_src) = LH.split_program declarations in

           (* Step 1. Dependency analysis on the top level declarations.  *)
           AD.sort_declarations const_type_decls >>= fun sorted_const_type_decls ->

           (* Step 2. Type check top level declarations *)
           TC.type_check_infer_program TC.Constants_and_types TC.empty_tc_context sorted_const_type_decls >>= fun ctx -> 

           (* Step 3: Inline type toplevel decls *)
           IC.inline_constants ctx sorted_const_type_decls >>= fun (inlined_ctx, const_inlined_type_and_consts) -> 

           (* Step 4. Dependency analysis on nodes and contracts *)
           AD.sort_declarations node_contract_src >>= fun sorted_node_contract_decls ->  

           (* Step 5. type check nodes and contracts *)
           TC.type_check_infer_program TC.Nodes_and_contracts inlined_ctx sorted_node_contract_decls >>
             
             (* Step 6. Inline constants in node equations *)
             IC.inline_constants ctx sorted_node_contract_decls >>= fun (_, const_inlined_nodes_and_contracts) ->
           
           (* The last node in the original ordering should remain the last node after sorting 
              as the user expects that to be the main node in the case where 
              no explicit annotations are provided. The reason we do this is because 
              it is difficut to make the topological sort stable *)
           
           (* reverse the list and find the name of the first node declaration from the original list *)
           let last_node = LH.get_last_node_name (declarations) in
           (match last_node with
           | None -> Res.ok (const_inlined_type_and_consts @ const_inlined_nodes_and_contracts)
           | Some ln ->
              Log.log L_trace "last node is: %a"  LA.pp_print_ident ln 
             ; Res.ok (const_inlined_type_and_consts
                                @ LH.move_node_to_last ln (const_inlined_nodes_and_contracts))) 
         ) in
       match tc_res with
       | Ok d -> Log.log L_note "Type checking done"
               ; Log.log L_trace "========\n%a\n==========\n" LA.pp_print_program d
               ; d  
       | Error (pos, err) -> LC.fail_at_position pos err in 

  (if Flags.only_tc () then exit 0)

  
  (* Simplify declarations to a list of nodes *)
  ; let nodes, globals = LD.declarations_to_nodes declarations' in
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
            raise (NoMainNode "No main node defined in input"))
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
        raise (NoMainNode "Main node not found in input")
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
