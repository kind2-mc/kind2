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
open LustreReporting
open Lexing
open MenhirLib.General
   
module LA = LustreAst
module LH = LustreAstHelpers
module LN = LustreNode
module LG = LustreGlobals
module LD = LustreDeclarations

module LNG = LustreNodeGen
module LPI = LustreParser.Incremental
module LL = LustreLexer          
module LPMI = LustreParser.MenhirInterpreter
module LPE = LustreParserErrors
module TC = LustreTypeChecker
module TCContext = TypeCheckerContext
module IC = LustreAstInlineConstants
module AD = LustreAstDependencies
module LAN = LustreAstNormalizer
module LS = LustreSyntaxChecks

let (>>=) = Res.(>>=)
          
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
  fail_at_position pos emsg

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
     fail_no_position "Parser Error: Parser rejected the input."
  

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

  (* Set the main file input in lex buffer.
     Currently the input value is blindly copied *)
  Lib.set_lexer_filename lexbuf (input_source);

  (* Create lexing buffer and incrementally parse it*)
  try
    (parse lexbuf (LPI.main lexbuf.lex_curr_p))
  with
  | LustreLexer.Lexer_error err -> fail_at_position (Lib.position_of_lexing lexbuf.lex_curr_p) err  

let type_check declarations =
  let tc_res =
    (Log.log L_note "(Experimental) Typechecking enabled.";

    (* Step 1. Basic syntax checks on declarations  *)
    LS.syntax_check declarations >>= fun declarations ->

    (* Step 2. Split program into top level const and type delcs, and node/contract decls *)
    let (const_type_decls, node_contract_src) = LH.split_program declarations in

    (* Step 3. Dependency analysis on the top level declarations.  *)
    AD.sort_globals const_type_decls >>= fun sorted_const_type_decls ->

    (* Step 4. Type check top level declarations *)
    TC.type_check_infer_globals TCContext.empty_tc_context sorted_const_type_decls >>= fun ctx ->

    (* Step 5: Inline type toplevel decls *)
    IC.inline_constants ctx sorted_const_type_decls >>= fun (inlined_ctx, const_inlined_type_and_consts) ->

    (* Step 6. Dependency analysis on nodes and contracts *)
    AD.sort_and_check_nodes_contracts node_contract_src >>= fun sorted_node_contract_decls ->

    (* Step 7. type check nodes and contracts *)
    TC.type_check_infer_nodes_and_contracts inlined_ctx sorted_node_contract_decls >>= fun (global_ctx) ->

    (* Step 8. Inline constants in node equations *)
    IC.inline_constants global_ctx sorted_node_contract_decls >>= fun (inlined_global_ctx, const_inlined_nodes_and_contracts) ->

    (* Step 9. Normalize AST: guard pres, abstract to locals where appropriate *)
    LAN.normalize inlined_global_ctx const_inlined_nodes_and_contracts >>= fun (normalized_nodes_and_contracts, gids) ->

    Res.ok (inlined_global_ctx,
      gids,
      const_inlined_type_and_consts @ normalized_nodes_and_contracts)
    )
  in
  match tc_res with
  | Ok (c, g, d) ->
    let unguarded_pre_warnings = LAN.get_warnings g in
    let error_or_warn = if Flags.lus_strict ()
      then fail_at_position
      else warn_at_position
    in List.iter (fun (p, e) -> error_or_warn p
      (Format.asprintf
        "@[<hov 2>Unguarded pre in expression@ %a@]"
        LA.pp_print_expr e))
      unguarded_pre_warnings;
    Log.log L_note "Type checking done"
    ; Log.log L_trace "========\n%a\n==========\n" LA.pp_print_program d
    ; (c, g, d)
  | Error (pos, err) -> fail_at_position pos err


let print_nodes_and_globals nodes globals =
  Log.log L_trace ("===============================================\n"
  ^^ "Free Constants: [@[<hv>%a@]];@ \n\n"
  ^^ "State Variable Bounds: [@[<hv>%a@]];@ \n\n"
  ^^ "Nodes: [@[<hv>%a@]];@ \n\n"
  ^^ "State Var Instances: [@[<hv>%a@]];@ \n\n"
  ^^ "State Var Definitions: [@[<hv>%a@]];@ \n\n"
  ^^ "All State Variables: [@[<hv>%a@]];@ \n\n"
  ^^ "===============================================\n")
  (pp_print_list
    (pp_print_pair
      (LustreIdent.pp_print_ident true)
      (LustreIndex.pp_print_index_trie true Var.pp_print_var)
      " = ")
    ";@ ") globals.LG.free_constants
  (pp_print_list
    (pp_print_pair
      (StateVar.pp_print_state_var)
      (pp_print_list
        (LustreExpr.pp_print_bound_or_fixed)
        ";@ ")
      " = ")
    ";@ ")
    (StateVar.StateVarHashtbl.fold
      (fun k v acc -> (k, v) :: acc)
      globals.LG.state_var_bounds
      [])
  (pp_print_list LustreNode.pp_print_node_debug ";@ ") nodes
  (pp_print_list LustreNode.pp_print_state_var_instances_debug ";@") nodes
  (pp_print_list LustreNode.pp_print_state_var_defs_debug ";@") nodes
  (pp_print_list StateVar.pp_print_state_var_debug ";@")
    (nodes |> List.map (fun n -> LustreNode.get_all_state_vars n @ n.oracles)
      |> List.flatten)


(* Parse from input channel *)
let of_channel in_ch =
  (* Get declarations from channel. *)
  let declarations = ast_of_channel in_ch in

  (* Provide lsp info if option is enabled *)
  if Flags.log_format_json () && Flags.lsp () then
    LspInfo.print_ast_info declarations;

  let nodes, globals =
    if Flags.old_frontend () then
      (* Simplify declarations to a list of nodes *)
      LD.declarations_to_nodes declarations
    else 
      let ctx, gids, decls = type_check declarations in
      let nodes, globals = LNG.compile ctx gids decls in
      (* The last node in the original ordering should remain the last node after sorting 
      as the user expects that to be the main node in the case where 
      no explicit annotations are provided. The reason we do this is because 
      it is difficut to make the topological sort stable *)
      let last_node = LH.get_last_node_name (declarations) in
      let nodes = match last_node with
      | None -> nodes
      | Some ln -> let ident = LustreIdent.mk_string_ident ln in
        let n = LustreNode.node_of_name ident nodes in
        let filtered =
          List.filter
            (fun x -> not (LustreIdent.equal x.LustreNode.name ident))
            nodes
        in
        n :: filtered
      in
      nodes, globals
  in
  print_nodes_and_globals nodes globals;

  if Flags.only_parse () then (exit 0);
  (* Name of main node *)
  let main_nodes =
    (* Command-line flag for main node given? *)
    match Flags.lus_main () with
    (* Use given identifier to choose main node *)
    | Some s -> [LustreIdent.mk_string_ident s]
    (* No main node name given on command-line *)
    | None -> (
      try 
        (* Find main node by annotation, or take last node as main *)
        LustreNode.find_main nodes
      with Not_found ->
        (* No main node found
           This only happens when there are no nodes in the input. *)
        raise (NoMainNode "No main node defined in input"))
  in
  (* Check that main nodes all exist *)
  let _ =
    try
      List.map (fun mn -> LN.node_of_name mn nodes) main_nodes
    with Not_found ->
      (* Node with name of main not found
        This can only happen when the name is passed as command-line argument *)
      raise (NoMainNode "Main node not found in input")
  in
  (* Return a subsystem tree from the list of nodes *)
  LN.subsystems_of_nodes main_nodes nodes, globals, declarations


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
