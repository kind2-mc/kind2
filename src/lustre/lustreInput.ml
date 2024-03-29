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
module LW = LustreWarnings

module LNG = LustreNodeGen
module LPI = LustreParser.Incremental
module LL = LustreLexer
module LPMI = LustreParser.MenhirInterpreter
module LPE = LustreParserErrors (* Auto-generated module at build time *)
module TC = LustreTypeChecker
module TCContext = TypeCheckerContext
module IC = LustreAstInlineConstants
module AD = LustreAstDependencies
module LAN = LustreAstNormalizer
module LS = LustreSyntaxChecks
module LIA = LustreAbstractInterpretation
module LDI = LustreDesugarIfBlocks
module LDF = LustreDesugarFrameBlocks
module RMA = LustreRemoveMultAssign
module LAD = LustreArrayDependencies
module LDN = LustreDesugarAnyOps
module LFR = LustreFlattenRefinementTypes
module LGI = LustreGenRefTypeImpNodes

type error = [
  | `LustreArrayDependencies of Lib.position * LustreArrayDependencies.error_kind
  | `LustreAstDependenciesError of Lib.position * LustreAstDependencies.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreAbstractInterpretationError of Lib.position * LustreAbstractInterpretation.error_kind
  | `LustreAstNormalizerError
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreUnguardedPreError of Lib.position * LustreAst.expr
  | `LustreParserError of Lib.position * string
  | `LustreDesugarIfBlocksError of Lib.position * LustreDesugarIfBlocks.error_kind
  | `LustreDesugarFrameBlocksError of Lib.position * LustreDesugarFrameBlocks.error_kind
]

let (let*) = Res.(>>=)
let (>>) = Res.(>>)

exception NoMainNode of string

(* The parser has succeeded and produced a semantic value.*)
let success (v : LustreAst.t): LustreAst.t =
  Debug.parse "Parsed :\n=========\n\n%a\n@." LA.pp_print_program v;
  v

(* Generates the appropriate parser error message *)
let build_parse_error_msg env =
  match LPMI.stack env with
  | lazy Nil -> None, "Syntax Error!"
  | lazy (Cons (LPMI.Element (state, _, _, p), _)) ->
    let pstate = LPMI.number state in
    let error_msg =
      try (LPE.message pstate)
      with Not_found -> "Syntax Error!"
    in
    Log.log L_debug "(Parser Error State: %d)" pstate;
    Some p, error_msg

(* Raises the [Parser_error] exception with appropriate position and error message *)
let fail env lexbuf =
  let pos, emsg = build_parse_error_msg env in
  let pos = match pos with
    | Some p -> position_of_lexing p
    | None -> position_of_lexing lexbuf.lex_curr_p
  in
  Error (`LustreParserError (pos, emsg))

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
  | LPMI.Accepted v -> Ok (success v)
  | LPMI.Rejected ->
    Error (`LustreParserError (Lib.dummy_pos, "Parser Error: Parser rejected the input."))
  

(* Parses input channel to generate an AST *)
let ast_of_channel(in_ch: in_channel) =

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
  | LustreLexer.Lexer_error err ->
    let pos = (Lib.position_of_lexing lexbuf.lex_curr_p) in
    Error (`LustreParserError (pos, err))

let type_check declarations =
  let tc_res = (
    (* Step 1. Basic syntax checks on declarations  *)
    let* warnings1, declarations = LS.syntax_check declarations in

    (* Step 2. Split program into top level const and type delcs, and node/contract decls *)
    let (const_type_decls, node_contract_src) = LH.split_program declarations in

    (* Step 3. Dependency analysis on the top level declarations.  *)
    let* sorted_const_type_decls = AD.sort_globals const_type_decls in
    
    (* Step 4. Type check top level declarations *)
    let* ctx, warnings2 = TC.type_check_infer_globals TCContext.empty_tc_context sorted_const_type_decls in

    (* Step 5: Inline type toplevel decls *)
    let* (inlined_ctx, const_inlined_type_and_consts) = IC.inline_constants ctx sorted_const_type_decls in
    
    (* Step 6. Desugar nondeterministic choice operators *)
    let node_contract_src = LDN.desugar_any_ops inlined_ctx node_contract_src in

    (* Step 7. Dependency analysis on nodes and contracts *)
    let* (sorted_node_contract_decls, toplevel_nodes, node_summary) = AD.sort_and_check_nodes_contracts node_contract_src in

    (* Step 8. Type check nodes and contracts *)
    let* global_ctx, warnings3 = TC.type_check_infer_nodes_and_contracts inlined_ctx sorted_node_contract_decls in

    (* Step 9. Flatten refinement types *)
    let sorted_node_contract_decls = LFR.flatten_ref_types global_ctx sorted_node_contract_decls in

    (* Step 10. Generate imported nodes associated with refinement types *)
    let sorted_node_contract_decls = LGI.gen_imp_nodes global_ctx sorted_node_contract_decls in

    (* Step 11. Remove multiple assignment from if blocks and frame blocks *)
    let sorted_node_contract_decls, gids = RMA.remove_mult_assign global_ctx sorted_node_contract_decls in

    (* Step 12. Desugar imperative if block to ITEs *)
    let* (sorted_node_contract_decls, gids) = (LDI.desugar_if_blocks global_ctx sorted_node_contract_decls gids) in

    (* Step 13. Desugar frame blocks by adding node equations and guarding oracles. *)
    let* (sorted_node_contract_decls, warnings4) = LDF.desugar_frame_blocks sorted_node_contract_decls in 

    (* Step 14. Inline constants in node equations *)
    let* (inlined_global_ctx, const_inlined_nodes_and_contracts) =
      IC.inline_constants global_ctx sorted_node_contract_decls
    in

    (* Step 15. Check that inductive array equations are well-founded *)
    let* _ = LAD.check_inductive_array_dependencies inlined_global_ctx node_summary const_inlined_nodes_and_contracts in

    (* Step 16. Infer tighter subrange constraints with abstract interpretation *)
    let* _ = LIA.interpret_global_consts inlined_global_ctx const_inlined_type_and_consts in
    let abstract_interp_ctx = LIA.interpret_program inlined_global_ctx gids const_inlined_nodes_and_contracts in

    (* Step 17. Normalize AST: guard pres, abstract to locals where appropriate *)
    let* (normalized_nodes_and_contracts, gids, warnings5) = 
      LAN.normalize inlined_global_ctx abstract_interp_ctx const_inlined_nodes_and_contracts gids
    in
    
    Res.ok (inlined_global_ctx,
      gids,
      const_inlined_type_and_consts @ normalized_nodes_and_contracts,
      toplevel_nodes,
      warnings1 @ warnings2 @ warnings3 @ warnings4 @ warnings5)
    )
  in
  match tc_res with
  | Error e -> Error e
  | Ok (c, g, d, toplevel, warnings) -> 
    let warnings = List.map (fun warning -> 
        if Flags.lus_strict () then (
          fail_at_position (LW.warning_position warning) (LW.warning_message warning)
        )
        else
          (warn_at_position (LW.warning_position warning) (LW.warning_message warning); Ok ())
    ) (LW.sort_warnings_by_pos warnings)
    in
    let warning = List.fold_left (>>) (Ok ()) warnings in
    Debug.parse "Type checking done";
    Debug.parse "========\n%a\n==========\n" LA.pp_print_program d;
    warning >> Ok (c, g, d, toplevel, warnings)
   (*  *)


let print_nodes_and_globals nodes globals =
  Debug.parse ("===============================================\n"
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
  (pp_print_list LustreNode.pp_print_state_var_instances_debug ";@ ") nodes
  (pp_print_list LustreNode.pp_print_state_var_defs_debug ";@ ") nodes
  (pp_print_list StateVar.pp_print_state_var_debug ";@ ")
    (nodes |> List.map (fun n -> LustreNode.get_all_state_vars n @ n.oracles)
      |> List.flatten)


(* Parse from input channel *)
let of_channel old_frontend only_parse in_ch =
  (* Get declarations from channel. *)
  let* declarations = ast_of_channel in_ch in

  (* Provide lsp info if option is enabled *)
  if Flags.log_format_json () && Flags.Lsp.lsp () then
    LspInfo.print_ast_info declarations;

  if old_frontend then
    Log.log L_note "Old front-end enabled" ;

  if only_parse then (
    if old_frontend then
      let _ = LD.declarations_to_nodes declarations in Ok None
    else
      match type_check declarations with
      | Ok _ -> Ok None
      | Error e -> Error e)
  else (
    let result =
      if old_frontend then
        (* Simplify declarations to a list of nodes *)
        let nodes, globals = LD.declarations_to_nodes declarations in
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
        Ok (nodes, globals, main_nodes)
      else
        let* (ctx, gids, decls, toplevel_nodes, _) = type_check declarations in
        let nodes, globals = LNG.compile ctx gids decls in
        let main_nodes = match Flags.lus_main () with
          | Some s -> 
            let s_ident = LustreIdent.mk_string_ident s in
            let main_lustre_node = LN.node_of_name s_ident nodes in
            if main_lustre_node.is_extern then 
            [s_ident] 
            (* If checking realizability and main node is not external (imported), then 
               we are actually checking realizability of Kind 2-generated imported nodes representing 
               the (1) the main node's contract instrumented with type info and 
                   (2) the main node's enviornment *)
            else [s_ident; 
                  LustreIdent.mk_string_ident (LGI.contract_tag ^ s);
                  LustreIdent.mk_string_ident (LGI.inputs_tag ^ s)]
          | None -> (
            match LustreNode.get_main_annotated_nodes nodes with
            | h :: t -> h :: t
            | [] ->
              match toplevel_nodes with
              | [] -> raise (NoMainNode "No node defined in input model")
              | _ -> toplevel_nodes |> List.map (fun s ->
                s |> HString.string_of_hstring |> LustreIdent.mk_string_ident)
          )
        in
        Ok (nodes, globals, main_nodes)
    in

    match result with
    | Ok (nodes, globals, main_nodes) ->
      (* Check that main nodes all exist *)
      main_nodes |> List.iter (fun mn ->
        if not (LN.exists_node_of_name mn nodes) then
          (* This can only happen when the name is passed as command-line argument *)
          let msg =
            Format.asprintf "Main node '%a' not found in input"
              (LustreIdent.pp_print_ident false) mn
          in
          raise (NoMainNode msg)
      ) ;
      let nodes = List.map (fun ({ LustreNode.name } as n) ->
          if List.exists (fun id -> LustreIdent.equal id name) main_nodes then
            { n with is_main = true }
          else n)
        nodes
      in
      print_nodes_and_globals nodes globals;

      (* Return a subsystem tree from the list of nodes *)
      Ok (Some (LN.subsystems_of_nodes main_nodes nodes, globals, declarations))
    | Error e -> Error e)


(* Returns the AST from a file. *)
let ast_of_file filename =
  (* Open the given file for reading *)
  let in_ch = match filename with
    | "" -> stdin
    | _ -> open_in filename
  in
  ast_of_channel in_ch


(* Open and parse from file *)
let of_file ?(old_frontend = Flags.old_frontend ()) only_parse filename =
  (* Open the given file for reading *)
  let in_ch = match filename with
    | "" -> stdin
    | _ -> open_in filename
  in
  of_channel old_frontend only_parse in_ch


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
