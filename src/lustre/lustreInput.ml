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
   
module LA = LustreAst
module LH = LustreAstHelpers
module LN = LustreNode
module LG = LustreGlobals
module LW = LustreWarnings
module NI = NodeId

module LNG = LustreNodeGen
module LPI = LustreParser.Incremental
module LL = LustreLexer
module LPMI = LustreParser.MenhirInterpreter
module TC = LustreTypeChecker
module TCContext = TypeCheckerContext
module IC = LustreAstInlineConstants
module AD = LustreAstDependencies
module LAN = LustreAstNormalizer
module LS = LustreSyntaxChecks
module LDI = LustreDesugarIfBlocks
module LDF = LustreDesugarFrameBlocks
module RMA = LustreRemoveMultAssign
module LAD = LustreArrayDependencies
module LGN = LustreGenNodes 
module LFR = LustreFlattenRefinementTypes
module LGI = LustreGenRefTypeImpNodes
module LIP = LustreInstantiatePolyNodes
module LUF = LustreUserFunctions
module LCF = LustreConstantsToFunctions
module GI = GeneratedIdentifiers

type error = [
  | `LustreArrayDependencies of Lib.position * LustreArrayDependencies.error_kind
  | `LustreAstDependenciesError of Lib.position * LustreAstDependencies.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind
  | `LustreAstNormalizerError
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreUnguardedPreError of Lib.position * LustreAst.expr
  | `LustreParserError of Lib.position * string
  | `LustreDesugarIfBlocksError of Lib.position * LustreDesugarIfBlocks.error_kind
  | `LustreConstantsToFunctionsError of Lib.position * LustreConstantsToFunctions.error_kind
  | `LustreGenRefTypeImpNodesError of Lib.position * LustreGenRefTypeImpNodes.error_kind
  | `LustreDesugarFrameBlocksError of Lib.position * LustreDesugarFrameBlocks.error_kind
]

let (let*) = Res.(>>=)
let (>>) = Res.(>>)

exception NoMainNode of string
exception MainTypeWithoutRealizability of string

(* The parser has succeeded and produced a semantic value.*)
let success (v : LustreAst.t): LustreAst.t =
  Debug.parse "Parsed :\n=========\n\n%a\n@." LA.pp_print_program v;
  v

(* Generates the appropriate parser error message *)
let build_parse_error_msg env =
  match LPMI.top env with
  | None -> None, "Syntax Error!"
  | Some (LPMI.Element (state, _, _, p)) ->
    let pstate = LPMI.number state in
    let error_msg = "Syntax Error!" in
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

let fail_or_warn warning =
  if Flags.lus_strict () && LW.error_if_lus_strict warning then (
    fail_at_position (LW.warning_position warning) (LW.warning_message warning)
  )
  else
    (warn_at_position (LW.warning_position warning) (LW.warning_message warning); Ok ())

let type_check declarations =
  let tc_res = (
    (* Step 1. Basic syntax checks on declarations  *)
    let* warnings1, declarations = LS.syntax_check declarations in

    (* Step 2. Split program into top level const and type decls, and node/contract decls *)
    let (const_type_decls, node_contract_src) = LH.split_program declarations in

    (* Step 3. Dependency analysis on the top level declarations.  *)
    let* sorted_const_type_decls = AD.sort_globals const_type_decls in
   
    (* Step 4. Type check top level declarations *)
    let* sorted_const_type_decls, ctx, warnings2 = TC.type_check_infer_globals TCContext.empty_tc_context sorted_const_type_decls in

    (* Step 5: Inline type toplevel decls *)
    let* (inlined_ctx, const_inlined_type_and_consts) = IC.inline_constants ctx sorted_const_type_decls in

    (* Step 6. Desugar nondeterministic choice operators *)
    let node_contract_src = LGN.gen_nodes inlined_ctx node_contract_src in

    (* Step 7. Dependency analysis on nodes and contracts *)
    let* (sorted_node_contract_decls, toplevel_nodes, scc_map, node_summary) =
      AD.sort_and_check_nodes_contracts node_contract_src
    in

    (* Step 8. Type check nodes and contracts *)
    let* global_ctx, sorted_node_contract_decls, warnings3 = TC.type_check_infer_nodes_and_contracts inlined_ctx sorted_node_contract_decls in

    (* Provide lsp info if option is enabled *)
    if Flags.log_format_json () && Flags.Lsp.lsp () then
      LspInfo.print_ast_info global_ctx declarations;

    (* Step 9. Generate imported nodes associated with refinement types if realizability checking is enabled *)
    let* sorted_node_contract_decls, global_ctx, gids = 
      if List.mem `CONTRACTCK (Flags.enabled ()) 
      then 
        let* decls1, ctx1, gids1 = LGI.gen_imp_nodes global_ctx const_inlined_type_and_consts in 
        let* decls2, ctx2, gids2 = LGI.gen_imp_nodes global_ctx sorted_node_contract_decls in
        Res.ok (
          decls1 @ decls2, 
          TypeCheckerContext.union ctx1 ctx2, 
          NodeId.Map.merge GI.union_keys2 gids1 gids2
        )
      else Res.ok (sorted_node_contract_decls, global_ctx, NodeId.Map.empty)
    in

    (* Step 10. Remove multiple assignment from if blocks and frame blocks *)
    let sorted_node_contract_decls, gids = RMA.remove_mult_assign global_ctx gids sorted_node_contract_decls in

    (* Step 11. Desugar imperative if block to ITEs *)
    let* (sorted_node_contract_decls, gids) = (LDI.desugar_if_blocks global_ctx sorted_node_contract_decls gids) in

    (* Step 12. Desugar frame blocks by adding node equations and guarding oracles. *)
    let* (sorted_node_contract_decls, warnings4) = LDF.desugar_frame_blocks sorted_node_contract_decls in

    (* Step 13. Inline constants in node equations *)
    let* (inlined_global_ctx, const_inlined_nodes_and_contracts) =
      IC.inline_constants global_ctx sorted_node_contract_decls
    in

    (* Step 14. Check that inductive array equations are well-founded *)
    let* _ = LAD.check_inductive_array_dependencies inlined_global_ctx node_summary const_inlined_nodes_and_contracts in

    (* Step 15. Instantiate polymorphic nodes with concrete types *)
    let inlined_global_ctx, gids, const_inlined_nodes_and_contracts = LIP.instantiate_polymorphic_nodes inlined_global_ctx gids const_inlined_nodes_and_contracts in

    (* Step 16. Flatten refinement types *)
    let const_inlined_type_and_consts, gids = LFR.flatten_ref_types inlined_global_ctx gids const_inlined_type_and_consts in
    let const_inlined_nodes_and_contracts, gids = LFR.flatten_ref_types inlined_global_ctx gids const_inlined_nodes_and_contracts in

    (* Step 17. Check no quantified variable in argument of non-inlinable function *)
    let inlinable_funcs =
      LUF.inlinable_functions inlined_global_ctx const_inlined_nodes_and_contracts
    in
    let* warnings5 =
      LS.no_quant_vars_in_calls_to_non_inlinable_funcs inlined_global_ctx inlinable_funcs declarations
    in

    (* Step 18. Convert free constants to functions without args *)
    let const_inlined_type_and_consts, new_func_ids, inlined_global_ctx = 
      LCF.gen_const_functions inlined_global_ctx const_inlined_type_and_consts in
    let* const_inlined_type_and_consts = 
      LCF.constants_to_calls new_func_ids const_inlined_type_and_consts in
    let* const_inlined_nodes_and_contracts = 
      LCF.constants_to_calls new_func_ids const_inlined_nodes_and_contracts
    in

    (* Step 19. Normalize AST: guard pres, abstract to locals where appropriate *)
    let* (normalized_decls, gids, warnings6) =
      LAN.normalize inlined_global_ctx inlinable_funcs 
                    (const_inlined_type_and_consts @ const_inlined_nodes_and_contracts) gids
    in

    Res.ok (inlined_global_ctx,
      gids,
      normalized_decls,
      toplevel_nodes,
      scc_map,
      warnings1 @ warnings2 @ warnings3 @ warnings4 @ warnings5 @ warnings6)
    )
  in
  match tc_res with
  | Error e -> Error e
  | Ok (c, g, d, toplevel, scc_map, warnings) -> 
    let warnings =
      List.map
        (fun warning -> fail_or_warn warning)
        (LW.sort_warnings_by_pos warnings)
    in
    let warning = List.fold_left (>>) (Ok ()) warnings in
    Debug.parse "Type checking done";
    Debug.parse "========\n%a\n==========\n" LA.pp_print_program d;
    warning >> Ok (c, g, d, toplevel, scc_map, warnings)
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
    (fun ppf (id, vt, _) ->
      pp_print_pair
        (LustreIdent.pp_print_ident true)
        (LustreIndex.pp_print_index_trie true Var.pp_print_var)
        " = "
        ppf
        (id, vt))
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
let of_channel only_parse in_ch =
  (* Get declarations from channel. *)
  let* declarations = ast_of_channel in_ch in

  if only_parse then (
    match type_check declarations with
    | Ok _ -> Ok None
    | Error e -> Error e
  )
  else (
    let result =
      let* (ctx, gids, decls, toplevel_nodes, scc_map, _) =
        type_check declarations
      in
      let nodes, globals = LNG.compile ctx gids scc_map decls in
      let contractck_enabled = List.mem `CONTRACTCK (Flags.enabled ()) in
      let main_nodes = match Flags.lus_main () with
        | Some s -> 
          let s_ident = LustreIdent.mk_string_ident s in (
          try
            let node_id = NI.mk_node_id ~node_type:Component (HString.mk_hstring s) in
            let main_lustre_node =  LN.node_of_node_id node_id nodes in 
            (* If checking realizability, then 
              we are actually checking realizability of Kind 2-generated imported nodes representing 
              the (1) the main node's contract instrumented with type info and 
                  (2) the main node's enviornment, if environment checking is enabled *)
            let main_nodes = 
              if (not main_lustre_node.is_extern) && contractck_enabled then 
                let node_id = NI.mk_node_id ~node_type:Contract (HString.mk_hstring s) in 
                let _ = LN.node_of_node_id node_id nodes in
                [node_id]
              else [node_id] 
            in
            let main_nodes = 
              if (Flags.Contracts.check_environment ()) && contractck_enabled then
                let node_id = NI.mk_node_id ~node_type:Environment (HString.mk_hstring s) in 
                let _ = LN.node_of_node_id node_id nodes in
                node_id :: main_nodes 
              else 
                main_nodes 
              in 
            main_nodes
          (* User-specified main node in command-line input might not exist *)
          with Not_found -> 
            let msg =
              Format.asprintf "Main node '%a' not found in input"
                (LustreIdent.pp_print_ident false) s_ident
            in
            raise (NoMainNode msg)
        )
        | None -> (
          match contractck_enabled, Flags.lus_main_const (), Flags.lus_main_type () with
          | true, None, None
          | false, None, _ -> (
            match LustreNode.get_main_annotated_nodes nodes with
            | (_ :: _ as node_names) -> node_names
            | [] ->
              match toplevel_nodes with
              | [] -> raise (NoMainNode "No node defined in input model")
              | _ -> toplevel_nodes |> List.map (fun s -> NI.mk_node_id s)
          )
          | _ -> []
        )
      in
      let main_nodes = match Flags.lus_main_const () with
        | Some s ->
          let s_ident = LustreIdent.mk_string_ident s in (
          try 
            let node_id =
              if contractck_enabled then
                (* Constants with definitions are treated as free constants
                   when checking realizability. *)
                NI.mk_node_id ~node_type:FreeConstant (HString.mk_hstring s)
              else
                NI.mk_node_id ~node_type:DefinedConstant (HString.mk_hstring s)
            in
            let _ = LN.node_of_node_id node_id nodes in
            node_id :: main_nodes
          (* User-specified main constant in command-line input might not exist *)
          with Not_found -> 
            let msg =
              Format.asprintf "No %s '%a' found in input"
                (if contractck_enabled then "free constant" else "defined constant")
                (LustreIdent.pp_print_ident false) s_ident
            in
            raise (NoMainNode msg)
          )
        | None -> (
          match contractck_enabled, Flags.lus_main (), Flags.lus_main_type () with
          | true, None, None -> (
            List.fold_left (fun acc n ->
              if NI.get_node_type n.LustreNode.node_id = FreeConstant then
                n.LustreNode.node_id :: acc
              else acc
            ) main_nodes nodes
          )
          | false, None, _ -> (
            List.fold_left (fun acc n ->
              if NI.get_node_type n.LustreNode.node_id = DefinedConstant then
                n.LustreNode.node_id :: acc
              else acc
            ) main_nodes nodes
          )
          | _ -> main_nodes
        )
      in
      let main_nodes = match Flags.lus_main_type () with
        | Some s -> 
          let s_ident = LustreIdent.mk_string_ident s in 
          if not contractck_enabled then
            let msg =
              Format.asprintf "Option --lus_main_type can only be used when realizability checking is enabled (--enable CONTRACTCK)"
            in
            raise (MainTypeWithoutRealizability msg)
          else (
            try 
              let node_id = NI.mk_node_id ~node_type:Type (HString.mk_hstring s) in
              let _ = LN.node_of_node_id node_id nodes in
              node_id :: main_nodes
            (* User-specified type alias in command-line input might not exist *)
            with Not_found -> 
              let msg =
                Format.asprintf "No refinement type with alias '%a' found in input"
                  (LustreIdent.pp_print_ident false) s_ident
              in
              raise (NoMainNode msg)
          )
        | None -> main_nodes
      in
      Ok (nodes, globals, main_nodes)
    in

    match result with
    | Ok (nodes, globals, main_nodes) ->
      let nodes = List.map (fun ({ LustreNode.node_id = id1; } as n) ->
          if List.exists (fun id2 -> NI.equal id1 id2) main_nodes then
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
let of_file only_parse filename =
  (* Open the given file for reading *)
  let in_ch = match filename with
    | "" -> stdin
    | _ -> open_in filename
  in
  of_channel only_parse in_ch


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
