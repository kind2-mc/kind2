(* This file is part of the Kind 2 model checker.

   Copyright (c) 2021 by the Board of Trustees of the University of Iowa

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
(** Check various syntactic properties that do not depend on type information
  
  @author Andrew Marmaduke *)

module LA = LustreAst
module LAH = LustreAstHelpers

module StringSet = Set.Make(
  struct
    let compare = HString.compare
    type t = HString.t
  end)

module StringMap = Map.Make(
  struct
    let compare = HString.compare
    type t = HString.t
  end)


type error_kind = Unknown of string
  | UndefinedLocal of HString.t
  | UndefinedNode of HString.t
  | DanglingIdentifier of HString.t
  | QuantifiedVariableInNodeArgument of HString.t * HString.t
  | SymbolicArrayIndexInNodeArgument of HString.t * HString.t
  | NodeCallInFunction of HString.t
  | NodeCallInRefinableContract of string * HString.t
  | IllegalTemporalOperator of string * string
  | IllegalImportOfStatefulContract of HString.t
  | UnsupportedClockedInputOrOutput
  | UnsupportedClockedLocal of HString.t
  | UnsupportedExpression of LustreAst.expr
  | UnsupportedOutsideMerge of LustreAst.expr
  | UnsupportedWhen of LustreAst.expr
  | UnsupportedParametricDeclaration
  | UnsupportedAssignment
  | AssumptionVariablesInContractNode
  | ClockMismatchInMerge

type error = [
  | `LustreSyntaxChecksError of Lib.position * error_kind
]

let error_message kind = match kind with
  | Unknown s -> s
  | UndefinedLocal id -> "Local variable '"
    ^ HString.string_of_hstring id ^ "' has no definition"
  | UndefinedNode id -> "Node or function '"
    ^ HString.string_of_hstring id ^ "' is undefined"
  | DanglingIdentifier id -> "Unknown identifier '"
    ^ HString.string_of_hstring id ^ "'"
  | QuantifiedVariableInNodeArgument (var, node) -> "Quantified variable '"
    ^ HString.string_of_hstring var ^ "' is not allowed in an argument to the node call '"
    ^ HString.string_of_hstring node ^ "'"
  | SymbolicArrayIndexInNodeArgument (idx, node) -> "Symbolic array index '"
    ^ HString.string_of_hstring idx ^ "' is not allowed in an argument to the node call '"
    ^ HString.string_of_hstring node ^ "'"
  | NodeCallInFunction node -> "Illegal call to node '"
    ^ HString.string_of_hstring node ^ "', functions can only call other functions, not nodes"
  | NodeCallInRefinableContract (kind, node) -> "Illegal call to " ^ kind ^ " '"
    ^ HString.string_of_hstring node ^ "' in the cone of influence of this contract: " ^ kind ^ " "
    ^ HString.string_of_hstring node ^ " has a refinable contract"
  | IllegalTemporalOperator (kind, variant) -> "Illegal " ^ kind ^ " in " ^ variant ^ " definition, "
    ^ variant ^ "s cannot have state"
  | IllegalImportOfStatefulContract contract -> "Illegal import of stateful contract '"
    ^ HString.string_of_hstring contract ^ "'. Functions can only be specified by stateless contracts"
  | UnsupportedClockedInputOrOutput -> "Clocked inputs or outputs are not supported"
  | UnsupportedClockedLocal id -> "Clocked node local variable not supported for '" ^ HString.string_of_hstring id ^ "'"
  | UnsupportedExpression e -> "The expression '" ^ LA.string_of_expr e ^ "' is not supported"
  | UnsupportedOutsideMerge e -> "The expression '" ^ LA.string_of_expr e ^ "' is only supported inside a merge"
  | UnsupportedWhen e -> "The `when` expression '" ^ LA.string_of_expr e ^ "' can only be the top most expression of a merge case"
  | UnsupportedParametricDeclaration -> "Parametric nodes and functions are not supported"
  | UnsupportedAssignment -> "Assignment not supported"
  | AssumptionVariablesInContractNode -> "Assumption variables not supported in contract nodes"
  | ClockMismatchInMerge -> "Clock mismatch for argument of merge"

let syntax_error pos kind = Error (`LustreSyntaxChecksError (pos, kind))

let (let*) = Result.bind
let (>>) = fun a b -> let* _ = a in b

type node_data = {
  has_contract: bool;
  imported: bool;
  contract_only_assumptive: bool;
  contract_imports: StringSet.t }

type contract_data = {
  stateful: bool;
  only_assumptive: bool;
  imports: StringSet.t }

type context = {
  nodes : node_data StringMap.t;
  functions : node_data StringMap.t;
  contracts : contract_data StringMap.t;
  free_consts : LustreAst.lustre_type option StringMap.t;
  consts : LustreAst.lustre_type option StringMap.t;
  locals : LustreAst.lustre_type option StringMap.t;
  quant_vars : LustreAst.lustre_type option StringMap.t;
  array_indices : LustreAst.lustre_type option StringMap.t;
  symbolic_array_indices : LustreAst.lustre_type option StringMap.t; }

let empty_ctx () = {
    nodes = StringMap.empty;
    functions = StringMap.empty;
    contracts = StringMap.empty;
    free_consts = StringMap.empty;
    consts = StringMap.empty;
    locals = StringMap.empty;
    quant_vars = StringMap.empty;
    array_indices = StringMap.empty;
    symbolic_array_indices = StringMap.empty;
  }

let ctx_add_node ctx i ty = {
    ctx with nodes = StringMap.add i ty ctx.nodes
  }

let ctx_add_contract ctx i ty = {
    ctx with contracts = StringMap.add i ty ctx.contracts
  }

let ctx_add_func ctx i ty = {
    ctx with functions = StringMap.add i ty ctx.functions
  }

let ctx_add_free_const ctx i ty = {
    ctx with free_consts = StringMap.add i ty ctx.free_consts
  }

let ctx_add_const ctx i ty = {
    ctx with consts = StringMap.add i ty ctx.consts
  }

let ctx_add_local ctx i ty = {
    ctx with locals = StringMap.add i ty ctx.locals
  }

let ctx_add_quant_var ctx i ty = {
    ctx with quant_vars = StringMap.add i ty ctx.quant_vars
  }

let ctx_add_array_index ctx i ty = {
    ctx with array_indices = StringMap.add i ty ctx.array_indices
  }

let ctx_add_symbolic_array_index ctx i ty = {
    ctx with symbolic_array_indices = StringMap.add i ty ctx.symbolic_array_indices
  }

let build_global_ctx (decls:LustreAst.t) =
  let get_imports = function
    | Some eqns -> List.fold_left (fun a e -> match e with
      | LA.ContractCall (_, i, _, _) -> StringSet.add i a
      | _ -> a)
      StringSet.empty eqns
    | None -> StringSet.empty
  in
  let is_only_assumptive = function
    | Some eqns -> List.fold_left (fun a e -> match e with
      | LA.Guarantee _ -> false && a
      | Mode _ -> false && a
      | _ -> a)
      true eqns
    | None -> false
  in
  let over_decls acc = function
    | LA.TypeDecl (_, AliasType (_, _, (EnumType (_, _, variants) as ty))) -> 
      List.fold_left (fun a v -> ctx_add_const a v (Some ty)) acc variants
    | ConstDecl (_, FreeConst (_, i, ty)) -> ctx_add_free_const acc i (Some ty)
    | ConstDecl (_, UntypedConst (_, i, _)) -> ctx_add_const acc i None
    | ConstDecl (_, TypedConst (_, i, _, ty)) -> ctx_add_const acc i (Some ty)
    (* The types here can be constructed from the available information
      but this type information is not needed for syntax checks for now *)
    | NodeDecl (_, (i, imported, _, _, _, _, _, c)) ->
      let has_contract = match c with | Some _ -> true | None -> false in
      let contract_only_assumptive = is_only_assumptive c in
      let contract_imports = get_imports c in
      let data = { has_contract; 
        imported; 
        contract_only_assumptive;
        contract_imports }
      in
      ctx_add_node acc i data
    | FuncDecl (_, (i, imported, _, _, _, _, _, c)) -> 
      let has_contract = match c with | Some _ -> true | None -> false in
      let contract_only_assumptive = is_only_assumptive c in
      let contract_imports = get_imports c in
      let data = { has_contract;
        imported;
        contract_only_assumptive;
        contract_imports }
      in
      ctx_add_func acc i data
    | ContractNodeDecl (_, (i, _, _, _, eqns)) ->
      let stateful = match LAH.contract_has_pre_or_arrow eqns with
        | Some _ -> true
        | None -> false
      in
      let only_assumptive = is_only_assumptive (Some eqns) in
      let imports = get_imports (Some eqns) in
      ctx_add_contract acc i {stateful; imports; only_assumptive }
    | _ -> acc
  in
  List.fold_left over_decls (empty_ctx ()) decls

let build_contract_ctx ctx (eqns:LustreAst.contract) =
  let over_eqns acc = function
    | LA.GhostConst (FreeConst (_, i, ty)) -> ctx_add_free_const acc i (Some ty)
    | LA.GhostConst (UntypedConst (_, i, _)) -> ctx_add_const acc i None
    | LA.GhostConst (TypedConst (_, i, _, ty)) -> ctx_add_const acc i (Some ty)
    | LA.GhostVar (FreeConst (_, i, ty)) -> ctx_add_free_const acc i (Some ty)
    | LA.GhostVar (UntypedConst (_, i, _)) -> ctx_add_const acc i None
    | LA.GhostVar (TypedConst (_, i, _, ty)) -> ctx_add_const acc i (Some ty)
    | _ -> acc
  in
  List.fold_left over_eqns ctx eqns

let build_local_ctx ctx locals inputs outputs =
  let over_locals acc = function
    | LA.NodeConstDecl (_, FreeConst (_, i, ty)) -> ctx_add_local acc i (Some ty)
    | NodeConstDecl (_, UntypedConst (_, i, _)) -> ctx_add_local acc i None
    | NodeConstDecl (_, TypedConst (_, i, _, ty)) -> ctx_add_local acc i (Some ty)
    | NodeVarDecl (_, (_, i, ty, _)) -> ctx_add_local acc i (Some ty)
  in
  let over_inputs acc (_, i, ty, _, _) = ctx_add_local acc i (Some ty) in
  let over_outputs acc (_, i, ty, _) = ctx_add_local acc i (Some ty) in
  let ctx = List.fold_left over_locals ctx locals in
  let ctx = List.fold_left over_inputs ctx inputs in
  List.fold_left over_outputs ctx outputs

let build_equation_ctx ctx = function
  | LA.StructDef (_, items) ->
    let over_items ctx = function
      | LA.ArrayDef (_, i, indices) ->
        let output_type_opt = StringMap.find_opt i ctx.locals |> Lib.join in
        let is_symbolic = match output_type_opt with
          | Some ty -> (match ty with
            | ArrayType (_, (_, e)) ->
              let vars = LAH.vars e in
              let check_var e = StringMap.mem e ctx.free_consts
                || StringMap.mem e ctx.locals
              in
              LA.SI.exists check_var vars
            | _ -> false)
          | None -> false
        in
        let over_indices acc id =
          if is_symbolic
          then ctx_add_symbolic_array_index acc id output_type_opt
          else ctx_add_array_index acc id output_type_opt
        in
        List.fold_left over_indices ctx indices
      | _ -> ctx
    in
    List.fold_left over_items ctx items

let locals_must_have_definitions locals items =
  let rec find_local_def_lhs id test = function
    | LA.SingleIdent (_, id')
    | TupleSelection (_, id', _)
    | FieldSelection (_, id', _)
    | ArraySliceStructItem (_, id', _)
    | ArrayDef (_, id', _)
      -> test || id = id'
    | TupleStructItem (_, items) ->
      let test_items = items |> List.map (find_local_def_lhs id test)
        |> List.fold_left (fun x y -> x || y) false
      in
      test || test_items
  in
  let find_local_def id = function
    | LA.Body eqn -> (match eqn with
      | LA.Assert _ -> false
      | LA.Equation (_, lhs, _) -> (match lhs with
        | LA.StructDef (_, vars)
          -> List.fold_left (find_local_def_lhs id) false vars))
    | LA.AnnotMain _ -> false
    | LA.AnnotProperty _ -> false
  in
  let over_locals = function
    | LA.NodeConstDecl _ -> Ok ()
    | LA.NodeVarDecl (_, (pos, id, _, _)) ->
      let test = List.find_opt (fun item -> find_local_def id item) items in
      match test with
      | Some _ -> Ok ()
      | None -> syntax_error pos (UndefinedLocal id)
  in
  Res.seq (List.map over_locals locals)

let no_dangling_calls ctx = function
  | LA.Condact (pos, _, _, i, _, _)
  | Activate (pos, i, _, _, _)
  | Call (pos, i, _) ->
    let check_nodes = StringMap.mem i ctx.nodes in
    let check_funcs = StringMap.mem i ctx.functions in
    (match check_nodes, check_funcs with
    | true, _ -> Ok ()
    | _, true -> Ok ()
    | false, false -> syntax_error pos (UndefinedNode i))
  | _ -> Ok ()

let no_dangling_identifiers ctx = function
  | LA.Ident (pos, i) -> 
    let check_ids = [
      StringMap.mem i ctx.consts;
      StringMap.mem i ctx.free_consts;
      StringMap.mem i ctx.locals;
      StringMap.mem i ctx.quant_vars;
      StringMap.mem i ctx.array_indices;
      StringMap.mem i ctx.symbolic_array_indices; ]
    in
    let check_ids = List.filter (fun x -> x) check_ids in
    if List.length check_ids > 0 then Ok ()
    else syntax_error pos (DanglingIdentifier i)
  | _ -> Ok ()

let no_quant_var_or_symbolic_index_in_node_call ctx = function
  | LA.Call (pos, i, args) ->
    let vars = List.flatten (List.map (fun e -> LA.SI.elements (LAH.vars e)) args) in
    let over_vars j = 
      let found_quant = StringMap.mem j ctx.quant_vars in
      let found_symbolic_index = StringMap.mem j ctx.symbolic_array_indices in
      (match found_quant, found_symbolic_index with
      | true, _ -> syntax_error pos (QuantifiedVariableInNodeArgument (j, i))
      | _, true -> syntax_error pos (SymbolicArrayIndexInNodeArgument (j, i))
      | false, false -> Ok ())
    in
    let check = List.map over_vars vars in
    List.fold_left (>>) (Ok ()) check
  | _ -> Ok ()

let no_calls_to_node ctx = function
  | LA.Condact (pos, _, _, i, _, _)
  | Activate (pos, i, _, _, _)
  | Call (pos, i, _) ->
    let check_nodes = StringMap.mem i ctx.nodes in
    if check_nodes then syntax_error pos (NodeCallInFunction i)
    else Ok ()
  | _ -> Ok ()

(* Note: this check is simpler if done after the contract imports have all been
  resolved and combined (e.g. after a LustreNode has been constructed).
  Therefore, it may make sense to move this check to that point instead of 
  tracing through the imports early on in the LustreAST here *)
let no_calls_to_nodes_with_contracts_subject_to_refinement ctx expr =
  let rec check_only_assumptive imports =
    let over_imports i a = match StringMap.find_opt i ctx.contracts with
      | Some { only_assumptive; imports } ->
        a || only_assumptive || check_only_assumptive imports
      | None -> a (* Situation is bogus regardless *)
    in
    StringSet.fold over_imports imports false
  in
  match expr with
  | LA.Condact (pos, _, _, i, _, _)
  | Activate (pos, i, _, _, _)
  | Call (pos, i, _) ->
    let node_check = StringMap.find_opt i ctx.nodes in
    let fn_check = StringMap.find_opt i ctx.functions in
    (match node_check, fn_check with
    | Some { has_contract = true; 
        imported = false;
        contract_only_assumptive;
        contract_imports }
      , _
      -> 
      let only_assumptive = contract_only_assumptive
        || check_only_assumptive contract_imports
      in
      if not only_assumptive then
        syntax_error pos (NodeCallInRefinableContract ("node", i))
      else Ok ()
    | _, Some { has_contract = true; 
        imported = false;
        contract_only_assumptive;
        contract_imports }
      -> 
      let only_assumptive = contract_only_assumptive
        || check_only_assumptive contract_imports
      in
      if not only_assumptive then
        syntax_error pos (NodeCallInRefinableContract ("function", i))
      else Ok ()
    | _ -> Ok ())
  | _ -> Ok ()

let no_temporal_operator is_const expr =
  let decl_ctx = if is_const then "constant" else "function or function contract" in
  match expr with
  | LA.Pre (pos, _) -> syntax_error pos (IllegalTemporalOperator ("pre", decl_ctx))
  | Arrow (pos, _, _) -> syntax_error pos (IllegalTemporalOperator ("arrow", decl_ctx))
  | Fby (pos, _, _, _) -> syntax_error pos (IllegalTemporalOperator ("fby", decl_ctx))
  | _ -> Ok ()

let no_stateful_contract_imports ctx contract =
  let rec check_import_stateful pos initial i =
    match StringMap.find_opt i ctx.contracts with
    | Some { stateful; imports } ->
      if not stateful then
        StringSet.fold (fun j a -> a >> (check_import_stateful pos initial j))
          imports
          (Ok ())
      else syntax_error pos (IllegalImportOfStatefulContract initial)
    | None -> Ok ()
  in
  let over_eqn acc = function
    | LA.ContractCall (pos, i, _, _) ->
      let check = check_import_stateful pos i i in
      acc >> check
    | _ -> acc
  in
  List.fold_left over_eqn (Ok ()) contract

let no_clock_inputs_or_outputs pos = function
  | LA.ClockTrue -> Ok ()
  | _ -> syntax_error pos UnsupportedClockedInputOrOutput

let unsupported_expr = function
  | LA.ArraySlice (pos, _, _) as e -> syntax_error pos (UnsupportedExpression e)
  | LA.ArrayConcat (pos, _, _) as e -> syntax_error pos (UnsupportedExpression e)
  | LA.Current (pos, _) as e -> syntax_error pos (UnsupportedExpression e)
  | LA.NArityOp (pos, LA.OneHot, _) as e -> syntax_error pos (UnsupportedExpression e)
  | LA.Fby (pos, _, _, _) as e -> syntax_error pos (UnsupportedExpression e)
  | LA.TernaryOp (pos, LA.With, _, _, _) as e -> syntax_error pos (UnsupportedExpression e)
  | LA.CallParam (pos, _, _, _) as e -> syntax_error pos (UnsupportedExpression e)
  | _ -> Ok ()

let rec expr_only_supported_in_merge observer expr =
  let r = expr_only_supported_in_merge in
  let r_list obs e = Res.seqM (fun x _ -> x) () (List.map (r obs) e) in
  match expr with
  | LA.When (pos, _, _) as e -> syntax_error pos (UnsupportedWhen e)
  | Merge (_, _, e) -> 
    Res.seq_ (List.map (fun (_, e) -> match e with
      | LA.When (_, e, _) | e -> r true e)
      e)
  | Ident _ | Const _ | ModeRef _ -> Ok ()
  | RecordProject (_, e, _)
  | TupleProject (_, e, _)
  | UnaryOp (_, _, e)
  | ConvOp (_, _, e)
  | Pre (_, e)
  | Current (_, e)
  | Quantifier (_, _, _, e) -> r observer e
  | BinaryOp (_, _, e1, e2) 
  | StructUpdate (_, e1, _, e2)
  | CompOp (_, _, e1, e2)
  | Fby (_, e1, _, e2)
  | Arrow (_, e1, e2)
  | ArrayIndex (_, e1, e2)
  | ArrayConcat (_, e1, e2)
  | ArrayConstr (_, e1, e2) -> r observer e1 >> r observer e2
  | TernaryOp (_, _, e1, e2, e3)
  | ArraySlice (_, e1, (e2, e3))
    -> r observer e1 >> r observer e2 >> r observer e3
  | NArityOp (_, _, e)
  | GroupExpr (_, _, e)
  | Call (_, _, e)
  | CallParam (_, _, _, e) -> r_list observer e
  | RecordExpr (_, _, e) -> r_list observer (List.map (fun (_, x) -> x) e)
  | Condact (_, e1, e2, _, e3, e4 )
    -> r observer e1 >> r observer e2 >> r_list observer e3 >> r_list observer e4
  | Activate (pos, _, _, _, _) as e ->
    if observer then Ok ()
    else syntax_error pos (UnsupportedOutsideMerge e)
  | RestartEvery (_, _, e1, e2) -> r_list observer e1 >> r observer e2

let parametric_nodes_unsupported pos params =
  if List.length params == 0 then Ok ()
  else syntax_error pos (UnsupportedParametricDeclaration)

let rec syntax_check (ast:LustreAst.t) =
  let ctx = build_global_ctx ast in
  Res.seq (List.map (check_declaration ctx) ast)

and check_declaration ctx = function
  | TypeDecl (span, decl) -> Ok (LA.TypeDecl (span, decl))
  | ConstDecl (span, decl) ->
    let check = match decl with
      | LA.FreeConst _ -> Ok ()
      | UntypedConst (_, _, e)
      | TypedConst (_, _, e, _) -> check_const_expr_decl ctx e
    in
    check >> Ok (LA.ConstDecl (span, decl))
  | NodeDecl (span, decl) -> check_node_decl ctx span decl
  | FuncDecl (span, decl) -> check_func_decl ctx span decl
  | ContractNodeDecl (span, decl) -> check_contract_node_decl ctx span decl
  | NodeParamInst (span, _) -> syntax_error span.start_pos UnsupportedParametricDeclaration

and check_const_expr_decl ctx expr =
  let composed_checks ctx e =
    (no_temporal_operator true e)
      >> (no_dangling_identifiers ctx e)
  in
  check_expr ctx composed_checks expr

and common_node_equations_checks ctx e =
  (unsupported_expr e)
    >> (no_dangling_calls ctx e)
    >> (no_dangling_identifiers ctx e)
    >> (no_quant_var_or_symbolic_index_in_node_call ctx e)

and common_contract_checks ctx e =
  (unsupported_expr e)
    >> (no_dangling_calls ctx e)
    >> (no_dangling_identifiers ctx e)
    >> (no_quant_var_or_symbolic_index_in_node_call ctx e)
    >> (no_calls_to_nodes_with_contracts_subject_to_refinement ctx e)

and check_input_items (pos, _id, _ty, clock, _const) =
  no_clock_inputs_or_outputs pos clock

and check_output_items (pos, _id, _ty, clock) =
  no_clock_inputs_or_outputs pos clock

and check_local_items local = match local with
  | LA.NodeConstDecl _ -> Ok ()
  | NodeVarDecl (_, (_, _, _, LA.ClockTrue)) -> Ok ()
  | NodeVarDecl (_, (pos, i, _, _)) -> syntax_error pos (UnsupportedClockedLocal i)

and check_node_decl ctx span (id, ext, params, inputs, outputs, locals, items, contract) =
  let ctx = build_local_ctx ctx locals inputs outputs in
  let decl = LA.NodeDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contract))
  in
  (parametric_nodes_unsupported span.start_pos params)
  >> (locals_must_have_definitions locals items)
    >> (check_items ctx common_node_equations_checks items)
    >> (match contract with 
    | Some c -> check_contract false ctx common_contract_checks c
    | None -> Ok ())
    >> (Res.seq_ (List.map check_input_items inputs))
    >> (Res.seq_ (List.map check_output_items outputs))
    >> (Res.seq_ (List.map check_local_items locals))
    >> (Ok decl)

and check_func_decl ctx span (id, ext, params, inputs, outputs, locals, items, contract) =
  let ctx = build_local_ctx ctx locals inputs outputs in
  let decl = LA.FuncDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contract))
  in
  let composed_items_checks ctx e =
    (common_node_equations_checks ctx e)
      >> (no_calls_to_node ctx e)
      >> (no_temporal_operator false e)
  in
  (parametric_nodes_unsupported span.start_pos params)
  >> (check_items ctx composed_items_checks items)
    >> (match contract with
      | Some c -> check_contract false ctx common_contract_checks c
        >> (check_contract false ctx (fun _ -> no_temporal_operator false) c)
        >> no_stateful_contract_imports ctx c
      | None -> Ok ())
    >> (Res.seq_ (List.map check_input_items inputs))
    >> (Res.seq_ (List.map check_output_items outputs))
    >> (Res.seq_ (List.map check_local_items locals))
    >> (Ok decl)

and check_contract_node_decl ctx span (id, params, inputs, outputs, contract) =
  let ctx = build_local_ctx ctx [] inputs outputs in
  let decl = LA.ContractNodeDecl
    (span, (id, params, inputs, outputs, contract))
  in
  (check_contract true ctx common_contract_checks contract)
    >> (Res.seq_ (List.map check_input_items inputs))
    >> (Res.seq_ (List.map check_output_items outputs))
    >> (Ok decl)

and check_items ctx f items =
  let check_item ctx f = function
    | LA.Body (Equation (_, lhs, e)) ->
      let ctx = build_equation_ctx ctx lhs in
      let StructDef (_, struct_items) = lhs in
      check_struct_items ctx struct_items
        >> check_expr ctx f e
        >> (expr_only_supported_in_merge false e)
    | Body (Assert (_, e))
    | AnnotProperty (_, _, e) -> check_expr ctx f e
    | AnnotMain _ -> Ok ()
  in
  Res.seqM (fun x _ -> x) () (List.map (check_item ctx f) items)

and check_struct_items ctx items =
  let r items = check_struct_items ctx items in
  match items with
  | [] -> Ok ()
  | (LA.SingleIdent _) :: tail -> r tail
  | (ArrayDef _) :: tail -> r tail
  | (TupleStructItem (pos, _)) :: _
  | (TupleSelection (pos, _, _)) :: _
  | (FieldSelection (pos, _, _)) :: _
  | (ArraySliceStructItem (pos, _, _)) :: _
    -> syntax_error pos UnsupportedAssignment

and check_contract is_contract_node ctx f contract =
  let ctx = build_contract_ctx ctx contract in
  let check_list e = Res.seqM (fun x _ -> x) () (List.map (check_expr ctx f) e) in
  let check_contract_item ctx f = function
    | LA.Assume (_, _, _, e) -> check_expr ctx f e
    | Guarantee (_, _, _, e) -> check_expr ctx f e
    | Mode (_, _, rs, gs) ->
      let rs = List.map (fun (_, _, e) -> e) rs in
      let gs = List.map (fun (_, _, e) -> e) gs in
      check_list rs >> check_list gs
    | GhostVar (UntypedConst (_, _, e)) -> check_expr ctx f e
    | GhostVar (TypedConst (_, _, e, _)) -> check_expr ctx f e
    | AssumptionVars (pos, _) ->
      if not is_contract_node then Ok ()
      else syntax_error pos AssumptionVariablesInContractNode
    | _ -> Ok ()
  in
  Res.seqM (fun x _ -> x) () (List.map (check_contract_item ctx f) contract)

and check_expr ctx f (expr:LustreAst.expr) =
  let check_list e = Res.seqM (fun x _ -> x) () (List.map (check_expr ctx f) e) in
  let expr' = f ctx expr in
  let r = match expr with
    | LA.RecordProject (_, e, _)
    | TupleProject (_, e, _)
    | UnaryOp (_, _, e)
    | ConvOp (_, _, e)
    | When (_, e, _)
    | Current (_, e)
    | Pre (_, e)
      -> check_expr ctx f e
    | Quantifier (_, _, vars, e) ->
        let over_vars ctx (_, i, ty) = ctx_add_quant_var ctx i (Some ty) in
        let ctx = List.fold_left over_vars ctx vars in
        check_expr ctx f e
    | BinaryOp (_, _, e1, e2)
    | CompOp (_, _, e1, e2)
    | StructUpdate (_, e1, _, e2)
    | ArrayConstr (_, e1, e2)
    | ArrayIndex (_, e1, e2)
    | ArrayConcat (_, e1, e2)
    | Fby (_, e1, _, e2)
    | Arrow (_, e1, e2)
      -> (check_expr ctx f e1) >> (check_expr ctx f e2)
    | TernaryOp (_, _, e1, e2, e3)
    | ArraySlice (_, e1, (e2, e3))
      -> (check_expr ctx f e1) >> (check_expr ctx f e2) >> (check_expr ctx f e3)
    | NArityOp (_, _, e)
    | GroupExpr (_, _, e)
    | Call (_, _, e)
    | CallParam (_, _, _, e)
      -> check_list e
    | RecordExpr (_, _, e)
    | Merge (_, _, e)
      -> let e = List.map (fun (_, e) -> e) e in check_list e
    | Condact (_, e1, e2, _, e3, e4)
      -> (check_expr ctx f e1) >> (check_expr ctx f e2)
        >> (check_list e3) >> (check_list e4)
    | Activate (_, _, e1, e2, e3)
      -> (check_expr ctx f e1) >> (check_expr ctx f e2) >> (check_list e3)
    | RestartEvery (_, _, e1, e2)
      -> (check_list e1) >> (check_expr ctx f e2)
    | _ -> Ok ()
  in
  expr' >> r

let no_mismatched_clock is_bool e =
  let ctx = empty_ctx () in
  let check_when clock = function
    | LA.When (pos, _, c) ->
      let clocks_match = (match c, clock with
        | ClockTrue, LA.ClockTrue -> true
        | ClockPos i, ClockPos j -> HString.equal i j
        | ClockNeg i, ClockNeg j -> HString.equal i j
        | ClockConstr (i1, i2), ClockConstr (j1, j2) ->
          HString.equal i1 j1 && HString.equal i2 j2
        | _ -> false)
      in
      if not clocks_match then syntax_error pos ClockMismatchInMerge
      else Ok ()
    | _ -> Ok ()
  in
  let check_merge = function
    | LA.Merge (_, clock, exprs) ->
      if not is_bool then
        let case (i, e) = check_expr ctx
          (fun _ -> check_when (ClockConstr (i, clock))) e
        in
        List.fold_left (>>) (Ok ()) (List.map case exprs)
      else
        let true_variant = List.nth_opt exprs 0 in
        let false_variant = List.nth_opt exprs 1 in
        (match true_variant, false_variant with
        | Some (_, e1), Some (_, e2) ->
          check_when (ClockPos clock) e1
            >> check_when (ClockNeg clock) e2
        | _ -> Ok ())
    | _ -> Ok ()
  in
  check_expr ctx (fun _ -> check_merge) e
