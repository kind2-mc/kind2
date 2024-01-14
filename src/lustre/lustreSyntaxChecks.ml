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
module H = HString

exception Cycle (* Exception raised locally when a cycle in contract imports is detected *)

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
  | DuplicateLocal of HString.t * Lib.position
  | DuplicateOutput of HString.t * Lib.position
  | DuplicateProperty of HString.t
  | UndefinedNode of HString.t
  | UndefinedContract of HString.t
  | DanglingIdentifier of HString.t
  | QuantifiedVariableInPre of HString.t
  | QuantifiedVariableInNodeArgument of HString.t * HString.t
  | SymbolicArrayIndexInNodeArgument of HString.t * HString.t
  | ChooseOpInFunction
  | NodeCallInFunction of HString.t
  | NodeCallInRefinableContract of string * HString.t
  | NodeCallInConstant of HString.t
  | NodeCallInGlobalTypeDecl of HString.t
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
  | MisplacedVarInFrameBlock of LustreAst.ident
  | MisplacedAssertInFrameBlock
  | IllegalClockExprInActivate of LustreAst.expr

type error = [
  | `LustreSyntaxChecksError of Lib.position * error_kind
]

let error_message kind = match kind with
  | Unknown s -> s
  | UndefinedLocal id -> "Local variable '"
    ^ HString.string_of_hstring id ^ "' has no definition"
  | DuplicateLocal (id, pos) -> "Local variable '"
    ^ HString.string_of_hstring id ^ "' has already been defined at position " ^ 
     (Lib.string_of_t Lib.pp_print_position pos) 
  | DuplicateOutput (id, pos) -> "Output variable '"
    ^ HString.string_of_hstring id ^ "' has already been defined at position " ^
    (Lib.string_of_t Lib.pp_print_position pos) 
  | DuplicateProperty id -> "Property '"
  ^ HString.string_of_hstring id ^ "' has more than one definition"
  | UndefinedNode id -> "Node or function '"
    ^ HString.string_of_hstring id ^ "' is undefined"
  | UndefinedContract id -> "Contract '"
    ^ HString.string_of_hstring id ^ "' is undefined"
  | DanglingIdentifier id -> "Unknown identifier '"
    ^ HString.string_of_hstring id ^ "'"
  | QuantifiedVariableInPre var -> "Quantified variable '"
    ^ HString.string_of_hstring var ^ "' is not allowed in an argument to pre operator"
  | QuantifiedVariableInNodeArgument (var, node) -> "Quantified variable '"
    ^ HString.string_of_hstring var ^ "' is not allowed in an argument to the node call '"
    ^ HString.string_of_hstring node ^ "'"
  | SymbolicArrayIndexInNodeArgument (idx, node) -> "Symbolic array index '"
    ^ HString.string_of_hstring idx ^ "' is not allowed in an argument to the node call '"
    ^ HString.string_of_hstring node ^ "'"
  | ChooseOpInFunction -> "Illegal choose operator in function"
  | NodeCallInFunction node -> "Illegal call to node '"
    ^ HString.string_of_hstring node ^ "', functions and function contracts can only call other functions, not nodes"
  | NodeCallInRefinableContract (kind, node) -> "Illegal call to " ^ kind ^ " '"
    ^ HString.string_of_hstring node ^ "' in the cone of influence of this contract: " ^ kind ^ " "
    ^ HString.string_of_hstring node ^ " has a refinable contract"
  | NodeCallInConstant id -> "Illegal node call or choose operator in definition of constant '" ^ HString.string_of_hstring id ^ "'"
  | NodeCallInGlobalTypeDecl id -> "Illegal node call or choose operator in definition of global type '" ^ HString.string_of_hstring id ^ "'"
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
  | MisplacedVarInFrameBlock id -> "Variable '" ^ HString.string_of_hstring id ^ "' is defined in the frame block but not declared in the frame block header"
  | MisplacedAssertInFrameBlock -> "Assertion not allowed in frame block initialization"
  | IllegalClockExprInActivate e -> "Illegal clock expression '" ^ LA.string_of_expr e ^ "' in activate"

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

(* Expression contains a pre, an arrow, or a call to a node *)
let rec has_stateful_op ctx =
function
| LA.Pre _ | Arrow _ -> true

| RestartEvery _
| ChooseOp _ -> true

| Condact (_, e, r, i, l1, l2) ->
  StringMap.mem i ctx.nodes ||
  has_stateful_op ctx e ||
  has_stateful_op ctx r ||
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l1
  ||
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l2

| Activate (_, i, e, r, l) ->
  StringMap.mem i ctx.nodes ||
  has_stateful_op ctx e ||
  has_stateful_op ctx r ||
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l

| Call (_, i, l) ->
  StringMap.mem i ctx.nodes ||
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l

| Const _ | Ident _ | ModeRef _ -> false

| RecordProject (_, e, _) | ConvOp (_, _, e)
| UnaryOp (_, _, e) | When (_, e, _)
| TupleProject (_, e, _) | Quantifier (_, _, _, e) ->
  has_stateful_op ctx e

| BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2)
| ArrayIndex (_, e1, e2) | ArrayConstr (_, e1, e2)  ->
  has_stateful_op ctx e1 || has_stateful_op ctx e2

| TernaryOp (_, _, e1, e2, e3) ->
  has_stateful_op ctx e1 || has_stateful_op ctx e2 || has_stateful_op ctx e3

| GroupExpr (_, _, l) ->
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l

| Merge (_, _, l)
| RecordExpr (_, _, l) ->
  List.fold_left
    (fun acc (_, e) -> acc || has_stateful_op ctx e)
    false l

| StructUpdate (_, e1, li, e2) ->
  has_stateful_op ctx e1 ||
  has_stateful_op ctx e2 ||
  List.fold_left
    (fun acc l_or_i -> acc ||
      (match l_or_i with
      | LA.Label _ -> false
      | Index (_, e) -> has_stateful_op ctx e
      )
    )
    false li


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
      | LA.Guarantee _ | Mode _ -> false
      | _ -> a)
      true eqns
    | None -> false
  in
  let contract_decls, others =
    List.partition (function LA.ContractNodeDecl _ -> true | _ -> false) decls
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
    | _ -> acc
  in
  let ctx = List.fold_left over_decls (empty_ctx ()) others in
  let over_contract_eq (stateful, imports, only_assumptive) = function
    | LA.GhostConst (FreeConst _) ->
      (stateful, imports, only_assumptive)
    | GhostConst (UntypedConst (_, _, e))
    | GhostConst (TypedConst (_, _, e, _))
    | GhostVars (_, _, e)
    | Assume (_, _, _, e) ->
      (stateful || has_stateful_op ctx e, imports, only_assumptive)
    | Guarantee (_, _, _, e) ->
      (stateful || has_stateful_op ctx e, imports, false)
    | Mode (_, _, reqs, enss) ->
      let req_or_ens_has_stateful_op req_ens_lst =
        List.fold_left
          (fun acc (_, _, e) -> acc || has_stateful_op ctx e)
          false req_ens_lst
      in
      let stateful' = stateful ||
        req_or_ens_has_stateful_op reqs || req_or_ens_has_stateful_op enss
      in
      (stateful', imports, false)
    | ContractCall (_, i, ins, _) ->
      let arg_has_stateful_op ins =
        List.fold_left
          (fun acc e -> acc || has_stateful_op ctx e)
          false ins
      in
      (stateful || arg_has_stateful_op ins,
       StringSet.add i imports,
       only_assumptive
      )
    | AssumptionVars _ ->
      (stateful, imports, only_assumptive)
  in
  let over_contract_decls acc = function
    | LA.ContractNodeDecl (_, (i, _, _, _, eqns)) ->
      let stateful, imports, only_assumptive =
        List.fold_left
          over_contract_eq
          (false, StringSet.empty, true)
          eqns
      in
      ctx_add_contract acc i {stateful; imports; only_assumptive }
    | _ -> acc
  in
  List.fold_left over_contract_decls ctx contract_decls

let build_contract_ctx ctx (eqns:LustreAst.contract) =
  let over_eqns acc = function
    | LA.GhostConst (FreeConst (_, i, ty)) -> ctx_add_free_const acc i (Some ty)
    | LA.GhostConst (UntypedConst (_, i, _)) -> ctx_add_const acc i None
    | LA.GhostConst (TypedConst (_, i, _, ty)) -> ctx_add_const acc i (Some ty)
    | LA.GhostVars (_, GhostVarDec (_, l), _) -> 
      List.fold_left (fun acc (_, i, ty) -> ctx_add_const acc i (Some ty)) acc l

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
              let vars = LAH.vars_without_node_call_ids e in
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
    
let rec find_var_def_count_lhs id = function
  | LA.SingleIdent (pos, id')
  | TupleSelection (pos, id', _)
  | FieldSelection (pos, id', _)
  | ArraySliceStructItem (pos, id', _)
  | ArrayDef (pos, id', _)
    -> if id = id' then [pos] else []
  | TupleStructItem (_, items) ->
    List.map (find_var_def_count_lhs id) items |> List.flatten
  
  
let rec find_var_def_count id = function
  | LA.Body eqn -> (match eqn with
    | LA.Assert _ -> []
    | LA.Equation (_, lhs, _) -> (match lhs with
      | LA.StructDef (_, vars)
        -> List.map (find_var_def_count_lhs id) vars) |> 
           List.flatten)
  | LA.IfBlock (_, _, l1, l2) ->
    let x1 = List.map (find_var_def_count id) l1 |> 
             List.flatten in
    let x2 = List.map (find_var_def_count id) l2 |> 
             List.flatten in
    let len1 = List.length x1 in
    let len2 = List.length x2 in 
    (* Detect duplicate definitions in the same branch *)
    if (len1 > 1) then x1
    else if (len2 > 1) then x2
    (* Local is defined in at least one branch *)
    else if (len1 = 1) then x1
    else if (len2 = 1) then x2
    (* Local isn't defined in this if block *)
    else []
  | LA.FrameBlock (pos, vars, nes, nis) -> (
    let nes = List.map (fun x -> (LA.Body x)) nes in
    let x1 = List.filter (fun (_, var) -> var = id) vars in
    let poss, _ = List.split x1 in
    let x2 = List.map (find_var_def_count id) nis |> 
             List.flatten in
    let x3 = List.map (find_var_def_count id) nes |> 
             List.flatten in
    let len1 = List.length x1 in
    let len2 = List.length x2 in 
    let len3 = List.length x3 in
    if (len1 + len2 + len3 = 0) 
    then []
    (* Detect duplicate definitions in any components of the frame block *)
    else if (len1 > 1) then poss
    else if (len2 > 1) then x2
    else if (len3 > 1) then x3
    else [pos]
  )
  | LA.AnnotMain _ -> []
  | LA.AnnotProperty _ -> []

let locals_exactly_one_definition locals items =
  let over_locals = function
    | LA.NodeConstDecl _ -> Ok ()
    | LA.NodeVarDecl (_, (pos, id, _, _)) ->
      let poss = (List.map (find_var_def_count id) items) |> List.flatten in
      match List.length poss with
      | 1 -> Ok ()
      | 0 -> syntax_error pos (UndefinedLocal id)
      | _ -> 
        let poss = List.sort Lib.compare_pos poss in
        syntax_error (List.hd (List.tl poss)) (DuplicateLocal (id, List.hd poss))
  in
  Res.seq (List.map over_locals locals)

let outputs_at_most_one_definition outputs items =
  let over_outputs = function
  | (_, id, _, _) ->
    let poss = List.map (find_var_def_count id) items |> List.flatten in
    match List.length poss with
      | 0 
      | 1 -> Ok ()
      | _ -> 
        let poss = List.sort Lib.compare_pos poss in
        syntax_error (List.hd (List.tl poss)) (DuplicateOutput (id, List.hd poss))
  in
  Res.seq (List.map over_outputs outputs)

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

let no_a_dangling_identifier ctx pos i =
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

let no_dangling_identifiers ctx = function
  | LA.Ident (pos, i) -> 
    no_a_dangling_identifier ctx pos i
  | _ -> Ok ()

let no_node_calls_in_constant i e =
  if LAH.expr_contains_call e
  then syntax_error (LAH.pos_of_expr e) (NodeCallInConstant i)
  else Ok ()

let no_quant_var_or_symbolic_index_in_node_call ctx = function
  | LA.Call (pos, i, args) ->
    let vars =
      List.fold_left
        (fun acc e -> LA.SI.union acc (LAH.vars_without_node_call_ids e))
        LA.SI.empty
        args
    in
    let over_vars j = 
      let found_quant = StringMap.mem j ctx.quant_vars in
      let found_symbolic_index = StringMap.mem j ctx.symbolic_array_indices in
      (match found_quant, found_symbolic_index with
      | true, _ -> syntax_error pos (QuantifiedVariableInNodeArgument (j, i))
      | _, true -> syntax_error pos (SymbolicArrayIndexInNodeArgument (j, i))
      | false, false -> Ok ())
    in
    let check = List.map over_vars (LA.SI.elements vars) in
    List.fold_left (>>) (Ok ()) check
  | LA.Pre (_, ArrayIndex (_, _, _)) -> Ok ()
  | LA.Pre (pos, e) ->
    let vars = LAH.vars_without_node_call_ids e in
    let over_vars j = 
      let found_quant = StringMap.mem j ctx.quant_vars in
      if found_quant then syntax_error pos (QuantifiedVariableInPre j)
      else Ok ()
    in
    let check = List.map over_vars (LA.SI.elements vars) in
    List.fold_left (>>) (Ok ()) check
  | _ -> Ok ()

let no_calls_to_node ctx = function
  | LA.Condact (pos, _, _, i, _, _)
  | Activate (pos, i, _, _, _)
  | RestartEvery (pos, i, _, _)
  | Call (pos, i, _) ->
    let check_nodes = StringMap.mem i ctx.nodes in
    if check_nodes then syntax_error pos (NodeCallInFunction i)
    else Ok ()
  | ChooseOp (pos, _, _, _) -> syntax_error pos ChooseOpInFunction
  | _ -> Ok ()

(* Note: this check is simpler if done after the contract imports have all been
  resolved and combined (e.g. after a LustreNode has been constructed).
  Therefore, it may make sense to move this check to that point instead of 
  tracing through the imports early on in the LustreAST here *)
let no_calls_to_nodes_subject_to_refinement ctx expr =
  try
    let rec check_only_assumptive visited imports =
      let over_imports i a = match StringMap.find_opt i ctx.contracts with
        | Some { only_assumptive; imports } ->
          if StringSet.mem i visited then raise Cycle ;
          a && only_assumptive && (
            let visited = StringSet.add i visited in
            check_only_assumptive visited imports
          )
        | None -> a (* Situation is bogus regardless *)
      in
      StringSet.fold over_imports imports true
    in
    let check_node_data pos kind i = function
      | Some { has_contract = true; 
          imported = false;
          contract_only_assumptive;
          contract_imports } -> (
        let only_assumptive = contract_only_assumptive
            && check_only_assumptive StringSet.empty contract_imports
        in
        if not only_assumptive then
          syntax_error pos (NodeCallInRefinableContract (kind, i))
        else Ok ()
      )
      | _ -> Ok ()
    in
    match expr with
    | LA.Condact (pos, _, _, i, _, _)
    | Activate (pos, i, _, _, _)
    | RestartEvery (pos, i, _, _)
    | Call (pos, i, _) ->
      check_node_data pos "node" i (StringMap.find_opt i ctx.nodes)
      >> check_node_data pos "function" i (StringMap.find_opt i ctx.functions)
    | _ -> Ok ()
  with Cycle ->
    Ok () (* Cycle will be rediscovered by lustreAstDependencies *)

let no_temporal_operator decl_ctx expr =
  match expr with
  | LA.Pre (pos, _) -> syntax_error pos (IllegalTemporalOperator ("pre", decl_ctx))
  | Arrow (pos, _, _) -> syntax_error pos (IllegalTemporalOperator ("arrow", decl_ctx))
  | _ -> Ok ()

let no_stateful_contract_imports ctx contract =
  try
    let rec check_import_stateful visited pos initial i =
      if StringSet.mem i visited then raise Cycle ;
      match StringMap.find_opt i ctx.contracts with
      | Some { stateful; imports } ->
        if not stateful then
          let visited = StringSet.add i visited in
          StringSet.fold
            (fun j a ->
              a >> (check_import_stateful visited pos initial j)
            )
            imports
            (Ok ())
        else syntax_error pos (IllegalImportOfStatefulContract initial)
      | None -> Ok ()
    in
    let over_eqn acc = function
      | LA.ContractCall (pos, i, _, _) ->
        acc >> (check_import_stateful StringSet.empty pos i i)
      | _ -> acc
    in
    List.fold_left over_eqn (Ok ()) contract
  with Cycle ->
    Ok () (* Cycle will be rediscovered by lustreAstDependencies *)

let no_clock_inputs_or_outputs pos = function
  | LA.ClockTrue -> Ok ()
  | _ -> syntax_error pos UnsupportedClockedInputOrOutput

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
  | Quantifier (_, _, _, e) -> r observer e
  | ChooseOp (_, _, e, None) -> r false e
  | ChooseOp (_, _, e1, Some e2) -> r false e1 >> r false e2
  | BinaryOp (_, _, e1, e2) 
  | StructUpdate (_, e1, _, e2)
  | CompOp (_, _, e1, e2)
  | Arrow (_, e1, e2)
  | ArrayIndex (_, e1, e2)
  | ArrayConstr (_, e1, e2) -> r observer e1 >> r observer e2
  | TernaryOp (_, _, e1, e2, e3)
    -> r observer e1 >> r observer e2 >> r observer e3
  | GroupExpr (_, _, e)
  | Call (_, _, e) -> r_list observer e
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

and check_ty_node_calls i ty = 
  match ty with 
    | LA.RefinementType (_, _, e, None) ->
      if LAH.expr_contains_call e
        then syntax_error (LAH.pos_of_expr e) (NodeCallInGlobalTypeDecl i)
        else Ok ()
    | LA.RefinementType (_, _, e1, Some e2) ->
      if LAH.expr_contains_call e1 
        then syntax_error (LAH.pos_of_expr e1) (NodeCallInGlobalTypeDecl i)
        else if LAH.expr_contains_call e2 
          then syntax_error (LAH.pos_of_expr e2) (NodeCallInGlobalTypeDecl i)
          else Ok ()
    | TupleType (_, tys) 
    | GroupType (_, tys) -> Res.seq_ (List.map (check_ty_node_calls i) tys)
    | RecordType (_, _, tis) -> Res.seq_ (List.map (fun (_, _, ty) -> check_ty_node_calls i ty) tis)
    | ArrayType (_, (ty, e)) -> 
      check_ty_node_calls i ty 
      >> if LAH.expr_contains_call e
        then syntax_error (LAH.pos_of_expr e) (NodeCallInGlobalTypeDecl i)
        else Ok ()
    | _ -> Ok ()

and check_declaration ctx = function
(*!! Check for node calls in ref types *)
  | TypeDecl (span, FreeType (pos, id) ) -> Ok (LA.TypeDecl (span, FreeType (pos, id)))
  | TypeDecl (span, AliasType (pos, id, ty) ) -> 
    check_ty_node_calls id ty >> Ok (LA.TypeDecl (span, AliasType (pos, id, ty)))
  | ConstDecl (span, decl) ->
    let check = match decl with
      | LA.FreeConst _ -> Ok ()
      | UntypedConst (_, i, e) -> check_const_expr_decl i ctx e
      | TypedConst (_, i, e, ty) -> check_const_expr_decl i ctx e >> check_ty_node_calls i ty
    in
    check >> Ok (LA.ConstDecl (span, decl))
  | NodeDecl (span, decl) -> check_node_decl ctx span decl
  | FuncDecl (span, decl) -> check_func_decl ctx span decl
  | ContractNodeDecl (span, decl) -> check_contract_node_decl ctx span decl
  | NodeParamInst (span, _) -> syntax_error span.start_pos UnsupportedParametricDeclaration

and check_const_expr_decl i ctx expr =
  let composed_checks i ctx e =
    (no_dangling_identifiers ctx e)
    >> (no_node_calls_in_constant i e)
  in
  check_expr ctx (composed_checks i) expr

and common_node_equations_checks ctx e =
    (no_dangling_calls ctx e)
    >> (no_dangling_identifiers ctx e)
    >> (no_quant_var_or_symbolic_index_in_node_call ctx e)

and common_contract_checks ctx e =
    (no_dangling_calls ctx e)
    >> (no_dangling_identifiers ctx e)
    >> (no_quant_var_or_symbolic_index_in_node_call ctx e)
    >> (no_calls_to_nodes_subject_to_refinement ctx e)

(* Can't have from/within/at keywords in reachability queries in functions *)
and no_reachability_modifiers item = match item with 
  | LA.AnnotProperty (pos, _, _, Reachable (Some _)) -> 
    syntax_error pos (IllegalTemporalOperator ("pre", "reachability query modifier")) 
  | _ -> Ok ()

and check_input_items (pos, _id, _ty, clock, _const) =
  no_clock_inputs_or_outputs pos clock

and check_output_items (pos, _id, _ty, clock) =
  no_clock_inputs_or_outputs pos clock

and check_local_items ctx local = match local with
  | LA.NodeConstDecl (_, FreeConst _) -> Ok ()
  | LA.NodeConstDecl (_, UntypedConst (_, i, e)) -> check_const_expr_decl i ctx e
  | LA.NodeConstDecl (_, TypedConst (_, i, e, _)) -> check_const_expr_decl i ctx e
  | NodeVarDecl (_, (_, _, _, LA.ClockTrue)) -> Ok ()
  | NodeVarDecl (_, (pos, i, _, _)) -> syntax_error pos (UnsupportedClockedLocal i)

and check_node_decl ctx span (id, ext, params, inputs, outputs, locals, items, contract) =
  let ctx =
    (* Locals are not visible in contracts *)
    build_local_ctx ctx [] inputs outputs
  in
  let decl = LA.NodeDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contract))
  in
  (parametric_nodes_unsupported span.start_pos params)
  >> (match contract with
     | Some c -> check_contract false ctx common_contract_checks c
     | None -> Ok ())
  >> (locals_exactly_one_definition locals items)
  >> (outputs_at_most_one_definition outputs items)
  >> (check_items
       (build_local_ctx ctx locals [] []) (* Add locals to ctx *)
       common_node_equations_checks
       items
     )
  >> (Res.seq_ (List.map check_input_items inputs))
  >> (Res.seq_ (List.map check_output_items outputs))
  >> (Res.seq_ (List.map (check_local_items ctx) locals))
  >> (Ok decl)

and check_func_decl ctx span (id, ext, params, inputs, outputs, locals, items, contract) =
  let ctx =
    (* Locals are not visible in contracts *)
    build_local_ctx ctx [] inputs outputs
  in
  let decl = LA.FuncDecl
    (span, (id, ext, params, inputs, outputs, locals, items, contract))
  in
  let composed_items_checks ctx e =
    (common_node_equations_checks ctx e)
      >> (no_calls_to_node ctx e)
      >> (no_temporal_operator "function" e)
  in
  let function_contract_checks ctx e =
    (common_contract_checks ctx e)
    >> (no_calls_to_node ctx e)
    >> (no_temporal_operator "function contract" e)
  in
  (parametric_nodes_unsupported span.start_pos params)
  >> (match contract with
      | Some c -> check_contract false ctx function_contract_checks c
        >> no_stateful_contract_imports ctx c
      | None -> Ok ())
  >> (check_items
       (build_local_ctx ctx locals [] []) (* Add locals to ctx *)
       composed_items_checks
       items
     )
  >> (Res.seq_ (List.map no_reachability_modifiers items))
  >> (Res.seq_ (List.map check_input_items inputs))
  >> (Res.seq_ (List.map check_output_items outputs))
  >> (Res.seq_ (List.map (check_local_items ctx) locals))
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
  (* Record duplicate properties if we find them *)
  let over_props props = function
    | LA.AnnotProperty (pos, name, _, kind) ->
      let name = LustreAstHelpers.name_of_prop pos name kind in
      if StringSet.mem name props
      then syntax_error pos (DuplicateProperty name)
      else Ok (StringSet.add name props)
    | _ -> Ok props
  in
  let check_item ctx f = function
    | LA.Body (Equation (_, lhs, e)) ->
      let ctx' = build_equation_ctx ctx lhs in
      let StructDef (_, struct_items) = lhs in
      check_struct_items ctx struct_items
        >> check_expr ctx' f e
        >> (expr_only_supported_in_merge false e)
    | LA.IfBlock (_, e, l1, l2) -> 
      check_expr ctx f e >> (check_items ctx f l1) >> (check_items ctx f l2)
    | LA.FrameBlock (pos, vars, nes, nis) ->
      let var_ids = List.map snd vars in
      let nes = List.map (fun x -> LA.Body x) nes in
      check_items ctx (fun _ e -> no_temporal_operator "frame block initialization" e) nes >>
      check_items ctx f nes >> (check_items ctx f nis) >>
      (Res.seq_ (List.map (no_assert_in_frame_init pos) nes)) >>
      (Res.seq_ (List.map (fun (p, v) -> no_a_dangling_identifier ctx p v) vars)) >>
      (*  Make sure 'nes' and 'nis' LHS vars are in 'vars_ids' *)
      (Res.seq_ (List.map (check_frame_vars pos var_ids) nis)) >>
      (Res.seq_ (List.map (check_frame_vars pos var_ids) nes))
    | Body (Assert (_, e)) 
    | AnnotProperty (_, _, e, _) -> (check_expr ctx f e)
    | AnnotMain _ -> Ok ()
  in
  (* Check for duplicate properties *)
  Res.seq_chain (fun props -> over_props props) StringSet.empty items
  >> Res.seqM (fun x _ -> x) () (List.map (check_item ctx f) items)

and check_struct_items ctx items =
  let r items = check_struct_items ctx items in
  match items with
  | [] -> Ok ()
  | (LA.SingleIdent (pos, id)) :: tail ->
    no_a_dangling_identifier ctx pos id >> r tail
  | (ArrayDef (pos, id, _)) :: tail ->
    no_a_dangling_identifier ctx pos id >> r tail
  | (TupleStructItem (pos, _)) :: _
  | (TupleSelection (pos, _, _)) :: _
  | (FieldSelection (pos, _, _)) :: _
  | (ArraySliceStructItem (pos, _, _)) :: _
    -> syntax_error pos UnsupportedAssignment

(* Within a frame block, make sure vars in the LHS of 'ni' appear somehwere in 'vars'  *)
and check_frame_vars pos vars ni = 
  let vars_of_ni = List.map snd (LAH.defined_vars_with_pos ni) in
  let unlisted = 
    H.HStringSet.diff (H.HStringSet.of_list vars_of_ni) (H.HStringSet.of_list vars)
  in
  match H.HStringSet.choose_opt unlisted with
  | None -> Res.ok ()
  | Some var -> syntax_error pos (MisplacedVarInFrameBlock var)

and no_assert_in_frame_init pos = function
  | LA.Body (Assert _) -> syntax_error pos MisplacedAssertInFrameBlock
  | _ -> Res.ok ()


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
    | GhostVars (_, _, e) -> check_expr ctx f e
    | AssumptionVars (pos, _) ->
      if not is_contract_node then Ok ()
      else syntax_error pos AssumptionVariablesInContractNode
    | GhostConst decl -> (
      let check = match decl with
      | LA.FreeConst _ -> Ok ()
      | UntypedConst (_, i, e)
      | TypedConst (_, i, e, _) -> check_const_expr_decl i ctx e
      in
      check >> Ok ()
    )
    | ContractCall (pos, i, args, outputs) -> (
      if StringMap.mem i ctx.contracts then (
        check_expr_list ctx f args
        >> Res.seqM (fun x _ -> x) () (List.map
           (no_a_dangling_identifier ctx pos) outputs)
      )
      else syntax_error pos (UndefinedContract i)
    )
  in
  Res.seqM (fun x _ -> x) () (List.map (check_contract_item ctx f) contract)

and check_expr ctx f (expr:LustreAst.expr) =
  let res = f ctx expr in
  let check = function
    | LA.RecordProject (_, e, _)
    | TupleProject (_, e, _)
    | UnaryOp (_, _, e)
    | ConvOp (_, _, e)
    | When (_, e, _)
    | Pre (_, e)
      -> check_expr ctx f e
    | Quantifier (_, _, vars, e) ->
        let over_vars ctx (_, i, ty) = ctx_add_quant_var ctx i (Some ty) in
        let ctx = List.fold_left over_vars ctx vars in
        check_expr ctx f e
    | BinaryOp (_, _, e1, e2)
    | CompOp (_, _, e1, e2)
    | ArrayConstr (_, e1, e2)
    | ArrayIndex (_, e1, e2)
    | Arrow (_, e1, e2)
      -> (check_expr ctx f e1) >> (check_expr ctx f e2)
    | TernaryOp (_, _, e1, e2, e3)
      -> (check_expr ctx f e1) >> (check_expr ctx f e2) >> (check_expr ctx f e3)
    | GroupExpr (_, _, e)
    | Call (_, _, e)
      -> check_expr_list ctx f e
    | RecordExpr (_, _, e)
    | Merge (_, _, e)
      -> let e = List.map (fun (_, e) -> e) e in check_expr_list ctx f e
    | Condact (_, e1, e2, _, e3, e4)
      -> (check_expr ctx f e1) >> (check_expr ctx f e2)
        >> (check_expr_list ctx f e3) >> (check_expr_list ctx f e4)
    | Activate (_, _, e1, e2, e3) ->
      (check_expr ctx f e1) >> (check_expr ctx f e2) >> (check_expr_list ctx f e3)
    | RestartEvery (_, _, e1, e2)
      -> (check_expr_list ctx f e1) >> (check_expr ctx f e2)
    | StructUpdate (_, e1, l, e2) ->
      (check_expr ctx f e1) >> (check_expr ctx f e2) >>
      (let l =
         List.filter_map
          (function | LA.Label _ -> None | Index (_, e) -> Some e) l
       in
       check_expr_list ctx f l
      )
    | ChooseOp (_, (_, i, ty), e1, None) -> 
      let extn_ctx = ctx_add_local ctx i (Some ty) in
      (check_expr extn_ctx f e1)
    | ChooseOp (_, (_, i, ty), e1, Some e2) -> 
      let extn_ctx = ctx_add_local ctx i (Some ty) in
      (check_expr extn_ctx f e1) >> (check_expr extn_ctx f e2)
    | Ident _ | ModeRef _ | Const _ -> Ok ()
  in
  res >> check expr
and check_expr_list ctx f l =
  Res.seqM (fun x _ -> x) () (List.map (check_expr ctx f) l)

let no_mismatched_clock is_bool e =
  let ctx = empty_ctx () in
  let clocks_match c1 c2 =
    match c1, c2 with
    | LA.ClockTrue, LA.ClockTrue -> true
    | ClockPos i, ClockPos j -> HString.equal i j
    | ClockNeg i, ClockNeg j -> HString.equal i j
    | ClockConstr (i1, i2), ClockConstr (j1, j2) ->
      HString.equal i1 j1 && HString.equal i2 j2
    | _ -> false
  in
  let clocks_match_result pos c1 c2 =
    if clocks_match c1 c2 then Ok()
    else syntax_error pos ClockMismatchInMerge
  in
  let check_clocks clock = function
    | LA.When (pos, _, c) -> clocks_match_result pos c clock
    | LA.Activate (pos, _, c, _, _) ->
      let* clk_exp =
        match c with
        | LA.Ident (_, i) -> Ok (LA.ClockPos i)
        | LA.UnaryOp (_, LA.Not, LA.Ident (_, i)) -> Ok (LA.ClockNeg i)
        | LA.CompOp (_, LA.Eq, LA.Ident (_, c), LA.Ident (_, cv)) ->
          Ok (LA.ClockConstr (cv, c))
        | _ -> syntax_error pos (IllegalClockExprInActivate c)
      in
      clocks_match_result pos clk_exp clock
    | _ -> Ok ()
  in
  let check_merge = function
    | LA.Merge (_, clock, exprs) ->
      if not is_bool then
        let case (i, e) = check_expr ctx
          (fun _ -> check_clocks (ClockConstr (i, clock))) e
        in
        List.fold_left (>>) (Ok ()) (List.map case exprs)
      else
        let true_variant = List.nth_opt exprs 0 in
        let false_variant = List.nth_opt exprs 1 in
        (match true_variant, false_variant with
        | Some (_, e1), Some (_, e2) ->
          check_clocks (ClockPos clock) e1
            >> check_clocks (ClockNeg clock) e2
        | _ -> Ok ())
    | _ -> Ok ()
  in
  check_expr ctx (fun _ -> check_merge) e
