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
module NI = NodeId
module Ctx = TypeCheckerContext

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
  | UndefinedOutput of HString.t 
  | DuplicateProperty of HString.t
  | InvalidPropertyName of HString.t
  | UndefinedNode of HString.t
  | UndefinedContract of HString.t
  | DanglingIdentifier of HString.t
  | QuantifiedVariableInPre of HString.t
  | QuantifiedVariableInNodeArgument of HString.t * HString.t
  | SymbolicArrayIndexInNodeArgument of HString.t * HString.t
  | QuantifiedVariableInLazyGuardedNodeCall of HString.t * HString.t
  | SymbolicArrayIndexInLazyGuardedNodeCall of HString.t * HString.t
  | QuantifiedVariableInTypeAscription of HString.t 
  | SymbolicArrayIndexInTypeAscription of HString.t 
  | IllegalNodeCall of (HString.t * string)
  | IllegalAnyOp of string
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
  | MultAssignArrayDef
  | AssumptionVariablesInContractNode
  | MisplacedVarInFrameBlock of LustreAst.ident
  | MisplacedAssertInFrameBlock
  | OpaqueWithoutContract of LustreAst.ident
  | TransparentWithoutBody of LustreAst.ident
  | IllegalHistoryVar of LustreAst.ident
  | InductiveVarsWithArrayConstr of LustreAst.expr

type error = [
  | `LustreSyntaxChecksError of Lib.position * error_kind
]

let error_message kind = match kind with
  | Unknown s -> s
  | UndefinedLocal id -> "Local variable '"
    ^ HString.string_of_hstring id ^ "' is not defined via an equation or frame block"
  | DuplicateLocal (id, pos) -> "Local variable '"
    ^ HString.string_of_hstring id ^ "' has already been defined at position " ^ 
     (Lib.string_of_t Lib.pp_print_position pos) 
  | DuplicateOutput (id, pos) -> "Output variable '"
    ^ HString.string_of_hstring id ^ "' has already been defined at position " ^
    (Lib.string_of_t Lib.pp_print_position pos) 
  | UndefinedOutput id -> "Output variable '"
    ^ HString.string_of_hstring id ^ "' is not defined via an equation or frame block"
  | DuplicateProperty id -> "Property '"
  ^ HString.string_of_hstring id ^ "' has more than one definition"
  | InvalidPropertyName id -> "Property name '"
  ^ HString.string_of_hstring id ^ "' contains forbidden characters. Property names cannot contain '[' or ']'."
  | UndefinedNode id -> "Node or function '"
    ^ HString.string_of_hstring id ^ "' is undefined"
  | UndefinedContract id -> "Contract '"
    ^ HString.string_of_hstring id ^ "' is undefined"
  | DanglingIdentifier id -> "Unknown identifier '"
    ^ HString.string_of_hstring id ^ "'"
  | QuantifiedVariableInPre var -> "Quantified variable '"
    ^ HString.string_of_hstring var ^ "' is not allowed in an argument to pre operator"
  | QuantifiedVariableInNodeArgument (var, node) -> "Quantified variable or refinement type bound variable '"
    ^ HString.string_of_hstring var ^ "' is not allowed in an argument of a call to node or non-inlinable function '"
    ^ HString.string_of_hstring node ^ "'"
  | SymbolicArrayIndexInNodeArgument (idx, node) -> "Symbolic array index '"
    ^ HString.string_of_hstring idx ^ "' is not allowed in an argument of a call to node or non-inlinable function '"
    ^ HString.string_of_hstring node ^ "'"
  | QuantifiedVariableInLazyGuardedNodeCall (var, node) -> "Quantified variable or refinement type bound variable '"
    ^ HString.string_of_hstring var ^ "' appears in a lazy branch guard, so calling non-inlinable function '"
    ^ HString.string_of_hstring node ^ "' in that branch is not allowed"
  | SymbolicArrayIndexInLazyGuardedNodeCall (idx, node) -> "Symbolic array index '"
    ^ HString.string_of_hstring idx ^ "' appears in a lazy branch guard, so calling non-inlinable function '"
    ^ HString.string_of_hstring node ^ "' in that branch is not allowed"
  | QuantifiedVariableInTypeAscription var -> "Quantified variable '"
    ^ HString.string_of_hstring var ^ "' is not allowed in type ascription with type that contains temporal operators or non-inlinable node or function calls"
  | SymbolicArrayIndexInTypeAscription idx -> "Symbolic array index '"
    ^ HString.string_of_hstring idx ^ "' is not allowed in type ascription with type that contains temporal operators or non-inlinable node or function calls"
  | IllegalNodeCall (node, variant) -> "Illegal call to node '"
    ^ HString.string_of_hstring node ^ "', " ^ variant ^ " can only include calls to other functions, not nodes"
  | IllegalAnyOp variant -> "Illegal `any` operator; "
    ^ variant ^ " cannot contain `any` operators. Maybe you meant to use `choose`?"
  | NodeCallInConstant id -> "Illegal node call, 'any'/'choose' operator, or type ascription in definition of constant '" ^ HString.string_of_hstring id ^ "'"
  | NodeCallInGlobalTypeDecl id -> "Illegal node call, 'any'/'choose' operator, or type ascription in definition of global type '" ^ HString.string_of_hstring id ^ "'"
  | IllegalTemporalOperator (kind, variant) -> "Illegal " ^ kind ^ " in expression, " ^ variant ^ " cannot have state"
  | IllegalImportOfStatefulContract contract -> "Illegal import of stateful contract '"
    ^ HString.string_of_hstring contract ^ "'. Functions can only be specified by stateless contracts"
  | UnsupportedClockedInputOrOutput -> "Clocked inputs or outputs are not supported"
  | UnsupportedClockedLocal id -> "Clocked node local variable not supported for '" ^ HString.string_of_hstring id ^ "'"
  | UnsupportedExpression e -> "The expression '" ^ LA.string_of_expr e ^ "' is not supported"
  | UnsupportedOutsideMerge e -> "The expression '" ^ LA.string_of_expr e ^ "' is only supported inside a merge"
  | UnsupportedWhen e -> "The `when` expression '" ^ LA.string_of_expr e ^ "' can only be the top most expression of a merge case"
  | UnsupportedParametricDeclaration -> "Parametric nodes and functions are not supported"
  | UnsupportedAssignment -> "Assignment not supported"
  | MultAssignArrayDef -> "Inductive array definition within multiple assignment is not supported"
  | AssumptionVariablesInContractNode -> "Assumption variables not supported in contract nodes"
  | MisplacedVarInFrameBlock id -> "Variable '" ^ HString.string_of_hstring id ^ "' is defined in the frame block but not declared in the frame block header"
  | MisplacedAssertInFrameBlock -> "Assertion not allowed in frame block initialization"
  | OpaqueWithoutContract n -> "An opaque annotation found for a node/function without a contract: " ^ HString.string_of_hstring n
  | TransparentWithoutBody n -> "A transparent annotation found for an imported node/function: " ^ HString.string_of_hstring n
  | IllegalHistoryVar id -> "History type constructor uses illegal quantified variable '" ^ HString.string_of_hstring id ^ "'"
  | InductiveVarsWithArrayConstr e -> "Array constructor expression '" ^ LA.string_of_expr e ^ "' not supported within multi-dimensional inductive array equation"

let syntax_error pos kind = Error (`LustreSyntaxChecksError (pos, kind))

type warning_kind = 
  | UnusedBoundVariableWarning of HString.t

let warning_message warning = match warning with
  | UnusedBoundVariableWarning id -> "Unused 'any' operator bound variable " ^ HString.string_of_hstring id

let error_if_lus_strict = function
  | UnusedBoundVariableWarning _ -> false

type warning = [
  | `LustreSyntaxChecksWarning of Lib.position * warning_kind
]

let mk_warning pos kind = `LustreSyntaxChecksWarning (pos, kind)

let (let*) = Result.bind
let (>>) = fun a b -> let* _ = a in b

type node_data = unit (* We used to need data, but not anymore *)

type contract_data = {
  stateful: bool;
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
  symbolic_array_indices : LustreAst.lustre_type option StringMap.t;
  lazy_cond_vars : LA.SI.t; }

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
  lazy_cond_vars = LA.SI.empty;
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

let ctx_add_lazy_cond_vars ctx vars = {
    ctx with lazy_cond_vars = LA.SI.union ctx.lazy_cond_vars vars
  }

let ctx_add_lazy_vars_from_guard ctx guard_expr =
  let vars = LAH.vars_without_node_call_ids guard_expr in
  let lazy_vars =
    LA.SI.filter
      (fun v -> StringMap.mem v ctx.quant_vars || StringMap.mem v ctx.symbolic_array_indices)
      vars
  in
  ctx_add_lazy_cond_vars ctx lazy_vars

(* Expression contains a pre, an arrow, or a call to a node *)
let rec has_stateful_op ctx =
function
| LA.Pre _ | Arrow _ -> true

| RestartEvery _
| AnyOp _ -> true
| ChooseOp _ -> false  

| Condact (_, e, r, i, l1, l2) ->
  StringMap.mem (NI.get_internal_name i) ctx.nodes ||
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
  StringMap.mem (NI.get_internal_name i) ctx.nodes ||
  has_stateful_op ctx e ||
  has_stateful_op ctx r ||
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l

| Call (_, _, node_id, l) ->
  StringMap.mem (NI.get_internal_name node_id) ctx.nodes ||
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l

| Const _ | Ident _ | ModeRef _  | EmptyMap _ | EmptySet _ -> false

| RecordProject (_, e, _) | ConvOp (_, _, e)
| UnaryOp (_, _, e) | When (_, e, _)
| Quantifier (_, _, _, e) | Extract (_, e, _, _) ->
  has_stateful_op ctx e

| BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2)
| IndexAccess (_, e1, e2, _) | ArrayConstr (_, e1, e2)  ->
  has_stateful_op ctx e1 || has_stateful_op ctx e2

| TypeAscription (_, e, _) -> has_stateful_op ctx e

| TernaryOp (_, _, e1, e2, e3) ->
  has_stateful_op ctx e1 || has_stateful_op ctx e2 || has_stateful_op ctx e3

| GroupExpr (_, _, l) ->
  List.fold_left
    (fun acc e -> acc || has_stateful_op ctx e)
    false l

| Merge (_, _, l)
| RecordExpr (_, _, _, l) ->
  List.fold_left
    (fun acc (_, e) -> acc || has_stateful_op ctx e)
    false l

| StructUpdate (_, e1, li, e2) ->
  has_stateful_op ctx e1 ||
  match e2 with 
  | Some e2 -> has_stateful_op ctx e2 
  | None -> false 
  ||
  List.fold_left
    (fun acc l_or_i -> acc ||
      (match l_or_i with
      | LA.Label _ -> false
      | GenericIndex (_, e) 
      | MapIndex (_, e)
      | SetIndex (_, e)
      | Index (_, e) -> has_stateful_op ctx e
      )
    )
    false li


let build_global_ctx (decls:LustreAst.t) =
  let contract_decls, others =
    List.partition (function LA.ContractNodeDecl _ -> true | _ -> false) decls
  in
  let over_decls acc = function
    | LA.TypeDecl (_, AliasType (_, _, _, (EnumType (_, _, variants) as ty))) -> 
      List.fold_left (fun a v -> ctx_add_const a v (Some ty)) acc variants
    | ConstDecl (_, FreeConst (_, i, ty)) -> ctx_add_free_const acc i (Some ty)
    | ConstDecl (_, UntypedConst (_, i, _)) -> ctx_add_const acc i None
    | ConstDecl (_, TypedConst (_, i, _, ty)) -> ctx_add_const acc i (Some ty)
    (* The types here can be constructed from the available information
      but this type information is not needed for syntax checks for now *)
    | NodeDecl (_, (node_id, _, _, _, _, _, _, _, _)) ->
      ctx_add_node acc (NI.get_internal_name node_id) ()
    | FuncDecl (_, (node_id, _, _, _, _, _, _, _, _), _) ->
      ctx_add_func acc (NI.get_internal_name node_id) ()
    | _ -> acc
  in
  let ctx = List.fold_left over_decls (empty_ctx ()) others in
  let over_contract_eq (stateful, imports) = function
    | LA.GhostConst (FreeConst _) ->
      (stateful, imports)
    | GhostConst (UntypedConst (_, _, e))
    | GhostConst (TypedConst (_, _, e, _))
    | GhostVars (_, _, e)
    | Assume (_, _, _, e) ->
      (stateful || has_stateful_op ctx e, imports)
    | Guarantee (_, _, _, e)
    | Decreases (_, e) ->
      (stateful || has_stateful_op ctx e, imports)
    | Mode (_, _, reqs, enss) ->
      let req_or_ens_has_stateful_op req_ens_lst =
        List.fold_left
          (fun acc (_, _, e) -> acc || has_stateful_op ctx e)
          false req_ens_lst
      in
      let stateful' = stateful ||
        req_or_ens_has_stateful_op reqs || req_or_ens_has_stateful_op enss
      in
      (stateful', imports)
    | ContractCall (_, node_id, _, ins, _) ->
      let arg_has_stateful_op ins =
        List.fold_left
          (fun acc e -> acc || has_stateful_op ctx e)
          false ins
      in
      (stateful || arg_has_stateful_op ins,
       StringSet.add (NI.get_internal_name node_id) imports
      )
    | AssumptionVars _ ->
      (stateful, imports)
  in
  let over_contract_decls acc = function
    | LA.ContractNodeDecl (_, (node_id, _, _, _, (_, eqns))) ->
      let stateful, imports =
        List.fold_left
          over_contract_eq
          (false, StringSet.empty)
          eqns
      in
      ctx_add_contract acc (NI.get_internal_name node_id) {stateful; imports }
    | _ -> acc
  in
  List.fold_left over_contract_decls ctx contract_decls

let build_contract_ctx ctx eqns =
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

let unwrap = function 
| Result.Ok r -> r 
| Error _ -> assert false

let build_equation_ctx ctx tc_ctx = function
  | LA.StructDef (_, items) ->
    let over_items ctx = function
      | LA.ArrayDef (_, i, indices) ->
        let output_type_opt = StringMap.find_opt i ctx.locals |> Lib.join in
        let is_symbolic = match output_type_opt with
          | Some ty -> 
            (* Chase type aliases if we have proper type context *)
            let ty = match tc_ctx with 
            | Some tc_ctx -> 
              LustreTypeChecker.expand_type_syn_reftype_history tc_ctx ty |> unwrap 
            | None -> ty 
            in
            (match ty with
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
  | LA.IfBlock (_, _, l1, l2)
  | LA.WhenBlock (_, _, l1, l2) ->
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

let outputs_exactly_one_definition outputs items =
  let over_outputs = function
  | (p, id, _, _) ->
    let poss = List.map (find_var_def_count id) items |> List.flatten in
    match List.length poss with
      | 0 -> syntax_error p (UndefinedOutput id) 
      | 1 -> Ok ()
      | _ -> 
        let poss = List.sort Lib.compare_pos poss in
        syntax_error (List.hd (List.tl poss)) (DuplicateOutput (id, List.hd poss))
  in
  Res.seq (List.map over_outputs outputs)

let no_dangling_calls ctx = function
  | LA.Condact (pos, _, _, node_id, _, _)
  | Activate (pos, node_id, _, _, _) 
  | Call (pos, _, node_id, _) ->
    let check_nodes = StringMap.mem (NI.get_internal_name node_id) ctx.nodes in
    let check_funcs = StringMap.mem (NI.get_internal_name node_id) ctx.functions in
    (match check_nodes, check_funcs with
    | true, _ -> Ok ()
    | _, true -> Ok ()
    | false, false -> syntax_error pos (UndefinedNode (NI.get_user_name node_id)))
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
  (*| LA.Call (pos, _, i, args) ->
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
    List.fold_left (>>) (Ok ()) check*)
  | LA.Pre (_, IndexAccess (_, _, _, _)) -> Ok ()
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

let no_calls_to_node scope ctx = function
  | LA.Condact (pos, _, _, node_id, _, _)
  | Activate (pos, node_id, _, _, _)
  | RestartEvery (pos, node_id, _, _) 
  | Call (pos, _, node_id, _) ->
    let check_nodes = StringMap.mem (NI.get_internal_name node_id) ctx.nodes in
    if check_nodes then
      syntax_error pos 
        (IllegalNodeCall (NI.get_user_name node_id, scope))
    else Ok ()
  | AnyOp (pos, _, _) -> syntax_error pos (IllegalAnyOp scope)
  | _ -> Ok ()

let no_temporal_operator decl_ctx expr =
  match expr with
  | LA.Pre (pos, _) -> syntax_error pos (IllegalTemporalOperator ("pre", decl_ctx))
  | Arrow (pos, _, _) -> syntax_error pos (IllegalTemporalOperator ("arrow", decl_ctx))
  | _ -> Ok []
  
let has_forbidden_chars (name : H.t option) =
    match name with 
    | Some n -> 
        (let s = HString.string_of_hstring n in
        String.contains s '[' || String.contains s ']')
    | None -> false

(* Record duplicate properties if we find them *)
let over_props props = function
  | LA.AnnotProperty (pos, name, _, kind) ->

    
    if has_forbidden_chars name then
      let name = LustreAstHelpers.name_of_prop pos name kind in
      syntax_error pos (InvalidPropertyName name)
    else
      let name = LustreAstHelpers.name_of_prop pos name kind in
      if StringSet.mem name props
      then syntax_error pos (DuplicateProperty name)
      else Ok (StringSet.add name props)
  | _ -> Ok props
let over_named_contract_prop props pos name =
  if has_forbidden_chars name then
    let name =
      match name with
      | Some name -> name
      | None -> HString.mk_hstring ""
    in
    syntax_error pos (InvalidPropertyName name)
  else
    match name with
    | None ->
        Ok props
    | Some name ->
        if StringSet.mem name props then
          syntax_error pos (DuplicateProperty name)
        else
          Ok (StringSet.add name props)
let over_contract_props props = function
  | LA.Assume (pos, name, _, _)
  | LA.Guarantee (pos, name, _, _) ->
      over_named_contract_prop props pos name

  | LA.Mode (_, _, rs, gs) ->
      let* props =
        Res.seq_chain
          (fun props (pos, name, _) ->
             over_named_contract_prop props pos name)
          props
          rs
      in
      Res.seq_chain
        (fun props (pos, name, _) ->
           over_named_contract_prop props pos name)
        props
        gs

  | LA.GhostVars _
  | LA.GhostConst _
  | LA.AssumptionVars _
  | LA.Decreases _
  | LA.ContractCall _ ->
      Ok props

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
      | LA.ContractCall (pos, node_id, _, _, _) ->
        acc >> (check_import_stateful StringSet.empty pos (NI.get_internal_name node_id) (NI.get_internal_name node_id))
      | _ -> acc
    in
    List.fold_left over_eqn (Ok ()) contract
  with Cycle ->
    Ok () (* Cycle will be rediscovered by lustreAstDependencies *)

let no_clock_inputs_or_outputs pos = function
  | LA.ClockTrue -> Ok ()
  | _ -> syntax_error pos UnsupportedClockedInputOrOutput

(* Make sure the History type constructor doesn't take a quantified variable as input *)
let check_quantified_vars ctx vars = 
  Res.seq (List.map (fun (_, _, ty) -> 
    match ty with
    | LA.History (pos, id) -> (
      match StringMap.find_opt id ctx.quant_vars with 
      | Some (Some _) -> syntax_error pos (IllegalHistoryVar id)
      | _ -> Res.ok ()
    )
    (* We don't currently need to recurse on other cases because a History type 
       cannot be nested within another type (see lustreParser.mly) *)
    | _ -> Ok ()
  ) vars)

let rec expr_only_supported_in_merge observer expr =
  let r = expr_only_supported_in_merge in
  let r_list obs e = Res.seqM (fun x _ -> x) () (List.map (r obs) e) in
  match expr with
  | LA.When (pos, _, _) as e -> syntax_error pos (UnsupportedWhen e)
  | Merge (_, _, e) -> 
    Res.seq_ (List.map (fun (_, e) -> match e with
      | LA.When (_, e, _) | e -> r true e)
      e)
  | Ident _ | Const _ | ModeRef _ | EmptyMap _ | EmptySet _ -> Ok ()
  | RecordProject (_, e, _)
  | UnaryOp (_, _, e)
  | ConvOp (_, _, e)
  | Pre (_, e)
  | Extract (_, e, _, _)
  | Quantifier (_, _, _, e) 
  | StructUpdate (_, e, _, None) -> r observer e
  | AnyOp (_, _, e)  
  | ChooseOp (_, _, e) -> r observer e 
  | BinaryOp (_, _, e1, e2) 
  | StructUpdate (_, e1, _, Some e2)
  | CompOp (_, _, e1, e2)
  | Arrow (_, e1, e2)
  | IndexAccess (_, e1, e2, _)
  | ArrayConstr (_, e1, e2) -> r observer e1 >> r observer e2
  | TypeAscription (_, e, _) -> r observer e
  | TernaryOp (_, _, e1, e2, e3)
    -> r observer e1 >> r observer e2 >> r observer e3
  | GroupExpr (_, _, e)
  | Call (_, _, _, e) -> r_list observer e
  | RecordExpr (_, _, _, e) -> r_list observer (List.map (fun (_, x) -> x) e)
  | Condact (_, e1, e2, _, e3, e4 )
    -> r observer e1 >> r observer e2 >> r_list observer e3 >> r_list observer e4
  | Activate (pos, _, _, _, _) as e ->
    if observer then Ok ()
    else syntax_error pos (UnsupportedOutsideMerge e)
  | RestartEvery (_, _, e1, e2) -> r_list observer e1 >> r observer e2

let check_opacity pos node_id contract is_ext = function
  | LA.Opaque when contract = None -> syntax_error pos (OpaqueWithoutContract node_id)
  | Transparent when is_ext -> syntax_error pos (TransparentWithoutBody node_id)
  | _ -> Ok ()

(* Empty check *)
let empty_ty_check _ _ = Ok []

let rec syntax_check (ast:LustreAst.t) =
  let ctx = build_global_ctx ast in
  let* warnings_decls = Res.seq (List.map (check_declaration ctx) ast) in 
  let warnings, decls = List.split warnings_decls in 
  Ok (List.flatten warnings, decls)

and check_ty_node_calls i ty = 
  match ty with 
    | LA.RefinementType (_, _, e) ->
      if LAH.expr_contains_call e
        then syntax_error (LAH.pos_of_expr e) (NodeCallInGlobalTypeDecl i)
        else Ok ()
    | TupleType (_, tys) 
    | GroupType (_, tys) -> Res.seq_ (List.map (check_ty_node_calls i) tys)
    | RecordType (_, _, tis) -> Res.seq_ (List.map (fun (_, _, ty) -> check_ty_node_calls i ty) tis)
    | ArrayType (_, (ty, e)) -> 
      check_ty_node_calls i ty 
      >> if LAH.expr_contains_call e
        then syntax_error (LAH.pos_of_expr e) (NodeCallInGlobalTypeDecl i)
        else Ok ()
    | UserType (_, tys, _) -> Res.seq_ (List.map (check_ty_node_calls i) tys)
    | Map (_, ty1, ty2) -> Res.seq_ (List.map (check_ty_node_calls i) [ty1; ty2])
    | Set (_, ty) -> check_ty_node_calls i ty
    | Bool _ | Int _ | Real _ | EnumType _
    | AbstractType _ | History _ | TArr _ | SBitVector _ | UBitVector _ -> Ok ()

and check_declaration: context -> LA.declaration -> ([> warning] list * LA.declaration, [> error]) result 
= fun ctx -> function
  | TypeDecl (span, FreeType (pos, id) ) -> Ok ([], LA.TypeDecl (span, FreeType (pos, id)))
  | TypeDecl (span, AliasType (pos, id, ps, ty) ) -> 
    check_ty_node_calls id ty >> Ok ([], LA.TypeDecl (span, AliasType (pos, id, ps, ty)))
  | ConstDecl (span, decl) ->
    let* warnings = match decl with
      | LA.FreeConst (_, i, ty) -> check_ty_node_calls i ty >> Res.ok [] 
      | UntypedConst (_, i, e) -> check_const_expr_decl i ctx e
      | TypedConst (_, i, e, ty) -> check_ty_node_calls i ty >> check_const_expr_decl i ctx e 
    in
    Ok (warnings, LA.ConstDecl (span, decl))
  | NodeDecl (span, decl) -> check_node_decl ctx span decl
  | FuncDecl (span, decl, is_rec) -> check_func_decl ctx span decl is_rec
  | ContractNodeDecl (span, decl) -> check_contract_node_decl ctx span decl
  | NodeParamInst (span, _) -> syntax_error span.start_pos UnsupportedParametricDeclaration

and check_const_expr_decl: H.t -> context -> LA.expr -> ([> warning] list, [>  error]) result 
= fun i ctx expr ->
  let composed_checks i ctx e =
    (no_dangling_identifiers ctx e) >> 
    (no_node_calls_in_constant i e) >> Ok []
  in
  check_expr ctx (composed_checks i) expr

and common_node_equations_checks ctx e =
    (no_dangling_calls ctx e)
    >> (no_dangling_identifiers ctx e)
    >> (no_quant_var_or_symbolic_index_in_node_call ctx e)
    >> Ok []

and common_contract_checks ctx e =
    (no_dangling_calls ctx e)
    >> (no_dangling_identifiers ctx e)
    >> (no_quant_var_or_symbolic_index_in_node_call ctx e)
    >> Ok []

(* Can't have from/within/at keywords in reachability queries in functions *)
and no_reachability_modifiers item = match item with 
  | LA.AnnotProperty (pos, _, _, Reachable (Some _)) -> 
    syntax_error pos (IllegalTemporalOperator ("pre", "reachability query modifier")) 
  | _ -> Ok ()

and check_input_items (pos, _id, _ty, clock, _const) =
  no_clock_inputs_or_outputs pos clock

and check_output_items (pos, _id, _ty, clock) =
  no_clock_inputs_or_outputs pos clock

and check_local_items: context -> LA.node_local_decl -> ([> warning] list, [> error]) result 
= fun ctx local -> match local with
  | LA.NodeConstDecl (_, FreeConst _) -> Ok ([])
  | LA.NodeConstDecl (_, UntypedConst (_, i, e)) -> check_const_expr_decl i ctx e
  | LA.NodeConstDecl (_, TypedConst (_, i, e, _)) -> check_const_expr_decl i ctx e
  | NodeVarDecl (_, (_, _, _, LA.ClockTrue)) -> Ok ([])
  | NodeVarDecl (_, (pos, i, _, _)) -> syntax_error pos (UnsupportedClockedLocal i)

and check_node_decl ctx span (node_id, ext, opac, params, inputs, outputs, locals, items, contract) =
  let props = StringSet.empty in
  let decl = LA.NodeDecl
    (span, (node_id, ext, opac, params, inputs, outputs, locals, items, contract))
  in
  check_opacity span.start_pos (NI.get_internal_name node_id) contract ext opac
  >> (locals_exactly_one_definition locals items)
  >> (if ext then (Res.ok []) else (outputs_exactly_one_definition outputs items))
  >> (Res.seq_ (List.map check_input_items inputs))
  >> (Res.seq_ (List.map check_output_items outputs)) >> 
  let* (warnings1, props) = (match contract with
  | Some c -> 
    let ctx =
      (* Locals are not visible in contracts *)
      build_local_ctx ctx [] inputs outputs
    in
    check_contract false ctx common_contract_checks empty_ty_check c props
  | None -> Ok (([], StringSet.empty))) in
  let ctx = build_local_ctx ctx locals inputs outputs in
  let* warnings2 = (Res.seq (List.map (check_local_items ctx) locals)) in
  let* (warnings3, _) = (check_items
  (build_local_ctx ctx locals [] []) (* Add locals to ctx *)
  common_node_equations_checks
  items 
  props) in
  (Ok (warnings1 @ List.flatten warnings2 @ warnings3, decl))

and check_func_decl ctx span (node_id, ext, opac, params, inputs, outputs, locals, items, contract) is_rec =
  let props = StringSet.empty in
  let ctx =
    (* Locals are not visible in contracts *)
    build_local_ctx ctx [] inputs outputs
  in
  let decl = LA.FuncDecl
    (span, (node_id, ext, opac, params, inputs, outputs, locals, items, contract), is_rec)
  in
  let composed_items_checks ctx e =
    (no_calls_to_node "functions" ctx e)
    >> (no_temporal_operator "functions" e)
    >> (common_node_equations_checks ctx e)
  in
  let function_contract_checks ctx e =
    (no_calls_to_node "function contracts" ctx e) >> 
    let* warnings1 =  (common_contract_checks ctx e) in
    let* warnings2 = (no_temporal_operator "function contracts" e) in 
    Ok (warnings1 @ warnings2)
  in
  check_opacity span.start_pos (NI.get_internal_name node_id) contract ext opac
  >> (Res.seq_ (List.map no_reachability_modifiers items))
  >> (Res.seq_ (List.map check_input_items inputs))
  >> (Res.seq_ (List.map check_output_items outputs)) >> 
  let* warnings1 = (Res.seq (List.map (check_local_items ctx) locals)) in
  let* (warnings2, props) = (match contract with
  | Some (p, c) -> no_stateful_contract_imports ctx c
    >> check_contract false ctx function_contract_checks empty_ty_check (p, c) props
  | None -> Ok ([], StringSet.empty)) in 
  let* (warnings3, _) = (check_items
    (build_local_ctx ctx locals [] []) (* Add locals to ctx *)
    composed_items_checks
    items
    props
  ) in
  (Ok (List.flatten warnings1 @ warnings2 @ warnings3, decl))

and check_contract_node_decl ctx span (id, params, inputs, outputs, contract) =
  let ctx = build_local_ctx ctx [] inputs outputs in
  let decl = LA.ContractNodeDecl
    (span, (id, params, inputs, outputs, contract))
  in
   (Res.seq_ (List.map check_input_items inputs))
    >> (Res.seq_ (List.map check_output_items outputs)) >> 
    let* (warnings, _) = (check_contract true ctx common_contract_checks empty_ty_check contract StringSet.empty) in
    (Ok (warnings, decl))

and check_items: context -> ?tc_ctx:Ctx.tc_context option -> (context -> LA.expr -> ([> warning] list, ([> error] as 'a)) result) ->
  LA.node_item list -> StringSet.t -> ([> warning] list * StringSet.t, 'a) result 
= fun ctx ?(tc_ctx=None) f items props ->
  
  let check_item: context -> Ctx.tc_context option -> (context -> LA.expr -> ([> warning] list, ([> error] as 'a)) result) ->
    LA.node_item -> ([> warning] list, 'a) result = fun ctx tc_ctx f -> function
    | LA.Body (Equation (_, lhs, e)) ->
      let ctx' = build_equation_ctx ctx tc_ctx lhs in
      let StructDef (_, struct_items) = lhs in
      check_struct_items ctx struct_items
        >> (expr_only_supported_in_merge false e)
        >> check_expr ctx' f e
    | LA.IfBlock (_, e, l1, l2) ->
      let* warnings1 = check_expr ctx f e in 
      let* (warnings2, props) = (check_items ctx ~tc_ctx f l1 props) in 
      let* (warnings3, _) = (check_items ctx ~tc_ctx f l2 props) in 
      Ok (warnings1 @ warnings2 @ warnings3)
    | LA.WhenBlock (_, e, l1, l2) ->
      let ctx_lazy = ctx_add_lazy_vars_from_guard ctx e in
      let lazy_when ctx e =
        (no_calls_to_node "a branch of a when block" ctx e)
        >> (no_temporal_operator "branches of a when block" e)
        >> (f ctx e)
      in
      let* warnings1 = check_expr ctx f e in
      let* warnings2, props = (check_items ctx_lazy ~tc_ctx lazy_when l1 props) in
      let* warnings3, _ = (check_items ctx_lazy ~tc_ctx lazy_when l2 props) in
      Ok (warnings1 @ warnings2 @ warnings3)
    | LA.FrameBlock (pos, vars, nes, nis) ->
      let var_ids = List.map snd vars in
      let nes = List.map (fun x -> LA.Body x) nes in
      (Res.seq_ (List.map (no_assert_in_frame_init pos) nes)) >>
      (Res.seq_ (List.map (fun (p, v) -> no_a_dangling_identifier ctx p v) vars)) >>
      (*  Make sure 'nes' and 'nis' LHS vars are in 'vars_ids' *)
      (Res.seq_ (List.map (check_frame_vars pos var_ids) nis)) >>
      (Res.seq_ (List.map (check_frame_vars pos var_ids) nes)) >> 
      let* (warnings1, props) = check_items ctx ~tc_ctx (fun _ e -> no_temporal_operator "frame block initializations" e) nes props in
      let* (warnings2, props) = check_items ctx ~tc_ctx f nes props in 
      let* (warnings3, _) = (check_items ctx ~tc_ctx f nis) props in
      Ok (warnings1 @ warnings2 @ warnings3)
    | Body (Assert (_, e)) 
    | AnnotProperty (_, _, e, _) -> (check_expr ctx f e)
    | AnnotMain _ -> Ok ([])
  in
  (* Check for duplicate properties *)
  let* props =
    Res.seq_chain
      (fun properties item -> over_props properties item)
      props
      items
  in  
  let* warnings = Res.seq (List.map (check_item ctx tc_ctx f) items) in 
    (Ok (List.flatten warnings, props))

and check_struct_items ctx items =
  let r items = check_struct_items ctx items in
  match items with
  | [] -> Ok ()
  | LA.ArrayDef (pos, _, _) :: _ :: _ 
  | _ :: ArrayDef (pos, _, _) :: _ ->  syntax_error pos MultAssignArrayDef
  | (SingleIdent (pos, id)) :: tail ->
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


and check_contract: bool -> context -> (context -> LA.expr -> ([> warning] list, ([> error] as 'a)) result) -> 
  (context -> LA.lustre_type -> ([> warning] list, 'a) result) ->
  LA.contract -> StringSet.t -> ([> warning] list * StringSet.t, 'a) result 
= fun is_contract_node ctx f oqv_on_ty (_, contract) props ->
  let ctx = build_contract_ctx ctx contract in
  let check_list e = Res.seq (List.map (check_expr ctx f) e) in
  let check_contract_item ctx f = function
    | LA.Assume (_, _, _, e) -> check_expr ctx f e
    | Guarantee (_, _, _, e) -> check_expr ctx f e
    | Mode (_, _, rs, gs) ->
      let rs = List.map (fun (_, _, e) -> e) rs in
      let gs = List.map (fun (_, _, e) -> e) gs in
      let* warnings1 = check_list rs in
      let* warnings2 = check_list gs in 
      Ok (List.flatten warnings1 @ List.flatten warnings2)
    | GhostVars (_, GhostVarDec (_, l), e) ->
      let* warnings1 = Res.seq (List.map (fun (_, _, ty) -> oqv_on_ty ctx ty) l) in
      let* warnings2 = check_expr ctx f e in
      Ok (List.flatten warnings1 @ warnings2)
    | AssumptionVars (pos, _) ->
      if not is_contract_node then Ok ([])
      else syntax_error pos AssumptionVariablesInContractNode
    | GhostConst decl -> (
      let* warnings1 =
        match decl with
        | LA.FreeConst (_, _, ty) -> oqv_on_ty ctx ty
        | LA.TypedConst (_, _, _, ty) -> oqv_on_ty ctx ty
        | LA.UntypedConst _ -> Ok []
      in
      match decl with
      | LA.FreeConst _ -> Ok warnings1
      | UntypedConst (_, i, e)
      | TypedConst (_, i, e, _) ->
        let* warnings2 = check_const_expr_decl i ctx e in
        Ok (warnings1 @ warnings2)
    )
    | ContractCall (pos, node_id, _, args, outputs) -> (
      if StringMap.mem (NI.get_internal_name node_id) ctx.contracts then (
        Res.seqM (fun x _ -> x) () (List.map
           (no_a_dangling_identifier ctx pos) outputs) >>
        check_expr_list ctx f args
      )
      else syntax_error pos (UndefinedContract (NI.get_internal_name node_id))
    )
    | Decreases (_, e) -> check_expr ctx f e
  in
  let* props =
  Res.seq_chain
    (fun props item -> over_contract_props props item)
    props
    contract
  in
  let* warnings = Res.seq (List.map (check_contract_item ctx f) contract) in 
  Ok(List.flatten warnings, props)

and check_ty ctx f = function 
| LA.RefinementType (_, (_, i, ty), expr) -> 
  let ctx = ctx_add_quant_var ctx i (Some ty) in
  check_expr ctx f expr
| GroupType (_, tys) 
| TupleType (_, tys) -> 
  let* warnings = Res.seq (List.map (check_ty ctx f) tys) in 
  Res.ok (List.flatten warnings)
| Map (_, ty1, ty2) 
| TArr (_, ty1, ty2) -> 
  let* warnings = Res.seq (List.map (check_ty ctx f) [ty1; ty2]) in 
  Res.ok (List.flatten warnings)
| Set (_, ty) -> 
  check_ty ctx f ty
| ArrayType (_, (ty, expr)) -> 
  let* warnings1 = check_ty ctx f ty in 
  let* warnings2 = check_expr ctx f expr in 
  Res.ok (warnings1 @ warnings2)
| RecordType (_, _, tis) -> 
  let* warnings = Res.seq (List.map (fun (_, _, ty) -> check_ty ctx f ty) tis) in 
  Res.ok (List.flatten warnings)
| Int _ | Bool _ | SBitVector _ | UBitVector _ 
| Real _ | AbstractType _ | UserType _ | EnumType _
| History _ -> Res.ok []



and check_expr: context -> (context -> LA.expr -> ([> warning] list, ([> error] as 'a)) result) ->
  LA.expr -> ([> warning] list, 'a) result = fun ctx f (expr:LustreAst.expr) ->
  let lazy_ite ctx e =
    (no_calls_to_node "a branch of a when-then-else" ctx e)
    >> (no_temporal_operator "branches of a when-then-else" e)
    >> (f ctx e)
  in
  let lazy_bool_op op ctx e =
    (no_calls_to_node ("the argument of " ^ op)  ctx e)
    >> (no_temporal_operator ("arguments of " ^ op) e)
    >> (f ctx e)
  in
  let res = f ctx expr in
  let check = function
    | LA.RecordProject (_, e, _)
    | UnaryOp (_, _, e)
    | ConvOp (_, _, e)
    | When (_, e, _)
    | Extract (_, e, _, _)
    | Pre (_, e) -> 
      check_expr ctx f e 
    | TypeAscription (_, e, ty) ->
      let* warnings1 = check_expr ctx f e in
      let* warnings2 = check_ty ctx f ty in
      Res.ok (warnings1 @ warnings2)
    | Quantifier (_, _, vars, e) ->
      let over_vars (warnings, ctx) (_, i, ty) = 
        let* warnings2 = check_ty ctx f ty in
        Res.ok (warnings @ warnings2, ctx_add_quant_var ctx i (Some ty))
      in
      let* (warnings, ctx) = Res.seq_chain over_vars ([], ctx) vars in
      let* _ = check_quantified_vars ctx vars in
      let* warnings2 = check_expr ctx f e in 
      Res.ok (warnings @ warnings2)
    | BinaryOp (_, AndThen, e1, e2) ->
      let ctx_lazy = ctx_add_lazy_vars_from_guard ctx e1 in
      let* warnings1 = (check_expr ctx (lazy_bool_op "'and then'") e1) in 
      let* warnings2 = (check_expr ctx_lazy (lazy_bool_op "'and then'") e2) in 
      Ok (warnings1 @ warnings2)
    | BinaryOp (_, OrElse, e1, e2) ->
      let ctx_lazy = ctx_add_lazy_vars_from_guard ctx e1 in
      let* warnings1 = (check_expr ctx (lazy_bool_op "'or else'") e1) in 
      let* warnings2 = (check_expr ctx_lazy (lazy_bool_op "'or else'") e2) in 
      Ok (warnings1 @ warnings2)
    | BinaryOp (_, LazyImpl, e1, e2) ->
      let ctx_lazy = ctx_add_lazy_vars_from_guard ctx e1 in
      let* warnings1 = (check_expr ctx (lazy_bool_op "==>") e1) in 
      let* warnings2 = (check_expr ctx_lazy (lazy_bool_op "==>") e2) in 
      Ok (warnings1 @ warnings2)
    | BinaryOp (_, _, e1, e2)
    | CompOp (_, _, e1, e2)
    | IndexAccess (_, e1, e2, _)
    | Arrow (_, e1, e2) ->
      let* warnings1 = (check_expr ctx f e1) in 
      let* warnings2 = (check_expr ctx f e2) in 
      Ok (warnings1 @ warnings2)
    | ArrayConstr (p, e1, e2) as e -> 
      let* warnings1 = (check_expr ctx f e1) in 
      let* warnings2 = (check_expr ctx f e2) in 
      let ivars = 
        StringMap.bindings ctx.array_indices @ StringMap.bindings ctx.symbolic_array_indices 
        |> List.map fst |> LA.SI.of_list
      in
      let num_ivars = LA.SI.cardinal ivars in
      let evars = LustreAstHelpers.vars_without_node_call_ids e1 in 
      let ie_vars = LA.SI.inter ivars evars in 
      let num_ie_vars = LA.SI.cardinal ie_vars in
      (* Disallow inductive variables in ArrayConstrs if the array is multidimensional *)
      if num_ivars >= 2 && num_ie_vars >= 1 
      then syntax_error p (InductiveVarsWithArrayConstr e) 
      else Ok (warnings1 @ warnings2)
    | TernaryOp (_, Ite, e1, e2, e3) -> 
      let* warnings1 = (check_expr ctx f e1) in
      let* warnings2 = (check_expr ctx f e2) in 
      let* warnings3 = (check_expr ctx f e3) in 
      Ok (warnings1 @ warnings2 @ warnings3)
    | TernaryOp (_, LazyIte, e1, e2, e3) -> 
      let ctx_lazy = ctx_add_lazy_vars_from_guard ctx e1 in
      let* warnings1 = (check_expr ctx f e1) in
      let* warnings2 = (check_expr ctx_lazy lazy_ite e2) in
      let* warnings3 = (check_expr ctx_lazy lazy_ite e3) in
      Ok (warnings1 @ warnings2 @ warnings3)
    | GroupExpr (_, _, e)
    | Call (_, _, _, e)
      -> check_expr_list ctx f e
    | RecordExpr (_, _, _, e)
    | Merge (_, _, e)
      -> let e = List.map (fun (_, e) -> e) e in check_expr_list ctx f e
    | Condact (_, e1, e2, _, e3, e4) -> 
      let* warnings1 = (check_expr ctx f e1) in 
      let* warnings2 = (check_expr ctx f e2) in
      let* warnings3 = (check_expr_list ctx f e3) in
      let* warnings4 = (check_expr_list ctx f e4) in 
      Ok (warnings1 @ warnings2 @ warnings3 @ warnings4)
    | Activate (_, _, e1, e2, e3) ->
      let* warnings1 = (check_expr ctx f e1) in 
      let* warnings2 = (check_expr ctx f e2) in 
      let* warnings3 = (check_expr_list ctx f e3) in 
      Ok (warnings1 @ warnings2 @ warnings3)
    | RestartEvery (_, _, e1, e2) -> 
      let* warnings1 = (check_expr_list ctx f e1) in 
      let* warnings2 = (check_expr ctx f e2) in
      Ok (warnings1 @ warnings2)
    | StructUpdate (_, e1, l, e2) ->
      let* warnings1 = (check_expr ctx f e1) in 
      let* warnings2 = match e2 with 
      | Some e2 -> check_expr ctx f e2 
      | None -> Res.ok [] 
      in
      let l =
         List.filter_map
          (function | LA.Label _ -> None | Index (_, e) 
                    | GenericIndex (_, e) | MapIndex (_, e) | SetIndex (_, e) -> 
          (* Procrastinate on dangling identifier checks for lone Ident expressions 
             until type checking. This is necessary because we don't have the 
             right context to distinguish a dangling identifier from one referencing 
             a record type field *)
          match e with 
          | LA.Ident (_, _) -> None 
          | _ -> Some e) l
       in
       let* warnings3 = check_expr_list ctx f l in 
       Ok (warnings1 @ warnings2 @ warnings3)
    | AnyOp (pos, (_, i, ty), e) 
    | ChooseOp (pos, (_, i, ty), e) -> 
      let* warnings1 = check_ty ctx f ty in 
      let extn_ctx = ctx_add_local ctx i (Some ty) in
      let warnings2 = 
        (* When using "any <type>" (e.g. "any int") syntax, the parser automatically 
           generates a bound variable with (NI.get_internal_name node_id) "_" that is trivially unused in 'e' *)
        if not (LAH.expr_contains_id i e) && not (i = HString.mk_hstring "_")
        then [mk_warning pos (UnusedBoundVariableWarning i)] 
        else []
      in
      let* warnings3 = (check_expr extn_ctx f e) in
      Ok (warnings1 @ warnings2 @ warnings3)
    | EmptyMap (_, Some (kt, vt)) -> 
      let* warnings1 = check_ty ctx f kt in
      let* warnings2 = check_ty ctx f vt in 
      Res.ok (warnings1 @ warnings2) 
    | EmptySet (_, Some ty) -> 
      check_ty ctx f ty
    | Ident _ | ModeRef _ | Const _ | EmptyMap _ | EmptySet _ -> Ok ([])
  in
  let* warnings1 = res in 
  let* warnings2 = check expr in 
  Ok (warnings1 @ warnings2)

and check_expr_list ctx f l =
  let* warnings = Res.seq (List.map (check_expr ctx f) l) in 
  Ok(List.flatten warnings)

and ovq_check_expr inlinable_funcs tc_ctx ctx = function
| LA.Call (pos, _, node_id, args) ->
  let inlinable_funcs = 
    List.map NI.get_internal_name (NI.Set.elements inlinable_funcs) 
    |> LA.SI.of_list 
  in
  let is_non_inlinable =
    not (LA.SI.mem (NI.get_internal_name node_id) inlinable_funcs)
  in
  let vars =
    List.fold_left
      (fun acc e -> LA.SI.union acc (LAH.vars_without_node_call_ids e))
      LA.SI.empty
      args
  in
  let over_vars j =
    let found_quant_in_non_inlinable =
      StringMap.mem j ctx.quant_vars && is_non_inlinable
    in
    let found_symbolic_index_in_non_inlinable =
      StringMap.mem j ctx.symbolic_array_indices &&
      is_non_inlinable
    in
    (match found_quant_in_non_inlinable, found_symbolic_index_in_non_inlinable with
    | true, _ -> syntax_error pos (QuantifiedVariableInNodeArgument (j, (NI.get_internal_name node_id)))
    | _, true -> syntax_error pos (SymbolicArrayIndexInNodeArgument (j, (NI.get_internal_name node_id)))
    | false, false -> Ok [])
  in
  let over_lazy_context =
    if not is_non_inlinable || LA.SI.is_empty ctx.lazy_cond_vars then
      Ok []
    else
      let vars = LA.SI.elements ctx.lazy_cond_vars in
      match List.find_opt (fun v -> StringMap.mem v ctx.quant_vars) vars with
      | Some v ->
        syntax_error pos (QuantifiedVariableInLazyGuardedNodeCall (v, (NI.get_internal_name node_id)))
      | None -> (
        match List.find_opt (fun v -> StringMap.mem v ctx.symbolic_array_indices) vars with
        | Some v ->
          syntax_error pos (SymbolicArrayIndexInLazyGuardedNodeCall (v, (NI.get_internal_name node_id)))
        | None -> Ok []
      )
  in
  let check = List.map over_vars (LA.SI.elements vars) in
  List.fold_left (>>) (Ok []) (check @ [over_lazy_context])
| LA.TypeAscription (pos, expr, ty) -> 
  let args = [expr] in 
  let ty = Ctx.expand_type_syn tc_ctx ty in
  let is_inlinable_e e = 
    match LAH.has_pre_or_arrow e with 
    | Some _ -> false 
    | None -> not (Ctx.expr_contains_node_call tc_ctx e)
  in 
  let is_inlinable = LAH.fold_lustre_ty is_inlinable_e true (&&) ty in 
  let vars =
    List.fold_left
      (fun acc e -> LA.SI.union acc (LAH.vars_without_node_call_ids e))
      LA.SI.empty
      args
  in
  let over_vars j =
    let found_quant_in_non_inlinable =
      StringMap.mem j ctx.quant_vars && not is_inlinable
    in
    let found_symbolic_index_in_non_inlinable =
      StringMap.mem j ctx.symbolic_array_indices &&
      not is_inlinable
    in
    (match found_quant_in_non_inlinable, found_symbolic_index_in_non_inlinable with
    | true, _ -> syntax_error pos (QuantifiedVariableInTypeAscription j)
    | _, true -> syntax_error pos (SymbolicArrayIndexInTypeAscription j)
    | false, false -> Ok [])
  in
  let check = List.map over_vars (LA.SI.elements vars) in
  List.fold_left (>>) (Ok []) check

| _ -> Ok []

(* Check types for quantified variables in calls to non-inlinable functions. 
   In particular, refinement type bound variables that refer to array/map/set elements 
   are treated as quantified because they will be quantified in the generated properties *)
and oqv_check_type tc_ctx inlinable_funcs is_nested ctx ty =
  let ovq = ovq_check_expr inlinable_funcs tc_ctx in
  match ty with
  | LA.RefinementType (_, (_, i, inner_ty), e) ->
    let ctx_here =
      if is_nested then ctx_add_quant_var ctx i (Some inner_ty) else ctx
    in
    let* warnings1 = check_expr ctx_here ovq e in
    let* warnings2 = oqv_check_type tc_ctx inlinable_funcs is_nested ctx_here inner_ty in
    Ok (warnings1 @ warnings2)
  | LA.ArrayType (_, (b_ty, sz)) ->
    let* warnings1 = check_expr ctx ovq sz in
    let* warnings2 = oqv_check_type tc_ctx inlinable_funcs true ctx b_ty in
    Ok (warnings1 @ warnings2)
  | LA.Map (_, kt, vt) ->
    let* warnings1 = oqv_check_type tc_ctx inlinable_funcs true ctx kt in
    let* warnings2 = oqv_check_type tc_ctx inlinable_funcs true ctx vt in
    Ok (warnings1 @ warnings2)
  | LA.Set (_, t) ->
    oqv_check_type tc_ctx inlinable_funcs true ctx t
  | LA.TupleType (_, tys) | LA.GroupType (_, tys) ->
    let* warnings1 = Res.seq (List.map (oqv_check_type tc_ctx inlinable_funcs true ctx) tys) in
    Ok (List.flatten warnings1)
  | LA.RecordType (_, _, tis) ->
    let* warnings1 =
      Res.seq (List.map (fun (_, _, t) -> oqv_check_type tc_ctx inlinable_funcs true ctx t) tis)
    in
    Ok (List.flatten warnings1)
  | LA.TArr (_, a, r) ->
    let* warnings1 = oqv_check_type tc_ctx inlinable_funcs true ctx a in
    let* warnings2 = oqv_check_type tc_ctx inlinable_funcs true ctx r in
    Ok (warnings1 @ warnings2)
  | LA.UserType (_, ty_args, _) ->
    let* warnings1 = Res.seq (List.map (oqv_check_type tc_ctx inlinable_funcs is_nested ctx) ty_args) in
    Ok (List.flatten warnings1)
  | LA.History (_, id) -> (
      match Ctx.lookup_ty tc_ctx id with
      | Some ty' -> oqv_check_type tc_ctx inlinable_funcs is_nested ctx ty'
      | None -> Ok [])
  | LA.Int _ | LA.Bool _ | LA.Real _ | LA.SBitVector _ | LA.UBitVector _
  | LA.AbstractType _ | LA.EnumType _ ->
    Ok []

let oqv_check_inputs oqv_on_ty base_ctx inputs =
  let* warnings1 =
    Res.seq (List.map (fun (_, _, ty, _, _) -> oqv_on_ty base_ctx ty) inputs)
  in
  Ok (List.flatten warnings1)

let oqv_check_outputs oqv_on_ty base_ctx outputs =
  let* warnings1 =
    Res.seq (List.map (fun (_, _, ty, _) -> oqv_on_ty base_ctx ty) outputs)
  in
  Ok (List.flatten warnings1)

let oqv_check_locals oqv_on_ty base_ctx locals =
  let* warnings1 =
    Res.seq
      (List.map
         (function
           | LA.NodeConstDecl (_, FreeConst (_, _, ty))
           | LA.NodeConstDecl (_, TypedConst (_, _, _, ty)) ->
             oqv_on_ty base_ctx ty
           | LA.NodeConstDecl (_, UntypedConst _) -> Ok []
           | LA.NodeVarDecl (_, (_, _, ty, _)) ->
             oqv_on_ty base_ctx ty)
         locals)
  in
  Ok (List.flatten warnings1)

let oqv_check_node_decl inlinable_funcs ctx tc_ctx (_, _, _, _, inputs, outputs, locals, items, contract) =
  let props = StringSet.empty in
  let ctx_io = build_local_ctx ctx [] inputs outputs in
  let oqv_on_ty ctx ty = oqv_check_type tc_ctx inlinable_funcs false ctx ty in
  let* warnings1 = oqv_check_inputs oqv_on_ty ctx_io inputs in
  let* warnings2 = oqv_check_outputs oqv_on_ty ctx_io outputs in
  let* (warnings3, props) =
    match contract with
    | Some c ->
      (* Locals are not visible in contracts, so use io ctx *)
      check_contract false ctx_io (ovq_check_expr inlinable_funcs tc_ctx) oqv_on_ty c props
    | None -> Ok (([], StringSet.empty))
  in
  let ctx_full = build_local_ctx ctx locals inputs outputs in
  let* warnings4 = oqv_check_locals oqv_on_ty ctx_full locals in
  let* (warnings5, _) =
    check_items
      (build_local_ctx ctx_full locals [] [])
      ~tc_ctx:(Some tc_ctx)
      (ovq_check_expr inlinable_funcs tc_ctx)
      items
      props
  in
  Ok (warnings1 @ warnings2 @ warnings3 @ warnings4 @ warnings5)

let oqv_check_contract_node_decl inlinable_funcs ctx tc_ctx (_, _, inputs, outputs, contract) =
  let props = StringSet.empty in
  let ctx_io = build_local_ctx ctx [] inputs outputs in
  let oqv_on_ty ctx ty = oqv_check_type tc_ctx inlinable_funcs false ctx ty in
  let* warnings1 = oqv_check_inputs oqv_on_ty ctx_io inputs in
  let* warnings2 = oqv_check_outputs oqv_on_ty ctx_io outputs in
  let* (warnings3, _) =
    check_contract true ctx_io (ovq_check_expr inlinable_funcs tc_ctx) oqv_on_ty contract props
  in
  Ok (warnings1 @ warnings2 @ warnings3)

let oqv_check_decl: NI.Set.t -> context -> Ctx.tc_context -> LA.declaration -> ([> warning] list, [> error]) result
= fun inlinable_funcs ctx tc_ctx -> function
  | NodeDecl (_, decl) ->
    oqv_check_node_decl inlinable_funcs ctx tc_ctx decl
  | FuncDecl (_, decl, _) ->
    oqv_check_node_decl inlinable_funcs ctx tc_ctx decl
  | ContractNodeDecl (_, decl) ->
    oqv_check_contract_node_decl inlinable_funcs ctx tc_ctx decl
  | _ -> Ok []

let no_quant_vars_in_calls_to_non_inlinable_funcs tc_ctx inlinable_funcs ast =
  let ctx = build_global_ctx ast in
  let* warnings = Res.seq (List.map (oqv_check_decl inlinable_funcs ctx tc_ctx) ast) in
  Ok (List.flatten warnings)
