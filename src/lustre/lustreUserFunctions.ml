(* This file is part of the Kind 2 model checker.

   Copyright (c) 2024 by the Board of Trustees of the University of Iowa

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

module A = LustreAst
module NI = NodeId
module AH = LustreAstHelpers
module Ctx = TypeCheckerContext

let valid_outputs ctx = function
  | [(_, _, ty, _)] -> ( (* single output variable *)
    not (Ctx.type_contains_array ctx ty)
  )
  | _ -> false

let valid_locals ctx locals =
  locals |> List.for_all (function
  | A.NodeConstDecl (_, TypedConst (_,_,_,ty)) ->
    not (Ctx.type_contains_array ctx ty)
  | A.NodeConstDecl _ -> true
  | NodeVarDecl (_, (_, _, ty, _)) ->
    not (Ctx.type_contains_array ctx ty)
  )

let valid_items set items =
  items |> List.for_all (function
    | A.Body (Equation (_, StructDef (_, [A.SingleIdent _]), rhs)) ->
      NI.Set.subset (AH.calls_of_expr rhs) set
    | AnnotProperty _ -> true
    | A.Body (Equation (_, _, _))
    | Body (Assert _)
    | AnnotMain _ -> false
    | Auto _ -> true (* no-op, removed earlier in pipeline *)
    | FrameBlock _
    | IfBlock _
    | WhenBlock _
    | MatchBlock _ -> assert false (* desugared earlier in pipeline *)
  )

let is_output_defined outputs items =
  let output_id =
    match outputs with
    | [(_, id, _, _)] -> id
    | _ -> assert false
  in
  items |> List.exists (function
    | A.Body (Equation (_, StructDef (_, [A.SingleIdent (_, id)]), _)) ->
      HString.equal id output_id
    | _ -> false
  )

let have_ref_type ctx outputs =
  outputs |> List.exists (fun (_, _, ty, _) ->
    Ctx.type_contains_ref ctx ty
  )

let rec can_be_abstracted' ctx contracts (_, items) =
  items |> List.exists (function
    | A.Guarantee _ -> true
    | Mode (_, _, _, ensures) -> ensures <> []
    | ContractCall (_, id, _, _, _) -> (
        match NI.Map.find_opt id contracts with
        | None -> assert false
        | Some (_, _, _, outputs, contract) ->
          have_ref_type ctx outputs
          || can_be_abstracted' ctx contracts contract
    )
    | _ -> false
  )

let can_be_abstracted ctx contracts outputs contract =
  have_ref_type ctx outputs
  ||
  match contract with
  | None -> false
  | Some contract -> can_be_abstracted' ctx contracts contract

(* [true] if the contract of the function, if any, is never used in place of
   its body: there is nothing to abstract its calls with, or it is transparent.
   This is [LustreNode.has_effective_contract] at the level of the AST. *)
let has_no_effective_contract ctx contracts opac contract outputs =
  opac = A.Transparent || not (can_be_abstracted ctx contracts outputs contract)

let is_inlinable (set: NI.Set.t) contracts ctx opac contract outputs locals items =
  has_no_effective_contract ctx contracts opac contract outputs &&
  valid_outputs ctx outputs &&
  valid_locals ctx locals &&
  valid_items set items &&
  is_output_defined outputs items

(* Whether no output or local variable of a function is of a type that contains
   an array, once its type parameters are replaced as [subst] says *)
let no_array_vars ?(subst = []) ctx outputs locals =
  let no_array ty =
    not (Ctx.type_contains_array ctx (AH.apply_type_subst_in_type subst ty))
  in
  List.for_all (fun (_, _, ty, _) -> no_array ty) outputs
  && locals |> List.for_all (function
    | A.NodeConstDecl (_, TypedConst (_, _, _, ty)) -> no_array ty
    | A.NodeConstDecl _ -> true
    | NodeVarDecl (_, (_, _, ty, _)) -> no_array ty)

(* Whether the instantiation of the function [id] of [decls] with the type
   arguments [ty_args] of a call meets the conditions of
   [uf_callable_functions] on the types of its variables: no output of a
   refinement type unless the function is transparent, and no output or local
   of a type that contains an array. [uf_callable_functions] checks the
   declarations as they are written, with the type parameters of a polymorphic
   function, while the calls are compiled once the functions are instantiated,
   with the set computed from the instantiations: without this check, the two
   would disagree, and a call accepted here would reach the compilation of
   the nodes as a call to a node applied to quantified variables.

   A type argument may mention [caller_ty_params], the type parameters of the
   polymorphic node that makes the call, which only its instantiations give a
   type to. Any of them may be an array type: they are taken to be one, which
   rules out any output or local whose type mentions them, whatever type an
   instantiation gives them. *)
let uf_callable_instance ctx decls ~caller_ty_params id ty_args =
  let some_array =
    let pos = Lib.dummy_pos in
    A.ArrayType (pos, (A.Int pos, A.Const (pos, Num (HString.mk_hstring "1"))))
  in
  let caller_subst = List.map (fun p -> p, some_array) caller_ty_params in
  let ty_args = List.map (AH.apply_type_subst_in_type caller_subst) ty_args in
  ty_args = []
  || decls |> List.exists (function
    | A.FuncDecl (_, (id', _, opac, params, _, outputs, locals, _, _), _)
      when NI.equal id id' ->
      List.length params = List.length ty_args
      &&
      let subst = List.combine params ty_args in
      (* A refinement type of an output is a contract, which abstracts a
         function that is not transparent (see [has_no_effective_contract]) *)
      let outputs =
        List.map
          (fun (p, i, ty, c) -> p, i, AH.apply_type_subst_in_type subst ty, c)
          outputs
      in
      (opac = A.Transparent || not (have_ref_type ctx outputs))
      && no_array_vars ~subst ctx outputs locals
    | _ -> false)

let inlinable_functions: Ctx.tc_context -> A.declaration list -> NI.Set.t 
= fun ctx decls ->
  List.fold_left (fun (set, contracts) dcl ->
    match dcl with
    | A.ContractNodeDecl (_, contract_node_decl) -> (
      let (id, _, _, _, _) = contract_node_decl in
      set, NI.Map.add id contract_node_decl contracts
    )
    (* A non-imported non-recursive function *)
    | A.FuncDecl (_, (id, false, opac, [], _, outputs, locals, items, contract), { is_lemma = false; is_rec = false }) -> (
      if is_inlinable set contracts ctx opac contract outputs locals items then
        NI.Set.add id set, contracts
      else
        set, contracts
    )
    (* A type ascription *) 
    | A.NodeDecl (_, (id, _, _, _, _, _, _, _, _)) -> 
      if NI.get_node_type id = NI.TypeAscription then
        NI.Set.add id set, contracts 
      else 
        set, contracts
    | _ -> set, contracts
  )
  (NI.Set.empty, NI.Map.empty)
  decls
  |> fst

(* The polymorphic non-recursive functions that meet the conditions of
   [inlinable_functions] with their type parameters as they are, given the
   set [inlinable] of the monomorphic ones. Only the instantiations of a
   polymorphic function are inlined, and [inlinable_functions] leaves its
   declaration out; but the declaration of a polymorphic recursive function
   calls the declarations of the polymorphic functions it calls, and is what
   [LustreSyntaxChecks] looks a call up by (see [uf_callable_functions]). *)
let generic_inlinable_functions ctx decls inlinable =
  List.fold_left (fun (set, contracts) dcl ->
    match dcl with
    | A.ContractNodeDecl (_, contract_node_decl) -> (
      let (id, _, _, _, _) = contract_node_decl in
      set, NI.Map.add id contract_node_decl contracts
    )
    (* A non-imported non-recursive polymorphic function *)
    | A.FuncDecl
        (_, (id, false, opac, _ :: _, _, outputs, locals, items, contract),
         { is_lemma = false; is_rec = false })
      -> (
      let calls_ok = NI.Set.union inlinable set in
      if is_inlinable calls_ok contracts ctx opac contract outputs locals items
      then NI.Set.add id set, contracts
      else set, contracts
    )
    | _ -> set, contracts
  )
  (NI.Set.empty, NI.Map.empty)
  decls
  |> fst

(* Whether the body of a function is made of equations that define all of its
   outputs and local variables, each a single variable or a tuple of them,
   and of properties: no assertion, and no array element defined on its own *)
let defines_all_vars outputs locals items =
  let defined =
    List.fold_left (fun acc item ->
      match acc, item with
      | None, _ -> None
      | Some acc, A.Body (Equation (_, StructDef (_, lhs), _)) ->
        List.fold_left (fun acc s ->
          match acc, s with
          | Some acc, A.SingleIdent (_, id) -> Some (A.SI.add id acc)
          | _ -> None)
          (Some acc) lhs
      | Some acc, (AnnotProperty _ | AnnotMain _ | Auto _) -> Some acc
      | Some _, (Body (Assert _) | FrameBlock _ | IfBlock _ | WhenBlock _
                | MatchBlock _) -> None)
      (Some A.SI.empty) items
  in
  match defined with
  | None -> false
  | Some defined ->
    List.for_all (fun (_, id, _, _) -> A.SI.mem id defined) outputs
    && locals |> List.for_all (function
      | A.NodeVarDecl (_, (_, id, _, _)) -> A.SI.mem id defined
      | A.NodeConstDecl _ -> true)

(* The functions and nodes the equations of a body call, among the declared
   ones [declared] (a constructor of an algebraic datatype is applied as a
   call, but is not declared as a function) *)
let callees declared items =
  List.fold_left (fun acc item ->
    match item with
    | A.Body (Equation (_, _, rhs)) ->
      NI.Set.union acc (NI.Set.inter declared (AH.calls_of_expr rhs))
    | _ -> acc)
    NI.Set.empty items

(* The recursive functions a call applied to quantified variables can be
   compiled to an application of the unrolled symbol of (see
   [LustreAstNormalizer.mk_fresh_qcall]): those whose recursive calls past
   their unrollings are left unconstrained, which [LustreFunDefs] defines
   the symbol as, the function unrolled as many times as the analysis
   unrolls it.

   The conditions are those of the non-recursive functions that can be
   inlined, whatever the analysis:

   - The function has no effective contract, or is transparent. A contract
     abstracts a translucent function in compositional analyses only, but a
     translucent function with a contract is left out in every analysis, as
     a non-recursive one is. Its symbol would otherwise be defined in some
     analyses and not in others. In an analysis where a contract abstracts
     the function, the contract only constrains its symbol at the arguments
     of its instances, so under a quantifier it would be an arbitrary
     function and a property that does hold of it could be reported
     falsifiable.
   - No output or local is of a type that contains an array, and the body
     is made of equations that define all of its outputs and locals, without
     assertions. [LustreFunDefs] builds no definition from another body, and
     the symbol would be arbitrary under the quantifier as well.
   - Every function the body calls can be inlined, or is a recursive
     function that meets these conditions in turn. [LustreFunDefs] defines
     a function together with the functions of its recursive group and the
     functions they call: if one of them cannot be defined, none is. An
     imported function, or a function that can neither be inlined nor be
     defined, is an arbitrary function under the quantifier.

   The last condition makes the set a greatest fixpoint: a recursive group
   is in it if all of its functions meet the other conditions and call no
   function outside of it but those that can be inlined or are in it.

   The declaration of a polymorphic function is in the set if it meets the
   conditions with its type parameters as they are, and a polymorphic
   non-recursive function it calls is taken to be inlinable under the same
   terms (see [generic_inlinable_functions]): [LustreSyntaxChecks] looks a
   call up by the declaration of the polymorphic function. Each
   instantiation is in the set on its own terms, and is what the call is
   compiled to: [LustreAstNormalizer] rejects a call to an instantiation that
   is not in the set, for one that a type argument gives a variable of an
   array or a refinement type.

   A polymorphic function is checked with its type parameters as they are:
   an instantiation of it may still have an output of a refinement type, or
   an output or local of an array type (see [uf_callable_instance]).

   The remaining condition of [LustreFunDefs] -- the solver or logic takes
   recursive definitions -- is not checked: whether a call is accepted does
   not depend on the options. A call to a function that is not defined for
   this reason is accepted here, and [LustreTransSys] warns about it. *)
let uf_callable_functions: Ctx.tc_context -> A.declaration list -> NI.Set.t
= fun ctx decls ->
  let inlinable = inlinable_functions ctx decls in
  let inlinable =
    NI.Set.union inlinable (generic_inlinable_functions ctx decls inlinable)
  in
  let declared =
    List.fold_left (fun acc dcl ->
      match dcl with
      | A.FuncDecl (_, (id, _, _, _, _, _, _, _, _), _)
      | A.NodeDecl (_, (id, _, _, _, _, _, _, _, _)) -> NI.Set.add id acc
      | _ -> acc)
      NI.Set.empty decls
  in
  (* The recursive functions that meet the conditions on themselves, with
     the functions they call *)
  let candidates, _ =
    List.fold_left (fun (cands, contracts) dcl ->
      match dcl with
      | A.ContractNodeDecl (_, contract_node_decl) -> (
        let (id, _, _, _, _) = contract_node_decl in
        cands, NI.Map.add id contract_node_decl contracts
      )
      (* A non-imported recursive function *)
      | A.FuncDecl
          (_, (id, false, opac, _, _, outputs, locals, items, contract),
           { A.is_rec = true; is_lemma = false })
        -> (
        if has_no_effective_contract ctx contracts opac contract outputs
           && no_array_vars ctx outputs locals
           && defines_all_vars outputs locals items
        then
          NI.Map.add id (callees declared items) cands, contracts
        else
          cands, contracts
      )
      | _ -> cands, contracts
    )
    (NI.Map.empty, NI.Map.empty)
    decls
  in
  (* Remove the functions that call a function that is neither inlinable nor
     a remaining candidate, until there is none *)
  let rec fixpoint cands =
    let cands' =
      NI.Map.filter
        (fun _ calls ->
           NI.Set.for_all
             (fun c -> NI.Set.mem c inlinable || NI.Map.mem c cands)
             calls)
        cands
    in
    if NI.Map.cardinal cands' = NI.Map.cardinal cands then cands
    else fixpoint cands'
  in
  fixpoint candidates
  |> NI.Map.bindings
  |> List.map fst
  |> NI.Set.of_list
