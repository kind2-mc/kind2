(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(* Generation of well-formedness predicates for recursive ADTs.

   A refinement type on a field of a recursive ADT constrains infinitely many
   values (every node at every depth), so unlike a record or a non-recursive
   ADT it cannot be expanded into a finite conjunction over the type's
   structure. Instead each such ADT gets a recursive predicate, e.g.

     function rec wf_NatList(.wf_arg: NatList) returns (.wf_res: bool);
     (*@contract decreases .wf_arg; *)
     let
       .wf_res = when Cons?(.wf_arg)
                 then .wf_arg.hd >= 0 and wf_NatList(.wf_arg.tl)
                 else true;
     tel

   Callers use it as an ordinary constraint: assumed where the value comes
   from an assumption boundary, proved where it does not.

   The declaration is tagged NodeId.WellFormedness, which is both what
   distinguishes it from a user declaration of the same name and how the passes
   that must treat it specially recognize it.

   Predicates are generated once polymorphic datatypes are instantiated, one
   per monomorphic recursive datatype, so that a field whose type comes from a
   type argument is constrained by that argument's own predicate. They are
   built directly in the desugared form the later passes expect. *)

module A = LustreAst
module AH = LustreAstHelpers
module Ctx = TypeCheckerContext
module LDAT = LustreDesugarADTs
module AN = LustreAstNormalizer

(* Bound names of the generated predicate. A leading '.' cannot occur in a user
   identifier, so neither can be shadowed by a constructor field name. *)
let self_var = HString.mk_hstring ".wf_arg"
let out_var = HString.mk_hstring ".wf_res"

(* The constructor a (possibly instantiation-qualified) constructor stands for,
   and the datatype declaring it, which is how selectors and testers name them *)
let source_ctor ctx ctor =
  let ctor =
    HString.string_of_hstring ctor |> Type.source_ctor_name |> HString.mk_hstring
  in
  match Ctx.lookup_constructor ctx ctor with
  | Some (ty_name, _) -> ty_name, ctor
  | None -> assert false

(* The constraints of one constructor's fields, on a value built with it *)
let ctor_constraints ctx adt_map pos arg (ctor, fields) =
  let base_ty, ctor = source_ctor ctx ctor in
  let pk = A.Selector (A.Kind2Generated, A.UserType (pos, [], base_ty), ctor) in
  let conjuncts =
    List.concat_map
      (fun (fname, fty) ->
        AN.mk_ref_type_expr adt_map ctx None (A.FieldProject (pos, arg, fname, pk)) fty)
      fields
  in
  (A.ADTTester (pos, arg, ctor), AH.mk_conj pos conjuncts)

let mk_wf_predicate ctx adt_map pos ty_name ctors =
  let span = { A.start_pos = pos; A.end_pos = pos } in
  let arg = A.Ident (pos, self_var) in
  (* A chain of lazy conditionals, the last constructor covering what is left *)
  let body =
    match List.rev_map (ctor_constraints ctx adt_map pos arg) ctors with
    | [] -> assert false
    | (_, last) :: rest ->
      List.fold_left
        (fun acc (tester, conj) -> A.TernaryOp (pos, A.LazyIte, tester, conj, acc))
        last rest
  in
  let eq =
    A.Body (A.Equation (pos, A.StructDef (pos, [A.SingleIdent (pos, out_var)]), body))
  in
  (* Every recursive call is on a field of the argument, hence a structural subterm *)
  let contract = (pos, [A.Decreases (pos, arg)]) in
  let node_id = LDAT.wf_pred_id ty_name in
  let ips = [ (pos, self_var, A.UserType (pos, [], ty_name), A.ClockTrue, false) ] in
  let ops = [ (pos, out_var, A.Bool pos, A.ClockTrue) ] in
  let ctx = Ctx.add_node_param_attr ctx node_id ips in
  let ctx = Ctx.add_ty_vars_node ctx node_id [] in
  let ctx = Ctx.add_ty_node ctx node_id (A.TArr (pos, A.UserType (pos, [], ty_name), A.Bool pos)) true in
  ctx,
  A.FuncDecl
    ( span,
      (node_id, false, A.Default, [], ips, ops, [], [ eq ], Some contract),
      { A.is_rec = true; A.is_lemma = false } )

let gen_wf_predicates ctx adt_map decls =
  let ctx, preds =
    List.fold_left
      (fun (ctx, preds) decl ->
        match decl with
        (* A datatype with type parameters is constrained through its instantiations *)
        | A.TypeDecl (_, A.AliasType (pos, ty_name, [], (A.ADT (_, _, ctors) as ty)))
          when AH.is_directly_recursive_adt ty_name ctors && Ctx.type_contains_ref ctx ty ->
          let ctx, pred = mk_wf_predicate ctx adt_map pos ty_name ctors in
          ctx, pred :: preds
        | A.TypeDecl _ | A.ConstDecl _ | A.NodeDecl _ | A.FuncDecl _
        | A.ContractNodeDecl _ | A.NodeParamInst _ -> ctx, preds)
      (ctx, []) decls
  in
  ctx, List.rev preds
