(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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
module Ctx = TypeCheckerContext
module Chk = LustreTypeChecker
module AH = LustreAstHelpers

type error_kind = ConstInClockedTemporalExpr of HString.t

type error = [ `LustreGenNodesError of Lib.position * error_kind ]

let error_message kind = match kind with
  | ConstInClockedTemporalExpr id ->
    "A temporal expression in a clocked position that reads constant '"
    ^ HString.string_of_hstring id ^ "' is not supported"

(* Raised where the offending expression is, and turned into an error by
   gen_nodes *)
exception Const_in_clocked_temporal_expr of Lib.position * error_kind

let mk_fresh_fn_name: ?inserted:bool -> Lib.position -> NI.t -> NI.node_type -> NI.t = 
fun ?(inserted = false) pos node_name node_type -> 
  let pos = Lib.string_of_t Lib.pp_print_line_and_column pos in
  let pos = String.sub pos 1 (String.length pos - 2) |> HString.mk_hstring in
  let name = match node_type with
  | Any -> HString.mk_hstring ".any_"
  | Choose -> HString.mk_hstring ".choose_"
  | TypeAscription ->
    (* Ascriptions inserted by Kind 2 are reported as subtype obligations *)
    HString.mk_hstring (if inserted then ".subtype_" else ".type_ascription_")
  | ClockedExpr -> HString.mk_hstring ".clocked_expr_"
  | _ -> assert false
  in
  let name = HString.concat2 name pos |> HString.concat2 (NI.get_name node_name)  in
  NI.mk_node_id ~node_type ~user_name:name name

(* Not every identifier occurring in an expression or a type denotes a variable
   that a generated node must take as an argument. Global constants are in
   scope everywhere, and nullary ADT constructors are parsed as identifiers
   even though they denote values. *)
let node_arguments: Ctx.tc_context -> HString.t list -> HString.t list =
fun ctx ids ->
  List.filter (fun i ->
    match Ctx.lookup_const ctx i with
    | Some (_, _, Ctx.Global) -> false
    | _ -> Ctx.lookup_constructor ctx i |> Option.is_none
  ) ids

(* Resolve a match arm before the nodes its body needs are generated, returning
   the arm's pattern, a substitution to apply to its body, and the context the
   body is processed in.

   The arm's variables are bound to the types of the constructor fields they
   stand for, as they are when the arm is type checked later; a variable that
   shadows a global constant is also renamed apart.  Without this a variable
   whose name is a constant's would be taken for that constant, and a node
   generated from the arm body would read the constant instead of the field. *)
(* What this pass could learn about a match scrutinee's type. [Illtyped] means
   the scrutinee has a type error, so the later pass rejects the program;
   [Unknown] means only that the type could not be determined here. *)
type scrutinee = Known of A.lustre_type | Illtyped | Unknown

let resolve_arm: Ctx.tc_context -> scrutinee -> A.pattern
  -> Ctx.tc_context * A.pattern * (HString.t * A.expr) list =
fun ctx scrut pat ->
  (* Only a global constant (an enum variant among them) is renamed away: it is
     in scope everywhere, so it is the one thing a generated node cannot take a
     parameter for.  A variable of the enclosing node keeps its name, which a
     match block's own shadowing check still reports. *)
  let shadows_global id =
    match Ctx.lookup_const ctx id with
    | Some (_, _, Ctx.Global) -> true
    | Some (_, _, (Ctx.Input | Ctx.Output | Ctx.Local | Ctx.Ghost)) | None -> false
  in
  (* Type checking has not run yet, so a variable pattern naming a nullary
     constructor is not a binder *)
  let binders =
    AH.pat_bound_vars_with_pos pat
    |> List.filter (fun (id, _) ->
         Ctx.lookup_constructor ctx id |> Option.is_none && shadows_global id)
    |> List.sort_uniq (fun (i, _) (j, _) -> HString.compare i j)
  in
  let renamed =
    List.map (fun (id, ipos) -> (id, ipos, AH.fresh_bound_ident id)) binders
  in
  let pat =
    List.fold_left (fun pat (id, _, fresh) -> AH.rename_pat_var id fresh pat)
      pat renamed
  in
  (* Fall back on the constructors the pattern itself names when the scrutinee
     cannot supply the field types. The types are then the ones the datatype
     declares, so a polymorphic datatype's remain in terms of its type
     parameters, but every variable of the pattern is bound. *)
  let rec bind_from_pattern ctx = function
    | A.VarPat _ -> ctx
    | A.Pat (_, ctor, sub_pats) ->
      match Ctx.lookup_constructor ctx ctor with
      | None -> ctx
      | Some (_, field_tys) ->
        if List.length field_tys <> List.length sub_pats then ctx
        else
          List.fold_left2 (fun ctx ty sub_pat ->
            match sub_pat with
            | A.VarPat (_, i) ->
              if Ctx.lookup_constructor ctx i |> Option.is_some then ctx
              else Ctx.add_ty (Ctx.remove_const ctx i) i ty
            | A.Pat _ -> bind_from_pattern ctx sub_pat
          ) ctx field_tys sub_pats
  in
  (* The scrutinee's type gives the field types instantiated, so it is preferred
     wherever it is available *)
  let ctx, rejected =
    match scrut with
    | Known scrut_ty ->
      (match Chk.bind_pattern_ty ctx scrut_ty pat with
      | Ok (ctx, _) -> ctx, false
      | Error _ -> bind_from_pattern ctx pat, true)
    | Illtyped -> bind_from_pattern ctx pat, true
    | Unknown -> bind_from_pattern ctx pat, false
  in
  (* A binder of a pattern the later pass rejects keeps its own name if nothing
     could type it: renaming it apart would leave the abstractions below unable
     to stand in for an arm body that mentions it, and the program is reported as
     an error either way. The rename is kept when the scrutinee's type is merely
     unknown, since the program may well be sound and reading the shadowed
     constant would prove the wrong thing. *)
  let pat, subst =
    List.fold_left (fun (pat, subst) (id, ipos, fresh) ->
      if rejected && Ctx.lookup_ty ctx fresh |> Option.is_none then
        (AH.rename_pat_var fresh id pat, subst)
      else (pat, (id, A.Ident (ipos, fresh)) :: subst)
    ) (pat, []) renamed
  in
  (ctx, pat, subst)

(* What can be learnt about a match scrutinee's type before the nodes its own
   subexpressions need are generated. *)
let scrutinee_type: Ctx.tc_context -> NI.t -> A.expr -> scrutinee =
fun ctx node_name scrut ->
  match scrut with
  (* An any/choose operator carries its binder's declared type. Type inference
     only runs on these once they are desugared, so read the type off the
     syntax instead. *)
  | A.AnyOp (_, (_, _, ty), _) | A.ChooseOp (_, (_, _, ty), _) -> Known ty
  | _ ->
    (match Chk.infer_type_expr ctx (Some node_name) scrut with
    | Ok (ty, _, _) -> Known ty
    | Error _ -> Illtyped
    (* A pass this expression is not desugared for yet raised, which says
       nothing about whether the program is well typed *)
    | exception _ -> Unknown)

(* Add the signatures of generated node and function declarations to a context,
   so that the type of a call to one can be inferred. Best-effort: a signature
   that cannot be built here (e.g. because its types still contain operators that
   are desugared below) is simply skipped, and the error, if any, is reported by
   the later type-checking pass. *)
let add_node_sigs: Ctx.tc_context -> A.declaration list -> Ctx.tc_context =
fun ctx decls ->
  let add ctx pos node_decl is_func =
    try
      match Chk.tc_ctx_of_node_decl pos ctx node_decl is_func with
      | Ok (_, ctx, _) -> ctx
      | Error _ -> ctx
    with _ -> ctx
  in
  List.fold_left (fun ctx decl ->
    match decl with
    | A.NodeDecl (span, node_decl) -> add ctx span.A.start_pos node_decl false
    | A.FuncDecl (span, node_decl, _) -> add ctx span.A.start_pos node_decl true
    | A.TypeDecl _ | A.ConstDecl _ | A.ContractNodeDecl _ | A.NodeParamInst _ -> ctx
  ) ctx decls

(* When a branch of a when-then-else expression is temporal (it uses '->' or
   'pre'), abstract it into a call to a fresh internal node whose outputs equal
   the original expression and whose arguments are the variables used in the
   expression. Non-temporal branches are returned unchanged. *)
let abstract_temporal_branch:
  Ctx.tc_context -> NI.t -> A.declaration list -> A.expr -> A.expr * A.declaration list =
fun ctx node_name gen_decls orig_e ->
  match AH.has_pre_or_arrow orig_e with
  | None -> orig_e, []
  | Some _ ->
    (* The branch can call a node generated for one of its own subexpressions,
       which the enclosing context does not know about yet *)
    let ctx = add_node_sigs ctx gen_decls in
    let pos = AH.pos_of_expr orig_e in
    let span = { A.start_pos = pos; A.end_pos = pos } in
    let node_id = mk_fresh_fn_name pos node_name ClockedExpr in
    (* A generated node is not compiled correctly when it takes a constant of the
       enclosing scope as an argument, so the constants the branch reads are
       inlined first. Each name is inlined at most once, since a cyclic
       definition is only reported by a later pass. *)
    let rec inline_consts seen e =
      let sigma =
        AH.vars_without_node_call_ids e |> Ctx.SI.elements |> node_arguments ctx
        |> List.filter_map (fun i ->
             if Ctx.SI.mem i seen then None
             else match Ctx.lookup_const ctx i with
               (* A constant declared without a value stands for itself *)
               | Some (A.Ident (_, j), _, _) when HString.equal i j -> None
               | Some (def, _, _) -> Some (i, def)
               | None -> None)
      in
      match sigma with
      | [] -> e
      | sigma ->
        let seen = List.fold_left (fun acc (i, _) -> Ctx.SI.add i acc) seen sigma in
        inline_consts seen (AH.apply_subst_in_expr sigma e)
    in
    let e = inline_consts Ctx.SI.empty orig_e in
    (* A generated node has no modes of its own, so a mode reference becomes a
       boolean parameter and is passed as the reference itself, which resolves at
       the call site *)
    let e, mode_refs = AH.name_mode_refs e in
    (* The variables used in the expression become the node's arguments *)
    let inputs = AH.vars_without_node_call_ids e |> Ctx.SI.elements |> node_arguments ctx in
    let inputs_call = List.map (fun str ->
      match List.find_opt (fun (i, _, _) -> HString.equal i str) mode_refs with
      | Some (_, mpos, ids) -> A.ModeRef (mpos, ids)
      | None -> A.Ident (pos, str)
    ) inputs in
    let input_tys = List.map (fun input -> Ctx.lookup_ty ctx input) inputs in
    (* If the type of any free variable cannot be determined here (e.g. a
       match-arm pattern variable that is only substituted by a later pass),
       skip the abstraction, returning the branch as it came in: the rewrites
       above are only sound inside the generated node. *)
    if List.exists Option.is_none input_tys then orig_e, []
    else
    let input_decls = List.map2 (fun input ty ->
      let ty = match ty with Some ty -> ty | None -> assert false in
      let is_const = match Ctx.lookup_const ctx input with Some _ -> true | None -> false in
      (pos, input, ty, A.ClockTrue, is_const)
    ) inputs input_tys in
    (* The output type is the type of the branch expression. If the type cannot
       be inferred here, leave the branch unchanged and let the later
       type-checking pass report the error. A failed assertion means inference
       was handed something a pass it precedes does not expect, which this pass
       is in no position to repair either; any other exception is left to
       propagate rather than be turned into a silent change of clock. *)
    match Chk.infer_type_expr ctx (Some node_name) e with
    | Error _ | exception Assert_failure _ -> orig_e, []
    | Ok (out_ty, _, _) ->
    (* A constant declared without a value cannot be inlined, and a generated
       node taking one as an argument is not compiled correctly. Checked after
       inference so that an ill-typed branch still gets its type error. *)
    let () =
      match List.find_opt (fun i -> Ctx.lookup_const ctx i |> Option.is_some) inputs with
      | Some i -> raise (Const_in_clocked_temporal_expr (pos, ConstInClockedTemporalExpr i))
      | None -> ()
    in
    (* Choose an output name that does not clash with any of the argument names *)
    let rec fresh_output name =
      if List.exists (fun i -> HString.equal i name) inputs
      then fresh_output (HString.concat2 name (HString.mk_hstring "_"))
      else name
    in
    (* A branch of a group type defines one output per component, so that the
       call standing in for it keeps the branch's width. Groups nest whenever a
       component is itself a group expression, and contribute their own width. *)
    let rec flatten_group_ty = function
      | A.GroupType (_, tys) -> List.concat_map flatten_group_ty tys
      | ty -> [ty]
    in
    let out_tys = flatten_group_ty out_ty in
    let op_ids = List.mapi (fun i ty ->
      let name = Lib.StringValues.type_ascription_output_name in
      let name = if i = 0 then name else name ^ string_of_int i in
      (fresh_output (HString.mk_hstring name), ty)
    ) out_tys in
    let ops = List.map (fun (id, ty) -> (pos, id, ty, A.ClockTrue)) op_ids in
    let lhs =
      A.StructDef (pos, List.map (fun (id, _) -> A.SingleIdent (pos, id)) op_ids)
    in
    let eq = A.Body (A.Equation (pos, lhs, e)) in
    (* The generated node might be polymorphic, so find all the needed type variables *)
    let ty_params = Ctx.ty_vars_of_expr ctx node_name e |> Ctx.SI.elements in
    let ty_args = List.map (fun id -> A.UserType (pos, [], id)) ty_params in
    let decl =
      A.NodeDecl (span,
        (node_id, false, A.Transparent, ty_params, input_decls, ops, [], [eq], None))
    in
    A.Call (pos, ty_args, node_id, inputs_call), [decl]

(* Abstract the ascription (e : ty) into a call to a fresh node whose output
   has type ty, so that ty yields proof obligations on e *)
let mk_type_ascription: ?inserted:bool -> Ctx.tc_context -> NI.t -> Lib.position -> A.expr -> A.lustre_type -> A.expr * A.declaration =
fun ?(inserted = false) ctx node_name pos e ty ->
    let span = { A.start_pos = pos; A.end_pos = pos; } in
    let node_id = mk_fresh_fn_name ~inserted pos node_name TypeAscription in
    let ip_id = HString.mk_hstring Lib.StringValues.type_ascription_input_name in 
    let op_id = HString.mk_hstring Lib.StringValues.type_ascription_output_name in
    let ip = pos, ip_id, ty, A.ClockTrue, false in
    let mono = Chk.expand_type_syn_reftype_history ctx ty |> Result.get_ok in
    let op = pos, op_id, mono, A.ClockTrue in
    let eq = A.Body (A.Equation (pos, A.StructDef (pos, [A.SingleIdent (pos, op_id)]), A.Ident (pos, ip_id))) in
    (* The generated function might be polymorphic, so we find all the needed type variables *)
    let ty_params = 
      Ctx.SI.union (Ctx.ty_vars_of_type ctx node_name ty) 
                   (Ctx.ty_vars_of_expr ctx node_name e)
      |> Ctx.SI.elements
    in 
    let ty_args = List.map (fun id -> A.UserType (pos, [], id)) ty_params in
    let ty = Ctx.expand_type_syn ctx ty in
    let inputs = AH.vars_of_type ty |> Ctx.SI.elements |> node_arguments ctx in
    let inputs_call = List.map (fun str -> A.Ident (pos, str)) inputs in
    let inputs = List.map (fun input -> (pos, input, Ctx.lookup_ty ctx input, A.ClockTrue)) inputs in
    let inputs = List.map (fun (p, inp, opt, cl) -> match opt with 
      | Some ty -> 
        let is_const = match Ctx.lookup_const ctx inp with | Some _ -> true | None -> false in
        p, inp, ty, cl, is_const 
      | None -> assert false
    ) inputs in
    let decl =
        A.NodeDecl (span, (node_id, false, Transparent, ty_params, ip :: inputs, [op], [], [eq], None)) 
    in 
    A.Call (pos, ty_args, node_id, e :: inputs_call), decl

(* The type of a record or constructor expression e of type name, when the
   types of its fields, instantiated with the type arguments, contain a refinement.
   e must not contain generated calls, as their nodes are not in the context yet. *)
let refined_construction_type: Ctx.tc_context -> NI.t -> A.expr -> A.ident -> A.lustre_type list -> A.lustre_type list -> A.lustre_type option =
fun ctx node_name e name ty_args field_tys ->
  let pos = AH.pos_of_expr e in
  let ty_vars = Ctx.lookup_ty_ty_vars ctx name |> Option.value ~default:[] in
  let field_tys = match ty_args with
    | [] -> Some field_tys
    | _ :: _ ->
      if List.length ty_vars = List.length ty_args then
        let sigma = List.combine ty_vars ty_args in
        Some (List.map (AH.apply_type_subst_in_type sigma) field_tys)
      else None
  in
  match field_tys with
  | None -> None
  | Some field_tys ->
    if not (List.exists (Ctx.type_contains_ref ctx) field_tys) then None
    else match ty_args, ty_vars with
    | _ :: _, _ | [], [] -> Some (A.UserType (pos, ty_args, name))
    | [], _ :: _ ->
      (* The type arguments are inferred from the fields. If inference is not
         possible here (e.g. a field mentions a contract ghost variable), the
         expression is left unchecked. *)
      match Chk.infer_type_expr ctx (Some node_name) e with
      | Ok (_, A.RecordExpr (_, _, inferred, _), _) -> Some (A.UserType (pos, inferred, name))
      | Ok (ty, A.ADTTerm _, _) -> Some ty
      | Ok _ | Error _ -> None

(* Wrap a record or constructor expression in an inserted ascription to its
   type when its field types contain a refinement, so that the refinement is
   checked on the field values. The generated node takes the variables of the
   type as arguments, so a type mentioning a locally bound variable (or one
   whose type is unknown here) is left unchecked. *)
let ascribe_construction ~insert ~bound ctx node_name orig e name ty_args field_tys gen_nodes =
  match refined_construction_type ctx node_name orig name ty_args field_tys with
  | Some ty when insert ->
    let ty_vars = AH.vars_of_type (Ctx.expand_type_syn ctx ty) in
    let unknown = node_arguments ctx (Ctx.SI.elements ty_vars) |> List.exists (fun v ->
      Ctx.SI.mem v bound || Option.is_none (Ctx.lookup_ty ctx v))
    in
    if unknown then e, gen_nodes
    else
      let call, decl =
        mk_type_ascription ~inserted:true ctx node_name (AH.pos_of_expr e) e ty
      in
      call, decl :: gen_nodes
  | Some _ | None -> e, gen_nodes

let rec desugar_type: Ctx.tc_context -> NI.t -> NI.t list -> A.lustre_type -> A.lustre_type * A.declaration list =
fun ctx node_name fun_ids ty -> 
  let r = desugar_type ctx node_name fun_ids in 
  match ty with 
  | Int _ | Bool _ | Real _ | SBitVector _ | UBitVector _ 
  | EnumType _ | AbstractType _ 
  | UserType _ | History _ -> ty, [] 
  | Map (p, kt, vt) -> 
    let kt, gen_nodes1 = r kt in 
    let vt, gen_nodes2 = r vt in
    Map (p, kt, vt), gen_nodes1 @ gen_nodes2
  | Set (p, ty) ->
    let ty, gen_nodes = r ty in
    Set (p, ty), gen_nodes  
  | ArrayType (p, (ty, len)) ->
    let ty, gen_nodes1 = r ty in
    let len, gen_nodes2 = desugar_expr ~insert:false ctx node_name fun_ids len in
    ArrayType (p, (ty, len)), gen_nodes1 @ gen_nodes2
  | TArr (p, ty1, ty2) ->
    let ty1, gen_nodes1 = r ty1 in
    let ty2, gen_nodes2 = r ty2 in
    TArr (p, ty1, ty2), gen_nodes1 @ gen_nodes2
  | GroupType (p, tys) ->
    let tys, gen_nodes = List.map r tys |> List.split in
    GroupType (p, tys), List.flatten gen_nodes 
  | TupleType (p, tys) ->
    let tys, gen_nodes = List.map r tys |> List.split in
    TupleType (p, tys), List.flatten gen_nodes 
  | RecordType (p, id, tis) ->
    let tis, gen_nodes = List.map (fun (p, id, ty) -> let ty, d = r ty in (p, id, ty), d) tis |> List.split in
    RecordType (p, id, tis), List.flatten gen_nodes
  | RefinementType (p1, (p2, id, ty), e) ->
    let ty, gen_nodes1 = r ty in
    (* The binder is in scope in the predicate, so the nodes the predicate needs
       are generated in a context that holds it *)
    let e, gen_nodes2 =
      desugar_expr ~insert:false (Ctx.add_ty (Ctx.remove_const ctx id) id ty)
        node_name fun_ids e
    in
    RefinementType (p1, (p2, id, ty), e), gen_nodes1 @ gen_nodes2
  | ADT (p, name, constructors) ->
    let constructors, gen_nodes = List.map (fun (cname, fields) ->
      let fields, gen_nodes = List.map (fun (fn, ty) ->
        let ty', gn = r ty in ((fn, ty'), gn)
      ) fields |> List.split in
      (cname, fields), List.flatten gen_nodes
    ) constructors |> List.split in
    ADT (p, name, constructors), List.flatten gen_nodes

(* Ascriptions are inserted for record and constructor expressions only when
   insert holds, as they are not allowed where a constant expression is
   expected. bound holds the variables bound inside the expression. *)
and desugar_expr: ?insert:bool -> ?bound:Ctx.SI.t -> Ctx.tc_context -> NI.t -> NI.t list -> A.expr -> A.expr * A.declaration list =
fun ?(insert = true) ?(bound = Ctx.SI.empty) ctx node_name fun_ids expr -> 
  let rec_call = desugar_expr ~insert ~bound ctx node_name fun_ids in
  (* Arguments for constant parameters of node id must be constant expressions *)
  let desugar_args id args =
    (* When the arguments cannot be matched one-to-one with the parameters
       (e.g. a tuple spread over several parameters), none of them is checked *)
    let is_const_param = match Ctx.lookup_node_param_attr ctx id with
      | Some attrs when List.length attrs = List.length args -> List.map snd attrs
      | Some _ -> List.map (fun _ -> true) args
      | None ->
        let is_constructor = Option.is_some (Ctx.lookup_constructor ctx (NI.get_name id)) in
        List.map (fun _ -> not is_constructor) args
    in
    List.map2 (fun is_const e ->
      desugar_expr ~insert:(insert && not is_const) ~bound ctx node_name fun_ids e
    ) is_const_param args |> List.split
  in
  match expr with
  | TypeAscription (pos, e, ty) ->
    let e, gen_nodes1 = rec_call e in
    let ty, gen_nodes2 = desugar_type ctx node_name fun_ids ty in
    let call, decl = mk_type_ascription ctx node_name pos e ty in
    call, decl :: gen_nodes1 @ gen_nodes2
  | A.ChooseOp (pos, (_, id, ty), expr1)
  | A.AnyOp (pos, (_, id, ty), expr1) -> 
    let ty, ty_gen_nodes = desugar_type ctx node_name fun_ids ty in
    (* The binder is in scope in the predicate, so the nodes the predicate needs
       are generated in a context that holds it *)
    let expr1, gen_nodes =
      desugar_expr ~insert ~bound:(Ctx.SI.add id bound)
        (Ctx.add_ty (Ctx.remove_const ctx id) id ty) node_name fun_ids expr1
    in
    let span = { A.start_pos = pos; A.end_pos = pos } in
    let contract = 
      [A.Guarantee (AH.pos_of_expr expr1, None, false, expr1)] 
    in
    let inputs =
      let vars_of_expr1 = AH.vars_without_node_call_ids expr1 in
      let vars_of_exprs =
        Ctx.SI.diff vars_of_expr1 (Ctx.SI.singleton id)
      in 
      Ctx.SI.union vars_of_exprs (AH.vars_of_type ty)
      |> Ctx.SI.elements |> node_arguments ctx
    in
    let inputs_call = List.map (fun str -> A.Ident (pos, str)) inputs in
    let ctx = Ctx.add_ty ctx id ty in
    let inputs = List.map (fun input -> (pos, input, Ctx.lookup_ty ctx input, A.ClockTrue)) inputs in
    let inputs = List.map (fun (p, inp, opt, cl) -> match opt with 
      | Some ty -> 
        let is_const = match Ctx.lookup_const ctx inp with | Some _ -> true | None -> false in
        p, inp, ty, cl, is_const 
      | None -> assert false
    ) inputs in
    (* The generated imported node might be polymorphic, so we find all the needed type variables *)
    let ty_params = 
      Ctx.SI.union (Ctx.ty_vars_of_type ctx node_name ty) 
                   (Ctx.ty_vars_of_expr ctx node_name expr1)
      |> Ctx.SI.elements
    in 
    let ty_vars = List.map (fun id -> A.UserType (pos, [], id)) ty_params in
    let generated_node, name = match expr with 
    | AnyOp _ -> 
        (* `any` operators are nondeterministic *)
        let name = mk_fresh_fn_name pos node_name Any in
        A.NodeDecl (span, 
        (name, true, A.Opaque, ty_params, inputs,
        [pos, id, ty, A.ClockTrue], [], [], Some (pos, contract))), 
        name
    | ChooseOp _ -> 
        (* `choose` operators are deterministic *)
        let name = mk_fresh_fn_name pos node_name Choose in
        A.FuncDecl (span, 
        (name, true, A.Opaque, ty_params, inputs,
        [pos, id, ty, A.ClockTrue], [], [], Some (pos, contract)), { is_lemma = false; is_rec = false }), 
        name
    | _ -> assert false
    in
    A.Call(pos, ty_vars, name, inputs_call), gen_nodes @ ty_gen_nodes @ [generated_node]

  | Ident _ as e -> e, []
  | Last _ as e -> e, []
  | ModeRef (_, _) as e -> e, []
  | A.EmptySet (pos, None) -> A.EmptySet (pos, None), []
  | A.EmptySet (pos, Some ty) ->
    let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
    A.EmptySet (pos, Some ty), gen_nodes
  | A.EmptyMap (pos, None) -> A.EmptyMap (pos, None), []
  | A.EmptyMap (pos, Some (kt, vt)) ->
    let kt', gen_nodes1 = desugar_type ctx node_name fun_ids kt in
    let vt', gen_nodes2 = desugar_type ctx node_name fun_ids vt in
    A.EmptyMap (pos, Some (kt', vt')), gen_nodes1 @ gen_nodes2
  | Const (_, _) as e -> e, []
  | FieldProject (pos, e, idx, pk) ->
    let e, gen_nodes = rec_call e in
    FieldProject (pos, e, idx, pk), gen_nodes
  | UnaryOp (pos, op, e) -> 
    let e, gen_nodes = rec_call e in
    UnaryOp (pos, op, e), gen_nodes
  | BinaryOp (pos, op, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    BinaryOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
  | TernaryOp (pos, LazyIte, e1, e2, e3) ->
    (* The branches of a when-then-else expression are evaluated under the
       guard clock. When a branch is a temporal expression (it uses '->' or
       'pre'), abstract it into a call to a fresh internal node so that its
       temporal behavior is driven by the guard. *)
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    let e3, gen_nodes3 = rec_call e3 in
    let e2, gen_nodes2' = abstract_temporal_branch ctx node_name gen_nodes2 e2 in
    let e3, gen_nodes3' = abstract_temporal_branch ctx node_name gen_nodes3 e3 in
    TernaryOp (pos, LazyIte, e1, e2, e3),
    gen_nodes1 @ gen_nodes2 @ gen_nodes2' @ gen_nodes3 @ gen_nodes3'
  | TernaryOp (pos, op, e1, e2, e3) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    let e3, gen_nodes3 = rec_call e3 in
    TernaryOp (pos, op, e1, e2, e3), gen_nodes1 @ gen_nodes2 @ gen_nodes3
  | ConvOp (pos, op, e) -> 
    let e, gen_nodes = rec_call e in
    ConvOp (pos, op, e), gen_nodes
  | CompOp (pos, op, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    CompOp (pos, op, e1, e2), gen_nodes1 @ gen_nodes2
  | Extract (pos, e, ub, lb) -> 
    let e, gen_nodes = rec_call e in 
    Extract (pos, e, ub, lb), gen_nodes
  | RecordExpr (pos, ident, ps, expr_list) ->
    let ps, gen_nodes_ty = List.map (desugar_type ctx node_name fun_ids) ps |> List.split in
    let id_list, exprs_gen_nodes = 
      List.map (fun (i, e) -> (i, (rec_call) e)) expr_list |> List.split 
    in
    let expr_list, gen_nodes = List.split exprs_gen_nodes in
    let e = A.RecordExpr (pos, ident, ps, List.combine id_list expr_list) in
    let gen_nodes = List.flatten gen_nodes_ty @ List.flatten gen_nodes in
    let field_tys = match Ctx.lookup_ty_syn ctx ident [] with
      | Some (A.RecordType (_, _, fields)) -> List.map (fun (_, _, ty) -> ty) fields
      | Some _ | None -> []
    in
    ascribe_construction ~insert ~bound ctx node_name expr e ident ps field_tys gen_nodes
  | GroupExpr (pos, kind, expr_list) ->
    let expr_list, gen_nodes = List.map (rec_call) expr_list |> List.split in
    GroupExpr (pos, kind, expr_list), List.flatten gen_nodes
  | StructUpdate (pos, e1, idx, Some e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    StructUpdate (pos, e1, idx, Some e2), gen_nodes1 @ gen_nodes2
  | StructUpdate (pos, e, idx, None) ->
    let e, gen_nodes = rec_call e in
    StructUpdate (pos, e, idx, None), gen_nodes 
  | ArrayConstr (pos, e1, e2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    ArrayConstr (pos, e1, e2), gen_nodes1 @ gen_nodes2
  | IndexAccess (pos, e1, e2, kind) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    IndexAccess (pos, e1, e2, kind), gen_nodes1 @ gen_nodes2
  | Quantifier (pos, kind, tis , e) ->
    let tis, gen_nodes_ty = List.map (fun (p, id, ty) ->
      let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
      (p, id, ty), gen_nodes
    ) tis |> List.split in
    (* The binders are in scope in the body, so the nodes the body needs are
       generated in a context that holds them *)
    let body_ctx =
      List.fold_left
        (fun ctx (_, id, ty) -> Ctx.add_ty (Ctx.remove_const ctx id) id ty) ctx tis
    in
    let bound = Ctx.SI.union bound (Ctx.SI.of_list (List.map (fun (_, id, _) -> id) tis)) in
    let e, gen_nodes = desugar_expr ~insert ~bound body_ctx node_name fun_ids e in
    Quantifier (pos, kind, tis, e), List.flatten gen_nodes_ty @ gen_nodes
  | When (pos, e, clock) -> 
    let e, gen_nodes = rec_call e in
    When (pos, e, clock), gen_nodes
  | Condact (pos, e1, e2, id, expr_list1, expr_list2) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    let expr_list1, gen_nodes3 = desugar_args id expr_list1 in
    let expr_list2, gen_nodes4 = List.map rec_call expr_list2 |> List.split in
    Condact (pos, e1, e2, id, expr_list1, expr_list2), gen_nodes1 @ gen_nodes2 @ 
                                                      List.flatten gen_nodes3 @ List.flatten gen_nodes4
  | Activate (pos, ident, e1, e2, expr_list) ->
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    Activate (pos, ident, e1, e2, expr_list), gen_nodes1 @ gen_nodes2
  | Merge (pos, ident, expr_list) ->
    let id_list, exprs_gen_nodes = 
      List.map (fun (i, e) -> (i, (rec_call) e)) expr_list |> List.split 
    in
    let expr_list, gen_nodes = List.split exprs_gen_nodes in
    Merge (pos, ident, List.combine id_list expr_list), List.flatten gen_nodes
  | RestartEvery (pos, ident, expr_list, e) ->
    let expr_list, gen_nodes1 = desugar_args ident expr_list in
    let e, gen_nodes2 = rec_call e in
    RestartEvery (pos, ident, expr_list, e), List.flatten gen_nodes1 @ gen_nodes2
  | Pre (pos, e) -> 
    let e, gen_nodes = rec_call e in
    Pre (pos, e), gen_nodes
  | Arrow (pos, e1, e2) -> 
    let e1, gen_nodes1 = rec_call e1 in
    let e2, gen_nodes2 = rec_call e2 in
    Arrow (pos, e1, e2), gen_nodes1 @ gen_nodes2
  | Call (pos, ty_args, id, expr_list) ->
    let ty_args, gen_nodes_ty = List.map (desugar_type ctx node_name fun_ids) ty_args |> List.split in
    let args, gen_nodes = desugar_args id expr_list in
    let e = A.Call (pos, ty_args, id, args) in
    let gen_nodes = List.flatten gen_nodes_ty @ List.flatten gen_nodes in
    (* A call without type arguments to a constructor's name is a constructor application *)
    (match ty_args, Ctx.lookup_constructor ctx (NI.get_name id) with
    | [], Some (ty_name, field_tys) ->
      let orig = A.ADTTerm (pos, [], NI.get_name id, expr_list) in
      ascribe_construction ~insert ~bound ctx node_name orig e ty_name [] field_tys gen_nodes
    | _ :: _, _ | [], None -> e, gen_nodes)
  | Match (pos, e, arms, ty_opt) ->
    (* Each match arm body is evaluated under the clock determined by the
       scrutinee matching the arm's pattern (the match is desugared into a
       lazy if-then-else chain later in the pipeline). When a body is a
       temporal expression (it uses '->' or 'pre'), abstract it into a call
       to a fresh internal node so that its temporal behavior is driven by
       that clock, just as is done for when-then-else branches.

       The arms are resolved against the scrutinee as written, before the nodes
       its own subexpressions need are generated and while its type can still be
       inferred. *)
    let scrut_ty = scrutinee_type ctx node_name e in
    let arms = List.map (fun (pat, arm_e) -> resolve_arm ctx scrut_ty pat, arm_e) arms in
    let e, gen_nodes1 = rec_call e in
    let arms, gen_nodes2 = List.map (fun ((arm_ctx, pat, subst), arm_e) ->
      let arm_e = AH.apply_subst_in_expr subst arm_e in
      let bound = Ctx.SI.union bound (AH.pat_bound_vars pat) in
      let arm_e, gen_nodes = desugar_expr ~insert ~bound arm_ctx node_name fun_ids arm_e in
      let arm_e, gen_nodes' = abstract_temporal_branch arm_ctx node_name gen_nodes arm_e in
      (pat, arm_e), gen_nodes @ gen_nodes'
    ) arms |> List.split in
    Match (pos, e, arms, ty_opt), gen_nodes1 @ List.flatten gen_nodes2
  | ADTTerm (pos, ty_args, ctor, args) ->
    let ty_args, gen_nodes_ty = List.map (desugar_type ctx node_name fun_ids) ty_args |> List.split in
    let args, gen_nodes = List.map rec_call args |> List.split in
    let e = A.ADTTerm (pos, ty_args, ctor, args) in
    let gen_nodes = List.flatten gen_nodes_ty @ List.flatten gen_nodes in
    (match Ctx.lookup_constructor ctx ctor with
    | Some (ty_name, field_tys) ->
      ascribe_construction ~insert ~bound ctx node_name expr e ty_name ty_args field_tys gen_nodes
    | None -> e, gen_nodes)
  | AbstractSymConst _ -> assert false (* never produced before lustreGenNodes runs *)
  | ADTTester (pos, e, c) ->
    let e, gen_nodes = rec_call e in
    ADTTester (pos, e, c), gen_nodes

let desugar_contract_item: ?insert:bool -> Ctx.tc_context -> NI.t -> NI.t list -> A.contract_node_equation -> A.contract_node_equation * A.declaration list =
fun ?(insert = true) ctx node_name fun_ids ci ->
  let rec_call = desugar_expr ~insert ctx node_name fun_ids in
  match ci with
  | A.GhostVars (pos, lhs, e) ->
    let lhs, gen_nodes_ty = match lhs with
      | A.GhostVarDec (p, tis) ->
          let tis, gen_nodes_ty = List.map (fun (p, id, ty) ->
            let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
            (p, id, ty), gen_nodes
          ) tis |> List.split in
          A.GhostVarDec (p, tis), List.flatten gen_nodes_ty
    in
    let e, gen_nodes = rec_call e in
    A.GhostVars (pos, lhs, e), gen_nodes_ty @ gen_nodes
  | Assume (pos, name, b, e) ->
    let e, gen_nodes = rec_call e in 
    Assume (pos, name, b, e), gen_nodes
  | Guarantee (pos, name, b, e) -> 
    let e, gen_nodes = rec_call e in 
    Guarantee (pos, name, b, e), gen_nodes
  | Decreases (pos, e) ->
    let e, gen_nodes = desugar_expr ~insert:false ctx node_name fun_ids e in
    Decreases (pos, e), gen_nodes
  | Mode (pos, i, reqs, enss) ->
    let (reqs, gen_nodes1) = 
      List.map (fun (pos, id, expr) -> (pos, id, rec_call expr)) reqs |> 
      List.map (fun (pos, id, (expr, decls)) -> ((pos, id, expr), decls)) |> 
      List.split in 
    let (enss, gen_nodes2) = 
      List.map (fun (pos, id, expr) -> (pos, id, rec_call expr)) enss |> 
      List.map (fun (pos, id, (expr, decls)) -> ((pos, id, expr), decls)) |> 
      List.split in 
    Mode (pos, i, reqs, enss), (List.flatten gen_nodes1) @ (List.flatten gen_nodes2)
  | ContractCall (pos, i, ty_args, exprs, ids) ->
    let ty_args, gen_nodes_ty = List.map (desugar_type ctx node_name fun_ids) ty_args |> List.split in
    let (exprs, gen_nodes) = List.map rec_call exprs |> List.split in
    ContractCall (pos, i, ty_args, exprs, ids), List.flatten gen_nodes_ty @ List.flatten gen_nodes
  | A.GhostConst (A.FreeConst (pos, id, ty)) ->
    let ty, gen_nodes = desugar_type ctx node_name fun_ids ty in
    A.GhostConst (A.FreeConst (pos, id, ty)), gen_nodes
  | A.GhostConst (A.TypedConst (pos, id, e, ty)) ->
    let ty, gen_nodes_ty = desugar_type ctx node_name fun_ids ty in
    let e, gen_nodes = desugar_expr ~insert:false ctx node_name fun_ids e in
    A.GhostConst (A.TypedConst (pos, id, e, ty)), gen_nodes_ty @ gen_nodes
  | A.GhostConst (A.UntypedConst (pos, id, e)) ->
    let e, gen_nodes = desugar_expr ~insert:false ctx node_name fun_ids e in
    A.GhostConst (A.UntypedConst (pos, id, e)), gen_nodes
  | AssumptionVars _ as ci -> ci, []

let desugar_contract: ?insert:bool -> Ctx.tc_context -> NI.t -> NI.t list -> A.contract option -> A.contract option * A.declaration list =
fun ?(insert = true) ctx node_name fun_ids contract ->
  match contract with
  | Some (pos, contract_items) ->
    (* A contract's ghost variables, ghost constants and modes are in scope in
       its own items, so the items are desugared in a context that holds them.
       One declaration at a time, repeating while a pass adds something, so that
       a declaration this pass cannot resolve yet (a call to a contract that is
       type checked later, say) costs only itself, and an order that needs an
       earlier pass to run first still resolves. Best-effort, as for the node
       signatures below: what cannot be added is left to the later
       type-checking pass to report on. *)
    let rec add_decls ctx pending =
      let ctx, unresolved =
        List.fold_left (fun (ctx, unresolved) item ->
          match Chk.tc_ctx_of_contract ctx Ctx.Ghost node_name (pos, [item]) with
          | Ok (_, ctx, _) -> (ctx, unresolved)
          | Error _ -> (ctx, item :: unresolved)
          | exception _ -> (ctx, item :: unresolved)
        ) (ctx, []) pending
      in
      if List.length unresolved = List.length pending then ctx
      else add_decls ctx (List.rev unresolved)
    in
    let ctx = add_decls ctx contract_items in
    let items, gen_nodes = (List.map (desugar_contract_item ~insert ctx node_name fun_ids) contract_items) |> List.split in
    Some (pos, items), List.flatten gen_nodes
  | None -> None, []

(* bound holds the pattern variables of the enclosing match block arms *)
let rec desugar_node_item: ?insert:bool -> ?bound:Ctx.SI.t -> Ctx.tc_context -> NI.t -> NI.t list -> A.node_item -> A.node_item * A.declaration list =
fun ?(insert = true) ?(bound = Ctx.SI.empty) ctx node_name fun_ids ni ->
  let rec_call = desugar_node_item ~insert ~bound ctx node_name fun_ids in
  match ni with
  | A.Body (Equation (pos, lhs, rhs)) -> 
    let rhs, gen_nodes = desugar_expr ~insert ~bound ctx node_name fun_ids rhs in 
    A.Body (Equation (pos, lhs, rhs)), gen_nodes
  | AnnotProperty (pos, name, e, k) -> 
    let e, gen_nodes = desugar_expr ~insert ~bound ctx node_name fun_ids e in 
    AnnotProperty(pos, name, e, k), gen_nodes
  | IfBlock (pos, cond, nis1, nis2) -> 
    let nis1, gen_nodes1 = List.map rec_call nis1 |> List.split in
    let nis2, gen_nodes2 = List.map rec_call nis2 |> List.split in
    let cond, gen_nodes3 = desugar_expr ~insert ~bound ctx node_name fun_ids cond in
    A.IfBlock (pos, cond, nis1, nis2), List.flatten gen_nodes1 @ List.flatten gen_nodes2 @ gen_nodes3
  | WhenBlock (pos, cond, nis1, nis2) ->
    (* The right-hand side of each equation in a when block branch becomes a
       branch of a lazy if-then-else once the block is desugared (later in the
       pipeline). Abstract a temporal right-hand side into a call to a fresh
       internal node here, while new node declarations can still be generated
       and type checked. *)
    let process_branch_item ni =
      match ni with
      | A.Body (A.Equation (epos, lhs, rhs)) ->
        let rhs, gen_nodes1 = desugar_expr ~insert ~bound ctx node_name fun_ids rhs in
        let rhs, gen_nodes2 = abstract_temporal_branch ctx node_name gen_nodes1 rhs in
        A.Body (A.Equation (epos, lhs, rhs)), gen_nodes1 @ gen_nodes2
      | _ -> rec_call ni
    in
    let nis1, gen_nodes1 = List.map process_branch_item nis1 |> List.split in
    let nis2, gen_nodes2 = List.map process_branch_item nis2 |> List.split in
    let cond, gen_nodes3 = desugar_expr ~insert ~bound ctx node_name fun_ids cond in
    A.WhenBlock (pos, cond, nis1, nis2), List.flatten gen_nodes1 @ List.flatten gen_nodes2 @ gen_nodes3
  | MatchBlock (pos, scrut, arms, ty) ->
    (* A match block becomes a chain of when blocks later in the pipeline, so
       its arms need the same temporal abstraction as a when-block branch *)
    let process_branch_item ctx bound ni =
      match ni with
      | A.Body (A.Equation (epos, lhs, rhs)) ->
        let rhs, gen_nodes1 = desugar_expr ~insert ~bound ctx node_name fun_ids rhs in
        let rhs, gen_nodes2 = abstract_temporal_branch ctx node_name gen_nodes1 rhs in
        A.Body (A.Equation (epos, lhs, rhs)), gen_nodes1 @ gen_nodes2
      | A.Body (A.Assert _) | A.IfBlock _ | A.WhenBlock _ | A.MatchBlock _
      | A.FrameBlock _ | A.AnnotMain _ | A.AnnotProperty _ | A.Auto _ ->
        desugar_node_item ~insert ~bound ctx node_name fun_ids ni
    in
    let scrut_ty = scrutinee_type ctx node_name scrut in
    let arms, gen_nodes1 =
      List.map (fun (p, items) ->
        let arm_ctx, p, subst = resolve_arm ctx scrut_ty p in
        let items = List.map (AH.apply_subst_in_node_item subst) items in
        let bound = Ctx.SI.union bound (AH.pat_bound_vars p) in
        let items, gn = List.map (process_branch_item arm_ctx bound) items |> List.split in
        (p, items), List.flatten gn) arms
      |> List.split
    in
    let scrut, gen_nodes2 = desugar_expr ~insert ~bound ctx node_name fun_ids scrut in
    A.MatchBlock (pos, scrut, arms, ty), List.flatten gen_nodes1 @ gen_nodes2
  | FrameBlock (pos, vars, nes, nis) -> 
    let nes = List.map (fun x -> A.Body x) nes in
    let nes, gen_nodes1 = List.map rec_call nes |> List.split in
    let nes = List.map (fun ne -> match ne with
      | A.Body (A.Equation _ as eq) -> eq
      | _ -> assert false
    ) nes in
    let nis, gen_nodes2 = List.map rec_call nis |> List.split in
    FrameBlock(pos, vars, nes, nis), List.flatten gen_nodes1 @ List.flatten gen_nodes2
  | Body (Assert (pos, e)) ->
    let e, gen_nodes = desugar_expr ~insert ~bound ctx node_name fun_ids e in
    Body (Assert (pos, e)), gen_nodes
  | AnnotMain _ -> ni, []
  | Auto _ -> ni, []
    

(* The calls in an expression, including those in the expressions of the
   types it mentions (type arguments and binder types) *)
let rec calls_of_expr e =
  let r = calls_of_expr in
  let rs es = NI.Set.flatten (List.map r es) in
  let call id es = NI.Set.add id (rs es) in
  match e with
  | A.Ident _ | A.ModeRef _ | A.Const _ | A.Last _
  | A.EmptyMap (_, None) | A.EmptySet (_, None) -> NI.Set.empty
  | A.EmptyMap (_, Some (kt, vt)) -> NI.Set.union (calls_of_type kt) (calls_of_type vt)
  | A.EmptySet (_, Some ty) | A.AbstractSymConst (_, ty) -> calls_of_type ty
  | A.FieldProject (_, e, _, _) | A.UnaryOp (_, _, e) | A.ConvOp (_, _, e)
  | A.Extract (_, e, _, _) | A.When (_, e, _) | A.Pre (_, e) | A.ADTTester (_, e, _) -> r e
  | A.BinaryOp (_, _, e1, e2) | A.CompOp (_, _, e1, e2) | A.Arrow (_, e1, e2)
  | A.ArrayConstr (_, e1, e2) | A.IndexAccess (_, e1, e2, _) -> rs [e1; e2]
  | A.TernaryOp (_, _, e1, e2, e3) -> rs [e1; e2; e3]
  | A.AnyOp (_, (_, _, ty), e) | A.ChooseOp (_, (_, _, ty), e) | A.TypeAscription (_, e, ty) ->
    NI.Set.union (calls_of_type ty) (r e)
  | A.GroupExpr (_, _, es) -> rs es
  | A.RecordExpr (_, _, tys, flds) ->
    NI.Set.flatten (rs (List.map snd flds) :: List.map calls_of_type tys)
  | A.StructUpdate (_, e1, idx, e2) ->
    NI.Set.flatten
      [r e1; AH.fold_label_or_index NI.Set.empty NI.Set.union r idx;
       (match e2 with Some e2 -> r e2 | None -> NI.Set.empty)]
  | A.Quantifier (_, _, tis, e) ->
    NI.Set.flatten (r e :: List.map (fun (_, _, ty) -> calls_of_type ty) tis)
  | A.Merge (_, _, arms) -> rs (List.map snd arms)
  | A.Condact (_, e1, e2, id, es1, es2) -> call id (e1 :: e2 :: es1 @ es2)
  | A.Activate (_, id, e1, e2, es) -> call id (e1 :: e2 :: es)
  | A.RestartEvery (_, id, es, e) -> call id (e :: es)
  | A.Call (_, tys, id, es) -> NI.Set.flatten (call id es :: List.map calls_of_type tys)
  | A.ADTTerm (_, tys, _, es) -> NI.Set.flatten (rs es :: List.map calls_of_type tys)
  | A.Match (_, e, arms, _) -> rs (e :: List.map snd arms)

and calls_of_type ty =
  AH.fold_lustre_ty ~into_ty_args:true calls_of_expr NI.Set.empty NI.Set.union ty

(* The calls in the items of a node body *)
let rec calls_of_items items =
  let calls_of_eq = function
    | A.Equation (_, _, e) | A.Assert (_, e) -> calls_of_expr e
  in
  List.fold_left (fun acc item ->
    let calls = match item with
      | A.Body eq -> calls_of_eq eq
      | A.IfBlock (_, c, items1, items2) | A.WhenBlock (_, c, items1, items2) ->
        NI.Set.flatten [calls_of_expr c; calls_of_items items1; calls_of_items items2]
      | A.MatchBlock (_, scrut, arms, _) ->
        NI.Set.flatten (calls_of_expr scrut :: List.map (fun (_, items) -> calls_of_items items) arms)
      | A.FrameBlock (_, _, eqs, items) ->
        NI.Set.flatten (calls_of_items items :: List.map calls_of_eq eqs)
      | A.AnnotProperty (_, _, e, A.Provided p) -> NI.Set.union (calls_of_expr e) (calls_of_expr p)
      | A.AnnotProperty (_, _, e, (A.Invariant | A.Reachable _)) -> calls_of_expr e
      | A.AnnotMain _ | A.Auto _ -> NI.Set.empty
    in
    NI.Set.union acc calls
  ) NI.Set.empty items

let calls_of_const_decl = function
  | A.FreeConst (_, _, ty) -> calls_of_type ty
  | A.UntypedConst (_, _, e) -> calls_of_expr e
  | A.TypedConst (_, _, e, ty) -> NI.Set.union (calls_of_expr e) (calls_of_type ty)

(* The calls in the declarations of the local variables and constants of a node *)
let calls_of_locals locals =
  NI.Set.flatten (List.map (function
    | A.NodeVarDecl (_, (_, _, ty, _)) -> calls_of_type ty
    | A.NodeConstDecl (_, c) -> calls_of_const_decl c
  ) locals)

(* The calls in a contract, including the contract nodes it imports *)
let calls_of_contract contract =
  let calls_of_item = function
    | A.GhostConst c -> calls_of_const_decl c
    | A.GhostVars (_, A.GhostVarDec (_, tis), e) ->
      NI.Set.flatten (calls_of_expr e :: List.map (fun (_, _, ty) -> calls_of_type ty) tis)
    | A.Assume (_, _, _, e) | A.Guarantee (_, _, _, e) | A.Decreases (_, e) -> calls_of_expr e
    | A.Mode (_, _, reqs, enss) ->
      NI.Set.flatten (List.map (fun (_, _, e) -> calls_of_expr e) (reqs @ enss))
    | A.ContractCall (_, id, _, es, _) ->
      NI.Set.flatten (NI.Set.singleton id :: List.map calls_of_expr es)
    | A.AssumptionVars _ -> NI.Set.empty
  in
  match contract with
  | Some (_, items) -> NI.Set.flatten (List.map calls_of_item items)
  | None -> NI.Set.empty

(* The calls in the types of the inputs and outputs of a node *)
let calls_of_signature inputs outputs =
  NI.Set.flatten
    (List.map (fun (_, _, ty, _, _) -> calls_of_type ty) inputs
     @ List.map (fun (_, _, ty, _) -> calls_of_type ty) outputs)

(* The recursive functions, and the functions and contract nodes their
   definitions use directly or indirectly (through bodies, contracts and
   signatures), which are encoded together with them (see LustreFunDefs) *)
let functions_of_recursive_definitions decls =
  let uses = List.fold_left (fun acc decl -> match decl with
    | A.FuncDecl (_, (id, _, _, _, inputs, outputs, locals, items, contract), _) ->
      let calls =
        NI.Set.flatten
          [calls_of_items items; calls_of_contract contract;
           calls_of_signature inputs outputs; calls_of_locals locals]
      in
      NI.Map.add id calls acc
    | A.ContractNodeDecl (_, (id, _, inputs, outputs, contract)) ->
      let calls =
        NI.Set.union (calls_of_contract (Some contract)) (calls_of_signature inputs outputs)
      in
      NI.Map.add id calls acc
    | A.TypeDecl _ | A.ConstDecl _ | A.NodeDecl _ | A.NodeParamInst _ -> acc
  ) NI.Map.empty decls
  in
  let rec visit seen id =
    if NI.Set.mem id seen then seen
    else match NI.Map.find_opt id uses with
      | Some calls -> NI.Set.fold (fun c seen -> visit seen c) calls (NI.Set.add id seen)
      | None -> seen
  in
  List.fold_left (fun seen decl ->
    match decl with
    | A.FuncDecl (_, (id, _, _, _, _, _, _, _, _), { A.is_rec = true; _ }) -> visit seen id
    | A.FuncDecl _ | A.TypeDecl _ | A.ConstDecl _ | A.NodeDecl _
    | A.ContractNodeDecl _ | A.NodeParamInst _ -> seen
  ) NI.Set.empty decls

let gen_nodes_of_decls: Ctx.tc_context -> A.declaration list -> A.declaration list =
fun ctx decls ->
  let fun_ids = List.filter_map
    (fun decl -> match decl with | A.FuncDecl (_, (id, _, _, _, _, _, _, _, _), _) -> Some id | _ -> None)
    decls
  in
  (* Pre-populate the context with the signatures of all nodes and functions so
     that the types of node calls appearing in abstracted when branches can be
     inferred (node/contract type checking happens later in the pipeline) *)
  let rec_def_funs = functions_of_recursive_definitions decls in
  (* Which parameters are constant is read from the declarations, so that it
     is known for every node whatever the order of the declarations *)
  let ctx =
    List.fold_left (fun ctx decl ->
      match decl with
      | A.NodeDecl (_, (id, _, _, _, inputs, _, _, _, _))
      | A.FuncDecl (_, (id, _, _, _, inputs, _, _, _, _), _) -> Ctx.add_node_param_attr ctx id inputs
      | A.TypeDecl _ | A.ConstDecl _ | A.ContractNodeDecl _ | A.NodeParamInst _ -> ctx
    ) ctx decls
  in
  let ctx = add_node_sigs ctx decls in
  let decls =
  List.fold_left (fun decls decl ->
    match decl with
    | A.NodeDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract)) ->
      let ctx = Chk.add_full_node_ctx ctx id params inputs outputs locals in
      let inputs, gen_nodes_in = List.map (fun (p, id', ty, c, b) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c, b), gen_nodes
      ) inputs |> List.split in
      let outputs, gen_nodes1 = List.map (fun (p, id', ty, c) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c), gen_nodes
      ) outputs |> List.split in
      let locals, gen_nodes_loc = List.map (function
        | A.NodeVarDecl (pos, (p, id', ty, c)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeVarDecl (pos, (p, id', ty, c)), gen_nodes
        | A.NodeConstDecl (pos, A.FreeConst (_, id', ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.FreeConst (pos, id', ty)), gen_nodes
        | A.NodeConstDecl (pos, A.TypedConst (_, id', e, ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.TypedConst (pos, id', e, ty)), gen_nodes
        | A.NodeConstDecl (pos, (A.UntypedConst _ as cd)) ->
            A.NodeConstDecl (pos, cd), []
      ) locals |> List.split in
      let items, gen_nodes2 = List.map (desugar_node_item ctx id fun_ids) items |> List.split in
      let contract, gen_nodes3 = desugar_contract ctx id fun_ids contract in
      let gen_nodes = List.flatten gen_nodes_in @ List.flatten gen_nodes1 @ List.flatten gen_nodes_loc @ List.flatten gen_nodes2 @ gen_nodes3 in
      decls @ gen_nodes @ [A.NodeDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract))] 
    | A.FuncDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract), is_rec) ->
      let ctx = Chk.add_full_node_ctx ctx id params inputs outputs locals in
      let inputs, gen_nodes_in = List.map (fun (p, id', ty, c, b) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c, b), gen_nodes
      ) inputs |> List.split in
      let outputs, gen_nodes_out = List.map (fun (p, id', ty, c) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c), gen_nodes
      ) outputs |> List.split in
      let locals, gen_nodes_loc = List.map (function
        | A.NodeVarDecl (pos, (p, id', ty, c)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeVarDecl (pos, (p, id', ty, c)), gen_nodes
        | A.NodeConstDecl (pos, A.FreeConst (_, id', ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.FreeConst (pos, id', ty)), gen_nodes
        | A.NodeConstDecl (pos, A.TypedConst (_, id', e, ty)) ->
            let ty, gen_nodes = desugar_type ctx id fun_ids ty in
            A.NodeConstDecl (pos, A.TypedConst (pos, id', e, ty)), gen_nodes
        | A.NodeConstDecl (pos, (A.UntypedConst _ as cd)) ->
            A.NodeConstDecl (pos, cd), []
      ) locals |> List.split in
      (* An ascription would prevent the encoding of a recursive definition as
         an SMT definition *)
      let insert = not (NI.Set.mem id rec_def_funs) in
      let items, gen_nodes = List.map (desugar_node_item ~insert ctx id fun_ids) items |> List.split in
      let contract, gen_nodes2 = desugar_contract ~insert ctx id fun_ids contract in
      let gen_nodes = 
        List.flatten gen_nodes_in @ List.flatten gen_nodes_out @ List.flatten gen_nodes_loc @ List.flatten gen_nodes 
      in
      decls @ gen_nodes @ gen_nodes2 @
      [A.FuncDecl (span, (id, ext, opac, params, inputs, outputs, locals, items, contract), is_rec)]
    | A.ContractNodeDecl (span, (id, params, inputs, outputs, contract)) ->
      let ctx = Chk.add_io_node_ctx ctx id params inputs outputs in
      let inputs, gen_nodes_in = List.map (fun (p, id', ty, c, b) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c, b), gen_nodes
      ) inputs |> List.split in
      let outputs, gen_nodes_out = List.map (fun (p, id', ty, c) ->
        let ty, gen_nodes = desugar_type ctx id fun_ids ty in
        (p, id', ty, c), gen_nodes
      ) outputs |> List.split in
      let insert = not (NI.Set.mem id rec_def_funs) in
      let contract, gen_nodes = desugar_contract ~insert ctx id fun_ids (Some contract) in
      let contract = match contract with
      | Some contract -> contract
      | None -> assert false in (* Must have a contract *)
      let gen_nodes = List.flatten gen_nodes_in @ List.flatten gen_nodes_out @ gen_nodes in
      decls @ gen_nodes @ [A.ContractNodeDecl (span, (id, params, inputs, outputs, contract))] 
    | decl -> decl :: decls
  ) [] decls in 
  decls

let gen_nodes: Ctx.tc_context -> A.declaration list
  -> (A.declaration list, [> error]) result =
fun ctx decls ->
  try Ok (gen_nodes_of_decls ctx decls) with
  | Const_in_clocked_temporal_expr (pos, kind) ->
    Error (`LustreGenNodesError (pos, kind))
