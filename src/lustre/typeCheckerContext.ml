(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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
 
(** The type checker context use for typechecking the surface level language
  
     @author Apoorv Ingle *)

module LA = LustreAst
module SI = LA.SI
module LH = LustreAstHelpers          

type tc_type  = LA.lustre_type
(** Type alias for lustre type from LustreAst  *)

module IMap = struct
  (* everything that [Stdlib.Map] gives us  *)
  include Map.Make(struct
              type t = LA.ident
              let compare i1 i2 = HString.compare i1 i2
            end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end
(** Map for types with identifiers as keys *)


type enum_variants = LA.ident list IMap.t
(** A store of the variants for defined enumeration types *)

type ty_alias_store = tc_type IMap.t
(** A store of type Aliases, i.e. for user defined types  *)

type ty_store = tc_type IMap.t
(** A store of identifier and their types*)

type node_ty_store = tc_type LA.NodeNameMap.t
(** A store of identifier and their types*)

(** A store of monomorphized node names and their type arguments *)

type source = 
| Input
| Output
| Local
| Global
| Ghost

type const_store = (LA.expr * tc_type option * source) IMap.t 
(** A Store of constant identifier and their (const) values with types. 
 *  The values of the associated identifiers should be evaluated to a 
 *  Bool or an Int at constant propogation phase of type checking. *)

type ty_set = SI.t
(** set of valid user type identifiers *)

type ty_var_store = (HString.t list) LA.NodeNameMap.t
(** A store of type variable IDs for each node ID *)

type ty_ty_var_store = (HString.t list) IMap.t
(** A store of type variable IDs for each user type *)

type contract_exports = (ty_store) LA.NodeNameMap.t
(** Mapping for all the exports of the contract, modes and contract ghost const and vars *)

type param_store = (HString.t * bool) list LA.NodeNameMap.t
(** A store of parameter names and flags indicating if the argument is constant *)

type tc_context = { ty_syns: ty_alias_store       (* store of the type alias mappings *)
                  ; ty_ctx: ty_store              (* store of the types of identifiers and nodes *)
                  ; contract_ctx: node_ty_store        (* store of the types of contracts *)
                  ; node_ctx: node_ty_store       (* store of the types of nodes *)
                  ; node_param_attr: param_store  (* store of the parameter attributes of nodes *)
                  ; vl_ctx: const_store           (* store of typed constants to its value *)
                  ; u_types: ty_set               (* store of all declared user types,
                                                     this is poor mans kind (type of type) context *)
                  ; contract_export_ctx:          (* stores all the export variables  of the contract *)
                      contract_exports 
                  ; enum_vars: enum_variants
                  ; ty_vars:                      (* stores the type variables associated with each node *)
                      ty_var_store              
                  ; contract_ty_vars:             (* stores  the type variables associated with each contract *)
                      ty_var_store  
                  ; ty_ty_vars: ty_ty_var_store      (* stores the type variables associated with each user type *)
                  }
(** The type checker global context *)

let (let*) = Res.(>>=)

let empty_tc_context: tc_context =
  { ty_syns = IMap.empty
  ; ty_ctx = IMap.empty
  ; contract_ctx = LA.NodeNameMap.empty
  ; node_ctx = LA.NodeNameMap.empty
  ; node_param_attr = LA.NodeNameMap.empty
  ; vl_ctx = IMap.empty
  ; u_types = SI.empty
  ; contract_export_ctx = LA.NodeNameMap.empty
  ; enum_vars = IMap.empty
  ; ty_vars = LA.NodeNameMap.empty
  ; contract_ty_vars = LA.NodeNameMap.empty
  ; ty_ty_vars = IMap.empty
  (* ; ty_args = IMap.empty *)
  }
(** The empty context with no information *)

(**********************************************
 * Helper functions for type checker context *
 **********************************************)
                  
let member_ty_syn: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.ty_syns)
(** Checks if the type is a type synonym  *)

let member_ty: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.ty_ctx)
(** Checks if the identifier is a typed identifier *)
               
let member_contract: tc_context -> LA.node_name -> bool
  = fun ctx i -> LA.NodeNameMap.mem i (ctx.contract_ctx)
(** Checks if the contract name is in the context *)

let member_node: tc_context -> LA.node_name -> bool
  = fun ctx i -> LA.NodeNameMap.mem i (ctx.node_ctx)
(** Checks if the node name is in the context *)

let member_u_types : tc_context -> LA.ident -> bool
  = fun ctx i -> SI.mem i ctx.u_types
(** Checks if the type identifier is a user defined type *)

let member_val: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.vl_ctx)
(** Checks if the identifier is a constant  *)

let rec lookup_ty_syn: tc_context -> LA.ident -> tc_type list -> tc_type option 
= fun ctx i ty_args ->
  match IMap.find_opt i (ctx.ty_syns) with
  | Some ty -> (
    let ps =
      match IMap.find_opt i (ctx.ty_ty_vars) with
      | Some ps -> ps
      | None -> []
    in
    let sigma = List.combine ps ty_args in
    let ty = LustreAstHelpers.apply_type_subst_in_type sigma ty in
    match ty with
    | LA.UserType (_, ty_args, uid) ->
      if uid = i then Some ty
      else lookup_ty_syn ctx uid ty_args
    | _ -> Some ty
  )
  | None -> None
(** Picks out the type synonym from the context
    If it is user type then chases it (recursively looks up) 
    the actual type. This chasing is necessary to check type equality 
    between user defined types. *)

let rec expand_type_syn: tc_context -> tc_type -> tc_type
  = fun ctx -> function
  | UserType (_, ty_args, i) as ty -> (
    match IMap.find_opt i (ctx.ty_syns) with
    | None -> ty
    | Some ty -> (
      match ty with
      | UserType (_, _, uid) when uid = i -> ty
      | _ -> (
        let ty_vars =
          match IMap.find_opt i (ctx.ty_ty_vars) with
          | Some ps -> ps
          | None -> []
        in
        let sigma = List.combine ty_vars ty_args in
        let ty = LustreAstHelpers.apply_type_subst_in_type sigma ty in
        expand_type_syn ctx ty
      )
    )
  )
  | TupleType (p, tys) ->
    let tys = List.map (expand_type_syn ctx) tys in
    TupleType (p, tys)
  | GroupType (p, tys) ->
    let tys = List.map (expand_type_syn ctx) tys in
    GroupType (p, tys)
  | RecordType (p, name, tys) ->
    let tys = List.map (fun (p, i, t) -> p, i, expand_type_syn ctx t) tys in
    RecordType (p, name, tys)
  | ArrayType (p, (ty, e)) ->
    let ty = expand_type_syn ctx ty in
    ArrayType (p, (ty, e))
  | TArr (p, ty1, ty2) -> 
    let ty1 = expand_type_syn ctx ty1 in 
    let ty2 = expand_type_syn ctx ty2 in 
    TArr (p, ty1, ty2)
  | LA.RefinementType (p1, (p2, id, ty), e) -> 
    let ty = expand_type_syn ctx ty in
    LA.RefinementType (p1, (p2, id, ty), e)
  | ty -> ty
(** Chases the type (and nested types) to its base form to resolve type synonyms *)

let lookup_ty: tc_context -> LA.ident -> tc_type option
  = fun ctx i ->
  match (IMap.find_opt i (ctx.ty_ctx)) with
  | Some ty -> Some (expand_type_syn ctx ty) 
  | None -> None
(** Picks out the type of the identifier to type context map *)

let lookup_contract_ty: tc_context -> LA.node_name -> tc_type option
  = fun ctx i -> LA.NodeNameMap.find_opt i (ctx.contract_ctx)
(** Lookup a contract type  *)
               
let lookup_node_ty: tc_context -> LA.node_name -> tc_type option
  = fun ctx i -> LA.NodeNameMap.find_opt i (ctx.node_ctx)
(** Lookup a node type  *)

let lookup_node_ty_vars: tc_context -> LA.node_name -> HString.t list option
  = fun ctx i -> LA.NodeNameMap.find_opt i (ctx.ty_vars)
(** Lookup a node's type variables *)

let lookup_contract_ty_vars: tc_context -> LA.node_name -> HString.t list option
  = fun ctx i -> LA.NodeNameMap.find_opt i (ctx.contract_ty_vars)
(** Lookup a contract's type variables *)

let lookup_ty_ty_vars: tc_context -> LA.ident -> HString.t list option
  = fun ctx i -> IMap.find_opt i (ctx.ty_ty_vars)
(** Lookup a node's type variables *)

let lookup_node_param_attr: tc_context -> LA.node_name -> (HString.t * bool) list option
  = fun ctx i -> LA.NodeNameMap.find_opt i (ctx.node_param_attr)

let lookup_node_param_ids: tc_context -> LA.node_name -> HString.t list option
  = fun ctx i ->
  match LA.NodeNameMap.find_opt i (ctx.node_param_attr) with
  | Some l -> Some (List.map fst l)
  | None -> None

let lookup_const: tc_context -> LA.ident -> (LA.expr * tc_type option * source) option
  = fun ctx i -> IMap.find_opt i (ctx.vl_ctx)
(** Lookup a constant identifier *)

let lookup_variants: tc_context -> LA.ident -> LA.ident list option
  = fun ctx i -> IMap.find_opt i (ctx.enum_vars)
(** Lookup the variants for an enumeration type name *)

let add_ty_syn: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with ty_syns = IMap.add i ty (ctx.ty_syns)}
(** add a type synonym in the typing context *)

let add_ty: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with ty_ctx = IMap.add i ty (ctx.ty_ctx)}
(** Add type binding into the typing context *)
                  
let add_ty_contract: tc_context -> LA.node_name -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with contract_ctx = LA.NodeNameMap.add i ty (ctx.contract_ctx)}
(**  Add the type of the contract *)

let add_ty_node: tc_context -> LA.node_name -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with node_ctx = LA.NodeNameMap.add i ty (ctx.node_ctx)}
(**  Add the type of the node *)

let add_ty_vars_node: tc_context -> LA.node_name -> LA.ident list -> tc_context
  = fun ctx i ty_vars -> 
    {ctx with ty_vars = LA.NodeNameMap.add i ty_vars (ctx.ty_vars)}
(**  Add the type variables of the node *)

let add_ty_vars_ty: tc_context -> LA.ident -> LA.ident list -> tc_context
  = fun ctx i ty_ty_vars -> 
    {ctx with ty_ty_vars = IMap.add i ty_ty_vars (ctx.ty_ty_vars)}
(**  Add the type variables of the node *)

let add_ty_vars_contract: tc_context -> LA.node_name -> LA.ident list -> tc_context
  = fun ctx i contract_ty_vars -> 
    {ctx with contract_ty_vars = LA.NodeNameMap.add i contract_ty_vars (ctx.contract_ty_vars)}
(**  Add the type variables of the contract *)

let add_node_param_attr : tc_context -> LA.node_name -> LA.const_clocked_typed_decl list -> tc_context
  = fun ctx i args ->
  let v =
    List.map (function (_, id, _, _, is_const) -> (id, is_const)) args
  in
  {ctx with node_param_attr = LA.NodeNameMap.add i v (ctx.node_param_attr)}

let add_ty_decl: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with u_types = SI.add i (ctx.u_types)}
(** Add a user declared type in the typing context *)

let add_enum_variants: tc_context -> LA.ident -> LA.ident list -> tc_context
  = fun ctx i vs -> {ctx with enum_vars = IMap.add i vs (ctx.enum_vars) }
(** Add an enumeration type and associated variants to the typing context *)

let is_enum_variant ctx id =
  match lookup_const ctx id with
  | Some (_, Some (UserType (_, _, uid)), _) ->
    lookup_variants ctx uid != None
  | _ -> false

let remove_ty: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with ty_ctx= IMap.remove i (ctx.ty_ctx)}
(** Removes a type binding  *)

let remove_ty_ctx: tc_context -> tc_context 
  = fun ctx -> {ctx with ty_ctx = IMap.empty}

let add_const: tc_context -> LA.ident -> LA.expr -> tc_type -> source -> tc_context
  = fun ctx i e ty sc -> {ctx with vl_ctx = IMap.add i (e, (Some ty), sc) ctx.vl_ctx} 
(** Adds a constant variable along with its expression and type  *)

let add_untyped_const : tc_context -> LA.ident -> LA.expr -> source -> tc_context
= fun ctx i e sc -> {ctx with vl_ctx = IMap.add i (e, None, sc) ctx.vl_ctx} 

let union: tc_context -> tc_context -> tc_context
  = fun ctx1 ctx2 -> { ty_syns = (IMap.union (fun _ _ v2 -> Some v2)
                                  (ctx1.ty_syns)
                                  (ctx2.ty_syns))
                    ; ty_ctx = (IMap.union (fun _ _ v2 -> Some v2)
                                  (ctx1.ty_ctx)
                                  (ctx2.ty_ctx))
                    ; contract_ctx = (LA.NodeNameMap.union (fun _ _ v2 -> Some v2)
                                        (ctx1.contract_ctx)
                                        (ctx2.contract_ctx))
                    ; node_ctx = (LA.NodeNameMap.union (fun _ _ v2 -> Some v2)
                                        (ctx1.node_ctx)
                                        (ctx2.node_ctx))
                    ; node_param_attr = (LA.NodeNameMap.union (fun _ _ v2 -> Some v2)
                                          (ctx1.node_param_attr)
                                          (ctx2.node_param_attr))
                    ; vl_ctx = (IMap.union (fun _ _ v2 -> Some v2)
                                  (ctx1.vl_ctx)
                                  (ctx2.vl_ctx))
                    ; u_types = SI.union ctx1.u_types ctx2.u_types
                    ; contract_export_ctx = (LA.NodeNameMap.union (fun _ _ v2 -> Some v2)
                                              (ctx1.contract_export_ctx)
                                              (ctx2.contract_export_ctx))
                    ; enum_vars = (IMap.union (fun _ _ v2 -> Some v2)
                      (ctx1.enum_vars) (ctx2.enum_vars))
                    ; ty_vars = (LA.NodeNameMap.union (fun _ _ v2 -> Some v2)
                                   (ctx1.ty_vars)
                                   (ctx2.ty_vars))
                    ; contract_ty_vars = (LA.NodeNameMap.union (fun _ _ v2 -> Some v2)
                                   (ctx1.contract_ty_vars)
                                   (ctx2.contract_ty_vars))
                    ; ty_ty_vars = (IMap.union (fun _ _ v2 -> Some v2)
                                   (ctx1.ty_ty_vars)
                                   (ctx2.ty_ty_vars))
                     }
(** Unions the two typing contexts *)

let singleton_ty: LA.ident -> tc_type -> tc_context
  = fun i ty -> add_ty empty_tc_context i ty
(** Lifts the type binding as a typing context  *)

let singleton_const: LA.ident -> LA.expr -> tc_type -> source -> tc_context =
  fun i e ty sc -> add_const empty_tc_context i e ty sc
(** Lifts the constant binding as a typing context  *)

let extract_arg_ctx: LA.const_clocked_typed_decl -> tc_context
  = fun input -> let (i, ty) = LH.extract_ip_ty input in
                 (singleton_ty i ty) 
(** Extracts the input stream as a typing context *)

let extract_ret_ctx: LA.clocked_typed_decl -> tc_context
  = fun op -> let (i, ty) = LH.extract_op_ty op in
              singleton_ty i ty
(** Extracts the output stream as a typing context  *)

let extract_loc_ctx: LA.node_local_decl -> tc_context 
  = fun local -> 
    let (i, ty, e_opt) = LH.extract_loc_ty local in
    match e_opt with 
    | Some e ->  (add_ty (add_const empty_tc_context i e ty Local) i ty)
    | None -> singleton_ty i ty
(** Extracts a local decl as a typing constant  *)
              
let extract_consts: LA.const_clocked_typed_decl -> tc_context
  = fun (pos, i, ty, _, is_const) ->
  if is_const
  then singleton_const i (LA.Ident (pos, i)) ty Local
  else empty_tc_context 
(** Extracts constants as a typing constant  *)

let get_constant_ids: tc_context -> LA.ident list
  = fun ctx -> IMap.keys ctx.vl_ctx
(** Returns the constants declared in the typing context  *)

let lookup_contract_exports: tc_context -> LA.node_name -> ty_store option
  = fun ctx i -> LA.NodeNameMap.find_opt i (ctx.contract_export_ctx)
(** Lookup a contract exports  *)

let add_contract_exports: tc_context -> LA.node_name -> ty_store -> tc_context
  = fun ctx i exps -> {ctx with contract_export_ctx = LA.NodeNameMap.add i exps  ctx.contract_export_ctx }
(** Add the symbols that the contracts *)
               
(** {1 Pretty Printers}  *)

let pp_print_type_syn: Format.formatter -> (LA.ident * tc_type) -> unit
  = fun ppf (i, ty) -> Format.fprintf ppf "(%a:=%a)" LA.pp_print_ident i LA.pp_print_lustre_type ty
(** Pretty print type synonyms*)
                     
let pp_print_type_binding: Format.formatter -> (LA.ident * tc_type) -> unit
  = fun ppf (i, ty) -> Format.fprintf ppf "(%a:%a)" LA.pp_print_ident i LA.pp_print_lustre_type ty
(** Pretty print type bindings*)  

let pp_print_type_binding_node: Format.formatter -> (LA.node_name * tc_type) -> unit
  = fun ppf (i, ty) -> Format.fprintf ppf "(%a:%a)" LA.pp_print_node_name i LA.pp_print_lustre_type ty
(** Pretty print type bindings*)  

let pp_print_ty_var_binding: Format.formatter -> (LA.node_name * HString.t list) -> unit
  = fun ppf (i, ty_vars) ->
    Format.fprintf ppf "(%a:{%a})" 
    LA.pp_print_node_name i 
    (Lib.pp_print_list HString.pp_print_hstring ",") (ty_vars)
(** Pretty print type bindings*)  

let pp_print_ty_var_binding_ty: Format.formatter -> (LA.ident * HString.t list) -> unit
  = fun ppf (i, ty_vars) ->
    Format.fprintf ppf "(%a:{%a})" 
    LA.pp_print_ident i 
    (Lib.pp_print_list HString.pp_print_hstring ",") (ty_vars)
(** Pretty print type bindings*)  

let pp_print_ty_arg_binding: Format.formatter -> (LA.ident * LA.lustre_type list) -> unit
  = fun ppf (i, ty_vars) ->
    Format.fprintf ppf "(%a:{%a})" 
    LA.pp_print_ident i 
    (Lib.pp_print_list LA.pp_print_lustre_type ",") (ty_vars)
(** Pretty print type bindings*)  

let pp_print_val_binding: Format.formatter -> (LA.ident * (LA.expr * tc_type option * source)) -> unit
  = fun ppf (i, (v, ty, sc)) ->
  Format.fprintf ppf "(%a:%a :-> %a (%s))"
    LA.pp_print_ident i 
    (Lib.pp_print_option LA.pp_print_lustre_type) ty 
    LA.pp_print_expr v
    (if sc = Local then "local" else "global")
(** Pretty print value bindings (used for constants)*)

let pp_print_ty_syns: Format.formatter -> ty_alias_store -> unit
  = fun ppf m -> Lib.pp_print_list (pp_print_type_syn) ", " ppf (IMap.bindings m)
(** Pretty print type synonym context *)

let pp_print_tymap: Format.formatter -> ty_store -> unit
  = fun ppf m -> Lib.pp_print_list (pp_print_type_binding) ", " ppf (IMap.bindings m)
(** Pretty print type binding context *)

let pp_print_tymap_node: Format.formatter -> node_ty_store -> unit
  = fun ppf m -> Lib.pp_print_list (pp_print_type_binding_node) ", " ppf (LA.NodeNameMap.bindings m)
(** Pretty print type binding context *)
               
let pp_print_vstore: Format.formatter -> const_store -> unit
  = fun  ppf m -> Lib.pp_print_list (fun ppf (i, (e, ty, sc))
    -> pp_print_val_binding ppf (i, (e, ty, sc)))  ", " ppf (IMap.bindings m)
(** Pretty print value store *)

let pp_print_u_types: Format.formatter -> SI.t -> unit
  = fun ppf m -> Lib.pp_print_list LA.pp_print_ident ", " ppf (SI.elements m)
(** Pretty print declared user types *)

let pp_print_type_variables: Format.formatter -> ty_var_store -> unit
  = fun ppf m -> Lib.pp_print_list pp_print_ty_var_binding ", " ppf (LA.NodeNameMap.bindings m)
(** Pretty print declared user types *)

let pp_print_type_variables_ty: Format.formatter -> ty_ty_var_store -> unit
  = fun ppf m -> Lib.pp_print_list pp_print_ty_var_binding_ty ", " ppf (IMap.bindings m)
(** Pretty print declared user types *)

let pp_print_contract_exports: Format.formatter -> contract_exports -> unit
  = fun ppf m ->
  Lib.pp_print_list
    (fun ppf (i, exm) ->
      Format.fprintf ppf "(contract %a -> [%a])"
        LA.pp_print_node_name i
        pp_print_tymap exm) ", " ppf (LA.NodeNameMap.bindings m)
(** Pretty print contract exports  *)

let pp_print_enum_variants: Format.formatter -> enum_variants -> unit
  = fun ppf m ->
    Lib.pp_print_list
    (fun ppf (i, exm) ->
      Format.fprintf ppf "(enum %a -> [%a])"
        LA.pp_print_ident i
        (Lib.pp_print_list HString.pp_print_hstring ",") exm)
          ", " ppf (IMap.bindings m)
(** Pretty print enumeration types and their variants *)

let pp_print_tc_context: Format.formatter -> tc_context -> unit
  = fun ppf ctx -> 
  Format.fprintf ppf
      ("Type Synonyms={%a}\n"
       ^^ "Type Context={%a}\n"
       ^^ "Node Context={%a}\n"
       ^^ "Contract Context={%a}\n"
       ^^ "Const Store={%a}\n"
       ^^ "Declared Types={%a}\n"
       ^^ "Contract exports={%a}\n"
       ^^ "Enumeration Variants={%a}\n"
       ^^ "Type variables={%a}\n"
       ^^ "Contract type variables={%a}\n"
       ^^ "Type decl type variables={%a}\n")
      pp_print_ty_syns (ctx.ty_syns)
      pp_print_tymap (ctx.ty_ctx)
      pp_print_tymap_node (ctx.node_ctx)
      pp_print_tymap_node (ctx.contract_ctx)
      pp_print_vstore (ctx.vl_ctx)
      pp_print_u_types (ctx.u_types)
      pp_print_contract_exports (ctx.contract_export_ctx)
      pp_print_enum_variants (ctx.enum_vars)
      pp_print_type_variables (ctx.ty_vars)
      pp_print_type_variables (ctx.contract_ty_vars)
      pp_print_type_variables_ty (ctx.ty_ty_vars)
(** Pretty print the complete type checker context*)
                         
(** {1 Helper functions that uses context }  *)

let rec arity_of_expr ty_ctx = function
  | LA.GroupExpr (_, ExprList, es) ->
    List.fold_left (+) 0 (List.map (arity_of_expr ty_ctx) es)
  | TernaryOp (_, Ite, _, e, _) -> arity_of_expr ty_ctx e
  | Condact (_, _, _, id, _, _)
  | Activate (_, id, _, _, _)
  | RestartEvery (_, id, _, _) -> 
    let node_ty = lookup_node_ty ty_ctx (id, None, None) |> Lib.get in
    let (_, o) = LH.type_arity node_ty in
    o
  | Call (_, _, id, _) ->
    let node_ty = lookup_node_ty ty_ctx id |> Lib.get in
    let (_, o) = LH.type_arity node_ty in
    o
  | Pre (_, e) -> arity_of_expr ty_ctx e
  | Arrow (_, e, _) -> arity_of_expr ty_ctx e
  | RecordProject (_, e, _) -> arity_of_expr ty_ctx e
  | TupleProject (_, e, _) -> arity_of_expr ty_ctx e
  | When (_, e, _) -> arity_of_expr ty_ctx e
  | Merge (_, _, cs) -> arity_of_expr ty_ctx (List.hd cs |> snd)
  | _ -> 1

let rec traverse_group_expr_list f ctx proj es =
  match proj, es with
  | 0, e :: _ -> f 0 e
  | i, e :: es -> (
    let a = arity_of_expr ctx e in
    if a<=i then traverse_group_expr_list f ctx (i-a) es
    else f proj e
  )
  | _ -> assert false

  let rec is_type_num: tc_context -> tc_type -> (bool, HString.t) result
  = fun ctx ty -> match ty with
  | Int _
    | UInt8 _       
    | UInt16 _   
    | UInt32 _   
    | UInt64 _  
    | Int8 _   
    | Int16 _    
    | Int32 _    
    | Int64 _    
    | IntRange _
    | Real _ -> Ok true
  | RefinementType (_, (_, _, ty), _) -> is_type_num ctx ty
  | History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id) 
      | Some ty -> is_type_num ctx ty)
  | _ -> Ok false

let rec is_type_int: tc_context -> tc_type -> (bool, HString.t) result
  = fun ctx ty -> match ty with
  | Int _
  | IntRange _ -> Ok true
  | RefinementType (_, (_, _, ty), _) -> is_type_int ctx ty
  | History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id) 
      | Some ty -> is_type_int ctx ty)
  | _ -> Ok false

let rec is_type_real_or_int: tc_context -> tc_type -> (bool, HString.t) result
  = fun ctx ty -> match ty with
  | Real _
  | Int _
  | IntRange _ -> Ok true
  | RefinementType (_, (_, _, ty), _) -> is_type_real_or_int ctx ty
  | History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id) 
      | Some ty -> is_type_real_or_int ctx ty)
  | _ -> Ok false

let rec is_type_int_or_machine_int: tc_context -> tc_type -> (bool, HString.t) result
  = fun ctx ty -> match ty with
  |  Int _
     | UInt8 _       
     | UInt16 _   
     | UInt32 _   
     | UInt64 _  
     | Int8 _   
     | Int16 _    
     | Int32 _    
     | Int64 _    
     | IntRange _ -> Ok true
  | RefinementType (_, (_, _, ty), _) -> is_type_int_or_machine_int ctx ty
  | History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id) 
      | Some ty -> is_type_int_or_machine_int ctx ty)
  | _ -> Ok false

let rec is_type_unsigned_machine_int: tc_context -> tc_type -> (bool, HString.t) result
  = fun ctx ty -> match ty with
  | UInt8 _       
    | UInt16 _   
    | UInt32 _   
    | UInt64 _ -> Ok true    
  | RefinementType (_, (_, _, ty), _) -> is_type_unsigned_machine_int ctx ty
  | History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id) 
      | Some ty -> is_type_unsigned_machine_int ctx ty)
  | _ -> Ok false  

let rec is_type_signed_machine_int: tc_context -> tc_type -> (bool, HString.t) result
  = fun ctx ty -> match ty with
  | Int8 _       
    | Int16 _   
    | Int32 _   
    | Int64 _ -> Ok true 
  | RefinementType (_, (_, _, ty), _) -> is_type_signed_machine_int ctx ty 
  | History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id) 
      | Some ty -> is_type_signed_machine_int ctx ty) 
  | _ -> Ok false  
       
let is_type_machine_int: tc_context -> tc_type -> (bool, HString.t) result = fun ctx ty ->
  let* b1 = is_type_signed_machine_int ctx ty in 
  let* b2 = is_type_unsigned_machine_int ctx ty in 
  Ok (b1 || b2)

let rec is_type_array : tc_context -> tc_type -> (bool, HString.t) result 
  = fun ctx ty -> match ty with
  | ArrayType _ -> Ok true
  | RefinementType (_, (_, _, ty), _) -> is_type_array ctx ty
  | History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id) 
      | Some ty -> is_type_unsigned_machine_int ctx ty)
  | _ -> Ok false

let rec is_machine_type_of_associated_width: tc_context -> (tc_type * tc_type) -> (bool, HString.t) result
= fun ctx tys -> match tys with
  | Int8 _, UInt8 _       
    | Int16 _,UInt16 _   
    | Int32 _, UInt32 _   
    | Int64 _, UInt64 _
    | UInt8 _, UInt8 _       
    | UInt16 _,UInt16 _   
    | UInt32 _, UInt32 _   
    | UInt64 _, UInt64 _ -> Ok true
  | RefinementType (_, (_, _, ty1), _), ty2 -> is_machine_type_of_associated_width ctx (ty1, ty2)
  | ty1, RefinementType (_, (_, _, ty2), _) -> is_machine_type_of_associated_width ctx (ty1, ty2)
  | ty1, History (_, id) -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id)
      | Some ty -> is_machine_type_of_associated_width ctx (ty1, ty))
  | History (_, id), ty2 -> 
    let ty = lookup_ty ctx id in 
    (match ty with 
      | None -> Error (id)
      | Some ty -> is_machine_type_of_associated_width ctx (ty, ty2))
  | _ -> Ok false

let rec type_contains_subrange ctx = function
  | LA.IntRange _ -> true
  | RefinementType (_, (_, _, ty), _) -> type_contains_subrange ctx ty
  | TupleType (_, tys) | GroupType (_, tys) ->
    List.fold_left (fun acc ty -> acc || type_contains_subrange ctx ty) false tys
  | RecordType (_, _, tys) ->
    List.fold_left (fun acc (_, _, ty) -> acc || type_contains_subrange ctx ty)
      false tys
  | ArrayType (_, (ty, _)) -> type_contains_subrange ctx ty
  | TArr (_, ty1, ty2) -> type_contains_subrange ctx ty1 || type_contains_subrange ctx ty2
  | History (_, id) -> 
    (match lookup_ty ctx id with 
    | Some ty -> type_contains_subrange ctx ty
    | _ -> assert false)
  | UserType (_, ty_args, id) -> (
    match lookup_ty_syn ctx id ty_args with
    | Some ty -> type_contains_subrange ctx ty
    | None -> assert false
  )
  | Bool _ | Int _ | Real _ | EnumType _
  | UInt8 _| UInt16 _| UInt32 _| UInt64 _
  | Int8 _ |Int16 _ |Int32 _ | Int64 _
  | AbstractType _ -> false

let rec type_contains_enum_or_subrange ctx = function
  | LA.IntRange _
  | EnumType _ -> true
  | RefinementType (_, (_, _, ty), _) -> type_contains_enum_or_subrange ctx ty
  | TupleType (_, tys) | GroupType (_, tys) ->
    List.fold_left (fun acc ty -> acc || type_contains_enum_or_subrange ctx ty) false tys
  | RecordType (_, _, tys) ->
    List.fold_left (fun acc (_, _, ty) -> acc || type_contains_enum_or_subrange ctx ty)
      false tys
  | ArrayType (_, (ty, _)) -> type_contains_enum_or_subrange ctx ty
  | TArr (_, ty1, ty2) -> type_contains_enum_or_subrange ctx ty1 || type_contains_enum_or_subrange ctx ty2
  | History (_, id) ->
    (match lookup_ty ctx id with
    | Some ty -> type_contains_enum_or_subrange ctx ty
    | _ -> assert false)
  | UserType (_, ty_args, id) -> (
    match lookup_ty_syn ctx id ty_args with
    | Some ty -> type_contains_enum_or_subrange ctx ty
    | None -> assert false
  )
  | Bool _ | Int _ | Real _
  | UInt8 _| UInt16 _| UInt32 _| UInt64 _
  | Int8 _ |Int16 _ |Int32 _ | Int64 _
  | AbstractType _ -> false

  let rec type_contains_ref ctx = function
  | LA.RefinementType _ -> true
  | TupleType (_, tys) | GroupType (_, tys) ->
    List.fold_left (fun acc ty -> acc || type_contains_ref ctx ty) false tys
  | RecordType (_, _, tys) ->
    List.fold_left (fun acc (_, _, ty) -> acc || type_contains_ref ctx ty)
      false tys
  | ArrayType (_, (ty, _)) -> type_contains_ref ctx ty
  | TArr(_, ty1, ty2) -> type_contains_ref ctx ty1 || type_contains_ref ctx ty2 
  | History (_, id) -> 
    (match lookup_ty ctx id with 
      | Some ty -> type_contains_ref ctx ty
      | _ -> assert false)
  | UserType (_, ty_args, id) -> (
    match lookup_ty_syn ctx id ty_args with
    | Some ty -> type_contains_ref ctx ty
    | None -> false
  )
  | Bool _ | Int _ | Real _  | EnumType _ | IntRange _
  | UInt8 _| UInt16 _| UInt32 _| UInt64 _
  | Int8 _ |Int16 _ |Int32 _ | Int64 _
  | AbstractType _ -> false

let type_contains_ref_or_subrange ctx ty =
  type_contains_ref ctx ty || type_contains_subrange ctx ty

let rec type_contains_enum_subrange_reftype ctx = function
  | LA.IntRange _
  | EnumType _ 
  | RefinementType _ -> true
  | TupleType (_, tys) | GroupType (_, tys) ->
    List.fold_left (fun acc ty -> acc || type_contains_enum_subrange_reftype ctx ty) false tys
  | RecordType (_, _, tys) ->
    List.fold_left (fun acc (_, _, ty) -> acc || type_contains_enum_subrange_reftype ctx ty)
      false tys
  | ArrayType (_, (ty, _)) -> type_contains_enum_subrange_reftype ctx ty
  | TArr (_, ty1, ty2) -> type_contains_enum_subrange_reftype ctx ty1 || type_contains_enum_subrange_reftype ctx ty2
  | History (_, id) -> 
    (match lookup_ty ctx id with 
      | Some ty -> type_contains_enum_subrange_reftype ctx ty
      | _ -> assert false)
  | UserType (_, ty_args, id) -> (
    match lookup_ty_syn ctx id ty_args with
    | Some ty -> type_contains_enum_subrange_reftype ctx ty
    | None -> assert false
  )
  | Bool _ | Int _ | Real _
  | UInt8 _| UInt16 _| UInt32 _| UInt64 _
  | Int8 _ |Int16 _ |Int32 _ | Int64 _
  | AbstractType _ -> false

let rec type_contains_abstract ctx = function
  | LA.UserType (_, ty_args, id) -> 
    (match lookup_ty_syn ctx id ty_args with 
    | Some (AbstractType _) 
    | None -> true 
    | Some ty -> type_contains_abstract ctx ty)
  | RefinementType (_, (_, _, ty), _) -> type_contains_abstract ctx ty
  | TupleType (_, tys) | GroupType (_, tys) ->
    List.fold_left (fun acc ty -> acc || type_contains_abstract ctx ty) false tys
  | RecordType (_, _, tys) ->
    List.fold_left (fun acc (_, _, ty) -> acc || type_contains_abstract ctx ty)
      false tys
  | ArrayType (_, (ty, _)) -> type_contains_abstract ctx ty
  | TArr (_, ty1, ty2) -> type_contains_abstract ctx ty1 || type_contains_abstract ctx ty2
  | History (_, id) -> 
    (match lookup_ty ctx id with 
    | Some ty -> type_contains_abstract ctx ty
    | _ -> assert false)
  | Bool _ | Int _ | Real _ | EnumType _ | IntRange _
  | UInt8 _| UInt16 _| UInt32 _| UInt64 _
  | Int8 _ |Int16 _ |Int32 _ | Int64 _
  | AbstractType _ -> false

let rec type_contains_array ctx = function
  | LA.ArrayType (_, (_, _)) -> true
  | RefinementType (_, (_, _, ty), _) -> type_contains_array ctx ty
  | TupleType (_, tys) | GroupType (_, tys) ->
    List.fold_left (fun acc ty -> acc || type_contains_array ctx ty) false tys
  | RecordType (_, _, tys) ->
    List.fold_left (fun acc (_, _, ty) -> acc || type_contains_array ctx ty)
      false tys
  | TArr (_, ty1, ty2) -> type_contains_array ctx ty1 || type_contains_array ctx ty2
  | History (_, id) ->
    (match lookup_ty ctx id with
    | Some ty -> type_contains_array ctx ty
    | _ -> assert false)
  | UserType (_, ty_args, id) -> (
    match lookup_ty_syn ctx id ty_args with
    | Some ty -> type_contains_array ctx ty
    | None -> assert false
  )
  | Bool _ | Int _ | Real _ | EnumType _ | IntRange _
  | UInt8 _| UInt16 _| UInt32 _| UInt64 _
  | Int8 _ |Int16 _ |Int32 _ | Int64 _
  | AbstractType _ -> false

let rec ty_vars_of_expr ctx node_name expr = 
  let call = ty_vars_of_expr ctx node_name in match expr with 
  (* Node calls *)
  | LA.Call (_, tys, _, es) -> 
    SI.union (SI.flatten (List.map (ty_vars_of_type ctx node_name) tys))
              (SI.flatten (List.map call es))
  | AnyOp (_, (_, _, ty), e, None) -> 
    SI.union (call e) (ty_vars_of_type ctx node_name ty)
  (* Quantified expressions *)
  | Quantifier (_, _, qs, e) -> 
    SI.diff (call e) (SI.flatten (List.map (fun (_, _, ty) -> ty_vars_of_type ctx node_name ty) qs)) 
  | Ident (_, id) -> (
    match lookup_ty ctx id with
    | None -> SI.empty (* e.g. any bound variable *)
    | Some ty -> ty_vars_of_type ctx node_name ty
  )
  | ModeRef _ -> SI.empty
  | RecordProject (_, e, _) -> call e 
  | TupleProject (_, e, _) -> call e
  (* Values *)
  | Const _ -> SI.empty
  (* Operators *)
  | UnaryOp (_,_,e) -> call e
  | BinaryOp (_,_,e1, e2) -> call e1 |> SI.union (call e2)
  | TernaryOp (_,_, e1, e2, e3) -> call e1 |> SI.union (call e2) |> SI.union (call e3) 
  | ConvOp  (_,_,e) -> call e
  | CompOp (_,_,e1, e2) -> (call e1) |> SI.union (call e2)
  (* Structured expressions *)
  | RecordExpr (_, _, _, flds) -> SI.flatten (List.map call (snd (List.split flds)))
  | GroupExpr (_, _, es) -> SI.flatten (List.map call es)
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) -> SI.union (call e1) (call e2)
  | ArrayConstr (_, e1, e2) -> SI.union (call e1) (call e2)
  | ArrayIndex (_, e1, e2) -> SI.union (call e1) (call e2)
  (* Clock operators *)
  | When (_, e, _) -> call e
  | Condact (_, e1, e2, _, es1, es2) ->
    SI.flatten (call e1 :: call e2:: (List.map call es1) @ (List.map call es2))
  | Activate (_, _, e1, e2, es) -> SI.flatten (call e1 :: call e2 :: List.map call es)
  | Merge (_, _, es) -> List.split es |> snd |> List.map call |> SI.flatten
  | RestartEvery (_, _, es, e) -> SI.flatten (call e :: List.map call es)
  | AnyOp (_, (_, i, _), e1, Some e2) -> SI.diff (SI.union (call e1) (call e2)) (SI.singleton i)
  (* Temporal operators *)
  | Pre (_, e) -> call e
  | Arrow (_, e1, e2) ->  SI.union (call e1) (call e2)

and ty_vars_of_type ctx node_name ty = 
  let call = ty_vars_of_type ctx node_name in 
  match ty with
  | UserType (_, ty_args, id) -> (
    match lookup_ty_syn ctx id ty_args with
    | Some ty -> ty_vars_of_type ctx node_name ty
    | None -> SI.empty
  )
  | RefinementType (_, (_, _, ty), e) 
  | ArrayType (_, (ty, e)) -> 
    SI.union (call ty) (ty_vars_of_expr ctx node_name e)
  | TupleType (_, tys) | GroupType (_, tys) -> 
    List.fold_left SI.union SI.empty (List.map call tys)
  | RecordType (_, _, tis) -> 
    let vars = List.map (fun (_, _, ty) -> call ty) tis in 
    List.fold_left SI.union SI.empty vars
  | TArr (_, ty1, ty2) -> SI.union (call ty1) (call ty2)
  | AbstractType (_, id) -> (
    match lookup_node_ty_vars ctx node_name,
          lookup_contract_ty_vars ctx node_name with
    | None, None -> SI.empty
    | Some tvars, _
    | _, Some tvars ->
      if List.mem id tvars then SI.singleton id
      else SI.empty
  )
  | History _ | Int _ | Int8 _ | Int16 _ | Int32 _ | Int64 _ | UInt8 _ | UInt16 _ | UInt32 _ | UInt64 _ 
  | Bool _ | IntRange _ | Real _  | EnumType _ -> SI.empty
