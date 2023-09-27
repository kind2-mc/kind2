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

type const_store = (LA.expr * tc_type option) IMap.t 
(** A Store of constant identifier and their (const) values with types. 
 *  The values of the associated identifiers should be evaluated to a 
 *  Bool or an Int at constant propogation phase of type checking *)

type ty_set = SI.t
(** set of valid user type identifiers *)

type contract_exports = (ty_store) IMap.t
(** Mapping for all the exports of the contract, modes and contract ghost const and vars *)

type param_store = (HString.t * bool) list IMap.t
(** A store of parameter names and flags indicating if the argument is constant *)

type tc_context = { ty_syns: ty_alias_store       (* store of the type alias mappings *)
                  ; ty_ctx: ty_store              (* store of the types of identifiers and nodes *)
                  ; contract_ctx: ty_store        (* store of the types of contracts *)
                  ; node_ctx: ty_store            (* store of the types of nodes *)
                  ; node_param_attr: param_store  (* store of the parameter attributes of nodes *)
                  ; vl_ctx: const_store           (* store of typed constants to its value *)
                  ; u_types: ty_set               (* store of all declared user types,
                                                     this is poor mans kind (type of type) context *)
                  ; contract_export_ctx:          (* stores all the export variables  of the contract *)
                      contract_exports 
                  ; enum_vars:enum_variants
                  }
(** The type checker global context *)

let empty_tc_context: tc_context =
  { ty_syns = IMap.empty
  ; ty_ctx = IMap.empty
  ; contract_ctx = IMap.empty
  ; node_ctx = IMap.empty
  ; node_param_attr = IMap.empty
  ; vl_ctx = IMap.empty
  ; u_types = SI.empty
  ; contract_export_ctx = IMap.empty
  ; enum_vars = IMap.empty
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
               
let member_contract: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.contract_ctx)
(** Checks if the contract name is in the context *)

let member_node: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.node_ctx)
(** Checks if the node name is in the context *)

let member_u_types : tc_context -> LA.ident -> bool
  = fun ctx i -> SI.mem i ctx.u_types
(** Checks of the type identifier is a user defined type *)

let member_val: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.vl_ctx)
(** Checks if the identifier is a constant  *)

let rec lookup_ty_syn: tc_context -> LA.ident -> tc_type option 
  = fun ctx i ->
  match (IMap.find_opt i (ctx.ty_syns)) with
  | Some ty -> (match ty with
               | LA.UserType (_, uid) ->
                  if uid = i 
                  then Some ty
                  else lookup_ty_syn ctx uid
               | _ -> Some ty )
  | None -> None
(** Picks out the type synonym from the context
    If it is user type then chases it (recursively looks up) 
    the actual type. This chasing is necessary to check type equality 
    between user defined types. *)

let expand_type_syn: tc_context -> tc_type -> tc_type
  = fun ctx ->
  function
  | UserType (_, i) as ty->
     (match lookup_ty_syn ctx i with
      | None -> ty
      | Some ty' -> ty')
  | ty -> ty 
(** Chases the type to its base form to resolve type synonyms *)

let rec expand_nested_type_syn: tc_context -> tc_type -> tc_type
  = fun ctx -> function
  | UserType _ as ty -> 
    expand_nested_type_syn ctx (expand_type_syn ctx ty)
  | TupleType (p, tys) ->
    let tys = List.map (expand_nested_type_syn ctx) tys in
    TupleType (p, tys)
  | GroupType (p, tys) ->
    let tys = List.map (expand_nested_type_syn ctx) tys in
    GroupType (p, tys)
  | RecordType (p, name, tys) ->
    let tys = List.map (fun (p, i, t) -> p, i, expand_nested_type_syn ctx t) tys in
    RecordType (p, name, tys)
  | ArrayType (p, (ty, e)) ->
    let ty = expand_nested_type_syn ctx ty in
    ArrayType (p, (ty, e))
  | ty -> ty
(** Chases the type (and nested types) to its base form to resolve type synonyms *)

let lookup_ty: tc_context -> LA.ident -> tc_type option
  = fun ctx i ->
  match (IMap.find_opt i (ctx.ty_ctx)) with
  | Some ty -> Some (expand_type_syn ctx ty) 
  | None -> None
(** Picks out the type of the identifier to type context map *)

let lookup_contract_ty: tc_context -> LA.ident -> tc_type option
  = fun ctx i -> IMap.find_opt i (ctx.contract_ctx)
(** Lookup a contract type  *)
               
let lookup_node_ty: tc_context -> LA.ident -> tc_type option
  = fun ctx i -> IMap.find_opt i (ctx.node_ctx)
(** Lookup a node type  *)

let lookup_node_param_attr: tc_context -> LA.ident -> (HString.t * bool) list option
  = fun ctx i -> IMap.find_opt i (ctx.node_param_attr)

let lookup_const: tc_context -> LA.ident -> (LA.expr * tc_type option) option
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
                  
let add_ty_contract: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with contract_ctx = IMap.add i ty (ctx.contract_ctx)}
(**  Add the type of the contract *)

let add_ty_node: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with node_ctx = IMap.add i ty (ctx.node_ctx)}
(**  Add the type of the node *)

let add_node_param_attr : tc_context -> LA.ident -> LA.const_clocked_typed_decl list -> tc_context
  = fun ctx i args ->
  let v =
    List.map (function (_, id, _, _, is_const) -> (id, is_const)) args
  in
  {ctx with node_param_attr = IMap.add i v (ctx.node_param_attr)}

let add_ty_decl: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with u_types = SI.add i (ctx.u_types)}
(** Add a user declared type in the typing context *)

let add_enum_variants: tc_context -> LA.ident -> LA.ident list -> tc_context
  = fun ctx i vs -> {ctx with enum_vars = IMap.add i vs (ctx.enum_vars) }
(** Add an enumeration type and associated variants to the typing context *)

let remove_ty: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with ty_ctx= IMap.remove i (ctx.ty_ctx)}
(** Removes a type binding  *)

let add_const: tc_context -> LA.ident -> LA.expr -> tc_type -> tc_context
  = fun ctx i e ty -> {ctx with vl_ctx = IMap.add i (e, (Some ty)) ctx.vl_ctx} 
(** Adds a constant variable along with its expression and type  *)

let add_untyped_const : tc_context -> LA.ident -> LA.expr -> tc_context
= fun ctx i e -> {ctx with vl_ctx = IMap.add i (e, None) ctx.vl_ctx} 

let union: tc_context -> tc_context -> tc_context
  = fun ctx1 ctx2 -> { ty_syns = (IMap.union (fun _ _ v2 -> Some v2)
                                  (ctx1.ty_syns)
                                  (ctx2.ty_syns))
                    ; ty_ctx = (IMap.union (fun _ _ v2 -> Some v2)
                                  (ctx1.ty_ctx)
                                  (ctx2.ty_ctx))
                    ; contract_ctx = (IMap.union (fun _ _ v2 -> Some v2)
                                        (ctx1.contract_ctx)
                                        (ctx2.contract_ctx))
                    ; node_ctx = (IMap.union (fun _ _ v2 -> Some v2)
                                        (ctx1.node_ctx)
                                        (ctx2.node_ctx))
                    ; node_param_attr = (IMap.union (fun _ _ v2 -> Some v2)
                                          (ctx1.node_param_attr)
                                          (ctx2.node_param_attr))
                    ; vl_ctx = (IMap.union (fun _ _ v2 -> Some v2)
                                  (ctx1.vl_ctx)
                                  (ctx2.vl_ctx))
                    ; u_types = SI.union ctx1.u_types ctx2.u_types
                    ; contract_export_ctx = (IMap.union (fun _ _ v2 -> Some v2)
                                              (ctx1.contract_export_ctx)
                                              (ctx2.contract_export_ctx))
                    ; enum_vars = (IMap.union (fun _ _ v2 -> Some v2)
                      (ctx1.enum_vars) (ctx2.enum_vars))
                     }
(** Unions the two typing contexts *)

let singleton_ty: LA.ident -> tc_type -> tc_context
  = fun i ty -> add_ty empty_tc_context i ty
(** Lifts the type binding as a typing context  *)

let singleton_const: LA.ident -> LA.expr -> tc_type -> tc_context =
  fun i e ty -> add_const empty_tc_context i e ty
(** Lifts the constant binding as a typing context  *)

let extract_arg_ctx: LA.const_clocked_typed_decl -> tc_context
  = fun input -> let (i, ty) = LH.extract_ip_ty input in
                 (singleton_ty i ty) 
(** Extracts the input stream as a typing context *)

let extract_ret_ctx: LA.clocked_typed_decl -> tc_context
  = fun op -> let (i, ty) = LH.extract_op_ty op in
              singleton_ty i ty
(** Extracts the output stream as a typing context  *)
              
let extract_consts: LA.const_clocked_typed_decl -> tc_context
  = fun (pos, i, ty, _, is_const) ->
  if is_const
  then singleton_const i (LA.Ident (pos, i)) ty
  else empty_tc_context 
(** Extracts constants as a typing constant  *)

let get_constant_ids: tc_context -> LA.ident list
  = fun ctx -> IMap.keys ctx.vl_ctx
(** Returns the constants declared in the typing context  *)

let lookup_contract_exports: tc_context -> LA.ident -> ty_store option
  = fun ctx i -> IMap.find_opt i (ctx.contract_export_ctx)
(** Lookup a contract exports  *)

let add_contract_exports: tc_context -> LA.ident -> ty_store -> tc_context
  = fun ctx i exps -> {ctx with contract_export_ctx = IMap.add i exps  ctx.contract_export_ctx }
(** Add the symbols that the contracts *)
               
(** {1 Pretty Printers}  *)

let pp_print_type_syn: Format.formatter -> (LA.ident * tc_type) -> unit
  = fun ppf (i, ty) -> Format.fprintf ppf "(%a:=%a)" LA.pp_print_ident i LA.pp_print_lustre_type ty
(** Pretty print type synonyms*)
                     
let pp_print_type_binding: Format.formatter -> (LA.ident * tc_type) -> unit
  = fun ppf (i, ty) -> Format.fprintf ppf "(%a:%a)" LA.pp_print_ident i LA.pp_print_lustre_type ty
(** Pretty print type bindings*)  

let pp_print_val_binding: Format.formatter -> (LA.ident * (LA.expr * tc_type option)) -> unit
  = fun ppf (i, (v, ty)) ->
  Format.fprintf ppf "(%a:%a :-> %a)"
    LA.pp_print_ident i (Lib.pp_print_option LA.pp_print_lustre_type) ty LA.pp_print_expr v
(** Pretty print value bindings (used for constants)*)

let pp_print_ty_syns: Format.formatter -> ty_alias_store -> unit
  = fun ppf m -> Lib.pp_print_list (pp_print_type_syn) ", " ppf (IMap.bindings m)
(** Pretty print type synonym context *)

let pp_print_tymap: Format.formatter -> ty_store -> unit
  = fun ppf m -> Lib.pp_print_list (pp_print_type_binding) ", " ppf (IMap.bindings m)
(** Pretty print type binding context *)
               
let pp_print_vstore: Format.formatter -> const_store -> unit
  = fun  ppf m -> Lib.pp_print_list (fun ppf (i, (e, ty))
    -> pp_print_val_binding ppf (i, (e, ty)))  ", " ppf (IMap.bindings m)
(** Pretty print value store *)

let pp_print_u_types: Format.formatter -> SI.t -> unit
  = fun ppf m -> Lib.pp_print_list LA.pp_print_ident ", " ppf (SI.elements m)
(** Pretty print declared user types *)

let pp_print_contract_exports: Format.formatter -> contract_exports -> unit
  = fun ppf m ->
  Lib.pp_print_list
    (fun ppf (i, exm) ->
      Format.fprintf ppf "(contract %a -> [%a])"
        LA.pp_print_ident i
        pp_print_tymap exm) ", " ppf (IMap.bindings m)
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
       ^^ "Enumeration Variants={%a}\n")
      pp_print_ty_syns (ctx.ty_syns)
      pp_print_tymap (ctx.ty_ctx)
      pp_print_tymap (ctx.node_ctx)
      pp_print_tymap (ctx.contract_ctx)
      pp_print_vstore (ctx.vl_ctx)
      pp_print_u_types (ctx.u_types)
      pp_print_contract_exports (ctx.contract_export_ctx)
      pp_print_enum_variants (ctx.enum_vars)
(** Pretty print the complete type checker context*)
                         
(** {1 Helper functions that uses context }  *)

let rec arity_of_expr ty_ctx = function
  | LA.GroupExpr (_, ExprList, es) ->
    List.fold_left (+) 0 (List.map (arity_of_expr ty_ctx) es)
  | TernaryOp (_, Ite, _, e, _) -> arity_of_expr ty_ctx e
  | Condact (_, _, _, id, _, _)
  | Activate (_, id, _, _, _)
  | RestartEvery (_, id, _, _)
  | Call (_, id, _) ->
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
