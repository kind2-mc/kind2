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
              let compare i1 i2 = Stdlib.compare i1 i2
            end)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end
(** Map for types with identifiers as keys *)


type ty_alias_store = tc_type IMap.t
(** A store of type Aliases, i.e. for user defined types  *)

type ty_store = tc_type IMap.t
(** A store of identifier and their types*)

type const_store = (LA.expr * tc_type) IMap.t 
(** A Store of constant identifier and their (const) values with types. 
 *  The values of the associated identifiers should be evaluated to a 
 *  Bool or an Int at constant propogation phase of type checking *)

type ty_set = SI.t
(** set of valid user type identifiers *)

type contract_exports = (ty_store) IMap.t
(** Mapping for all the exports of the contract, modes and contract ghost const and vars *)

type tc_context = { ty_syns: ty_alias_store (* store of the type alias mappings *)
                  ; ty_ctx: ty_store        (* store of the types of identifiers and nodes *)
                  ; contract_ctx: ty_store  (* store of the types of contracts *)
                  ; vl_ctx: const_store     (* store of typed constants to its value *)
                  ; u_types: ty_set         (* store of all declared user types,
                                               this is poor mans kind (type of type) context *)
                  ; contract_export_ctx:    (* stores all the export variables  of the contract *)
                      contract_exports 
                  }
(** The type checker global context *)

let empty_tc_context: tc_context =
  { ty_syns = IMap.empty
  ; ty_ctx = IMap.empty
  ; contract_ctx = IMap.empty
  ; vl_ctx = IMap.empty
  ; u_types = SI.empty
  ; contract_export_ctx = IMap.empty
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
(** Checks if the contract name is previously seen   *)

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
                  if (Stdlib.compare uid i = 0)
                  then Some ty
                  else lookup_ty_syn ctx uid
               | _ -> Some ty )
  | None -> None
(** Picks out the type synonym from the context
    If it is user type then chases it (recursively looks up) 
    the actual type. This chasing is necessary to check type equality 
    between user defined types. *)

let lookup_ty: tc_context -> LA.ident -> tc_type option
  = fun ctx i ->
  match (IMap.find_opt i (ctx.ty_ctx)) with
  | Some ty -> (match ty with
                | LA.UserType (_, uid) ->
                   lookup_ty_syn ctx uid
                | _ -> Some ty) 
  | None -> None
(** Picks out the type of the identifier to type context map *)

let lookup_contract_ty: tc_context -> LA.ident -> tc_type option
  = fun ctx i -> IMap.find_opt i (ctx.contract_ctx)
(** Lookup a contract type  *)

let lookup_const: tc_context -> LA.ident -> (LA.expr * tc_type) option
  = fun ctx i -> IMap.find_opt i (ctx.vl_ctx)
(** Lookup a constant identifier *)

let add_ty_syn: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with ty_syns = IMap.add i ty (ctx.ty_syns)}
(** add a type synonym in the typing context *)

let add_ty: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with ty_ctx = IMap.add i ty (ctx.ty_ctx)}
(** Add type binding into the typing context *)
                  
let add_ty_contract: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with contract_ctx = IMap.add i ty (ctx.contract_ctx)}
(**  Add the type of the contract *)

let add_ty_decl: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with u_types = SI.add i (ctx.u_types)}
(** Add a user declared type in the typing context *)

let remove_ty: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with ty_ctx= IMap.remove i (ctx.ty_ctx)}
(** Removes a type binding  *)

let add_const: tc_context -> LA.ident -> LA.expr -> tc_type -> tc_context
  = fun ctx i e ty -> {ctx with vl_ctx = IMap.add i (e, ty) ctx.vl_ctx} 
(** Adds a constant variable along with its expression and type  *)

let union: tc_context -> tc_context -> tc_context
  = fun ctx1 ctx2 -> { ty_syns = (IMap.union (fun k v1 v2 -> Some v2)
                                    (ctx1.ty_syns)
                                    (ctx2.ty_syns))
                     ; ty_ctx = (IMap.union (fun k v1 v2 -> Some v2)
                                   (ctx1.ty_ctx)
                                   (ctx2.ty_ctx))
                     ; contract_ctx = (IMap.union (fun k v1 v2 -> Some v2)
                                         (ctx1.contract_ctx)
                                         (ctx2.contract_ctx))
                     ; vl_ctx = (IMap.union (fun k v1 v2 -> Some v2)
                                   (ctx1.vl_ctx)
                                   (ctx2.vl_ctx))
                     ; u_types = SI.union ctx1.u_types ctx2.u_types
                     ; contract_export_ctx = (IMap.union (fun k v1 v2 -> Some v2)
                                                (ctx1.contract_export_ctx)
                                                (ctx2.contract_export_ctx))
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


(** {1 Pretty Printers}  *)

let pp_print_type_syn: Format.formatter -> (LA.ident * tc_type) -> unit
  = fun ppf (i, ty) -> Format.fprintf ppf "(%a:=%a)" LA.pp_print_ident i LA.pp_print_lustre_type ty
(** Pretty print type synonyms*)
                     
let pp_print_type_binding: Format.formatter -> (LA.ident * tc_type) -> unit
  = fun ppf (i, ty) -> Format.fprintf ppf "(%a:%a)" LA.pp_print_ident i LA.pp_print_lustre_type ty
(** Pretty print type bindings*)  

let pp_print_val_binding: Format.formatter -> (LA.ident * (LA.expr * tc_type)) -> unit
  = fun ppf (i, (v, ty)) ->
  Format.fprintf ppf "(%a:%a :-> %a)" LA.pp_print_ident i LA.pp_print_lustre_type ty LA.pp_print_expr v
(** Pretty print value bindings (used for constants)*)

let pp_print_ty_syns: Format.formatter -> ty_alias_store -> unit
  = fun ppf m -> Lib.pp_print_list (pp_print_type_syn) ", " ppf (IMap.bindings m)
(** Pretty print type synonym context *)

let pp_print_tymap: Format.formatter -> ty_store -> unit
  = fun ppf m -> Lib.pp_print_list (pp_print_type_binding) ", " ppf (IMap.bindings m)
(** Pretty print type binding context *)
               
let pp_print_vstore: Format.formatter -> const_store -> unit
  = fun  ppf m -> Lib.pp_print_list (fun ppf (i, (e, ty)) -> pp_print_val_binding ppf (i, (e, ty)))  ", " ppf (IMap.bindings m)
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
(** Pretty pring contract exports  *)

let pp_print_tc_context ppf ctx
  = Format.fprintf ppf
      ("Type Synonyms={%a}\n"
       ^^ "Type Context={%a}\n"
       ^^ "Contract Context={%a}\n"
       ^^ "Const Store={%a}\n"
       ^^ "Declared Types={%a}\n"
       ^^ "Contract exports={%a}\n")
      pp_print_ty_syns (ctx.ty_syns)
      pp_print_tymap (ctx.ty_ctx)
      pp_print_tymap (ctx.contract_ctx)
      pp_print_vstore (ctx.vl_ctx)
      pp_print_u_types (ctx.u_types)
      pp_print_contract_exports (ctx.contract_export_ctx)
(** Pretty print the complete type checker context*)
                                    
