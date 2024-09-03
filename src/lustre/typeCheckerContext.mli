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
(** The type checker context used for typechecking the surface level language
  
     @author Apoorv Ingle *)

module LA = LustreAst
module SI = LA.SI
          
type tc_type  = LA.lustre_type
(** Type alias for lustre type from LustreAst  *)

type source = 
| Input
| Output
| Local
| Global
| Ghost

module IMap : sig
  (* everything that [Stdlib.Map] gives us  *)
  include (Map.S with type key = LA.ident)
  val keys: 'a t -> key list
end
(** Map for types with identifiers as keys *)

type enum_variants = LA.ident list IMap.t
(** A store of the variants for defined enumeration types *)

type ty_alias_store = tc_type IMap.t
(** A store of type Aliases, i.e. for user defined types  *)

type ty_store = tc_type IMap.t
(** A store of identifier and their types*)

type const_store = (LA.expr * tc_type option * source) IMap.t 
(** A Store of constant identifier and their (const) values with types. 
 *  The values of the associated identifiers should be evaluated to a 
 *  Bool or an Int at constant propogation phase of type checking *)

type ty_set = SI.t
(** set of valid user type identifiers *)

type contract_exports = (ty_store) IMap.t
(** Mapping for all the exports of the contract, modes and contract ghost const and vars *)

type param_store = (HString.t * bool) list IMap.t
(** A store of parameter names and flags indicating if the argument is constant *)

type tc_context

val empty_tc_context: tc_context
(** An empty typing context *)

(**********************************************
 * Helper functions for type checker context *
 **********************************************)
                  
val member_ty_syn: tc_context -> LA.ident -> bool
(** Checks if the type is a type synonym  *)
  
val member_ty: tc_context -> LA.ident -> bool
(** Checks if the identifier is a typed identifier *)

val member_contract: tc_context -> LA.ident -> bool
(** Checks if the contract name is in the context *)

val member_node: tc_context -> LA.ident -> bool
(** Checks if the node name is in the context *)
  
val member_u_types : tc_context -> LA.ident -> bool
(** Checks of the type identifier is a user defined type *)
  
val member_val: tc_context -> LA.ident -> bool
(** Checks if the identifier is a constant  *)

val lookup_ty_syn: tc_context -> LA.ident -> tc_type list -> tc_type option 
(** Picks out the type synonym from the context
    If it is user type then chases it (recursively looks up) 
    the actual type. This chasing is necessary to check type equality 
    between user defined types. *)
    
val expand_type_syn: tc_context -> tc_type -> tc_type
(** Chases the type (and nested types) to its base form to resolve type synonyms *)

val lookup_ty: tc_context -> LA.ident -> tc_type option
(** Picks out the type of the identifier to type context map *)

val lookup_contract_ty: tc_context -> LA.ident -> tc_type option
(** Lookup a contract type  *)
                          
val lookup_node_ty: tc_context -> LA.ident -> tc_type option
(** Lookup a node type *)

val lookup_node_ty_vars: tc_context -> HString.t -> HString.t list option
(** Lookup a node's type variables *)

val lookup_node_ty_args: tc_context -> HString.t -> LA.lustre_type list option
(** Lookup a node's type arguments *)

val lookup_contract_ty_vars: tc_context -> HString.t -> HString.t list option
(** Lookup a contract's type variables *)

val lookup_ty_ty_vars: tc_context -> HString.t -> HString.t list option
(** Lookup a user type's type variables *)

val lookup_node_param_attr: tc_context -> LA.ident -> (HString.t * bool) list option
(** Track whether node parameters are constant or not *)

val lookup_node_param_ids: tc_context -> LA.ident -> HString.t list option

val lookup_const: tc_context -> LA.ident -> (LA.expr * tc_type option * source) option
(** Lookup a constant identifier *)

val lookup_variants: tc_context -> LA.ident -> LA.ident list option
(** Lookup the variants for an enumeration type name *)

val add_ty_syn: tc_context -> LA.ident -> tc_type -> tc_context
(** Add a type synonym in the typing context *)

val add_ty: tc_context -> LA.ident -> tc_type -> tc_context
(** Add type binding into the typing context *)

val add_ty_node: tc_context -> LA.ident -> tc_type -> tc_context
(** Add node/function type binding into the typing context *)

val add_ty_vars_node: tc_context -> HString.t -> HString.t list -> tc_context 
(** Add node/function type variables into the typing context *)

val add_ty_vars_ty: tc_context -> HString.t -> HString.t list -> tc_context 
(** Add type declaration type variables into the typing context *)

val add_ty_args_node: tc_context -> HString.t -> LA.lustre_type list -> tc_context 
(** Add node/function type arguments into the typing context *)

val add_ty_vars_contract: tc_context -> HString.t -> HString.t list -> tc_context 
(** Add contract type variables into the typing context *)

val add_node_param_attr: tc_context -> LA.ident -> LA.const_clocked_typed_decl list -> tc_context
(** Track whether node parameters are constant or not *)

val add_ty_contract: tc_context -> LA.ident -> tc_type -> tc_context
(** Add the type of the contract *)
                  
val add_ty_decl: tc_context -> LA.ident -> tc_context
(** Add a user declared type in the typing context *)

val add_enum_variants: tc_context -> LA.ident -> LA.ident list -> tc_context
(** Add an enumeration type and associated variants to the typing context *)

val is_enum_variant: tc_context -> LA.ident -> bool

val remove_ty: tc_context -> LA.ident -> tc_context
(** Removes a type binding  *)

val remove_ty_ctx: tc_context -> tc_context
                  
val add_const: tc_context -> LA.ident -> LA.expr -> tc_type -> source -> tc_context
(** Adds a constant variable along with its expression and type  *)

val add_untyped_const : tc_context -> LA.ident -> LA.expr -> source -> tc_context
(** Adds a constant variable along with its type  *)

val union: tc_context -> tc_context -> tc_context
(** Unions the two typing contexts *)

val singleton_ty: LA.ident -> tc_type -> tc_context
(** Lifts the type binding as a typing context  *)

val singleton_const: LA.ident -> LA.expr -> tc_type -> source -> tc_context
(** Lifts the constant binding as a typing context  *)

val extract_arg_ctx: LA.const_clocked_typed_decl -> tc_context
(** Extracts the input stream as a typing context *)

val extract_ret_ctx: LA.clocked_typed_decl -> tc_context
(** Extracts the output stream as a typing context  *)

val extract_loc_ctx: LA.node_local_decl -> tc_context
(** Extracts the local stream as a typing context  *)

val extract_consts: LA.const_clocked_typed_decl -> tc_context
(** Extracts constants as a typing constant  *)

val get_constant_ids: tc_context -> LA.ident list
(** Returns the constants declared in the typing context  *)

val lookup_contract_exports: tc_context -> LA.ident -> ty_store option
(** lookup the symbols exported by the contract *)

val add_contract_exports: tc_context -> LA.ident -> ty_store -> tc_context
(** Add the symbols that the contracts *)
  
(** {1 Pretty Printers} *)

val pp_print_type_syn: Format.formatter -> (LA.ident * tc_type) -> unit
(** Pretty print type synonyms*)
                     
val pp_print_type_binding: Format.formatter -> (LA.ident * tc_type) -> unit
(** Pretty print type bindings*)  

val pp_print_val_binding: Format.formatter -> (LA.ident * (LA.expr * tc_type option * source)) -> unit
(** Pretty print value bindings (used for constants)*)

val pp_print_ty_syns: Format.formatter -> ty_alias_store -> unit
(** Pretty print type synonym context *)

val pp_print_tymap: Format.formatter -> ty_store -> unit
(** Pretty print type binding context *)
               
val pp_print_vstore: Format.formatter -> const_store -> unit
(** Pretty print value store *)

val pp_print_u_types: Format.formatter -> SI.t -> unit
(** Pretty print declared user types *)

val pp_print_contract_exports: Format.formatter -> contract_exports -> unit
(** Pretty pring contract exports  *)
  
val pp_print_enum_variants: Format.formatter -> enum_variants -> unit
(** Pretty print enumeration types and their variants *)

val pp_print_tc_context: Format.formatter -> tc_context -> unit
(** Pretty print the complete type checker context*)

(** {1 Helper functions that uses context }  *)

val arity_of_expr: tc_context -> LA.expr -> int
(** Return the arity of a Lustre expression given a context *)

val traverse_group_expr_list: (int -> LA.expr -> 'a) -> tc_context -> int -> LA.expr list -> 'a
(** Traverse a group expr list *)

val is_type_num: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is a number type i.e. Int, Real, IntRange, or Machine Integer *)

val is_type_int: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is an integer type, i.e. Int, or IntRange *)

val is_type_real_or_int: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is a real or integer type, i.e, Real, Int, or IntRange *)

val is_type_int_or_machine_int: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is an integer type or machine int, i.e. Int, IntRange, or Machine Integer *)

val is_type_unsigned_machine_int: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is an unsigned machine int. i.e. UInt, UInt32 etc.  *)

val is_type_signed_machine_int: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is an signed machine int. i.e. Int, Int32 etc.  *)

val is_type_machine_int: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is a signed or unsiged machine integer.  *)

val is_type_array: tc_context -> LA.lustre_type -> (bool, HString.t) result
(** returns [true] if the type is an array type *)

val is_machine_type_of_associated_width: tc_context -> (LA.lustre_type * LA.lustre_type) -> (bool, HString.t) result
(** returns [true] if the first component of the type is of the same width 
  as the second component. eg. Int8 and UInt8 returns [true] but Int16 and UInt8 return [false] *)

val type_contains_subrange : tc_context -> LA.lustre_type -> bool
(** Returns true if the lustre type expression contains an IntRange or if it is an IntRange *)

val type_contains_ref : tc_context -> LA.lustre_type -> bool
(** Returns true if the lustre type expression contains a RefinementType or if it is an RefinementType *)

val type_contains_enum_subrange_reftype : tc_context -> LA.lustre_type -> bool
(** Returns true if the lustre type expression contains an EnumType/IntRange or if it is an EnumType/IntRange *)

val type_contains_abstract : tc_context -> tc_type -> bool
(** Returns true if the lustre type expression contains an abstract type (including polymorphic type variable) or if it is an abstract type *)

val ty_vars_of_expr: tc_context -> LA.index -> LA.expr -> SI.t
(** [ty_vars_of_type ctx node_name e] returns all type variable identifiers that appear in the expression [e] *)

val ty_vars_of_type: tc_context -> LA.index -> LA.lustre_type -> SI.t
(** [ty_vars_of_type ctx node_name ty] returns all type variable identifiers that appear in the type [ty] *)