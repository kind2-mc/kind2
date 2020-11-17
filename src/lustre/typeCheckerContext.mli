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
module AD = LustreAstDependencies
module SI = LA.SI
          
(** Type alias for lustre type from LustreAst  *)
type tc_type  = LA.lustre_type

(** Map for types with identifiers as keys *)
module IMap : sig
  (** everything that [Stdlib.Map] gives us  *)
  include (Map.S with type key = LA.ident)
  val keys: 'a t -> key list
end


type ty_alias_store
(** A store of type Aliases, i.e. for user defined types  *)

type ty_store
(** A store of identifier and their types*)

type const_store
(** A Store of constant identifier and their (const) values with types. 
 *  The values of the associated identifiers should be evaluated to a 
 *  Bool or an Int at constant propogation phase of type checking *)

type ty_set
(** set of valid user type identifiers *)

type node_summary
(** stores node call summaries *)

type tc_context
(** The type Checker context *)

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
(** Checks if the contract name is previously seen   *)
               
val member_u_types : tc_context -> LA.ident -> bool
(** Checks of the type identifier is a user defined type *)
  
val member_val: tc_context -> LA.ident -> bool
(** Checks if the identifier is a constant  *)

val lookup_ty_syn: tc_context -> LA.ident -> tc_type option 
(** picks out the type synonym from the context
    If it is user type then chases it (recursively looks up) 
    the actual type. This chasing is necessary to check type equality 
    between user defined types. *)

val lookup_ty: tc_context -> LA.ident -> tc_type option
(** Picks out the type of the identifier to type context map *)

val lookup_contract_ty: tc_context -> LA.ident -> tc_type option
(** Lookup a contract type  *)
                          
val lookup_const: tc_context -> LA.ident -> (LA.expr * tc_type) option
(** Lookup a constant identifier *)

val add_ty_syn: tc_context -> LA.ident -> tc_type -> tc_context
(** add a type synonym in the typing context *)

val add_ty: tc_context -> LA.ident -> tc_type -> tc_context
(** Add type binding into the typing context *)

val add_ty_contract: tc_context -> LA.ident -> tc_type -> tc_context
(**  Add the type of the contract *)
                  
val add_ty_decl: tc_context -> LA.ident -> tc_context
(** Add a user declared type in the typing context *)

val remove_ty: tc_context -> LA.ident -> tc_context
(** Removes a type binding  *)
                  
val add_const: tc_context -> LA.ident -> LA.expr -> tc_type -> tc_context
(** Adds a constant variable along with its expression and type  *)

val union: tc_context -> tc_context -> tc_context
(** Unions the two typing contexts *)

val singleton_ty: LA.ident -> tc_type -> tc_context
(** Lifts the type binding as a typing context  *)

val singleton_const: LA.ident -> LA.expr -> tc_type -> tc_context
(** Lifts the constant binding as a typing context  *)

val extract_arg_ctx: LA.const_clocked_typed_decl -> tc_context
(** Extracts the input stream as a typing context *)

val extract_ret_ctx: LA.clocked_typed_decl -> tc_context
(** Extracts the output stream as a typing context  *)

val extract_consts: LA.const_clocked_typed_decl -> tc_context
(** Extracts constants as a typing constant  *)

val get_node_summary: tc_context -> AD.node_summary
(** Retrives the node summary from the typechecker context *)

val add_node_summary: tc_context -> AD.node_summary -> tc_context 
(** Adds a node summary to the typechecker context *)

val get_constant_ids: tc_context -> LA.ident list
(** Returns the constants declared in the typing context  *)
  
(** {1 Pretty printers} *)

val pp_print_tc_context: Format.formatter -> tc_context -> unit
(** Pretty print the typing context  *)

val pp_print_node_summary: Format.formatter -> node_summary -> unit
(** Pretty print the node summary  *)
