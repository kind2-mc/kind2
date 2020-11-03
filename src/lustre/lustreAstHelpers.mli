(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(** Some helper functions on the surface level parsed AST *)

open LustreAst

module SI = Ident.IdentSet
(** {1 Helpers} *)

val pos_of_expr : expr -> Lib.position
(** Returns the position of an expression *)

val has_unguarded_pre : expr -> bool
(** Returns true if the expression has unguareded pre's *)

val has_pre_or_arrow : expr -> Lib.position option
(** Returns true if the expression has a `pre` or a `->`. *)

val contract_has_pre_or_arrow : contract -> Lib.position option
(** Returns true iff a contract mentions a `pre` or a `->`.
    Does not (cannot) check contract calls recursively, checks only inputs and
    outputs. *)

val node_local_decl_has_pre_or_arrow : node_local_decl -> Lib.position option
(** Checks whether a node local declaration has a `pre` or a `->`. *)

val node_item_has_pre_or_arrow : node_item -> Lib.position option
(** Checks whether a node equation has a `pre` or a `->`. *)

val replace_lasts : string list -> string -> SI.t -> expr -> expr * SI.t
(** [replace_lasts allowed prefix acc e] replaces [last x] expressions in AST
    [e] by abstract identifiers prefixed with [prefix]. Only identifiers that
    appear in the list [allowed] are allowed to appear under a last. It returns
    the new AST expression and a set of identifers for which the last
    application was replaced. *)

val vars: expr -> SI.t
(** returns all the [ident] that appear in the expr ast*)

val vars_of_struct_item: struct_item -> SI.t
(** returns all variables that appear in a [struct_item]   *)

val vars_lhs_of_eqn: node_item -> SI.t
(** returns all the variables that appear in the lhs of the equation of the node body *)

val vars_of_ty_ids: typed_ident -> SI.t
(**  returns all the variables that occur in the expression of a typed identifier declaration *)

val add_exp: Lib.position -> expr -> expr -> expr
(** Return an AST that adds two expressions*)

val abs_diff: Lib.position -> expr -> expr -> expr
(** returns an AST which is the absolute difference of two expr ast*)

val extract_ip_ty: const_clocked_typed_decl -> ident * lustre_type                                                
(** returns  the pair of identifier and its type from the node input streams *)

val extract_op_ty: clocked_typed_decl -> ident * lustre_type
(** returns the pair of identifier and its type from the node output streams *)

val is_const_arg: const_clocked_typed_decl -> bool
(** Returns [true] if the node input stream is a constant  *)

val is_type_num: lustre_type -> bool
(** returns [true] if the type is a number type i.e. Int, Real, IntRange. *)
  
val is_type_int: lustre_type -> bool
(** returns [true] if the type is an integer type i.e. Int, Machine Integers or an IntRange *)

val is_type_unsigned_machine_int: lustre_type -> bool
(** returns [true] if the type is an unsigned machine int. i.e. UInt, UInt32 etc.  *)

val is_type_signed_machine_int: lustre_type -> bool
(** returns [true] if the type is an signed machine int. i.e. Int, Int32 etc.  *)

val is_type_machine_int: lustre_type -> bool
(** returns [true] if the type is a signed or unsiged machine integer.  *)

val is_machine_type_of_associated_width: (lustre_type * lustre_type) -> bool
(** returns [true] if the first component of the type is of the same width 
    as the second component. eg. Int8 and UInt8 returns [true] but Int16 and UInt8 return [false] *)

val is_type_or_const_decl: declaration -> bool
(** returns [true] if it is a type or a constant declaration  *)

val split_program: declaration list -> (declaration list * declaration list)
(** Splits the program into two. First component are the type and constant declarations and
    Second component are the nodes, contract and function declarations. *)

val abstract_pre_subexpressions: expr -> expr
(** Abstracts out the pre expressions into a constant so that the built graph does not create a cycle.*)

val extract_node_equation: node_item -> (eq_lhs * expr) list
(** Extracts out all the node equations as an associated list of rhs and lhs of the equation *)

val get_last_node_name: declaration list -> ident option
(** Gets the name of the last node declared in the file. *)

val move_node_to_last: ident -> declaration list -> declaration list

val sort_typed_ident: typed_ident list -> typed_ident list
(** Sort typed identifiers  *)

val sort_idents: ident list -> ident list
(** Sort identifiers  *)
