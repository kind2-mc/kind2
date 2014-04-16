(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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


(** Minimally simplified Lustre AST

    @author Christoph Sticksel

*)

val pp_print_list : (Format.formatter -> 'a -> unit) ->
  ('b, Format.formatter, unit) format -> Format.formatter -> 'a list -> unit

type position = { pos_fname : string; pos_lnum : int; pos_cnum : int; }

val position_of_lexing : Lexing.position -> position

val pp_print_position : Format.formatter -> position -> unit

val dummy_pos : position

val dummy_pos_in_file : string -> position

val position_of_lexing : Lexing.position -> position

val is_dummy_pos : position -> bool

type ident = LustreIdent.t

type index = LustreIdent.index

type expr =
    Ident of position * ident
  | RecordProject of position * ident * index
  | TupleProject of position * ident * expr
  | True of position
  | False of position
  | Num of position * string
  | Dec of position * string
  | ToInt of position * expr
  | ToReal of position * expr
  | ExprList of position * expr list
  | TupleExpr of position * expr list
  | ArrayConstr of position * expr * expr
  | ArraySlice of position * ident * (expr * expr) list
  | ArrayConcat of position * expr * expr
  | RecordConstruct of position * ident * (ident * expr) list
  | Not of position * expr
  | And of position * expr * expr
  | Or of position * expr * expr
  | Xor of position * expr * expr
  | Impl of position * expr * expr
  | OneHot of position * expr list
  | Uminus of position * expr
  | Mod of position * expr * expr
  | Minus of position * expr * expr
  | Plus of position * expr * expr
  | Div of position * expr * expr
  | Times of position * expr * expr
  | IntDiv of position * expr * expr
  | Ite of position * expr * expr * expr
  | With of position * expr * expr * expr
  | Eq of position * expr * expr
  | Neq of position * expr * expr
  | Lte of position * expr * expr
  | Lt of position * expr * expr
  | Gte of position * expr * expr
  | Gt of position * expr * expr
  | When of position * expr * expr
  | Current of position * expr
  | Condact of position * expr * ident * expr list * expr list
  | Pre of position * expr
  | Fby of position * expr * int * expr
  | Arrow of position * expr * expr
  | Call of position * ident * expr list
  | CallParam of position * ident * lustre_type list * expr list

and lustre_type =
    Bool of position
  | Int of position
  | IntRange of position * expr * expr
  | Real of position
  | UserType of position * ident
  | TupleType of position * lustre_type list
  | RecordType of position * typed_ident list
  | ArrayType of position * (lustre_type * expr)
  | EnumType of position * ident list

and typed_ident = ident * lustre_type

type type_decl = 
  | AliasType of position * ident * lustre_type 
  | FreeType of position * ident

type clock_expr = ClockPos of ident | ClockNeg of ident | ClockTrue

type clocked_typed_decl = position * ident * lustre_type * clock_expr

type const_clocked_typed_decl = position * ident * lustre_type * clock_expr * bool

type const_decl =
    FreeConst of position * ident * lustre_type
  | UntypedConst of position * ident * expr
  | TypedConst of position * ident * expr * lustre_type

type var_decl = position * ident * lustre_type * clock_expr

type node_param =
  | TypeParam of ident

type node_local_decl = 
  | NodeConstDecl of position * const_decl 
  | NodeVarDecl of position * var_decl

type struct_item =
  | SingleIdent of position * ident
  | TupleStructItem of position * struct_item list
  | TupleSelection of position * ident * expr
  | FieldSelection of position * ident * ident
  | ArraySliceStructItem of position * ident * (expr * expr) list

type node_equation =
  | Assert of position * expr
  | Equation of position * struct_item list * expr
  | AnnotMain 
  | AnnotProperty of position * expr

type contract_clause = 
  | Requires of position * expr 
  | Ensures of position * expr

type contract = contract_clause list

type node_decl =
  ident * node_param list * const_clocked_typed_decl list * 
  clocked_typed_decl list * node_local_decl list * node_equation list * 
  contract

type func_decl =
    ident * (ident * lustre_type) list * (ident * lustre_type) list

type node_param_inst = ident * ident * lustre_type list

type declaration =
  | TypeDecl of position * type_decl
  | ConstDecl of position * const_decl
  | NodeDecl of position * node_decl
  | FuncDecl of position * func_decl
  | NodeParamInst of position * node_param_inst

type t = declaration list

val pp_print_expr : Format.formatter -> expr -> unit
val pp_print_array_slice : Format.formatter -> expr * expr -> unit
val pp_print_field_assign : Format.formatter -> ident * expr -> unit
val pp_print_clock_expr : Format.formatter -> clock_expr -> unit
val pp_print_lustre_type : Format.formatter -> lustre_type -> unit
val pp_print_typed_ident : Format.formatter -> typed_ident -> unit
val pp_print_clocked_typed_ident :
  Format.formatter -> position * ident * lustre_type * clock_expr -> unit
val pp_print_const_clocked_typed_ident :
  Format.formatter -> position * ident * lustre_type * clock_expr * bool -> unit
val pp_print_type_decl : Format.formatter -> type_decl -> unit
val pp_print_var_decl :
  Format.formatter -> position * ident * lustre_type * clock_expr -> unit
val pp_print_const_decl : Format.formatter -> const_decl -> unit
val pp_print_node_local_decl_var :
  Format.formatter -> node_local_decl -> unit
val pp_print_node_local_decl_const :
  Format.formatter -> node_local_decl -> unit
val pp_print_node_local_decl :
  Format.formatter -> node_local_decl list -> unit
val pp_print_struct_item : Format.formatter -> struct_item -> unit
val pp_print_node_equation : Format.formatter -> node_equation -> unit
val pp_print_contract_clause : Format.formatter -> contract_clause -> unit
val pp_print_contract : Format.formatter -> contract_clause list -> unit
val pp_print_declaration : Format.formatter -> declaration -> unit
val pp_print_program : Format.formatter -> t -> unit

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
