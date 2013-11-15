(* This file is part of the Kind verifier

 * Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
 * here after designated as the Copyright Holder.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the University of Iowa, nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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

type expr =
    Ident of position * ident
  | RecordProject of position * expr * ident
  | TupleProject of position * expr * expr
  | True of position
  | False of position
  | Num of position * string
  | Dec of position * string
  | ToInt of position * expr
  | ToReal of position * expr
  | ExprList of position * expr list
  | TupleExpr of position * expr list
  | ArrayConstr of position * expr * expr
  | ArraySlice of position * expr * (expr * expr) list
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
  | Intdiv of position * expr * expr
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
  | Condact of position * expr * expr * expr list
  | Pre of position * expr
  | Fby of position * expr * int * expr
  | Arrow of position * expr * expr
  | Call of position * ident * expr list
  | CallParam of position * ident * lustre_type list * expr list

and lustre_type =
    Bool
  | Int
  | IntRange of expr * expr
  | Real
  | UserType of ident
  | TupleType of lustre_type list
  | RecordType of typed_ident list
  | ArrayType of (lustre_type * expr)
  | EnumType of ident list

and typed_ident = ident * lustre_type

type type_decl = AliasType of ident * lustre_type | FreeType of ident

type clock_expr = ClockPos of ident | ClockNeg of ident | ClockTrue

type clocked_typed_decl = ident * lustre_type * clock_expr

type const_clocked_typed_decl = ident * lustre_type * clock_expr * bool

type const_decl =
    FreeConst of ident * lustre_type
  | UntypedConst of ident * expr
  | TypedConst of ident * expr * lustre_type

type var_decl = ident * lustre_type * clock_expr

type node_param =
  | TypeParam of ident

type node_local_decl = NodeConstDecl of const_decl | NodeVarDecl of var_decl

type struct_item =
    SingleIdent of ident
  | TupleStructItem of struct_item list
  | TupleSelection of ident * expr
  | FieldSelection of ident * ident
  | ArraySliceStructItem of ident * (expr * expr) list

type node_equation =
    Assert of expr
  | Equation of struct_item list * expr
  | AnnotMain
  | AnnotProperty of expr

type contract_clause = 
  | Requires of expr 
  | Ensures of expr

type contract = contract_clause list

type node_decl =
    ident * node_param list * const_clocked_typed_decl list * 
      clocked_typed_decl list * node_local_decl list * node_equation list * 
      contract

type func_decl =
    ident * (ident * lustre_type) list * (ident * lustre_type) list

type node_param_inst = ident * ident * lustre_type list

type declaration =
  | TypeDecl of type_decl
  | ConstDecl of const_decl
  | NodeDecl of node_decl
  | FuncDecl of func_decl
  | NodeParamInst of node_param_inst

type t = declaration list

val pp_print_expr : Format.formatter -> expr -> unit
val pp_print_array_slice : Format.formatter -> expr * expr -> unit
val pp_print_field_assign : Format.formatter -> ident * expr -> unit
val pp_print_clock_expr : Format.formatter -> clock_expr -> unit
val pp_print_lustre_type : Format.formatter -> lustre_type -> unit
val pp_print_typed_ident : Format.formatter -> typed_ident -> unit
val pp_print_clocked_typed_ident :
  Format.formatter -> ident * lustre_type * clock_expr -> unit
val pp_print_const_clocked_typed_ident :
  Format.formatter -> ident * lustre_type * clock_expr * bool -> unit
val pp_print_type_decl : Format.formatter -> type_decl -> unit
val pp_print_var_decl :
  Format.formatter -> ident * lustre_type * clock_expr -> unit
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
