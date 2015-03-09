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

open Lib


(** Minimally simplified Lustre AST

    A Lustre file is parsed into a list of declarations of

    - an alias type [type t = t'],
    - a global constant [const c = v], or
    - a node

    An alias type refers to a built-in type or to a previously
    declared type. A constant declaration is typed or untyped. 

    A node declaration consists of the signature of the node (inputs,
    outputs, local variables and constants) and a list of equations. 

    A node equation is an assignment to a variable, an assertion, a
    property annotation, or a main annotation.

    Additional types used are [expr] for an expression, [lustre_type]
    for a type, and [ident = LustreIdent.t] for identifiers. 

    @author Christoph Sticksel *)

(** Error while parsing *)
exception Parser_error

(** {1 Supporting Types} *)

(** An identifier *)
type ident = LustreIdent.t

(** An index *)
type index = LustreIdent.index

(** An index expression *)
type one_index = 
  | FieldIndex of position * ident 
  | NumIndex of position * int
  | VarIndex of position * ident

(** An expression *)
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

(** A type *)
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

(** An identifier with a type *)
and typed_ident = ident * lustre_type

(** {1 Declarations} *)

(** A declaration of an alias or free type *)
type type_decl = 
  | AliasType of position * ident * lustre_type 
  | FreeType of position * ident

(** A clock expression *)
type clock_expr = ClockPos of ident | ClockNeg of ident | ClockTrue

(** An identifier with a type and a clock as used for the type of variables *)
type clocked_typed_decl = position * ident * lustre_type * clock_expr

(** An identifier, possibly flagged as constant, with a type and a
    clock as used for the type of variables *)
type const_clocked_typed_decl = position * ident * lustre_type * clock_expr * bool

(** A constant declaration *)
type const_decl =
    FreeConst of position * ident * lustre_type
  | UntypedConst of position * ident * expr
  | TypedConst of position * ident * expr * lustre_type

(** A type parameter of a node *)
type node_param =
  | TypeParam of ident

(** A local constant or variable declaration of a node *)
type node_local_decl = 
  | NodeConstDecl of position * const_decl 
  | NodeVarDecl of position * clocked_typed_decl

(** The left-hand side of an equation *)
type struct_item =
  | SingleIdent of position * ident
  | IndexedIdent of position * ident * one_index list

  | TupleStructItem of position * struct_item list
  | TupleSelection of position * ident * expr
  | FieldSelection of position * ident * ident
  | ArraySliceStructItem of position * ident * (expr * expr) list

(** An Equation, assertion or annotation in the body of a node *)
type node_equation =
  | Assert of position * expr
  | Equation of position * struct_item list * expr
  | AnnotMain 
  | AnnotProperty of position * expr

(** A contract requirement. *)
type contract_require = position * expr

(** A contract ensure. *)
type contract_ensure = position * expr

(** Equations that can appear in a contract node. *)
type contract_node_equation =
  | GhostEquation of position * struct_item list * expr
  | Require of contract_require
  | Ensure of contract_ensure

(** A contract for a node is either an inlined contract (defined in
   the node itself), or a contract node call. *)
type contract =
  | InlinedContract of position
                       * ident
                       * contract_require list
                       * contract_ensure list
  | ContractCall of position * ident

(** A contract specification for a node (if it has one) is either a
    list of modes or a global contract and a list of modes. *)
type contract_spec =
  | Modes of contract list
  (** Only mode contracts. *)
  | GlobalAndModes of contract * contract list
  (** A global contract and some mode contracts. *)

(** Declaration of a node as a tuple of

    - its identifier,
    - its type parameters,
    - the list of its inputs,
    - the list of its outputs,
    - the list of its local constant and variable declarations,
    - its equations, assertions and annotiations, and
    - its optional contract specification. *)
type node_decl =
  ident
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * node_local_decl list
  * node_equation list
  * contract_spec option

(** A contract node declaration. Almost the same as a [node_decl] but
    with a different type for equations, and no contract
    specification. *)
type contract_node_decl =
  ident
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * node_local_decl list
  * contract_node_equation list

(** Declaration of a function as a tuple of 

    - its identifier,
    - the list of its inputs, and 
    - the list of its outputs 
*)
type func_decl =
    ident * (ident * lustre_type) list * (ident * lustre_type) list

(** An instance of a parametric node as a tuple of the identifier for
    the instance, the identifier of the parametric node and the list of
    type parameters *)
type node_param_inst = ident * ident * lustre_type list

(** A declaration of a type, a constant, a node, a function or an
    instance of a parametric node *)
type declaration =
  | TypeDecl of position * type_decl
  | ConstDecl of position * const_decl
  | NodeDecl of position * node_decl
  | ContractNodeDecl of position * contract_node_decl
  | FuncDecl of position * func_decl
  | NodeParamInst of position * node_param_inst

(** A Lustre program as a list of declarations *) 
type t = declaration list

(** {1 Helpers} *)

(** Pretty-printers *)
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
val pp_print_declaration : Format.formatter -> declaration -> unit
val pp_print_program : Format.formatter -> t -> unit

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
