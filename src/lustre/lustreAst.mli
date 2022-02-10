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

(** Minimally simplified Lustre abstract syntax tree

    The types in this module closely represent the abstract syntax of
    Lustre. No type checking or simplification is performed when
    constructing the abstract syntax tree, this is done when producing
    the intermediate Lustre representation in {!LustreDeclarations}. 

    Some values are reserved for future use and will cause the
    translation to intermediate Lustre to fail.

    A Lustre file is parsed into a {!declaration} list, where a
    declaration is either

    - a type definition [type t = t'],
    - a constant definition [const c = v], or
    - a node declaration.

    Almost all types are annotated with the position in the input file
    for better error reporting in the translation.

    @author Christoph Sticksel *)

open Lib

(** Error while parsing *)
exception Parser_error

(** {1 Types} *)

(** An identifier *)
type ident = HString.t

module SI: sig
  include (Set.S with type elt = ident)
  val flatten: t list -> t
end

(** A single index *)
type index = HString.t

(** A clock expression *)
type clock_expr =
  | ClockTrue
  | ClockPos of ident
  | ClockNeg of ident
  | ClockConstr of ident * ident

(* Some symbols for lustre expressions *)
type conversion_operator =
  | ToInt | ToReal
  | ToInt8 | ToInt16 | ToInt32 | ToInt64
  | ToUInt8 | ToUInt16 | ToUInt32 | ToUInt64

type unary_operator =
  | Not | Uminus
  | BVNot

type binary_operator =
  | And | Or | Xor | Impl
  | Mod | Minus | Plus | Div | Times | IntDiv
  | BVAnd | BVOr | BVShiftL | BVShiftR

type ternary_operator =
  | Ite
  | With (* With operator for recursive definitions *)

type n_arity_operator =
  | OneHot

type comparison_operator =
  | Eq | Neq  | Lte  | Lt  | Gte | Gt

type constant =
  | True | False
  | Num of HString.t
  | Dec of HString.t

type quantifier =
  | Forall | Exists

type group_expr =
  | ExprList (* List of expressions *)
  | TupleExpr (* Tuple expression *)
  | ArrayExpr (* Array expression *)

(** A Lustre type *)
type lustre_type =
  | TVar of position * ident
  | Bool of position
  | Int of position
  | UInt8 of position
  | UInt16 of position
  | UInt32 of position
  | UInt64 of position
  | Int8 of position
  | Int16 of position
  | Int32 of position
  | Int64 of position
  | IntRange of position * expr * expr
  | Real of position
  | UserType of position * ident
  | AbstractType of position * ident
  | TupleType of position * lustre_type list
  | GroupType of position * lustre_type list
  | RecordType of position * typed_ident list
  | ArrayType of position * (lustre_type * expr)
  | EnumType of position * ident * ident list
  | TArr of position * lustre_type * lustre_type
  (* TArr is always constructed as GroupType -> GroupType
   *  as we can have more than one arguments and return 
   *  values  *)
  
(** A Lustre expression *)
and expr =
  (* Identifiers *)
  | Ident of position * ident
  | ModeRef of position * ident list
  | RecordProject of position * expr * index
  | TupleProject of position * expr * int
  (* Values *)
  | Const of position * constant
  (* Operators *)
  | UnaryOp of position * unary_operator * expr
  | BinaryOp of position * binary_operator * expr * expr
  | TernaryOp of position * ternary_operator * expr * expr * expr
  | NArityOp of position * n_arity_operator * expr list
  | ConvOp of position * conversion_operator * expr
  | CompOp of position * comparison_operator * expr * expr
  (* Structured expressions *)
  | RecordExpr of position * ident * (ident * expr) list
  | GroupExpr of position * group_expr * expr list
  (* Update of structured expressions *)
  | StructUpdate of position * expr * label_or_index list * expr
  | ArrayConstr of position * expr * expr 
  | ArraySlice of position * expr * (expr * expr) 
  | ArrayIndex of position * expr * expr
  | ArrayConcat of position * expr * expr
  (* Quantified expressions *)
  | Quantifier of position * quantifier * typed_ident list * expr
  (* Clock operators *)
  | When of position * expr * clock_expr
  | Current of position * expr
  | Condact of position * expr * expr * ident * expr list * expr list
  | Activate of position * ident * expr * expr * expr list
  | Merge of position * ident * (ident * expr) list
  | RestartEvery of position * ident * expr list * expr
  (* Temporal operators *)
  | Pre of position * expr
  | Last of position * ident
  | Fby of position * expr * int * expr
  | Arrow of position * expr * expr
  (* Node calls *)
  | Call of position * ident * expr list
  | CallParam of position * ident * lustre_type list * expr list

(** An identifier with a type *)
and typed_ident = position * ident * lustre_type

(** A record field or an array or tuple index *)
and label_or_index = 
  | Label of position * index
  | Index of position * expr

(** {1 Declarations} *)

(** A declaration of an alias or free type *)
type type_decl = 
  | AliasType of position * ident * lustre_type 
  | FreeType of position * ident

(** An identifier with a type and a clock as used for the type of variables *)
type clocked_typed_decl = position * ident * lustre_type * clock_expr

(** An identifier, possibly flagged as constant, with a type and a
    clock as used for the type of variables *)
type const_clocked_typed_decl = position * ident * lustre_type * clock_expr * bool

(** A constant declaration *)
type const_decl =
  | FreeConst of position * ident * lustre_type
  | UntypedConst of position * ident * expr
  | TypedConst of position * ident * expr * lustre_type

(** A type parameter of a node *)
type node_param =
  | TypeParam of ident

(** A local constant or variable declaration of a node *)
type node_local_decl = 
  | NodeConstDecl of position * const_decl 
  | NodeVarDecl of position * clocked_typed_decl

(** Structural assignment on the left-hand side of an equation *)
type struct_item =
  | SingleIdent of position * ident
  | TupleStructItem of position * struct_item list
  | TupleSelection of position * ident * expr
  | FieldSelection of position * ident * ident
  | ArraySliceStructItem of position * ident * (expr * expr) list
  | ArrayDef of position * ident * ident list

(** The left-hand side of an equation *)
type eq_lhs = 
  | StructDef of position * struct_item list

(** An equation or assertion in the node body *)
type node_equation =
  | Assert of position * expr
  | Equation of position * eq_lhs * expr 

(** An item in a node declaration *)
type node_item =
  | Body of node_equation
  | AnnotMain of bool
  | AnnotProperty of position * HString.t option * expr

(* A contract ghost constant. *)
type contract_ghost_const = const_decl

(* A contract ghost variable. *)
type contract_ghost_var = const_decl

(* A contract assume. *)
type contract_assume = position * HString.t option * bool (* soft *) * expr

(* A contract guarantee. *)
type contract_guarantee = position * HString.t option * bool (* soft *) * expr

(* A contract requirement. *)
type contract_require = position * HString.t option * expr

(* A contract ensure. *)
type contract_ensure = position * HString.t option * expr

(* A contract mode. *)
type contract_mode =
  position * ident * (contract_require list) * (contract_ensure list)

(* A contract call. *)
type contract_call = position * ident * expr list * ident list

(* Variables for assumption generation *)
type contract_assump_vars = position * (position * HString.t) list

(* Equations that can appear in a contract node. *)
type contract_node_equation =
  | GhostConst of contract_ghost_const
  | GhostVar of contract_ghost_var
  | Assume of contract_assume
  | Guarantee of contract_guarantee
  | Mode of contract_mode
  | ContractCall of contract_call
  | AssumptionVars of contract_assump_vars

(* A contract is some ghost consts / var, and assumes guarantees and modes. *)
type contract = contract_node_equation list

  (*   contract_ghost_const list * contract_ghost_var list * ( *)
  (*   contract_assume list * contract_guarantee list * *)
  (*   contract_mode list * contract_call list *)
  (* ) list *)

(** Declaration of a node or function as a tuple of

    - its identifier,
    - a flag, true if the node / function is extern
    - its type parameters,
    - the list of its inputs,
    - the list of its outputs,
    - the list of its local constant and variable declarations,
    - its equations, assertions and annotiations, and
    - its optional contract specification *)
type node_decl =
  ident
  * bool
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * node_local_decl list
  * node_item list
  * contract option

(** A contract node declaration as a tuple of

  - its identifier,
  - its type parameters,
  - its inputs,
  - its outputs,
  - its body as a [contract]. *)
type contract_node_decl =
  ident
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * contract


(** An instance of a parametric node as a tuple of the identifier for
    the instance, the identifier of the parametric node and the list of
    type parameters *)
type node_param_inst = ident * ident * lustre_type list

type span = {
  start_pos : position;
  end_pos : position;
}

(** A declaration of a type, a constant, a node, a function or an
    instance of a parametric node *)
type declaration =
  | TypeDecl of span * type_decl
  | ConstDecl of span * const_decl
  | NodeDecl of span * node_decl
  | FuncDecl of span * node_decl
  | ContractNodeDecl of span * contract_node_decl
  | NodeParamInst of span * node_param_inst

(** A Lustre program as a list of declarations *) 
type t = declaration list

(** {1 Pretty-printers} *)
val pp_print_node_param_list : Format.formatter -> node_param list -> unit
val pp_print_ident : Format.formatter -> ident -> unit
val pp_print_label_or_index: Format.formatter -> label_or_index -> unit
val pp_print_expr : Format.formatter -> expr -> unit
val pp_print_array_slice : Format.formatter -> expr * expr -> unit
val pp_print_field_assign : Format.formatter -> ident * expr -> unit
val pp_print_clock_expr : Format.formatter -> clock_expr -> unit
val pp_print_lustre_type : Format.formatter -> lustre_type -> unit
val pp_print_typed_ident : Format.formatter -> typed_ident -> unit
val pp_print_clocked_typed_ident :
  Format.formatter -> Lib.position * ident * lustre_type * clock_expr -> unit
val pp_print_const_clocked_typed_ident :
  Format.formatter -> Lib.position * ident * lustre_type * clock_expr * bool -> unit
val pp_print_type_decl : Format.formatter -> type_decl -> unit
val pp_print_var_decl :
  Format.formatter -> Lib.position * ident * lustre_type * clock_expr -> unit
val pp_print_const_decl : Format.formatter -> const_decl -> unit
val pp_print_node_local_decl_var :
  Format.formatter -> node_local_decl -> unit
val pp_print_node_local_decl_const :
  Format.formatter -> node_local_decl -> unit
val pp_print_node_local_decl :
  Format.formatter -> node_local_decl list -> unit
val pp_print_struct_item : Format.formatter -> struct_item -> unit
val pp_print_eq_lhs: Format.formatter -> eq_lhs -> unit
val pp_print_node_body: Format.formatter -> node_equation -> unit
val pp_print_node_item : Format.formatter -> node_item -> unit
val pp_print_declaration : Format.formatter -> declaration -> unit
val pp_print_program : Format.formatter -> t -> unit

val pp_print_contract_item : Format.formatter -> contract_node_equation -> unit
val pp_print_contract_node_decl : Format.formatter -> contract_node_decl -> unit
val string_of_expr: expr -> string
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
