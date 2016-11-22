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

module SI : Set.S with type elt = Ident.t

(** Error while parsing *)
exception Parser_error

(** {1 Types} *)

(** An identifier *)
type ident = string

(** A single index *)
type index = string

(** A clock expression *)
type clock_expr =
  | ClockTrue
  | ClockPos of ident
  | ClockNeg of ident
  | ClockConstr of ident * ident

(** A Lustre expression *)
type expr =
    Ident of position * ident
  | ModeRef of position * ident list
  | RecordProject of position * expr * index
  | TupleProject of position * expr * expr
  | StructUpdate of position * expr * label_or_index list * expr
  | True of position
  | False of position
  | Num of position * string
  | Dec of position * string
  | ToInt of position * expr
  | ToReal of position * expr
  | ExprList of position * expr list
  | TupleExpr of position * expr list
  | ArrayExpr of position * expr list
  | ArrayConstr of position * expr * expr 
  | ArraySlice of position * expr * (expr * expr) 
  | ArrayConcat of position * expr * expr
  | RecordExpr of position * ident * (ident * expr) list
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
  | When of position * expr * clock_expr
  | Current of position * expr
  | Condact of position * expr * expr * ident * expr list * expr list
  | Activate of position * ident * expr * expr * expr list
  | Merge of position * ident * (ident * expr) list
  | RestartEvery of position * ident * expr list * expr
  | Pre of position * expr
  | Last of position * ident
  | Fby of position * expr * int * expr
  | Arrow of position * expr * expr
  | Call of position * ident * expr list
  | CallParam of position * ident * lustre_type list * expr list

(** A Lustre type *)
and lustre_type =
    Bool of position
  | Int of position
  | IntRange of position * expr * expr
  | Real of position
  | UserType of position * ident
  | TupleType of position * lustre_type list
  | RecordType of position * typed_ident list
  | ArrayType of position * (lustre_type * expr)
  | EnumType of position * ident option * ident list

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

(** The left-hand side of an equation *)
type eq_lhs = 
  | ArrayDef of position * ident * ident list
  | StructDef of position * struct_item list

type transition_to =
  | TransRestart of position * (position * ident)
  | TransResume of position * (position * ident)

type transition_branch =
  | Target of transition_to
  | TransIf of position * expr *
               transition_branch * transition_branch option
  
type automaton_transition = position * transition_branch

type auto_returns = Given of ident list | Inferred

(** An equation or assertion in the node body *)
type node_equation =
  | Assert of position * expr
  | Equation of position * eq_lhs * expr 
  | Automaton of position * ident option * state list * auto_returns

and state =
  | State of position * ident * bool *
             node_local_decl list *
             node_equation list *
             automaton_transition option *
             automaton_transition option

(** An item in a node declaration *)
type node_item =
  | EqAssert of node_equation
  | AnnotMain of bool
  | AnnotProperty of position * string option * expr

(* A contract ghost constant. *)
type contract_ghost_const = const_decl

(* A contract ghost variable. *)
type contract_ghost_var = const_decl

(* A contract assume. *)
type contract_assume = position * string option * expr

(* A contract guarantee. *)
type contract_guarantee = position * string option * expr

(* A contract requirement. *)
type contract_require = position * string option * expr

(* A contract ensure. *)
type contract_ensure = position * string option * expr

(* A contract mode. *)
type contract_mode =
  position * ident * (contract_require list) * (contract_ensure list)

(* A contract call. *)
type contract_call = position * ident * expr list * expr list

(* Equations that can appear in a contract node. *)
type contract_node_equation =
  | GhostConst of contract_ghost_const
  | GhostVar of contract_ghost_var
  | Assume of contract_assume
  | Guarantee of contract_guarantee
  | Mode of contract_mode
  | ContractCall of contract_call

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

(** A declaration of a type, a constant, a node, a function or an
    instance of a parametric node *)
type declaration =
  | TypeDecl of position * type_decl
  | ConstDecl of position * const_decl
  | NodeDecl of position * node_decl
  | FuncDecl of position * node_decl
  | ContractNodeDecl of position * contract_node_decl
  | NodeParamInst of position * node_param_inst

(** A Lustre program as a list of declarations *) 
type t = declaration list

(** {1 Pretty-printers} *)
val pp_print_node_param_list : Format.formatter -> node_param list -> unit
val pp_print_ident : Format.formatter -> ident -> unit
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
val pp_print_node_item : Format.formatter -> node_item -> unit
val pp_print_declaration : Format.formatter -> declaration -> unit
val pp_print_program : Format.formatter -> t -> unit

val pp_print_contract_node : Format.formatter -> contract_node_decl -> unit


(** {1 Helpers} *)

(** Returns the position of an expression *)
val pos_of_expr : expr -> Lib.position

(** Returns true if the expression has unguareded pre's *)
val has_unguarded_pre : expr -> bool

(** Returns true if the expression has a `pre` or a `->`. *)
val has_pre_or_arrow : expr -> Lib.position option

(** Returns true iff a contract mentions a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
val contract_has_pre_or_arrow : contract -> Lib.position option

(** Checks whether a node local declaration has a `pre` or a `->`. *)
val node_local_decl_has_pre_or_arrow : node_local_decl -> Lib.position option

(** Checks whether a node equation has a `pre` or a `->`. *)
val node_item_has_pre_or_arrow : node_item -> Lib.position option

(** [replace_lasts allowed prefix acc e] replaces [last x] expressions in AST
    [e] by abstract identifiers prefixed with [prefix]. Only identifiers that
    appear in the list [allowed] are allowed to appear under a last. It returns
    the new AST expression and a set of identifers for which the last
    application was replaced. *)
val replace_lasts : string list -> string -> SI.t -> expr -> expr * SI.t


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
