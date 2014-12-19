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
  | FieldIndex of Lib.position * ident 
  | NumIndex of Lib.position * int
  | VarIndex of Lib.position * ident

(** An expression *)
type expr =
    Ident of Lib.position * ident
  | RecordProject of Lib.position * ident * index
  | TupleProject of Lib.position * ident * expr
  | True of Lib.position
  | False of Lib.position
  | Num of Lib.position * string
  | Dec of Lib.position * string
  | ToInt of Lib.position * expr
  | ToReal of Lib.position * expr
  | ExprList of Lib.position * expr list
  | TupleExpr of Lib.position * expr list
  | ArrayConstr of Lib.position * expr * expr
  | ArraySlice of Lib.position * ident * (expr * expr) list
  | ArrayConcat of Lib.position * expr * expr
  | RecordConstruct of Lib.position * ident * (ident * expr) list
  | Not of Lib.position * expr
  | And of Lib.position * expr * expr
  | Or of Lib.position * expr * expr
  | Xor of Lib.position * expr * expr
  | Impl of Lib.position * expr * expr
  | OneHot of Lib.position * expr list
  | Uminus of Lib.position * expr
  | Mod of Lib.position * expr * expr
  | Minus of Lib.position * expr * expr
  | Plus of Lib.position * expr * expr
  | Div of Lib.position * expr * expr
  | Times of Lib.position * expr * expr
  | IntDiv of Lib.position * expr * expr
  | Ite of Lib.position * expr * expr * expr
  | With of Lib.position * expr * expr * expr
  | Eq of Lib.position * expr * expr
  | Neq of Lib.position * expr * expr
  | Lte of Lib.position * expr * expr
  | Lt of Lib.position * expr * expr
  | Gte of Lib.position * expr * expr
  | Gt of Lib.position * expr * expr
  | When of Lib.position * expr * expr
  | Current of Lib.position * expr
  | Condact of Lib.position * expr * ident * expr list * expr list
  | Pre of Lib.position * expr
  | Fby of Lib.position * expr * int * expr
  | Arrow of Lib.position * expr * expr
  | Call of Lib.position * ident * expr list
  | CallParam of Lib.position * ident * lustre_type list * expr list

(** A type *)
and lustre_type =
    Bool of Lib.position
  | Int of Lib.position
  | IntRange of Lib.position * expr * expr
  | Real of Lib.position
  | UserType of Lib.position * ident
  | TupleType of Lib.position * lustre_type list
  | RecordType of Lib.position * typed_ident list
  | ArrayType of Lib.position * (lustre_type * expr)
  | EnumType of Lib.position * ident list

(** An identifier with a type *)
and typed_ident = ident * lustre_type

(** {1 Declarations} *)

(** A declaration of an alias or free type *)
type type_decl = 
  | AliasType of Lib.position * ident * lustre_type 
  | FreeType of Lib.position * ident

(** A clock expression *)
type clock_expr = ClockPos of ident | ClockNeg of ident | ClockTrue

(** An identifier with a type and a clock as used for the type of variables *)
type clocked_typed_decl = Lib.position * ident * lustre_type * clock_expr

(** An identifier, possibly flagged as constant, with a type and a
    clock as used for the type of variables *)
type const_clocked_typed_decl = Lib.position * ident * lustre_type * clock_expr * bool

(** A constant declaration *)
type const_decl =
    FreeConst of Lib.position * ident * lustre_type
  | UntypedConst of Lib.position * ident * expr
  | TypedConst of Lib.position * ident * expr * lustre_type

(** A type parameter of a node *)
type node_param =
  | TypeParam of ident

(** A local constant or variable declaration of a node *)
type node_local_decl = 
  | NodeConstDecl of Lib.position * const_decl 
  | NodeVarDecl of Lib.position * clocked_typed_decl

(** The left-hand side of an equation *)
type struct_item =
  | SingleIdent of Lib.position * ident
  | IndexedIdent of Lib.position * ident * one_index list

  | TupleStructItem of Lib.position * struct_item list
  | TupleSelection of Lib.position * ident * expr
  | FieldSelection of Lib.position * ident * ident
  | ArraySliceStructItem of Lib.position * ident * (expr * expr) list

(** An Equation, assertion or annotation in the body of a node *)
type node_equation =
  | Assert of Lib.position * expr
  | Equation of Lib.position * struct_item list * expr
  | AnnotMain 
  | AnnotProperty of Lib.position * expr

(** A clause of an assume guarantee contract *)
type contract_clause = 
  | Requires of Lib.position * expr 
  | Ensures of Lib.position * expr

(** The contract of a node as a list of clauses *)
type contract = contract_clause list

(** Declaration of a node as a tuple of 

    - its identifier, 
    - its type parameters, 
    - the list of its inputs,
    - the list of its outputs,
    - the list of its local constant and variable declarations,
    - its equations, assertions and annotiations, and
    - its contract. 
*)
type node_decl =
  ident * node_param list * const_clocked_typed_decl list * 
  clocked_typed_decl list * node_local_decl list * node_equation list * 
  contract

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
  | TypeDecl of Lib.position * type_decl
  | ConstDecl of Lib.position * const_decl
  | NodeDecl of Lib.position * node_decl
  | FuncDecl of Lib.position * func_decl
  | NodeParamInst of Lib.position * node_param_inst

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
