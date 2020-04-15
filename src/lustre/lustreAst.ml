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

open Lib

module SI = Set.Make (Ident)

exception Parser_error


let error_at_position pos msg =
  match Log.get_log_format () with
  | Log.F_pt ->
    Log.log L_error "Parser error at %a: %s" Lib.pp_print_position pos msg
  | Log.F_xml -> Log.parse_log_xml L_error pos msg
  | Log.F_json -> Log.parse_log_json L_error pos msg
  | Log.F_relay -> ()


let warn_at_position pos msg = 
  match Log.get_log_format () with
  | Log.F_pt ->
    Log.log L_warn "Parser warning at %a: %s" Lib.pp_print_position pos msg
  | Log.F_xml -> Log.parse_log_xml L_warn pos msg
  | Log.F_json -> Log.parse_log_json L_warn pos msg
  | Log.F_relay -> ()


(* ********************************************************************** *)
(* Type declarations                                                      *)
(* ********************************************************************** *)


(* An identifier *)
type ident = string

type index = string

let pp_print_ident = Format.pp_print_string

let pp_print_index = Format.pp_print_string


(* A clock expression *)
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
  | Num of string
  | Dec of string

type quantifier =
  | Forall | Exists

type group_expr =
  | ExprList (* List of expressions *)
  | TupleExpr (* Tuple expression *)
  | ArrayExpr (* Array expression *)

(** A Lustre expression *)
type expr =
  (* Identifiers *)
  | Ident of position * ident
  | ModeRef of position * ident list
  | RecordProject of position * expr * index
  | TupleProject of position * expr * expr
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


(* A built-in type *)
and lustre_type =
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
  | RecordType of position * typed_ident list
  | ArrayType of position * (lustre_type * expr)
  | EnumType of position * ident option * ident list


(* A declaration of an unclocked type *)
and typed_ident = Lib.position * ident * lustre_type

(* A record field or an array or tuple index *)
and label_or_index = 
  | Label of Lib.position * index
  | Index of Lib.position * expr

(* A declaration of a type *)
type type_decl = 
  | AliasType of position * ident * lustre_type  
  | FreeType of position * ident

(* A declaration of a clocked type *)
type clocked_typed_decl = 
  position * ident * lustre_type * clock_expr


(* A declaration of a clocked type *)
type const_clocked_typed_decl = 
  position * ident * lustre_type * clock_expr * bool


(* A declaration of a constant *)
type const_decl = 
  | FreeConst of position * ident * lustre_type
  | UntypedConst of position * ident * expr 
  | TypedConst of position * ident * expr * lustre_type

(*
(* A variable declaration *)
type var_decl = position * ident * lustre_type * clock_expr
*)

(* A static parameter of a node *)
type node_param =
  | TypeParam of ident


(* A local declaration in a node *)
type node_local_decl =
  | NodeConstDecl of position * const_decl 
  | NodeVarDecl of position * clocked_typed_decl


(* Structural assignment in left-hand side of equation *)
type struct_item =
  | SingleIdent of position * ident
  | TupleStructItem of position * struct_item list
  | TupleSelection of position * ident * expr
  | FieldSelection of position * ident * ident
  | ArraySliceStructItem of position * ident * (expr * expr) list
  | ArrayDef of position * ident * ident list


(* The left-hand side of an equation *)
type eq_lhs =
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

(* An equation or assertion in the node body *)
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


(* An item in a node declaration *)
type node_item =
  | Body of node_equation
  | AnnotMain of bool
  | AnnotProperty of position * string option * expr


(* A contract ghost constant. *)
type contract_ghost_const = const_decl

(* A contract ghost variable. *)
type contract_ghost_var = const_decl

(* A contract assume. *)
type contract_assume = position * string option * bool (* soft *) * expr

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


(* A node or function declaration

Boolean flag indicates whether node / function is extern. *)
type node_decl =
  ident
  * bool
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * node_local_decl list
  * node_item list
  * contract option

(* A contract node declaration. Almost the same as a [node_decl] but
   with a different type for equations, and no contract
   specification. *)
type contract_node_decl =
  ident
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * contract


(* An instance of a parameterized node *)
type node_param_inst = ident * ident * lustre_type list
  
(* A declaration as parsed *)
type declaration = 
  | TypeDecl of position * type_decl
  | ConstDecl of position * const_decl
  | NodeDecl of position * node_decl
  | FuncDecl of position * node_decl
  | ContractNodeDecl of position * contract_node_decl
  | NodeParamInst of position * node_param_inst


(* A Lustre program *)
type t = declaration list


(* ********************************************************************** *)
(* Pretty-printing functions                                              *)
(* ********************************************************************** *)


(* Pretty-print a clock expression *)
let pp_print_clock_expr ppf = function
  | ClockTrue -> ()
  | ClockPos s -> Format.fprintf ppf "@ when %a" pp_print_ident s
  | ClockNeg s -> Format.fprintf ppf "@ when not %a" pp_print_ident s
  | ClockConstr (s, c) ->
    Format.fprintf ppf "@ when %a(%a)" pp_print_ident c pp_print_ident s


(* Pretty-print a Lustre expression *)
let rec pp_print_expr ppf = 

  let ppos ppf p =
    (if false then Format.fprintf else Format.ifprintf)
      ppf
      "%a" 
      pp_print_position p
  in

  (* Pretty-print a string *)
  let ps p = Format.fprintf ppf "%a%s" ppos p in 

  (* Pretty-print a unary operator *)
  let p1 p s e = 
    Format.fprintf ppf "@[<hv 2>%a(%s %a)@]" 
      ppos p 
      s 
      pp_print_expr e 
  in 

  (* Pretty-print a binary infix operator *)
  let p2 p s e1 e2 = 
    Format.fprintf ppf
      "@[<hv 2>%a(%a %s@ %a)@]" 
      ppos p 
      pp_print_expr e1 
      s 
      pp_print_expr e2 
  in 

  (* Pretty-print a ternary infix operator *)
  let p3 p s1 s2 s3 e1 e2 e3 = 
    Format.fprintf ppf
      "@[<hv 2>%a(%s@ %a@;<1 -1>%s@ %a@;<1 -1>%s@ %a)@]" 
      ppos p 
      s1 
      pp_print_expr e1 
      s2
      pp_print_expr e2 
      s3 
      pp_print_expr e3 
  in 
  
  (* Pretty-print a comma-separated list of expressions *)
  let rec pl ppf = function 
    | [] -> ()
    | [e] -> Format.fprintf ppf "%a" pp_print_expr e
    | e :: tl -> Format.fprintf ppf "%a,@ %a" pl [e] pl tl
  in

  (* Pretty-print a variadic prefix operator *)
  let pnp p s l = 
    Format.fprintf ppf
      "@[<hv 2>%a%s@,@[<hv 1>(%a)@]@]" 
      ppos p 
      s
      pl l
  in

  function
    
    | Ident (p, id) -> Format.fprintf ppf "%a%a" ppos p pp_print_ident id

    | ModeRef (p, ids) ->
      Format.fprintf ppf "%a::%a" ppos p (
        pp_print_list pp_print_ident "::"
      ) ids
 
    | GroupExpr (p, ExprList, l) -> Format.fprintf ppf "%a@[<hv 1>(%a)@]" ppos p pl l

    | GroupExpr (p, TupleExpr, l) -> Format.fprintf ppf "%a@[<hv 1>{%a}@]" ppos p pl l

    | GroupExpr (p, ArrayExpr, l) -> Format.fprintf ppf "%a@[<hv 1>[%a]@]" ppos p pl l

    | StructUpdate (p, e1, i, e2) -> 

      Format.fprintf ppf
        "@[<hv 1>(%a@ with@ @[<hv>%a@] =@ %a)@]"
        pp_print_expr e1
        (pp_print_list pp_print_label_or_index "") i
        pp_print_expr e2


    | ArrayConstr (p, e1, e2) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>(%a^%a)@]" 
        ppos p 
        pp_print_expr e1 
        pp_print_expr e2

    | ArraySlice (p, e, l) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a@[<hv 1>[%a]@]@]" 
        ppos p 
        pp_print_expr e
        pp_print_array_slice l 

    | ArrayConcat (p, e1, e2) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a|%a@]" 
        ppos p 
        pp_print_expr e1
        pp_print_expr e2 

    | RecordProject (p, e, f) -> 

      Format.fprintf ppf 
        "%a%a.%a" 
        ppos p 
        pp_print_expr e 
        pp_print_index f

    | RecordExpr (p, t, l) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a {%a}@]" 
        ppos p 
        pp_print_ident t
        (pp_print_list pp_print_field_assign ";@ ") l

    | TupleProject (p, e, f) -> 

      Format.fprintf ppf "%a%a.%%%a" ppos p pp_print_expr e pp_print_expr f

    | Const (p, True) -> ps p "true"
    | Const (p, False) -> ps p "false"
    | Const (p, Num n) -> ps p n
    | Const (p, Dec d) -> ps p d

    | ConvOp (p, ToInt, e) -> p1 p "int" e
    | ConvOp (p, ToUInt8, e) -> p1 p "uint8" e
    | ConvOp (p, ToUInt16, e) -> p1 p "uint16" e
    | ConvOp (p, ToUInt32, e) -> p1 p "uint32" e
    | ConvOp (p, ToUInt64, e) -> p1 p "uint64" e
    | ConvOp (p, ToInt8, e) -> p1 p "int8" e
    | ConvOp (p, ToInt16, e) -> p1 p "int16" e
    | ConvOp (p, ToInt32, e) -> p1 p "int32" e
    | ConvOp (p, ToInt64, e) -> p1 p "int64" e
    | ConvOp (p, ToReal, e) -> p1 p "real" e

    | UnaryOp (p, Not, e) -> p1 p "not" e
    | BinaryOp (p, And, e1, e2) -> p2 p "and" e1 e2
    | BinaryOp (p, Or, e1, e2) -> p2 p "or" e1 e2
    | BinaryOp (p, Xor, e1, e2) -> p2 p "xor" e1 e2
    | BinaryOp (p, Impl, e1, e2) -> p2 p "=>" e1 e2
    | NArityOp (p, OneHot, e) -> pnp p "#" e
    
    | Quantifier (pos, Forall, vars, e) -> 
      Format.fprintf ppf "@[<hv 2>forall@ @[<hv 1>(%a)@]@ %a@]" 
        (pp_print_list pp_print_typed_decl ";@ ") vars
        pp_print_expr e
    | Quantifier (pos, Exists, vars, e) -> 
      Format.fprintf ppf "@[<hv 2>exists@ @[<hv 1>(%a)@]@ %a@]" 
        (pp_print_list pp_print_typed_decl ";@ ") vars
        pp_print_expr e

    | UnaryOp (p, Uminus, e) -> p1 p "-" e
    | BinaryOp (p, Mod, e1, e2) -> p2 p "mod" e1 e2 
    | BinaryOp (p, Minus, e1, e2) -> p2 p "-" e1 e2
    | BinaryOp (p, Plus, e1, e2) -> p2 p "+" e1 e2
    | BinaryOp (p, Div, e1, e2) -> p2 p "/" e1 e2
    | BinaryOp (p, Times, e1, e2) -> p2 p "*" e1 e2
    | BinaryOp (p, IntDiv, e1, e2) -> p2 p "div" e1 e2

    | BinaryOp (p, BVAnd, e1, e2) -> p2 p "&" e1 e2
    | BinaryOp (p, BVOr, e1, e2) -> p2 p "|" e1 e2
    | UnaryOp (p, BVNot, e) -> p1 p "!" e
    | BinaryOp (p, BVShiftL, e1, e2) -> p2 p "shl" e1 e2
    | BinaryOp (p, BVShiftR, e1, e2) -> p2 p "shr" e1 e2

    | TernaryOp (p, Ite, e1, e2, e3) -> p3 p "if" "then" "else" e1 e2 e3
    | TernaryOp (p, With, e1, e2, e3) -> p3 p "with" "then" "else" e1 e2 e3

    | CompOp (p, Eq, e1, e2) -> p2 p "=" e1 e2
    | CompOp (p, Neq, e1, e2) -> p2 p "<>" e1 e2
    | CompOp (p, Lte, e1, e2) -> p2 p "<=" e1 e2
    | CompOp (p, Lt, e1, e2) -> p2 p "<" e1 e2
    | CompOp (p, Gte, e1, e2) -> p2 p ">=" e1 e2
    | CompOp (p, Gt, e1, e2) -> p2 p ">" e1 e2

    | When (p, e1, e2) ->
      Format.fprintf ppf "%a %a when %a"
        ppos p
        pp_print_expr e1
        pp_print_clock_expr e2

    | Current (p, e) -> p1 p "current" e
    | Condact (p, e1, er, n, e2, e3) -> 
  
      Format.fprintf ppf 
        "%acondact(%a,(restart %a every %a)(%a),%a)" 
        ppos p
        pp_print_expr e1
        pp_print_ident n
        pp_print_expr er
        (pp_print_list pp_print_expr ",@ ") e2
        (pp_print_list pp_print_expr ",@ ") e3

    | Activate (p, i, c, r, l) ->

      Format.fprintf ppf
        "(activate (restart %a every %a) every %a) (%a)"
        pp_print_ident i
        pp_print_expr r
        pp_print_expr c
        (pp_print_list pp_print_expr ",@ ") l 
        
    | Merge (p, c, l) ->

      Format.fprintf ppf
        "merge(%a,@ %a)"
        pp_print_ident c
        (pp_print_list (fun fmt (c,e) ->
             Format.fprintf fmt "%a -> %a"
               pp_print_ident c
               pp_print_expr e) ",@ ") l 

    | RestartEvery (p, i, l, c) ->
      Format.fprintf ppf
        "(restart %a every %a)(%a)"
        pp_print_ident i
        pp_print_expr c
        (pp_print_list pp_print_expr ",@ ") l 

    | Pre (p, e) -> p1 p "pre" e
    | Last (p, id) ->
      Format.fprintf ppf "last %a%a" ppos p pp_print_ident id
    | Fby (p, e1, i, e2) -> 

      Format.fprintf ppf 
        "%afby(p, %a,@ %d,@ %a)" 
        ppos p 
        pp_print_expr e1 
        i 
        pp_print_expr e2

    | Arrow (p, e1, e2) -> p2 p "->" e1 e2

    | Call (p, id, l) ->

      Format.fprintf ppf 
        "%a%a(%a)" 
        ppos p
        pp_print_ident id
        (pp_print_list pp_print_expr ",@ ") l

    | CallParam (p, id, t, l) -> 

      Format.fprintf ppf 
        "%a%a<<%a>>(%a)" 
        ppos p
        pp_print_ident id
        (pp_print_list pp_print_lustre_type "@ ") t
        (pp_print_list pp_print_expr ",@ ") l
        

(* Pretty-print an array slice *)
and pp_print_array_slice ppf (l, u) =
  if l = u then
    Format.fprintf ppf "%a" pp_print_expr l
  else
    Format.fprintf ppf "%a..%a" pp_print_expr l pp_print_expr u

and pp_print_field_assign ppf (i, e) = 

  Format.fprintf ppf 
    "@[<hv 2>%a =@ %a@]"
    pp_print_index i
    pp_print_expr e


(* Pretty-print a Lustre type *)
and pp_print_lustre_type ppf = function

  | Bool pos -> Format.fprintf ppf "bool"

  | Int pos -> Format.fprintf ppf "int"

  | UInt8 pos -> Format.fprintf ppf "uint8"

  | UInt16 pos -> Format.fprintf ppf "uint16"

  | UInt32 pos -> Format.fprintf ppf "uint32"

  | UInt64 pos -> Format.fprintf ppf "uint64"

  | Int8 pos -> Format.fprintf ppf "int8"

  | Int16 pos -> Format.fprintf ppf "int16"

  | Int32 pos -> Format.fprintf ppf "int32"

  | Int64 pos -> Format.fprintf ppf "int64"

  | IntRange (pos, l, u) -> 

    Format.fprintf ppf 
      "subrange [%a,%a] of int" 
      pp_print_expr l
      pp_print_expr u

  | Real pos -> Format.fprintf ppf "real"

  | UserType (pos, s) -> 

    Format.fprintf ppf "%a" pp_print_ident s

  | AbstractType (pos, s) ->

    Format.fprintf ppf "%a" pp_print_ident s

  | TupleType (pos, l) -> 

    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_lustre_type ",@ ") l

  | RecordType (pos, l) -> 

    Format.fprintf ppf 
      "struct @[<hv 2>{ %a }@]" 
      (pp_print_list pp_print_typed_ident ";@ ") l

  | ArrayType (pos, (t, e)) -> 

    Format.fprintf ppf 
      "%a^%a" 
      pp_print_lustre_type t 
      pp_print_expr e

  | EnumType (pos, _, l) -> 

    Format.fprintf ppf 
      "enum @[<hv 2>{ %a }@]" 
      (pp_print_list Format.pp_print_string ",@ ") l


(* Pretty-print a typed identifier *)
and pp_print_typed_ident ppf (p, s, t) = 
  Format.fprintf ppf 
    "@[<hov 2>%s:@ %a@]" 
    s 
    pp_print_lustre_type t


(* Pretty-print a typed identifier *)
and pp_print_typed_decl ppf (p, s, t) = 
  Format.fprintf ppf 
    "@[<hov 2>%s:@ %a@]" 
    s 
    pp_print_lustre_type t


(* Pretty-print a typed identifier with a clock *)
and pp_print_clocked_typed_ident ppf (pos, s, t, c) = 
  Format.fprintf ppf 
    "@[<hov 2>%a:@ %a%a@]" 
    pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


(* Pretty-print a typed identifier with a clock, possibly constant *)
and pp_print_const_clocked_typed_ident ppf (pos, s, t, c, o) = 
  Format.fprintf ppf "@[<hov 2>%t%a:@ %a%a@]" 
    (function ppf -> if o then Format.fprintf ppf "const ")
    pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


and pp_print_label_or_index ppf = function 

  | Label (pos, i) -> pp_print_index ppf i
  | Index (pos, e) -> pp_print_expr ppf e

(* Pretty-print a type declaration *)
let pp_print_type_decl ppf = function

  | AliasType (pos, s, t) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | FreeType (pos, t) -> 

    Format.fprintf ppf "%a" pp_print_ident t 


(* Pretty-print a variable declaration *)
let pp_print_var_decl ppf = function 

  | (pos, s, t, c) -> 

    Format.fprintf ppf 
      "@[<hov 2>%a:@ %a%a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_clock_expr c


(* Pretty-print a constant declaration *)
let pp_print_const_decl ppf = function

  | FreeConst (pos, s, t) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (pos, s, e) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (pos, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e


(* Pretty-print a single static node parameter *)
let pp_print_node_param ppf = function

  | TypeParam t ->
    Format.fprintf ppf "type %a" pp_print_ident t


(* Pretty-print a list of static node parameters *)
let pp_print_node_param_list ppf = function

  | [] -> ()

  | l ->
    
    Format.fprintf ppf
      "@[<hv 2><<%a>>@]"
      (pp_print_list pp_print_node_param ";@ ") l


(* Pretty-print a node-local variable declaration, skip others *)
let pp_print_node_local_decl_var ppf = function

  | NodeVarDecl (pos, v) -> pp_print_var_decl ppf v

  | _ -> ()


(* Pretty-print a node-local constant declaration, skip others *)
let pp_print_node_local_decl_const ppf = function

  | NodeConstDecl (pos, c) -> pp_print_const_decl ppf c

  | _ -> ()


(* Pretty-print a node-local declaration *)
let pp_print_node_local_decl ppf l = 

  let c, v = 
    List.partition (function NodeConstDecl _ -> true | _ -> false) l 
  in

  if c = [] then () else 

    Format.fprintf ppf 
      "%a@ " 
      (pp_print_list pp_print_node_local_decl_const "@;<1 -2>") c;

  if v = [] then () else 

    Format.fprintf ppf
      "@[<hv 2>var@ %a@]@ "
      (pp_print_list pp_print_node_local_decl_var "@ ") v 


let pp_print_array_def_index ppf ident =

  Format.fprintf ppf
    "[%a]"
    pp_print_ident ident


let rec pp_print_struct_item ppf = function

  | SingleIdent (pos, s) -> Format.fprintf ppf "%a" pp_print_ident s

  | TupleStructItem (pos, l) -> 

    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_struct_item ",@ ") l

  | TupleSelection (pos, e, i) -> 

    Format.fprintf ppf
      "%a[%a]"
      pp_print_ident e
      pp_print_expr i

  | FieldSelection (pos, e, i) -> 

    Format.fprintf ppf
      "%a.%a"
      pp_print_ident e
      pp_print_ident i

  | ArraySliceStructItem (pos, e, i) -> 

    Format.fprintf ppf
      "%a@[<hv 1>[%a]@]" 
      pp_print_ident e
      (pp_print_list pp_print_array_slice ",@ ") i
                            
  | ArrayDef (pos, i, l) ->

    Format.fprintf ppf
      "%a%a"
      pp_print_ident i
      (pp_print_list pp_print_array_def_index "") l


let pp_print_eq_lhs ppf = function

  | StructDef (pos, [l]) ->
    pp_print_struct_item ppf l
      
  | StructDef (pos, l) ->
    Format.fprintf ppf "(%a)"
      (pp_print_list pp_print_struct_item ",") l
  

let rec pp_print_body ppf = function

  | Assert (pos, e) -> 

    Format.fprintf ppf "assert %a;" pp_print_expr e

  | Equation (pos, lhs, e) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a;@]" 
      pp_print_eq_lhs lhs
      pp_print_expr e

  | Automaton (_, name, states, returns) ->
    pp_print_automaton ppf name states returns


(* Pretty-print a node equation *)
and pp_print_node_item ppf = function
  
  | Body b -> pp_print_body ppf b

  | AnnotMain true -> Format.fprintf ppf "--%%MAIN;"

  | AnnotMain false -> Format.fprintf ppf "--!MAIN : false;"

  | AnnotProperty (pos, None, e) ->
    Format.fprintf ppf "--%%PROPERTY %a;" pp_print_expr e 

  | AnnotProperty (pos, Some name, e) ->
    Format.fprintf ppf "--%%PROPERTY \"%s\" %a;" name pp_print_expr e 


and pp_print_automaton ppf name states returns =
  Format.fprintf ppf "@[<hv 2>automaton %s@.%a@]returns %a;"
    (match name with Some n -> n | None -> "")
    pp_print_states states
    pp_print_auto_returns returns


and pp_print_auto_returns ppf = function
  | Given l -> pp_print_list pp_print_ident "," ppf l
  | Inferred -> Format.fprintf ppf ".."

and pp_print_states ppf =
  pp_print_list pp_print_state "@." ppf


and pp_print_state ppf =
  function State (_, name, init, locals, eqs, unless, until) ->
    Format.fprintf ppf "state %s@.@[<hv 2>%a%a@[<hv 2>let@.%a@]@.tel@]@.%a@?" name
      (pp_print_auto_trans "unless") unless
      pp_print_node_local_decl locals
      (pp_print_list pp_print_body "@ ") eqs
      (pp_print_auto_trans "until") until

and pp_print_auto_trans kind ppf = function
  | None -> ()
  | Some (_, br) ->
    Format.fprintf ppf "%s %a;@." kind pp_print_transition_branch br

and pp_print_transition_branch ppf = function
  | Target (TransRestart (_, (_, t))) -> Format.fprintf ppf "restart %s" t
  | Target (TransResume (_, (_, t))) -> Format.fprintf ppf "resume %s" t
  | TransIf (_, e, br, None) ->
    Format.fprintf ppf "if@ %a@ %a"
      pp_print_expr e
      pp_print_transition_branch br
  | TransIf (_, e, br, Some br2) ->
    Format.fprintf ppf "if@ %a@ %a@ else@ %a@ end"
      pp_print_expr e
      pp_print_transition_branch br
      pp_print_transition_branch br2


let pp_print_contract_ghost_const ppf = function 

  | FreeConst (pos, s, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (pos, s, e) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (pos, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e

    
let pp_print_contract_ghost_var ppf = function 

  | FreeConst (pos, s, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (pos, s, e) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (pos, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e

    
let pp_print_contract_assume ppf (_, n, s, e) =
  Format.fprintf
    ppf
    "@[<hv 3>%sassume%s@ %a;@]"
    (if s then "weakly " else "")
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

let pp_print_contract_guarantee ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>guarantee%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

    
let pp_print_contract_require ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>require%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

let pp_print_contract_ensure ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>ensure%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

let cond_new_line b fmt () =
  if b then Format.fprintf fmt "@ " else Format.fprintf fmt ""

let pp_print_contract_mode ppf (_, id, reqs, enss) =
  Format.fprintf
    ppf
    "@[<hv 2>mode %a (%a%a%a%a@]%a) ;"
    pp_print_ident id
    (cond_new_line (reqs <> [])) ()
    (pp_print_list pp_print_contract_require "@ ") reqs
    (cond_new_line (enss <> [])) ()
    (pp_print_list pp_print_contract_ensure "@ ") enss
    (cond_new_line ((reqs,enss) <> ([],[]))) ()

let pp_print_contract_call fmt (_, id, in_params, out_params) =
  Format.fprintf
    fmt "@[<hov 2>import %a (@,%a@,) returns (@,%a@,) ;@]"
    pp_print_ident id
    (pp_print_list pp_print_expr ", ") in_params
    (pp_print_list pp_print_expr ", ") out_params

let all_empty = List.for_all (fun l -> l = [])

let pp_print_contract_item fmt = function
  | GhostConst c -> pp_print_contract_ghost_const fmt c
  | GhostVar v -> pp_print_contract_ghost_var fmt v
  | Assume a -> pp_print_contract_assume fmt a
  | Guarantee g -> pp_print_contract_guarantee fmt g
  | Mode m -> pp_print_contract_mode fmt m
  | ContractCall call -> pp_print_contract_call fmt call


let pp_print_contract fmt contract =
  Format.fprintf fmt "@[<v>%a@]"
    (pp_print_list pp_print_contract_item "@ ") contract


let pp_print_contract_spec ppf = function
| None -> ()
| Some contract ->
  Format.fprintf 
    ppf
    "@[<v 2>(*@contract@ %a@]@ *)@ "
    pp_print_contract contract


(* Pretty-prints a contract node. *)
let pp_print_contract_node_decl ppf (n,p,i,o,e)
 =
     Format.fprintf
       ppf
       "@[<hv>@[<hv 2>contract %a%t@ \
        @[<hv 1>(%a)@]@;<1 -2>\
        returns@ @[<hv 1>(%a)@];@]@.\
        @[<hv 2>let@ \
        %a@;<1 -2>\
        tel;@]@]@?"
       pp_print_ident n
       (function ppf -> pp_print_node_param_list ppf p)
       (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
       (pp_print_list pp_print_clocked_typed_ident ";@ ") o
       pp_print_contract e


let pp_print_node_or_fun_decl is_fun ppf (
  pos, (n, ext, p, i, o, l, e, r)
) =
    if e = [] then
      Format.fprintf ppf
        "@[<hv>@[<hv 2>%s%s %a%t@ \
        @[<hv 1>(%a)@]@;<1 -2>\
        returns@ @[<hv 1>(%a)@];@]@.\
        %a@?\
        %a@?@]@?"
        (if is_fun then "function" else "node")
        (if ext then " imported" else "")
        pp_print_ident n 
        (function ppf -> pp_print_node_param_list ppf p)
        (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
        (pp_print_list pp_print_clocked_typed_ident ";@ ") o
        pp_print_contract_spec r
        pp_print_node_local_decl l
    else
      Format.fprintf ppf
        "@[<hv>@[<hv 2>%s%s %a%t@ \
        @[<hv 1>(%a)@]@;<1 -2>\
        returns@ @[<hv 1>(%a)@];@]@.\
        %a@?\
        %a@?\
        @[<v 2>let@ \
        %a@;<1 -2>\
        tel;@]@]@?"
        (if is_fun then "function" else "node")
        (if ext then " imported" else "")
        pp_print_ident n 
        (function ppf -> pp_print_node_param_list ppf p)
        (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
        (pp_print_list pp_print_clocked_typed_ident ";@ ") o
        pp_print_contract_spec r
        pp_print_node_local_decl l
        (pp_print_list pp_print_node_item "@ ") e


(* Pretty-print a declaration *)
let pp_print_declaration ppf = function

  | TypeDecl (pos, t) -> 

    Format.fprintf ppf "type %a;" pp_print_type_decl t

  | ConstDecl (pos, c) -> pp_print_const_decl ppf c

  | NodeDecl (pos, decl) ->
    pp_print_node_or_fun_decl false ppf (pos, decl)

  | FuncDecl (pos, decl) ->
    pp_print_node_or_fun_decl true ppf (pos, decl)

  | ContractNodeDecl (pos, decl) ->
    pp_print_contract_node_decl ppf decl

  | NodeParamInst (pos, (n, s, p)) -> 

    Format.fprintf ppf
      "@[<hv>@[<hv 2>node %a =@ %a@[<hv 2><<%a>>@];@]" 
      pp_print_ident n 
      pp_print_ident n 
      (pp_print_list pp_print_lustre_type "@ ") p


let pp_print_program ppf p =

  Format.fprintf ppf
    "@[<v>%a@]" 
    (pp_print_list pp_print_declaration "@ ") 
    p




(***********)
(* Helpers *)
(***********)

let pos_of_expr = function
  | Ident (pos , _) | ModeRef (pos , _ ) | RecordProject (pos , _ , _)
  | TupleProject (pos , _ , _) | StructUpdate (pos , _ , _ , _) | Const (pos, _)
  | ConvOp (pos , _, _) | GroupExpr (pos , _, _ ) | ArrayConstr (pos , _ , _ )
  | ArraySlice (pos , _ , _) | ArrayConcat (pos , _ , _)
  | RecordExpr (pos , _ , _) | UnaryOp (pos , _, _) | BinaryOp (pos , _, _ , _)
  | NArityOp (pos , _, _ ) | TernaryOp (pos , _, _ , _ , _) | CompOp (pos , _, _ , _)
  | Quantifier (pos, _, _, _)
  | When (pos , _ , _) | Current (pos , _) | Condact (pos , _ , _ , _ , _, _)
  | Activate (pos , _ , _ , _ , _) | Merge (pos , _ , _ ) | Pre (pos , _)
  | Last (pos , _) | RestartEvery (pos, _, _, _)
  | Fby (pos , _ , _ , _) | Arrow (pos , _ , _) | Call (pos , _ , _ )
  | CallParam (pos , _ , _ , _ )
    -> pos


let rec has_unguarded_pre ung = function
  | Const _ | Ident _ | ModeRef _ -> false
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | Quantifier (_, _, _, e) -> has_unguarded_pre ung e

  | TupleProject (_, e1, e2) | BinaryOp (_, _, e1, e2) | ArrayConstr (_, e1, e2) 
  | CompOp (_, _, e1, e2) | ArrayConcat (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2

  | TernaryOp (_, _, e1, e2, e3)
  | ArraySlice (_, e1, (e2, e3)) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    let u3 = has_unguarded_pre ung e3 in
    u1 || u2 || u3
  
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
    let us = List.map (has_unguarded_pre ung) l in
    List.exists Lib.identity us

  | Merge (_, _, l) ->
    let us = List.map (has_unguarded_pre ung) (List.map snd l) in
    List.exists Lib.identity us

  | RestartEvery (_, _, l, e) ->
    let us = List.map (has_unguarded_pre ung) (e :: l) in
    List.exists Lib.identity us

  | Activate (_, _, e, r, l)  ->
    let us = List.map (has_unguarded_pre ung) (e :: r :: l) in
    List.exists Lib.identity us

  | Condact (_, e, r, _, l1, l2) ->
    let us = List.map (has_unguarded_pre ung) (e :: r :: l1 @ l2) in
    List.exists Lib.identity us

  | RecordExpr (_, _, ie) ->
    let us = List.map (fun (_, e) -> has_unguarded_pre ung e) ie in
    List.exists Lib.identity us

  | StructUpdate (_, e1, li, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let us = List.map (function
        | Label _ -> false
        | Index (_, e) -> has_unguarded_pre ung e
      ) li in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2 || List.exists Lib.identity us

  | Fby (_, e1, _, e2) ->
    let u1, u2 = has_unguarded_pre ung e1, has_unguarded_pre ung e2 in
    u1 || u2

  | Pre (pos, e) as p ->
    if ung then begin
      (* Fail only if in strict mode *)
      let err_or_warn =
        if Flags.lus_strict () then error_at_position else warn_at_position in

      err_or_warn pos
        (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]"
           pp_print_expr p)
    end;

    let u = has_unguarded_pre true e in
    ung || u

  | Last _ -> false

  (* TODO: Only report unguarded lasts contained in automaton states
     that are activable at the initial state *)
(*
  | Last (pos, _) as p ->
    if ung then begin
      (* Fail only if in strict mode *)
      let err_or_warn =
        if Flags.lus_strict () then error_at_position else warn_at_position in

      err_or_warn pos
        (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]"
           pp_print_expr p)
    end;
    ung
*)
    
  | Arrow (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre false e1 in
    u1 || u2

let has_unguarded_pre e =
  let u = has_unguarded_pre true e in
  if u && Flags.lus_strict () then raise Parser_error;
  u

(** If second argument is `Some _`, returns that. Otherwise runs `f`. *)
let unwrap_or f = function
| None -> f ()
| res -> res

(** If input list contains `Some _`, returns that. Otherwise returns `None`. *)
let some_of_list = List.fold_left (
  function
  | None -> Lib.identity
  | res -> (fun _ -> res)
) None

(** Checks whether an expression has a `pre` or a `->`. *)
let rec has_pre_or_arrow = function
  | Const _ | Ident _ | ModeRef _ -> None
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | Quantifier (_, _, _, e) ->
    has_pre_or_arrow e

  | TupleProject (_, e1, e2) | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) 
  | ArrayConcat (_, e1, e2) | ArrayConstr (_, e1, e2)  -> (
    match has_pre_or_arrow e1 with
    | None -> has_pre_or_arrow e2
    | res -> res
  )

  | TernaryOp (_, _, e1, e2, e3) | ArraySlice (_, e1, (e2, e3)) ->
    has_pre_or_arrow e1
    |> unwrap_or (
      fun _ ->
        has_pre_or_arrow e2
        |> unwrap_or (
          fun _ -> has_pre_or_arrow e3
        )
    )
  
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
    List.map has_pre_or_arrow l
    |> some_of_list

  | Merge (_, _, l) ->
    List.map has_pre_or_arrow (List.map snd l)
    |> some_of_list

  | RestartEvery (_, _, l, e) ->
    List.map has_pre_or_arrow (e :: l)
    |> some_of_list

  | Activate (_, _, e, r, l) ->
    List.map has_pre_or_arrow (e :: r :: l)
    |> some_of_list

  | Condact (_, e, r, _, l1, l2) ->
    List.map has_pre_or_arrow (e :: r :: l1 @ l2)
    |> some_of_list

  | RecordExpr (_, _, ie) ->
    List.map (fun (_, e) -> has_pre_or_arrow e) ie
    |> some_of_list

  | StructUpdate (_, e1, li, e2) ->
    has_pre_or_arrow e1
    |> unwrap_or (
      fun _ ->
        has_pre_or_arrow e2
        |> unwrap_or (
          fun _ ->
            List.map (function
              | Label _ -> None
              | Index (_, e) -> has_pre_or_arrow e
            ) li
            |> some_of_list
        )
    )

  | Fby (_, e1, _, e2) ->
    has_pre_or_arrow e1
    |> unwrap_or (fun _ -> has_pre_or_arrow e2)

  | Pre (pos, _) | Last (pos, _) -> Some pos

  | Arrow (pos, e1, e2) -> Some pos


(** Returns identifiers under a last operator *)
let rec lasts_of_expr acc = function
  | Const _ | Ident _ | ModeRef _ -> acc
    
  | RecordProject (_, e, _) | ConvOp (_, _, e)
  | UnaryOp (_, _, e) | Current (_, e) | When (_, e, _)
  | Quantifier (_, _, _, e) ->
    lasts_of_expr acc e

  | TupleProject (_, e1, e2) | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2) 
  | ArrayConcat (_, e1, e2) | ArrayConstr (_, e1, e2)  ->
    lasts_of_expr (lasts_of_expr acc e1) e2

  | TernaryOp (_, _, e1, e2, e3) | ArraySlice (_, e1, (e2, e3)) ->
    lasts_of_expr (lasts_of_expr (lasts_of_expr acc e1) e2) e3
  
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
    List.fold_left lasts_of_expr acc l

  | Merge (_, _, l) ->
    List.fold_left (fun acc (_, e) -> lasts_of_expr acc e) acc l

  | RestartEvery (_, _, l, e) ->
    List.fold_left lasts_of_expr acc (e :: l)

  | Activate (_, _, e, r, l) ->
    List.fold_left lasts_of_expr acc (e :: r :: l)

  | Condact (_, e, r, _, l1, l2) ->
    List.fold_left lasts_of_expr acc (e :: r :: l1 @ l2)

  | RecordExpr (_, _, ie) ->
    List.fold_left (fun acc (_, e) -> lasts_of_expr acc e) acc ie

  | StructUpdate (_, e1, li, e2) ->
    let acc = lasts_of_expr (lasts_of_expr acc e1) e2 in
    List.fold_left (fun acc -> function
        | Label _ -> acc
        | Index (_, e) -> lasts_of_expr acc e
      ) acc li
    
  | Fby (_, e1, _, e2) ->
    lasts_of_expr (lasts_of_expr acc e1) e2

  | Pre (pos, e) -> lasts_of_expr acc e
                      
  | Last (pos, i) -> SI.add i acc

  | Arrow (pos, e1, e2) ->
    lasts_of_expr (lasts_of_expr acc e1) e2


let rec replace_lasts allowed prefix acc ee = match ee with
  | Const _ | Ident _ | ModeRef _ ->
    ee, acc
    
  | RecordProject (pos, e, i) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else RecordProject (pos, e', i), acc'
         
  | ConvOp (pos, op, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else ConvOp (pos, op, e'), acc'

  | UnaryOp (pos, op, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else UnaryOp (pos, op, e'), acc'

  | Current (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Current (pos, e'), acc'

  | When (pos, e, c) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else When (pos, e', c), acc'

  | Quantifier (pos, q, vs, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Quantifier (pos, q, vs, e'), acc'

  | TupleProject (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else TupleProject (pos, e1', e2'), acc'

  | ArrayConstr (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else ArrayConstr (pos, e1', e2'), acc'

  | BinaryOp (pos, op, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else BinaryOp (pos, op, e1', e2'), acc'

  | CompOp (pos, op, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else CompOp (pos, op, e1', e2'), acc'

  | ArrayConcat (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else ArrayConcat (pos, e1', e2'), acc'

  | TernaryOp (pos, op, e1, e2, e3) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    let e3', acc' = replace_lasts allowed prefix acc' e3 in
    if e1 == e1' && e2 == e2' && e3 == e3' then ee, acc
    else TernaryOp (pos, op, e1', e2', e3'), acc'

  | ArraySlice (pos, e1, (e2, e3)) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    let e3', acc' = replace_lasts allowed prefix acc' e3 in
    if e1 == e1' && e2 == e2' && e3 == e3' then ee, acc
    else ArraySlice (pos, e1', (e2', e3')), acc'
  
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    if try List.for_all2 (==) l l' with _ -> false then ee, acc
    else (match ee with
        | GroupExpr (pos, g, l) -> GroupExpr (pos, g, l')
        | NArityOp (pos, op, l) -> NArityOp (pos, op, l')
        | Call (pos, n, l) -> Call (pos, n, l')
        | CallParam (pos, n, t, l) -> CallParam (pos, n, t, l')
        | _ -> assert false
      ), acc'

  | Merge (pos, c, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) (c, e) ->
          let e, acc = replace_lasts allowed prefix acc e in
          (c, e) :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    if try List.for_all2 (fun (_, x) (_, x') -> x == x') l l' with _ -> false
    then ee, acc
    else Merge (pos, c, l'), acc'

  | RestartEvery (pos, n, l, e) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    let e', acc' = replace_lasts allowed prefix acc' e in
    if try e == e' && List.for_all2 (==) l l'  with _ -> false then ee, acc
    else RestartEvery (pos, n, l', e'), acc

  | Activate (pos, n, e, r, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    let e', acc' = replace_lasts allowed prefix acc' e in
    let r', acc' = replace_lasts allowed prefix acc' r in
    if try e == e' && r == r' &&
           List.for_all2 (==) l l'  with _ -> false then ee, acc
    else Activate (pos, n, e', r', l'), acc'

  | Condact (pos, e, r, n, l1, l2) ->
    let l1', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l1 in
    let l1' = List.rev l1 in
    let l2', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc') l2 in
    let l2' = List.rev l2 in
    let e', acc' = replace_lasts allowed prefix acc' e in
    let r', acc' = replace_lasts allowed prefix acc' r in
    if try e == e' && r == r' &&
           List.for_all2 (==) l1 l1' &&
           List.for_all2 (==) l2 l2'
      with _ -> false then ee, acc
    else Condact (pos, e', r', n, l1', l2'), acc'

  | RecordExpr (pos, n, ie) ->
    let ie', acc' =
      List.fold_left (fun (ie, acc) (i, e) ->
          let e, acc = replace_lasts allowed prefix acc e in
          (i, e) :: ie, acc
        ) ([], acc) ie in
    let ie' = List.rev ie' in
    if try List.for_all2 (fun (_, e) (_, e') -> e == e') ie ie' with _ -> false
    then ee, acc
    else RecordExpr (pos, n, ie'), acc'

  | StructUpdate (pos, e1, li, e2) ->
    let li', acc' =
      List.fold_left (fun (li, acc) -> function
          | Label _ as s -> s :: li, acc
          | Index (i, e) as s ->
            let e', acc' = replace_lasts allowed prefix acc e in
            if e == e' then s :: li, acc
            else Index (i, e') :: li, acc
        ) ([], acc) li in
    let li' = List.rev li' in
    let e1', acc' = replace_lasts allowed prefix acc' e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if try e1 == e1' && e2 == e2' &&
           List.for_all2 (fun ei ei' -> match ei, ei' with
               | Label _, Label _ -> true
               | Index (_, e), Index (_, e') -> e == e'
               | _ -> false
             ) li li'
      with _ -> false then ee, acc
    else StructUpdate (pos, e1', li', e2'), acc'
        
  | Fby (pos, e1, i, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else Fby (pos, e1', i, e2'), acc'
    
  | Pre (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc else Pre (pos, e'), acc'
                      
  | Last (pos, i) ->
    if not (List.mem i allowed) then
      error_at_position pos
        "Only visible variables in the node are allowed under last";
    let acc = SI.add i acc in
    Ident (pos, prefix ^ ".last." ^ i), acc

  | Arrow (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else Arrow (pos, e1', e2'), acc'



(** Checks whether a struct item has a `pre` or a `->`. *)
let rec struct_item_has_pre_or_arrow = function
| SingleIdent _ | FieldSelection _ | ArrayDef _ -> None
| TupleStructItem (_, l) ->
  List.map struct_item_has_pre_or_arrow l
  |> some_of_list
| ArraySliceStructItem (_, _, l) ->
  List.map (
    fun (e1, e2) ->
      has_pre_or_arrow e1
      |> unwrap_or (fun _ -> has_pre_or_arrow e2)
  ) l
  |> some_of_list
| TupleSelection (_, _, e) -> has_pre_or_arrow e


(** Checks whether a constant declaration has a `pre` or a `->`. *)
let const_decl_has_pre_or_arrow = function
| FreeConst _ -> None
| UntypedConst (_, _, e) -> has_pre_or_arrow e
| TypedConst (_, _, e, _) -> has_pre_or_arrow e



(** Checks whether a node local declaration has a `pre` or a `->`. *)
let node_local_decl_has_pre_or_arrow = function
| NodeConstDecl (_, decl) -> const_decl_has_pre_or_arrow decl
| NodeVarDecl _ -> None


(** Checks whether an equation lhs has a `pre` or a `->`. *)
let eq_lhs_has_pre_or_arrow = function
| StructDef (_, l) ->
  List.map struct_item_has_pre_or_arrow l
  |> some_of_list

(** Checks whether a node equation has a `pre` or a `->`. *)
let node_item_has_pre_or_arrow = function
| Body (Assert (_, e)) -> has_pre_or_arrow e
| Body (Equation (_, lhs, e)) ->
  eq_lhs_has_pre_or_arrow lhs
  |> unwrap_or (fun _ -> has_pre_or_arrow e)
| AnnotMain _ -> None
| AnnotProperty (_, _, e) -> has_pre_or_arrow e
| Body (Automaton _) -> assert false

(** Checks whether a contract node equation has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_node_equation_has_pre_or_arrow = function
| GhostConst decl
| GhostVar decl -> const_decl_has_pre_or_arrow decl
| Assume (_, _, _, e)
| Guarantee (_, _, e) -> has_pre_or_arrow e
| Mode (_, _, reqs, enss) ->
  List.map (fun (_, _, e) -> has_pre_or_arrow e) reqs
  |> some_of_list
  |> unwrap_or (
    fun _ ->
      List.map (fun (_, _, e) -> has_pre_or_arrow e) enss
      |> some_of_list
  )
| ContractCall (_, _, ins, outs) ->
  List.map has_pre_or_arrow ins
  |> some_of_list
  |> unwrap_or (
    fun _ ->
      List.map has_pre_or_arrow outs
      |> some_of_list
  )

(** Checks whether a contract has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_has_pre_or_arrow l =
  List.map contract_node_equation_has_pre_or_arrow l
  |> some_of_list


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)

