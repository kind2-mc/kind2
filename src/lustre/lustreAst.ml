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

exception Parser_error


(* ********************************************************************** *)
(* Type declarations                                                      *)
(* ********************************************************************** *)


(* An identifier *)
type ident = HString.t

module SI = struct
  include (Set.Make (struct
               type t = ident
               let compare = HString.compare
             end))
  let flatten: t list -> t = fun sets ->
    List.fold_left union empty sets
end

           
type index = HString.t

let pp_print_ident = HString.pp_print_hstring

let pp_print_index = HString.pp_print_hstring


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

(** A Lustre expression *)
type expr =
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
  | ConvOp of position * conversion_operator * expr
  | CompOp of position * comparison_operator * expr * expr
  | ChooseOp of position * typed_ident * expr * expr option
  (* Structured expressions *)
  | RecordExpr of position * ident * (ident * expr) list
  | GroupExpr of position * group_expr * expr list
  (* Update of structured expressions *)
  | StructUpdate of position * expr * label_or_index list * expr
  | ArrayConstr of position * expr * expr  
  | ArrayIndex of position * expr * expr
  (* Quantified expressions *)
  | Quantifier of position * quantifier * typed_ident list * expr
  (* Clock operators *)
  | When of position * expr * clock_expr
  | Condact of position * expr * expr * ident * expr list * expr list
  | Activate of position * ident * expr * expr * expr list
  | Merge of position * ident * (ident * expr) list
  | RestartEvery of position * ident * expr list * expr
  (* Temporal operators *)
  | Pre of position * expr
  | Arrow of position * expr * expr
  (* Node calls *)
  | Call of position * ident * expr list

(** A Lustre type *)
and lustre_type =
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
  | IntRange of position * expr option * expr option
  | Real of position
  | UserType of position * ident
  | AbstractType of position * ident
  | TupleType of position * lustre_type list
  | GroupType of position * lustre_type list
  | RecordType of position * ident * typed_ident list
  | ArrayType of position * (lustre_type * expr)
  | EnumType of position * ident * ident list
  | TArr of position * lustre_type * lustre_type  


(* A declaration of an unclocked type *)
and typed_ident = position * ident * lustre_type

(* A record field or an array or tuple index *)
and label_or_index = 
  | Label of position * index
  | Index of position * expr

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

(* The left-hand side of an equation in a contract *)
type contract_eq_lhs =
  | GhostVarDec of position * typed_ident list

(* An equation or assertion in the node body *)
type node_equation =
  | Assert of position * expr
  | Equation of position * eq_lhs * expr

type prop_bound =
  | From of int
  | Within of int
  | At of int
  | FromWithin of int * int

type prop_kind =
  | Invariant
  | Reachable of prop_bound option
  | Provided of expr

(* An item in a node declaration *)
type node_item =
  | Body of node_equation
  | IfBlock of position * expr * node_item list * node_item list
  | FrameBlock of position * (position * ident) list * node_equation list * node_item list 
  | AnnotMain of position * bool
  | AnnotProperty of position * HString.t option * expr * prop_kind

(* A contract ghost constant. *)
type contract_ghost_const = const_decl

(* Multiple contract ghost variables declared simultaneously. *)
type contract_ghost_vars = position * contract_eq_lhs * expr

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
  | GhostVars of contract_ghost_vars
  | Assume of contract_assume
  | Guarantee of contract_guarantee
  | Mode of contract_mode
  | ContractCall of contract_call
  | AssumptionVars of contract_assump_vars

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

type span = {
  start_pos : position;
  end_pos : position;
}

(* A declaration as parsed *)
type declaration = 
  | TypeDecl of span * type_decl
  | ConstDecl of span * const_decl
  | NodeDecl of span * node_decl
  | FuncDecl of span * node_decl
  | ContractNodeDecl of span * contract_node_decl
  | NodeParamInst of span * node_param_inst


(* A Lustre program *)
type t = declaration list


(* ********************************************************************** *)
(* Pretty-printing functions                                              *)
(* ********************************************************************** *)


(* Pretty-print a clock expression *)
let pp_print_clock_expr ppf = function
  | ClockTrue -> ()
  | ClockPos s -> Format.fprintf ppf "when %a" pp_print_ident s
  | ClockNeg s -> Format.fprintf ppf "when not %a" pp_print_ident s
  | ClockConstr (s, c) ->
    Format.fprintf ppf "when %a(%a)" pp_print_ident c pp_print_ident s


(* Pretty-print a Lustre expression *)
let rec pp_print_expr ppf = 

  let ppos ppf p =
    (if false then Format.fprintf else Format.ifprintf)
      ppf
      "%a" 
      pp_print_position p
  in

  (* Pretty-print a string *)
  let ps p = Format.fprintf ppf "%a%a" ppos p HString.pp_print_hstring in 

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

  function
    
    | Ident (p, id) -> Format.fprintf ppf "%a%a" ppos p pp_print_ident id

    | ModeRef (p, ids) ->
      Format.fprintf ppf "%a::%a" ppos p (
        pp_print_list pp_print_ident "::"
      ) ids
 
    | GroupExpr (p, ExprList, l) -> Format.fprintf ppf "%a@[<hv 1>(%a)@]" ppos p pl l

    | GroupExpr (p, TupleExpr, l) -> Format.fprintf ppf "%a@[<hv 1>{%a}@]" ppos p pl l

    | GroupExpr (p, ArrayExpr, l) -> Format.fprintf ppf "%a@[<hv 1>[%a]@]" ppos p pl l

    | StructUpdate (_, e1, i, e2) -> 

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

    | ArrayIndex (p, e, l) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a@[<hv 1>[%a]@]@]" 
        ppos p 
        pp_print_expr e
        pp_print_expr l 

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

      Format.fprintf ppf "%a%a.%%%a" ppos p pp_print_expr e Format.pp_print_int f

    | Const (p, True) -> ps p (HString.mk_hstring "true")
    | Const (p, False) -> ps p (HString.mk_hstring "false")
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
    
    | Quantifier (_, Forall, vars, e) -> 
      Format.fprintf ppf "@[<hv 2>forall@ @[<hv 1>(%a)@]@ %a@]" 
        (pp_print_list pp_print_typed_decl ";@ ") vars
        pp_print_expr e
    | Quantifier (_, Exists, vars, e) -> 
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

    | CompOp (p, Eq, e1, e2) -> p2 p "=" e1 e2
    | CompOp (p, Neq, e1, e2) -> p2 p "<>" e1 e2
    | CompOp (p, Lte, e1, e2) -> p2 p "<=" e1 e2
    | CompOp (p, Lt, e1, e2) -> p2 p "<" e1 e2
    | CompOp (p, Gte, e1, e2) -> p2 p ">=" e1 e2
    | CompOp (p, Gt, e1, e2) -> p2 p ">" e1 e2

    | When (p, e1, e2) ->
      Format.fprintf ppf "%a%a %a"
        ppos p
        pp_print_expr e1
        pp_print_clock_expr e2

    | Condact (p, e1, er, n, e2, e3) -> 
  
      Format.fprintf ppf 
        "%acondact(%a,(restart %a every %a)(%a),%a)" 
        ppos p
        pp_print_expr e1
        pp_print_ident n
        pp_print_expr er
        (pp_print_list pp_print_expr ",@ ") e2
        (pp_print_list pp_print_expr ",@ ") e3

    | Activate (_, i, c, r, l) ->

      Format.fprintf ppf
        "(activate (restart %a every %a) every %a) (%a)"
        pp_print_ident i
        pp_print_expr r
        pp_print_expr c
        (pp_print_list pp_print_expr ",@ ") l 
        
    | Merge (_, c, l) ->

      Format.fprintf ppf
        "merge(%a,@ %a)"
        pp_print_ident c
        (pp_print_list (fun fmt (c,e) ->
             Format.fprintf fmt "%a -> %a"
               pp_print_ident c
               pp_print_expr e) ",@ ") l 

    | RestartEvery (_, i, l, c) ->
      Format.fprintf ppf
        "(restart %a every %a)(%a)"
        pp_print_ident i
        pp_print_expr c
        (pp_print_list pp_print_expr ",@ ") l 

    | Pre (p, e) -> p1 p "pre" e

    | Arrow (p, e1, e2) -> p2 p "->" e1 e2

    | Call (p, id, l) ->

      Format.fprintf ppf
        "%a%a(%a)"
        ppos p
        pp_print_ident id
        (pp_print_list pp_print_expr ",@ ") l
    
    | ChooseOp (p, id, e1, Some e2) ->

      Format.fprintf ppf
      "%achoose { %a | %a assuming %a }"
      ppos p
      pp_print_typed_ident id
      pp_print_expr e1
      pp_print_expr e2

    | ChooseOp (p, id, e, None) ->

      Format.fprintf ppf
      "%achoose { %a | %a }"
      ppos p
      pp_print_typed_ident id
      pp_print_expr e

(* Pretty-print an array slice *)
and pp_print_array_slice ppf (l, u) =
    Format.fprintf ppf "%a..%a" pp_print_expr l pp_print_expr u

and pp_print_field_assign ppf (i, e) = 

  Format.fprintf ppf 
    "@[<hv 2>%a =@ %a@]"
    pp_print_index i
    pp_print_expr e


(* Pretty-print a Lustre type *)
and pp_print_lustre_type ppf = function
  | TVar (_, i) -> pp_print_ident ppf i
  | Bool _ -> Format.fprintf ppf "bool"
  | Int _ -> Format.fprintf ppf "int"
  | UInt8 _ -> Format.fprintf ppf "uint8"
  | UInt16 _ -> Format.fprintf ppf "uint16"
  | UInt32 _ -> Format.fprintf ppf "uint32"
  | UInt64 _ -> Format.fprintf ppf "uint64"
  | Int8 _ -> Format.fprintf ppf "int8"
  | Int16 _ -> Format.fprintf ppf "int16"
  | Int32 _ -> Format.fprintf ppf "int32"
  | Int64 _ -> Format.fprintf ppf "int64"
  | IntRange (_, l, u) -> 
    let pp_print_opt ppf expr_opt = (match expr_opt with
      | Some expr -> pp_print_expr ppf expr
      | None -> Format.fprintf ppf "%s" unbounded_limit_string
    )
    in
    Format.fprintf ppf 
      "subrange [%a,%a] of int" 
      pp_print_opt l
      pp_print_opt u
  | Real _ -> Format.fprintf ppf "real"
  | UserType (_, s) -> 
    Format.fprintf ppf "%a" pp_print_ident s
  | AbstractType (_, s) ->
    Format.fprintf ppf "%a" pp_print_ident s
  | TupleType (_, l) -> 
    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_lustre_type ",@ ") l
  | GroupType (_, l) -> 
    Format.fprintf ppf 
      "@[<hv 1>(%a)@]" 
      (pp_print_list pp_print_lustre_type ",@ ") l
  | RecordType (_, i, l) -> 
    Format.fprintf ppf 
      "%a @[<hv 2>{ %a }@]"
      (pp_print_ident) i
      (pp_print_list pp_print_typed_ident ";@ ") l
  | ArrayType (_, (t, e)) -> 
    Format.fprintf ppf 
      "%a^%a" 
      pp_print_lustre_type t 
      pp_print_expr e
  | EnumType (_, _, l) -> 
    Format.fprintf ppf 
      "enum @[<hv 2>{ %a }@]"
      (pp_print_list HString.pp_print_hstring ",@ ") l
  | TArr (_, arg_ty, ret_ty) ->
     Format.fprintf ppf "@[%a->@,%a@]"
       pp_print_lustre_type arg_ty
       pp_print_lustre_type ret_ty 

(* Pretty-print a typed identifier *)
and pp_print_typed_ident ppf (_, s, t) = 
  Format.fprintf ppf 
    "@[<hov 2>%a:@ %a@]" 
    HString.pp_print_hstring s
    pp_print_lustre_type t


(* Pretty-print a typed identifier *)
and pp_print_typed_decl ppf (_, s, t) = 
  Format.fprintf ppf 
    "@[<hov 2>%a:@ %a@]" 
    HString.pp_print_hstring s
    pp_print_lustre_type t


(* Pretty-print a typed identifier with a clock *)
and pp_print_clocked_typed_ident ppf (_, s, t, c) = 
  Format.fprintf ppf 
    "@[<hov 2>%a:@ %a%a@]" 
    pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


(* Pretty-print a typed identifier with a clock, possibly constant *)
and pp_print_const_clocked_typed_ident ppf (_, s, t, c, o) = 
  Format.fprintf ppf "@[<hov 2>%t%a:@ %a%a@]" 
    (function ppf -> if o then Format.fprintf ppf "const ")
    pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


and pp_print_label_or_index ppf = function 

  | Label (_, i) -> pp_print_index ppf i
  | Index (_, e) -> pp_print_expr ppf e

(* Pretty-print a type declaration *)
let pp_print_type_decl ppf = function

  | AliasType (_, s, t) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | FreeType (_, t) -> 

    Format.fprintf ppf "%a" pp_print_ident t 


(* Pretty-print a variable declaration *)
let pp_print_var_decl ppf = function 

  | (_, s, t, c) -> 

    Format.fprintf ppf 
      "@[<hov 2>%a:@ %a%a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_clock_expr c


(* Pretty-print a constant declaration *)
let pp_print_const_decl ppf = function

  | FreeConst (_, s, t) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (_, s, e) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (_, s, e, t) -> 

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

  | NodeVarDecl (_, v) -> pp_print_var_decl ppf v

  | _ -> ()


(* Pretty-print a node-local constant declaration, skip others *)
let pp_print_node_local_decl_const ppf = function

  | NodeConstDecl (_, c) -> pp_print_const_decl ppf c

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

  | SingleIdent (_, s) -> Format.fprintf ppf "%a" pp_print_ident s

  | TupleStructItem (_, l) -> 

    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_struct_item ",@ ") l

  | TupleSelection (_, e, i) -> 

    Format.fprintf ppf
      "%a[%a]"
      pp_print_ident e
      pp_print_expr i

  | FieldSelection (_, e, i) -> 

    Format.fprintf ppf
      "%a.%a"
      pp_print_ident e
      pp_print_ident i

  | ArraySliceStructItem (_, e, i) -> 

    Format.fprintf ppf
      "%a@[<hv 1>[%a]@]" 
      pp_print_ident e
      (pp_print_list pp_print_array_slice ",@ ") i
                            
  | ArrayDef (_, i, l) ->

    Format.fprintf ppf
      "%a%a"
      pp_print_ident i
      (pp_print_list pp_print_array_def_index "") l


let pp_print_eq_lhs ppf = function
  | StructDef (_, [l]) ->
    pp_print_struct_item ppf l
      
  | StructDef (_, l) ->
    Format.fprintf ppf "(%a)"
      (pp_print_list pp_print_struct_item ",") l

let pp_print_contract_eq_lhs ppf = function
  | GhostVarDec (_, [(_, l, _)]) ->
    pp_print_ident ppf l
  
  | GhostVarDec (_, l) ->
    Format.fprintf ppf "(%a)"
      (pp_print_list pp_print_ident ", ") (List.map (fun (_, i, _) -> i) l)

let pp_print_typed_contract_eq_lhs ppf = function
  | GhostVarDec (_, l) ->
    Format.fprintf ppf "%a"
      (pp_print_list pp_print_typed_ident ", ") l


let rec pp_print_node_body ppf = function

  | Assert (_, e) -> 

    Format.fprintf ppf "assert %a;" pp_print_expr e

  | Equation (_, lhs, e) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a;@]" 
      pp_print_eq_lhs lhs
      pp_print_expr e


(* Pretty-print a node equation *)
and pp_print_node_item ppf = function
  
  | Body b -> pp_print_node_body ppf b

  | IfBlock (_, e, l1, []) -> 
    Format.fprintf ppf "if %a then %a fi"  
      pp_print_expr e 
      (pp_print_list pp_print_node_item " ") l1

  | IfBlock (_, e, l1, l2) -> 
    Format.fprintf ppf "if %a then %a else  %a fi"  
      pp_print_expr e 
      (pp_print_list pp_print_node_item " ") l1
      (pp_print_list pp_print_node_item " ") l2

  | FrameBlock (_, vars, nes, nis) -> Format.fprintf ppf "frame (%a) %a let %a tel" 
    (pp_print_list pp_print_ident ", ") (List.map snd vars)
    (pp_print_list pp_print_node_body " ") nes
    (pp_print_list pp_print_node_item " ") nis

  | AnnotMain (_, true) -> Format.fprintf ppf "--%%MAIN;"

  | AnnotMain (_, false) -> Format.fprintf ppf "--!MAIN : false;"

  | AnnotProperty (_, None, e, Invariant) ->
    Format.fprintf ppf "--%%PROPERTY %a;" pp_print_expr e 

  | AnnotProperty (_, None, e, Reachable Some (From b)) ->
    Format.fprintf ppf "--%%PROPERTY reachable %a from %d;" 
    pp_print_expr e 
    b

  | AnnotProperty (_, None, e, Reachable Some (Within b)) ->
    Format.fprintf ppf "--%%PROPERTY reachable %a within %d;" 
    pp_print_expr e 
    b

  | AnnotProperty (_, None, e, Reachable Some (At b)) ->
    Format.fprintf ppf "--%%PROPERTY reachable %a at %d;" 
    pp_print_expr e
    b

  | AnnotProperty (_, None, e, Reachable Some (FromWithin (l, u))) ->
    Format.fprintf ppf "--%%PROPERTY reachable %a from %d within %d;" 
    pp_print_expr e
    l
    u

  | AnnotProperty (_, None, e, Reachable None) ->
    Format.fprintf ppf "--%%PROPERTY reachable %a;" 
    pp_print_expr e

  | AnnotProperty (_, None, e1, Provided e2) ->
    Format.fprintf ppf "--%%PROPERTY %a provided %a;" 
    pp_print_expr e1
    pp_print_expr e2

  | AnnotProperty (_, Some name, e, Invariant) ->
    Format.fprintf ppf "--%%PROPERTY \"%a\" %a;"
      HString.pp_print_hstring name
      pp_print_expr e 

  | AnnotProperty (_, Some name, e, Reachable Some (From b)) ->
    Format.fprintf ppf "--%%PROPERTY reachable \"%a\" %a from %d;"
      HString.pp_print_hstring name
      pp_print_expr e 
      b

  | AnnotProperty (_, Some name, e, Reachable Some (Within b)) ->
    Format.fprintf ppf "--%%PROPERTY reachable \"%a\" %a within %d;"
      HString.pp_print_hstring name
      pp_print_expr e 
      b

  | AnnotProperty (_, Some name, e, Reachable Some (At b)) ->
    Format.fprintf ppf "--%%PROPERTY reachable \"%a\" %a at %d;"
      HString.pp_print_hstring name
      pp_print_expr e 
      b

  | AnnotProperty (_, Some name, e, Reachable Some (FromWithin (l, u))) ->
    Format.fprintf ppf "--%%PROPERTY reachable \"%a\" %a from %d within %d;"
      HString.pp_print_hstring name
      pp_print_expr e 
      l
      u

  | AnnotProperty (_, Some name, e, Reachable None ) ->
    Format.fprintf ppf "--%%PROPERTY reachable \"%a\" %a;"
      HString.pp_print_hstring name
      pp_print_expr e 

  | AnnotProperty (_, Some name, e1, Provided e2 ) ->
    Format.fprintf ppf "--%%PROPERTY \"%a\" %a provided %a;"
      HString.pp_print_hstring name
      pp_print_expr e1 
      pp_print_expr e2


let pp_print_contract_ghost_const ppf = function 

  | FreeConst (_, s, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (_, s, e) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (_, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e


let pp_print_contract_ghost_vars ppf = fun (_, lhs, e) ->
  Format.fprintf ppf 
  "@[<hv 3>var %a =@ %a;@]" 
  pp_print_typed_contract_eq_lhs lhs
  pp_print_expr e

    
let pp_print_contract_assume ppf (_, n, s, e) =
  Format.fprintf
    ppf
    "@[<hv 3>%sassume%s@ %a;@]"
    (if s then "weakly " else "")
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
    pp_print_expr e

let pp_print_contract_guarantee ppf (_, n, s, e) =
  Format.fprintf
    ppf
    "@[<hv 3>%sguarantee%s@ %a;@]"
    (if s then "weakly " else "")
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
    pp_print_expr e

    
let pp_print_contract_require ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>require%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
    pp_print_expr e

let pp_print_contract_ensure ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>ensure%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""
      ^ (HString.string_of_hstring s)
      ^ "\"")
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
    (pp_print_list pp_print_ident ", ") out_params

let pp_print_contract_assump_vars fmt (_, vars) =
  Format.fprintf
    fmt "@[<hov 2>assumption_vars %a ;@]"
    (pp_print_list pp_print_ident ", ")
    (List.map (fun (_,v) -> v) vars)

let pp_print_contract_item fmt = function
  | GhostConst c -> pp_print_contract_ghost_const fmt c
  | GhostVars vs -> pp_print_contract_ghost_vars fmt vs
  | Assume a -> pp_print_contract_assume fmt a
  | Guarantee g -> pp_print_contract_guarantee fmt g
  | Mode m -> pp_print_contract_mode fmt m
  | ContractCall call -> pp_print_contract_call fmt call
  | AssumptionVars vars -> pp_print_contract_assump_vars fmt vars


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
  _, (n, ext, p, i, o, l, e, r)
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

  | TypeDecl (_, t) -> 

    Format.fprintf ppf "type %a;" pp_print_type_decl t

  | ConstDecl (_, c) -> pp_print_const_decl ppf c

  | NodeDecl (span, decl) ->
    pp_print_node_or_fun_decl false ppf (span, decl)

  | FuncDecl (span, decl) ->
    pp_print_node_or_fun_decl true ppf (span, decl)

  | ContractNodeDecl (_, decl) ->
    pp_print_contract_node_decl ppf decl

  | NodeParamInst (_, (n, _, p)) -> 

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

let string_of_expr e = string_of_t pp_print_expr e 
    
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)

