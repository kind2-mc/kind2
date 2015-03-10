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

exception Parser_error

(* ********************************************************************** *)
(* Type declarations                                                      *)
(* ********************************************************************** *)


(* An identifier *)
type ident = string

type index = string

let pp_print_ident = Format.pp_print_string

let pp_print_index = Format.pp_print_string



(* A Lustre expression *)
type expr =

  (* Identifier *)
  | Ident of position * ident
  | RecordProject of position * expr * index
  | TupleProject of position * expr * expr

  (* Values *)
  | True of position
  | False of position
  | Num of position * string
  | Dec of position * string

  (* Conversions *)
  | ToInt of position * expr
  | ToReal of position * expr

  (* List of expressions *)
  | ExprList of position * expr list 

  (* Tuple expression *)
  | TupleExpr of position * expr list 

  (* Array expression *)
  | ArrayExpr of position * expr list 

  (* Array expression *)
  | ArrayConstr of position * expr * expr 

  (* Slice of array *)
  | ArraySlice of position * expr * (expr * expr) 

  (* Array concatenation *)
  | ArrayConcat of position * expr * expr

  (* Record expression *)
  | RecordExpr of position * ident * (ident * expr) list

  (* Boolean operators *)
  | Not of position * expr 
  | And of position * expr * expr 
  | Or of position * expr * expr
  | Xor of position * expr * expr 
  | Impl of position * expr * expr 
  | OneHot of position * expr list

  (* Arithmetic operators *)
  | Uminus of position * expr 
  | Mod of position * expr * expr
  | Minus of position * expr * expr
  | Plus of position * expr * expr
  | Div of position * expr * expr
  | Times of position * expr * expr
  | IntDiv of position * expr * expr

  (* If operator *)
  | Ite of position * expr * expr * expr 

  (* With operator for recursive definitions *)
  | With of position * expr * expr * expr 

  (* Relations *)
  | Eq of position * expr * expr 
  | Neq of position * expr * expr
  | Lte of position * expr * expr
  | Lt of position * expr * expr
  | Gte of position * expr * expr
  | Gt of position * expr * expr

  (* Clock operators *)
  | When of position * expr * expr 
  | Current of position * expr
  | Condact of position * expr * ident * expr list * expr list 
  
  (* Temporal operators *)
  | Pre of position * expr 
  | Fby of position * expr * int * expr 
  | Arrow of position * expr * expr 

  (* A node call *)
  | Call of position * ident * expr list 

  (* A node call setting static parameters *)
  | CallParam of position * ident * lustre_type list * expr list 


(* A built-in type *)
and lustre_type = 
  | Bool of position
  | Int of position
  | IntRange of position * expr * expr
  | Real of position
  | UserType of position * ident 
  | TupleType of position * lustre_type list
  | RecordType of position * typed_ident list
  | ArrayType of position * (lustre_type * expr)
  | EnumType of position * ident list


(* A record field *)
and typed_ident = ident * lustre_type

(* A declaration of a type *)
type type_decl = 
  | AliasType of position * ident * lustre_type  
  | FreeType of position * ident

(* A clock expression *)
type clock_expr =
  | ClockPos of ident
  | ClockNeg of ident
  | ClockTrue 


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


(* The left-hand side of an equation *)
type eq_lhs =
  | ArrayDef of position * ident * ident list
  | StructDef of position * struct_item list


(* An equation or assertion in the node body *)
type node_equation =
  | Assert of position * expr
  | Equation of position * eq_lhs * expr 
  | AnnotMain
  | AnnotProperty of position * expr

(* A require for a contract. *)
type require =
    position * expr

(* Constructs a require for a contract. *)
let mk_require pos e = pos, e

(* An ensure for a contract. *)
type ensure =
    position * expr

(* Constructs an ensure for a contract. *)
let mk_ensure pos e = pos, e

(* A contract clause *)
type contract =
    TermLib.contract_source * string * require list * ensure list

(* Creates a contract from a name, a list of requires and a list of
   ensures. *)
let mk_contract source lustre_ident requires ensures =
  source, lustre_ident, requires, ensures

(* A node declaration *)
type node_decl =
    ident
    * node_param list
    * const_clocked_typed_decl list
    * clocked_typed_decl list
    * node_local_decl list
    * node_equation list
    * contract list
  

(* A function declaration *)
type func_decl =
    ident
    * (ident * lustre_type) list
    * (ident * lustre_type) list


(* An instance of a parameterized node *)
type node_param_inst = ident * ident * lustre_type list
  

(* A declaration as parsed *)
type declaration = 
  | TypeDecl of position * type_decl
  | ConstDecl of position * const_decl
  | NodeDecl of position * node_decl
  | FuncDecl of position * func_decl
  | NodeParamInst of position * node_param_inst


(* A Lustre program *)
type t = declaration list


(* ********************************************************************** *)
(* Pretty-printing functions                                              *)
(* ********************************************************************** *)


(* Pretty-print a clock expression *)
let pp_print_clock_expr ppf = function

  | ClockPos s -> Format.fprintf ppf "@ when %a" pp_print_ident s
  | ClockNeg s -> Format.fprintf ppf "@ when not %a" pp_print_ident s
  | ClockTrue -> ()


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
 
    | ExprList (p, l) -> Format.fprintf ppf "%a@[<hv 1>(%a)@]" ppos p pl l

    | TupleExpr (p, l) -> Format.fprintf ppf "%a@[<hv 1>{%a}@]" ppos p pl l

    | ArrayExpr (p, l) -> Format.fprintf ppf "%a@[<hv 1>[%a]@]" ppos p pl l

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

      Format.fprintf ppf "%a%a[%a]" ppos p pp_print_expr e pp_print_expr f

    | True p -> ps p "true"
    | False p -> ps p "false"

    | Num (p, n) -> ps p n
    | Dec (p, d) -> ps p d

    | ToInt (p, e) -> p1 p "int" e
    | ToReal (p, e) -> p1 p "real" e

    | Not (p, e) -> p1 p "not" e
    | And (p, e1, e2) -> p2 p "and" e1 e2
    | Or (p, e1, e2) -> p2 p "or" e1 e2
    | Xor (p, e1, e2) -> p2 p "xor" e1 e2
    | Impl (p, e1, e2) -> p2 p "=>" e1 e2
    | OneHot (p, e) -> pnp p "#" e

    | Uminus (p, e) -> p1 p "-" e
    | Mod (p, e1, e2) -> p2 p "mod" e1 e2 
    | Minus (p, e1, e2) -> p2 p "-" e1 e2
    | Plus (p, e1, e2) -> p2 p "+" e1 e2
    | Div (p, e1, e2) -> p2 p "/" e1 e2
    | Times (p, e1, e2) -> p2 p "*" e1 e2
    | IntDiv (p, e1, e2) -> p2 p "div" e1 e2

    | Ite (p, e1, e2, e3) -> p3 p "if" "then" "else" e1 e2 e3

    | With (p, e1, e2, e3) -> p3 p "with" "then" "else" e1 e2 e3

    | Eq (p, e1, e2) -> p2 p "=" e1 e2
    | Neq (p, e1, e2) -> p2 p "<>" e1 e2
    | Lte (p, e1, e2) -> p2 p "<=" e1 e2
    | Lt (p, e1, e2) -> p2 p "<" e1 e2
    | Gte (p, e1, e2) -> p2 p ">=" e1 e2
    | Gt (p, e1, e2) -> p2 p ">" e1 e2

    | When (p, e1, e2) -> p2 p "when" e1 e2
    | Current (p, e) -> p1 p "current" e
    | Condact (p, e1, n, e2, e3) -> 
  
      Format.fprintf ppf 
        "%acondact(%a,%a(%a),%a)" 
        ppos p
        pp_print_expr e1
        pp_print_ident n
        (pp_print_list pp_print_expr ",@ ") e2
        (pp_print_list pp_print_expr ",@ ") e3

    | Pre (p, e) -> p1 p "pre" e
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

  | IntRange (pos, l, u) -> 

    Format.fprintf ppf 
      "subrange [%a,%a] of int" 
      pp_print_expr l
      pp_print_expr u

  | Real pos -> Format.fprintf ppf "real"

  | UserType (pos, s) -> 

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
      "(%a^%a)" 
      pp_print_lustre_type t 
      pp_print_expr e

  | EnumType (pos, l) -> 

    Format.fprintf ppf 
      "enum @[<hv 2>{ %a }@]" 
      (pp_print_list Format.pp_print_string ",@ ") l


(* Pretty-print a typed identifier *)
and pp_print_typed_ident ppf (s, t) = 
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


let pp_print_array_def_index ppf ident =

  Format.fprintf ppf
    "[%a]"
    pp_print_ident ident


let pp_print_eq_lhs ppf = function

  | StructDef (pos, [l]) -> pp_print_struct_item ppf l
      
  | StructDef (pos, l) -> (pp_print_list pp_print_struct_item "@,") ppf l
                            
  | ArrayDef (pos, i, l) ->

    Format.fprintf ppf
      "%a%a"
      pp_print_ident i
      (pp_print_list pp_print_array_def_index "") l
  

(* Pretty-print a node equation *)
let pp_print_node_equation ppf = function

  | Assert (pos, e) -> 

    Format.fprintf ppf "assert %a;" pp_print_expr e

  | Equation (pos, lhs, e) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a;@]" 
      pp_print_eq_lhs lhs
      pp_print_expr e

  | AnnotMain -> Format.fprintf ppf "--%%MAIN;"

  | AnnotProperty (pos, e) -> Format.fprintf ppf "--%%PROPERTY %a;" pp_print_expr e 

(* Pretty-print a require of a contract. *)
let pp_print_require ppf (pos,e) =
  Format.fprintf ppf "--%@requires %a;" pp_print_expr e

(* Pretty-print a require of a contract. *)
let pp_print_ensure ppf (pos,e) =
  Format.fprintf ppf "--%@ensures %a;" pp_print_expr e


(* Pretty-print a node contract *)
let pp_print_contract ppf (pos, name, requires, ensures) = 

  Format.fprintf
    ppf
    "--%@contract: %s@   @[<v>%a@,%a@]"
    name
    (pp_print_list pp_print_require "@,") requires
    (pp_print_list pp_print_ensure "@,") ensures
  

(* Pretty-print a declaration *)
let pp_print_declaration ppf = function

  | TypeDecl (pos, t) -> 

    Format.fprintf ppf "type %a;" pp_print_type_decl t

  | ConstDecl (pos, c) -> pp_print_const_decl ppf c

  | NodeDecl (pos, (n, p, i, o, l, e, contracts)) -> 

    Format.fprintf ppf
      "@[<hv>@[<hv 2>node %a%t@ \
       @[<hv 1>(%a)@]@;<1 -2>\
       returns@ @[<hv 1>(%a)@];@]@ \
       %a\
       %a\
       @[<hv 2>let@ \
       %a@;<1 -2>\
       tel;@]@]"
      pp_print_ident n 
      (function ppf -> pp_print_node_param_list ppf p)
      (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
      (pp_print_list pp_print_clocked_typed_ident ";@ ") o
      (pp_print_list pp_print_contract ";@ ") contracts
      pp_print_node_local_decl l
      (pp_print_list pp_print_node_equation "@ ") e 

  | FuncDecl (pos, (n, i, o)) -> 

    Format.fprintf ppf
      "@[<hv 2>function %a@ \
       @[<hv 1>(%a)@]@;<1 -2>\
       returns@ @[<hv 1>(%a)@];@]" 
      pp_print_ident n 
      (pp_print_list pp_print_typed_ident ";@ ") i
      (pp_print_list pp_print_typed_ident ";@ ") o

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
        
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
