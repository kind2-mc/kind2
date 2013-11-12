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

module I = LustreIdent

(* ********************************************************************** *)
(* Helper functions                                                       *)
(* ********************************************************************** *)

(* Pretty-print a list *)
let rec pp_print_list pp sep ppf = function 

  (* Output nothing for the empty list *) 
  | [] -> ()

  (* Output a single element in the list  *) 
  | e :: [] -> 
    pp ppf e

  (* Output a single element and a space *) 
  | e :: tl -> 

    (* Output one element *)
    pp_print_list pp sep ppf [e]; 

    (* Output separator *)
    Format.fprintf ppf sep; 

    (* Output the rest of the list *)
    pp_print_list pp sep ppf tl


(* ********************************************************************** *)
(* Type declarations                                                      *)
(* ********************************************************************** *)


(* A position in a file

   The column is the actual colum number, not an offset from the
   beginning of the file as in Lexing.position *)
type position =
  { pos_fname : string; pos_lnum: int; pos_cnum: int }


(* Pretty-print a position *)
let pp_print_position 
    ppf 
    { pos_fname; pos_lnum; pos_cnum } =

  Format.fprintf 
    ppf
    "(%s,%d,%d)"
    pos_fname
    pos_lnum
    pos_cnum


(* A dummy position, different from any valid position *)
let dummy_pos = { pos_fname = ""; pos_lnum = 0; pos_cnum = -1 }


(* A dummy position in the specified file *)
let dummy_pos_in_file fname = 
  { pos_fname = fname; pos_lnum = 0; pos_cnum = -1 }


(* Convert a position from Lexing to a position *)
let position_of_lexing 
    { Lexing.pos_fname;
      Lexing.pos_lnum;
      Lexing.pos_bol;
      Lexing.pos_cnum } = 

  (* Colum number is relative to the beginning of the file *)
  { pos_fname = pos_fname; 
    pos_lnum = pos_lnum; 
    pos_cnum = pos_cnum - pos_bol } 


(* Return true if position is a dummy position *)
let is_dummy_pos = function 
  | { pos_cnum = -1 } -> true 
  | _ -> false


(* An identifier *)
type ident = LustreIdent.t


(* A Lustre expression *)
type expr =

  (* Identifier *)
  | Ident of position * ident
  | RecordProject of position * ident * ident
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

  (* Array constructor of single expression *)
  | ArrayConstr of position * expr * expr 

  (* Array constructor of single expression *)
  | ArraySlice of position * expr * (expr * expr) list

  (* Array constructor of single expression *)
  | ArrayConcat of position * expr * expr

  (* Construction of a record *)
  | RecordConstruct of position * (ident * expr) list

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
  | Intdiv of position * expr * expr

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
  | Condact of position * expr * expr * expr list 
  
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
  | Bool
  | Int
  | IntRange of expr * expr
  | Real
  | UserType of ident 
  | TupleType of lustre_type list
  | RecordType of typed_ident list
  | ArrayType of (lustre_type * expr)
  | EnumType of ident list


(* A record field *)
and typed_ident = ident * lustre_type

(* A declaration of a type *)
type type_decl = 
  | AliasType of ident * lustre_type  
  | FreeType of ident

(* A clock expression *)
type clock_expr =
  | ClockPos of ident
  | ClockNeg of ident
  | ClockTrue 


(* A declaration of a clocked type *)
type clocked_typed_decl = ident * lustre_type * clock_expr


(* A declaration of a clocked type *)
type const_clocked_typed_decl = ident * lustre_type * clock_expr * bool


(* A declaration of a constant *)
type const_decl = 
  | FreeConst of ident * lustre_type
  | UntypedConst of ident * expr 
  | TypedConst of ident * expr * lustre_type


(* A variable declaration *)
type var_decl = ident * lustre_type * clock_expr


(* A static parameter of a node *)
type node_param =
  | TypeParam of ident


(* A local declaration in a node *)
type node_local_decl =
  | NodeConstDecl of const_decl 
  | NodeVarDecl of var_decl


type struct_item =
  | SingleIdent of ident
  | TupleStructItem of struct_item list
  | TupleSelection of ident * expr
  | FieldSelection of ident * ident
  | ArraySliceStructItem of ident * (expr * expr) list



(* An equation or assertion in the node body *)
type node_equation =
  | Assert of expr
  | Equation of struct_item list * expr 
  | AnnotMain
  | AnnotProperty of expr

(* A contract clause *)
type contract_clause =
  | Requires of expr
  | Ensures of expr

(* A contract as a list of clauses *)
type contract = contract_clause list 

(* A node declaration *)
type node_decl = ident * node_param list * const_clocked_typed_decl list * clocked_typed_decl list * node_local_decl list * node_equation list * contract 
  

(* A function declaration *)
type func_decl = ident * (ident * lustre_type) list * (ident * lustre_type) list


(* An instance of a parameterized node *)
type node_param_inst = ident * ident * lustre_type list
  

(* A declaration as parsed *)
type declaration = 
  | TypeDecl of type_decl
  | ConstDecl of const_decl
  | NodeDecl of node_decl
  | FuncDecl of func_decl
  | NodeParamInst of node_param_inst


(* A Lustre program *)
type t = declaration list


(* ********************************************************************** *)
(* Pretty-printing functions                                              *)
(* ********************************************************************** *)


(* Pretty-print a clock expression *)
let pp_print_clock_expr ppf = function

  | ClockPos s -> Format.fprintf ppf "@ when %a" I.pp_print_ident s
  | ClockNeg s -> Format.fprintf ppf "@ when not %a" I.pp_print_ident s
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
    
    | Ident (p, id) -> Format.fprintf ppf "%a%a" ppos p I.pp_print_ident id
 
    | ExprList (p, l) -> Format.fprintf ppf "%a@[<hv 1>(%a)@]" ppos p pl l

    | TupleExpr (p, l) -> Format.fprintf ppf "%a@[<hv 1>[%a]@]" ppos p pl l

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
        (pp_print_list pp_print_array_slice ",@ ") l 

    | ArrayConcat (p, e1, e2) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a|%a@]" 
        ppos p 
        pp_print_expr e1
        pp_print_expr e2 

    | RecordProject (p, id, f) -> 

      Format.fprintf ppf 
        "%a%a.%a" 
        ppos p 
        I.pp_print_ident id 
        I.pp_print_ident f

    | RecordConstruct (p, l) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>{%a}@]" 
        ppos p 
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
    | Intdiv (p, e1, e2) -> p2 p "div" e1 e2

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
    | Condact (p, e1, e2, e3) -> pnp p "condact" (e1 :: e2 :: e3)
  
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
        I.pp_print_ident id
        (pp_print_list pp_print_expr ",@ ") l

    | CallParam (p, id, t, l) -> 

      Format.fprintf ppf 
        "%a%a<<%a>>(%a)" 
        ppos p
        I.pp_print_ident id
        (pp_print_list pp_print_lustre_type "@ ") t
        (pp_print_list pp_print_expr ",@ ") l
        

(* Pretty-print an array slice *)
and pp_print_array_slice ppf (l, u) =
  
  Format.fprintf ppf "%a..%a" pp_print_expr l pp_print_expr u

and pp_print_field_assign ppf (i, e) = 

  Format.fprintf ppf 
    "@[<hv 2>%a =@ %a@]"
    I.pp_print_ident i
    pp_print_expr e


(* Pretty-print a Lustre type *)
and pp_print_lustre_type ppf = function

  | Bool -> Format.fprintf ppf "bool"

  | Int -> Format.fprintf ppf "int"

  | IntRange (l, u) -> 

    Format.fprintf ppf 
      "subrange [%a,%a] of int" 
      pp_print_expr l
      pp_print_expr u

  | Real -> Format.fprintf ppf "real"

  | UserType s -> 

    Format.fprintf ppf "%a" I.pp_print_ident s

  | TupleType l -> 

    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_lustre_type ",@ ") l

  | RecordType l -> 

    Format.fprintf ppf 
      "struct @[<hv 2>{ %a }@]" 
      (pp_print_list pp_print_typed_ident ";@ ") l

  | ArrayType (t, e) -> 

    Format.fprintf ppf 
      "(%a^%a)" 
      pp_print_lustre_type t 
      pp_print_expr e

  | EnumType l -> 

    Format.fprintf ppf 
      "enum @[<hv 2>{ %a }@]" 
      (pp_print_list I.pp_print_ident ",@ ") l


(* Pretty-print a typed identifier *)
and pp_print_typed_ident ppf (s, t) = 
  Format.fprintf ppf 
    "@[<hov 2>%a:@ %a@]" 
    I.pp_print_ident s 
    pp_print_lustre_type t


(* Pretty-print a typed identifier with a clock *)
and pp_print_clocked_typed_ident ppf (s, t, c) = 
  Format.fprintf ppf 
    "@[<hov 2>%a:@ %a%a@]" 
    I.pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


(* Pretty-print a typed identifier with a clock, possibly constant *)
and pp_print_const_clocked_typed_ident ppf (s, t, c, o) = 
  Format.fprintf ppf "@[<hov 2>%t%a:@ %a%a@]" 
    (function ppf -> if o then Format.fprintf ppf "const ")
    I.pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


(* Pretty-print a type declaration *)
let pp_print_type_decl ppf = function

  | AliasType (s, t) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a@]" 
      I.pp_print_ident s 
      pp_print_lustre_type t

  | FreeType t -> 

    Format.fprintf ppf "%a" I.pp_print_ident t 


(* Pretty-print a variable declaration *)
let pp_print_var_decl ppf = function 

  | s, t, c -> 

    Format.fprintf ppf 
      "@[<hov 2>%a:@ %a%a;@]" 
      I.pp_print_ident s 
      pp_print_lustre_type t
      pp_print_clock_expr c


(* Pretty-print a constant declaration *)
let pp_print_const_decl ppf = function

  | FreeConst (s, t) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a:@ %a;@]" 
      I.pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (s, e) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a =@ %a;@]" 
      I.pp_print_ident s 
      pp_print_expr e

  | TypedConst (s, e, t) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a:@ %a =@ %a;@]" 
      I.pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e


(* Pretty-print a single static node parameter *)
let pp_print_node_param ppf = function

  | TypeParam t ->
    Format.fprintf ppf "type %a" I.pp_print_ident t


(* Pretty-print a list of static node parameters *)
let pp_print_node_param_list ppf = function

  | [] -> ()

  | l ->
    
    Format.fprintf ppf
      "@[<hv 2><<%a>>@]"
      (pp_print_list pp_print_node_param ";@ ") l


(* Pretty-print a node-local variable declaration, skip others *)
let pp_print_node_local_decl_var ppf = function

  | NodeVarDecl v -> pp_print_var_decl ppf v

  | _ -> ()


(* Pretty-print a node-local constant declaration, skip others *)
let pp_print_node_local_decl_const ppf = function

  | NodeConstDecl c -> pp_print_const_decl ppf c

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

  | SingleIdent s -> Format.fprintf ppf "%a" I.pp_print_ident s

  | TupleStructItem l -> 

    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_struct_item ",@ ") l

  | TupleSelection (e, i) -> 

    Format.fprintf ppf
      "%a[%a]"
      I.pp_print_ident e
      pp_print_expr i

  | FieldSelection (e, i) -> 

    Format.fprintf ppf
      "%a.%a"
      I.pp_print_ident e
      I.pp_print_ident i

  | ArraySliceStructItem (e, i) -> 

    Format.fprintf ppf
      "%a@[<hv 1>[%a]@]" 
      I.pp_print_ident e
      (pp_print_list pp_print_array_slice ",@ ") i


(* Pretty-print a node equation *)
let pp_print_node_equation ppf = function

  | Assert e -> 

    Format.fprintf ppf "assert %a;" pp_print_expr e

  | Equation ([l], e) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a;@]" 
      pp_print_struct_item l
      pp_print_expr e

  | Equation (l, e) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>@[<hv 1>(%a)@] =@ %a;@]" 
      (pp_print_list pp_print_struct_item ",@ ") l
      pp_print_expr e

  | AnnotMain -> Format.fprintf ppf "--%%MAIN;"

  | AnnotProperty e -> Format.fprintf ppf "--%%PROPERTY %a;" pp_print_expr e 


(* Pretty-print a contract clause *)
let pp_print_contract_clause ppf = function 

  | Requires e -> 

    Format.fprintf ppf "--%@requires %a;" pp_print_expr e

  | Ensures e -> 

    Format.fprintf ppf "--%@ensures %a;" pp_print_expr e


(* Pretty-print a node contract *)
let pp_print_contract ppf c = 

  if c = [] then () else

    Format.fprintf ppf 
      "@[<v>%a@,@]" 
      (pp_print_list pp_print_contract_clause "@,") c
  

(* Pretty-print a declaration *)
let pp_print_declaration ppf = function

  | TypeDecl t -> 

    Format.fprintf ppf "type %a;" pp_print_type_decl t

  | ConstDecl c -> pp_print_const_decl ppf c

  | NodeDecl (n, p, i, o, l, e, r) -> 

    Format.fprintf ppf
      "@[<hv>@[<hv 2>node %a%t@ \
       @[<hv 1>(%a)@]@;<1 -2>\
       returns@ @[<hv 1>(%a)@];@]@ \
       %a\
       %a\
       @[<hv 2>let@ \
       %a@;<1 -2>\
       tel;@]@]" 
<<<<<<< Updated upstream
      I.pp_print_ident n 
=======
      pp_print_ident n 
>>>>>>> Stashed changes
      (function ppf -> pp_print_node_param_list ppf p)
      (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
      (pp_print_list pp_print_clocked_typed_ident ";@ ") o
      pp_print_contract r
      pp_print_node_local_decl l
      (pp_print_list pp_print_node_equation "@ ") e 

  | FuncDecl (n, i, o) -> 

    Format.fprintf ppf
      "@[<hv 2>function %a@ \
       @[<hv 1>(%a)@]@;<1 -2>\
       returns@ @[<hv 1>(%a)@];@]" 
      I.pp_print_ident n 
      (pp_print_list pp_print_typed_ident ";@ ") i
      (pp_print_list pp_print_typed_ident ";@ ") o

  | NodeParamInst (n, s, p) -> 

    Format.fprintf ppf
      "@[<hv>@[<hv 2>node %a =@ %a@[<hv 2><<%a>>@];@]" 
      I.pp_print_ident n 
      I.pp_print_ident n 
      (pp_print_list pp_print_lustre_type "@ ") p


let pp_print_program ppf p =

  Format.fprintf ppf
    "@[<v>%a@]" 
    (pp_print_list pp_print_declaration "@ ") 
    p
        
(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
