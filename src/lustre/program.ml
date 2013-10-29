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

type t 

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



(* Pretty-print a position *)
let pp_print_position 
    ppf 
    { Lexing.pos_fname; Lexing.pos_lnum; Lexing.pos_bol; Lexing.pos_cnum } =

  Format.fprintf 
    ppf
    "(%s,%d,%d)"
    pos_fname
    pos_lnum
    (pos_cnum - pos_bol)


type id = string 

(* Lustre expression *)
type expr =

  (* Identifier *)
  | Id of Lexing.position * id
  | RecordProject of Lexing.position * id * id
  | TupleProject of Lexing.position * id * int

  (* Constants *)
  | True of Lexing.position
  | False of Lexing.position
  | Num of Lexing.position * string
  | Dec of Lexing.position * string

  (* Boolean operators *)
  | Not of Lexing.position * expr 
  | And of Lexing.position * expr * expr 
  | Or of Lexing.position * expr * expr
  | Xor of Lexing.position * expr * expr 
  | Impl of Lexing.position * expr * expr 

  (* Arithmetic operators *)
  | Uminus of Lexing.position * expr 
  | Mod of Lexing.position * expr * expr
  | Minus of Lexing.position * expr * expr
  | Plus of Lexing.position * expr * expr
  | Div of Lexing.position * expr * expr
  | Times of Lexing.position * expr * expr
  | Intdiv of Lexing.position * expr * expr

  (* If operator *)
  | Ite of Lexing.position * expr * expr * expr 

  (* Relations *)
  | Eq of Lexing.position * expr * expr 
  | Neq of Lexing.position * expr * expr
  | Lte of Lexing.position * expr * expr
  | Lt of Lexing.position * expr * expr
  | Gte of Lexing.position * expr * expr
  | Gt of Lexing.position * expr * expr

  (* Clock operators *)
  | When of Lexing.position * expr * expr 
  | Current of Lexing.position * expr
  | Condact of Lexing.position * expr * expr * expr 
  
  (* Temporal operators *)
  | Pre of Lexing.position * expr 
  | Fby of Lexing.position * expr * int * expr 
  | Arrow of Lexing.position * expr * expr 

  (* Node call *)
  | Call of Lexing.position * string * expr list 


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
      "@[<hv 2>%a%s(%a)@]" 
      ppos p 
      s
      pl l
  in

  function
    
    | Id (p, id) -> ps p id
    | RecordProject (p, id, f) -> 
      Format.fprintf ppf "%a%s.%s" ppos p id f

    | TupleProject (p, id, f) -> 
      Format.fprintf ppf "%a%s[%d]" ppos p id f

    | True p -> ps p "true"
    | False p -> ps p "false"

    | Num (p, n) -> ps p n
    | Dec (p, d) -> ps p d

    | Not (p, e) -> p1 p "not" e
    | And (p, e1, e2) -> p2 p "and" e1 e2
    | Or (p, e1, e2) -> p2 p "or" e1 e2
    | Xor (p, e1, e2) -> p2 p "xor" e1 e2
    | Impl (p, e1, e2) -> p2 p "=>" e1 e2

    | Uminus (p, e) -> p1 p "-" e
    | Mod (p, e1, e2) -> p2 p "mod" e1 e2 
    | Minus (p, e1, e2) -> p2 p "-" e1 e2
    | Plus (p, e1, e2) -> p2 p "+" e1 e2
    | Div (p, e1, e2) -> p2 p "/" e1 e2
    | Times (p, e1, e2) -> p2 p "*" e1 e2
    | Intdiv (p, e1, e2) -> p2 p "div" e1 e2

    | Ite (p, e1, e2, e3) -> p3 p "if" "then" "else" e1 e2 e3

    | Eq (p, e1, e2) -> p2 p "=" e1 e2
    | Neq (p, e1, e2) -> p2 p "<>" e1 e2
    | Lte (p, e1, e2) -> p2 p "<=" e1 e2
    | Lt (p, e1, e2) -> p2 p "<" e1 e2
    | Gte (p, e1, e2) -> p2 p ">=" e1 e2
    | Gt (p, e1, e2) -> p2 p ">" e1 e2

    | When (p, e1, e2) -> p2 p "when" e1 e2
    | Current (p, e) -> p1 p "current" e
    | Condact (p, e1, e2, e3) -> pnp p "condact" [e1; e2; e3]
  
    | Pre (p, e) -> p1 p "pre" e
    | Fby (p, e1, i, e2) -> 

      Format.fprintf ppf 
        "%afby(p, %a,@ %d,@ %a)" 
        ppos p 
        pp_print_expr e1 
        i 
        pp_print_expr e2

    | Arrow (p, e1, e2) -> p2 p "->" e1 e2

    | Call (p, id, l) -> pnp p id l


(* Constant declaration *)
type const = id * expr 

type lustre_type = 
  | Bool
  | Int
  | Real
  | UserType of string 
  | RecordType of field list
  | ArrayType of (lustre_type * expr)
  | EnumType of string list

and field = string * lustre_type

(* Type definition *)
type type_decl = string * lustre_type  

type const_decl = string * expr * lustre_type option

type declaration = 
  | TypeDecl of type_decl
  | ConstDecl of const_decl

(* Node definition *)
type node 

let rec pp_print_lustre_type ppf = function
  | Bool -> Format.fprintf ppf "bool"
  | Int -> Format.fprintf ppf "int"
  | Real -> Format.fprintf ppf "real"
  | UserType s -> Format.fprintf ppf "%s" s
  | RecordType l -> Format.fprintf ppf "struct @[<hv 2>{ %a }@]" (pp_print_list pp_print_field ";@ ") l
  | ArrayType (t, e) -> Format.fprintf ppf "%a^%a" pp_print_lustre_type t pp_print_expr e
  | EnumType l -> 
    Format.fprintf ppf "enum @[<hv 2>{ %a }@]" (pp_print_list Format.pp_print_string ";@ ") l

and pp_print_field ppf (s, t) = 
  Format.fprintf ppf "%s: %a" s pp_print_lustre_type t


let pp_print_declaration ppf = function
  | TypeDecl (s, t) -> Format.fprintf ppf "type %s = %a;" s pp_print_lustre_type t
  | ConstDecl (s, e, None) -> Format.fprintf ppf "type %s = %a;" s pp_print_expr e
  | ConstDecl (s, e, Some t) -> 
    Format.fprintf ppf "type %s : %a = %a;" s pp_print_lustre_type t pp_print_expr e
