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

type id = string 

type expr =

  (* Identifier *)
  | Id of id
  | RecordProject of id * id
  | TupleProject of id * int

  (* Constants *)
  | True 
  | False
  | Num of string
  | Dec of string

  (* Boolean operators *)
  | Not of expr 
  | And of expr * expr 
  | Or of expr * expr
  | Xor of expr * expr 
  | Impl of expr * expr 

  (* Arithmetic operators *)
  | Uminus of expr 
  | Mod of expr * expr
  | Minus of expr * expr
  | Plus of expr * expr
  | Div of expr * expr
  | Times of expr * expr
  | Intdiv of expr * expr

  (* If operator *)
  | Ite of expr * expr * expr 

  (* Relations *)
  | Eq of expr * expr 
  | Neq of expr * expr
  | Lte of expr * expr
  | Lt of expr * expr
  | Gte of expr * expr
  | Gt of expr * expr

  (* Clock operators *)
  | When of expr * expr 
  | Current of expr
  | Condact of expr * expr * expr 
  
  (* Temporal operators *)
  | Pre of expr 
  | Fby of expr * int * expr 
  | Arrow of expr * expr 

  (* Node call *)
  | Call of string * expr list 


let rec pp_print_expr ppf = 

  let ps = Format.fprintf ppf "%s" in 

  let p1 s e = 
    Format.fprintf ppf "@[<hv 2>(%s@ %a)@]" s pp_print_expr e 
  in 

  let p2 s e1 e2 = 
    Format.fprintf ppf
      "@[<hv 2>(%a@ %s@ %a)@]" 
      pp_print_expr e1 
      s 
      pp_print_expr e2 
  in 

  let p3 s1 s2 s3 e1 e2 e3 = 
    Format.fprintf ppf
      "@[<hv 2>(%s@ %a@ %s@ %a@ %s@ %a)@]" 
      s1 
      pp_print_expr e1 
      s2
      pp_print_expr e2 
      s3 
      pp_print_expr e3 
  in 
  
  let p1p s e = 
    Format.fprintf ppf "@[<hv 2>%s(%a)@]" s pp_print_expr e 
  in 

  let p2p s e1 e2 = 
    Format.fprintf ppf
      "@[<hv 2>%s(%a,@ %a)@]" 
      s 
      pp_print_expr e1 
      pp_print_expr e2 
  in 

  let p3p s e1 e2 e3 = 
    Format.fprintf ppf
      "@[<hv 2>%s(%a,@ %a,@ %a)@]" 
      s
      pp_print_expr e1 
      pp_print_expr e2 
      pp_print_expr e2 
  in 
  
  let rec pl ppf = function 
    | [] -> ()
    | [e] -> Format.fprintf ppf "%a" pp_print_expr e
    | e :: tl -> Format.fprintf ppf "%a,@ %a" pl [e] pl tl
  in

  let pnp s l = 
    Format.fprintf ppf
      "@[<hv 2>%s(%a)@]" 
      s
      pl l
  in

  function
    
    | Id id -> ps id

    | RecordProject (id, f) -> Format.fprintf ppf "%s.%s" id f
    | TupleProject (id, f) -> Format.fprintf ppf "%s[%d]" id f

    | True -> ps "true"
    | False -> ps "false"

    | Num n -> ps n
    | Dec d -> ps d

    | Not e -> p1 "not" e
    | And (e1, e2) -> p2 "and" e1 e2
    | Or (e1, e2) -> p2 "or" e1 e2
    | Xor (e1, e2) -> p2 "xor" e1 e2
    | Impl (e1, e2) -> p2 "=>" e1 e2

    (* Arithmetic operators *)
    | Uminus e -> p1 "-" e
    | Mod (e1, e2) -> p2 "mod" e1 e2 
    | Minus (e1, e2) -> p2 "-" e1 e2
    | Plus (e1, e2) -> p2 "+" e1 e2
    | Div (e1, e2) -> p2 "/" e1 e2
    | Times (e1, e2) -> p2 "*" e1 e2
    | Intdiv (e1, e2) -> p2 "div" e1 e2

    (* If operator *)
    | Ite (e1, e2, e3) -> p3 "if" "then" "else" e1 e2 e3

    (* Relations *)
    | Eq (e1, e2) -> p2 "=" e1 e2
    | Neq (e1, e2) -> p2 "<>" e1 e2
    | Lte (e1, e2) -> p2 "<=" e1 e2
    | Lt (e1, e2) -> p2 "<" e1 e2
    | Gte (e1, e2) -> p2 ">=" e1 e2
    | Gt (e1, e2) -> p2 ">" e1 e2

    (* Clock operators *)
    | When (e1, e2) -> p2 "when" e1 e2
    | Current e -> p1 "current" e
    | Condact (e1, e2, e3) -> p3p "condact" e1 e2 e3
  
    (* Temporal operators *)
    | Pre e -> p1 "pre" e
    | Fby (e1, i, e2) -> 
      Format.fprintf ppf 
        "fby(%a,@ %d,@ %a)" pp_print_expr e1 i pp_print_expr e2
    | Arrow (e1, e2) -> p2 "->" e1 e2

    (* Node call *)
    | Call (id, l) -> pnp id l


(* Constant declaration *)
type const = id * expr 

(* Type definition *)
type typedef

(* Node definition *)
type node 


