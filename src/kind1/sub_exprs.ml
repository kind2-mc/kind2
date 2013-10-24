(*
This file is part of the Kind verifier

* Copyright (c) 2007-2010 by the Board of Trustees of the University of Iowa, 
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


open Types
open Util
open Expr_util


(* a map from expr to its children *)
let expr_chld_hash = (Hashtbl.create 1000) 

let expr_chld expr = 
  try 
    Hashtbl.find expr_chld_hash expr
  with Not_found -> []

let all_expr_chld expr_list =
  List.fold_right (fun x y -> (expr_chld x)@y) expr_list []  

let add_expr_chld_hash chld expr =
  let children = expr_chld expr in
    if [] != children then failwith "error" 
    else Hashtbl.replace expr_chld_hash expr chld

let rec map_expr_to_chld expr =
  if [] != expr_chld expr then ()
  else
  let f = expr in
  match f with 
    ZERO 
  | ONE 
  | STEP_BASE
  | POSITION_VAR _
  | INT_CONST _
  | REAL_CONST( _, _)
    -> () 
  | STRING _
    -> failwith "not sure about how to do this"
  | NUM _ 
  | FLOAT _
  | VAR_GET (_,_,_,_)
    -> () 
  | PLUS (l,r)
  | MINUS (l,r)
  | MULT (l,r)
  | DIV (l,r)
  | INTDIV (l,r)
  | MOD (l,r)
  | B_AND (l,r)
  | B_OR (l,r)
  | B_IFF (l,r)
  | B_IMPL (l,r)
    -> add_expr_chld_hash [l;r] f;
      map_expr_to_chld l;
      map_expr_to_chld r
  | B_NOT ex
  | UMINUS ex 
    -> add_expr_chld_hash [ex] f;
       map_expr_to_chld ex
  | REL (_, l ,r ) 
    -> add_expr_chld_hash [l;r] f;
      map_expr_to_chld l;
      map_expr_to_chld r
  | ITE (a,b,c)
  | STREAM_ITE (a,b,c) 
    -> add_expr_chld_hash [a;b;c] f;
       map_expr_to_chld a;
       map_expr_to_chld b;
       map_expr_to_chld c;
  | RECORD_LIT _
  | RECORDREF _
  | TUPLEREF  _
  | TUPLE_LIT _
  | PRED (_,_)
     -> failwith "what is a pred in expr?"


(* a map from sub_expr to its parent *)
let sub_prnt_hash = (Hashtbl.create 1000)

let sub_parents sub_expr =
  try 
    Hashtbl.find sub_prnt_hash sub_expr
  with Not_found -> []

let all_sub_parents sub_expr_list =
  List.fold_right (fun x y -> (sub_parents x)@y) sub_expr_list []  

let add_subexpr_hash sub_expr prnt =
  let parents = sub_parents sub_expr in
    Hashtbl.replace sub_prnt_hash sub_expr (unique_list (prnt::parents) )


let print_sub_hash () = 
  print_string "sub expr hash map \n";
  Hashtbl.iter (fun sub prnt -> 
    pr "SUB_EXPR: ";
    pr_expr sub;    
    print_string " ---> ";
    List.iter (fun x ->  pr_expr x;  pr " \n--#--\n ") prnt;
    pr "\n=================\n";
  )
    sub_prnt_hash


let rec map_subexpr_to_parents sub_expr =
 
  let f = sub_expr in
  match f with 
    ZERO 
  | ONE 
  | STEP_BASE
  | POSITION_VAR _
  | INT_CONST _
  | REAL_CONST( _, _)
    -> () 
  | STRING _
    -> failwith "not sure about how to do this"
  | NUM _ 
  | FLOAT _
  | VAR_GET (_,_,_,_)
    -> () 
  | PLUS (l,r)
  | MINUS (l,r)
  | MULT (l,r)
  | DIV (l,r)
  | INTDIV (l,r)
  | MOD (l,r)
  | B_AND (l,r)
  | B_OR (l,r)
  | B_IFF (l,r)
  | B_IMPL (l,r)
    -> add_subexpr_hash l f;
       add_subexpr_hash r f;
       map_subexpr_to_parents l;
       map_subexpr_to_parents r
  | B_NOT ex
  | UMINUS ex 
    -> add_subexpr_hash ex f;
       map_subexpr_to_parents ex
  | REL (_, l ,r ) 
    -> add_subexpr_hash l f;
       add_subexpr_hash r f;
       map_subexpr_to_parents l;
       map_subexpr_to_parents r
  | ITE (a,b,c)
  | STREAM_ITE (a,b,c) 
    -> add_subexpr_hash a f;
       add_subexpr_hash b f;
       add_subexpr_hash c f;
       map_subexpr_to_parents a;
       map_subexpr_to_parents b;
       map_subexpr_to_parents c;
  | RECORD_LIT _
  | RECORDREF _
  | TUPLEREF  _
  | TUPLE_LIT _
  | PRED (_,_)
     -> failwith "what is a pred in expr?"

  

let build_sub_expr_map eq = 
  let lhs,rhs = eq in
    add_subexpr_hash rhs lhs;
    map_subexpr_to_parents rhs ;
    add_expr_chld_hash [rhs] lhs ;
    map_expr_to_chld rhs 


let rec all_decedents chld =
  if ([] = chld ) then []
  else 
  let new_chld = unique_list (all_expr_chld chld)  in
    unique_list (chld@(all_decedents new_chld)) 

let expr_decedents_hash = Hashtbl.create 1000

let build_expr_decedents () =
  let unique_decedents x =
    let res = unique_list (all_decedents (expr_chld x))  in
      res in
  Hashtbl.iter 
    (fun x y -> Hashtbl.add expr_decedents_hash x (unique_decedents x) ) 
    expr_chld_hash 


let rec all_ansestors prnts =
  if ([] = prnts ) then []
  else 
  let new_prnts = unique_list (all_sub_parents prnts)  in
    unique_list (prnts@(all_ansestors new_prnts)) 

(* maps a expr to all its ancestors *)  
let sub_ancestor_hash = Hashtbl.create 1000

let build_sub_expr_ansestors () =
  let unique_ansestors x =
    let res = unique_list (all_ansestors (sub_parents x))  in
      res in
  Hashtbl.iter 
    (fun x y -> Hashtbl.add sub_ancestor_hash x (unique_ansestors x) ) 
    sub_prnt_hash 

let print_sub_ancestors () = 
  print_string "sub ansestors \n";
  Hashtbl.iter (fun sub prnt -> 
    pr "ANCESTORS: ";
    pr_expr sub;    
    print_string " ---> ";
    List.iter (fun x ->  pr_expr x;  pr " \n--#--\n ") prnt;
    pr "\n=================\n";
  )
    sub_ancestor_hash


let sub_ancestors_subs () =
    Hashtbl.fold (fun a b c -> a::c) sub_ancestor_hash [] 


let rec sub_pairs sorted_expr_list =
  match sorted_expr_list with
      [] -> []
    | hd::tl -> 
	let forbidden_list1 = (Hashtbl.find sub_ancestor_hash hd)  in
	let forbidden_list2 = 
	  try (Hashtbl.find expr_chld_hash hd) 
	  with Not_found -> 
	    [] in
	let allowed_list1 = filter_forbidden forbidden_list1 tl  in
	let allowed_list2 = filter_forbidden forbidden_list2 allowed_list1  in
	let cur_pairs = 
	  (List.map (fun x -> (hd,x)) allowed_list2 ) in
	  cur_pairs @ (sub_pairs tl)

let filter_type l ty =
  List.filter 
    (fun (x,y) -> if y = ty then true else false) 
    l

let remove_type l = List.map (fun (x,y) -> x) l


let pre_process_expr_list l ty filter_func = 
  let all_exprs = (remove_type (filter_type l ty)) in
    filter_func (unique_list all_exprs)


let interval_exprs all_terms filter_func = 
  let all_chls = List.map (fun x -> il_expr_chld_type (replace_stream_ite x)) all_terms in 
  let all_sub_exprs = List.flatten all_chls in
    List.iter(fun (x, y) -> print_string(Lus_convert_print.expr_string x ^"TYPE : "^ Lus_convert_print.type_string y^"\n")) all_sub_exprs
  (* let interval_sub_exprs = pre_process_expr_list all_sub_exprs (L_INT_RANGE(_)) filter_func in 
    filter_sub_exprs
  *)

let sub_exprs all_terms filter_func = 
  let all_chls = List.map (fun x -> il_expr_chld_type (replace_stream_ite x)) all_terms in 
  let all_sub_exprs = List.flatten all_chls in
  let bool_sub_exprs = pre_process_expr_list ((ONE,L_BOOL)::((ZERO,L_BOOL)::all_sub_exprs)) L_BOOL filter_func in 
  let int_sub_exprs = pre_process_expr_list all_sub_exprs L_INT filter_func in 
  let float_sub_exprs = pre_process_expr_list all_sub_exprs L_REAL filter_func in     
    bool_sub_exprs, int_sub_exprs, float_sub_exprs;

    

 

