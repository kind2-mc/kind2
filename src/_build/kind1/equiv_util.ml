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


open Util
open New_vars

let print_str_list str_list =
  List.iter (fun x -> pr x; pr " , ") str_list 

(* print a set of terms *)
let print_equiv_classes classes =
  let iter_fun x = 
    let term_str_list = List.map (fun y -> nvr_to_nvr_def_decl_body y ) x in 
    pr "CLASS: "; print_str_list x; pr"\n"; 
    pr "DEFS: "; print_str_list term_str_list; pr"\n" ;
    pr "REP:" ; pr (List.hd term_str_list); pr "\n" in
    pr "EQUIV CLASSES :: "; 
    List.iter (fun x -> iter_fun x ) classes ;
    pr "Total number of classes = "; print_int (List.length classes)

let rec mk_eqs_one_class one_class ty =
  match one_class with 
    [] 
    | _::[] ->[]
    | hd1::(hd2::tl) -> 
	let eq = Types.F_EQ(Types.PRED (hd1,[]), Types.PRED(hd2,[]), ty) in
	  eq:: (mk_eqs_one_class (hd2::tl) ty) 


let mk_eqs_equiv_classes classes ty =
  let eqs = List.map (fun x -> mk_eqs_one_class x ty) classes in
    List.flatten eqs  

(* Given a counter model in hash_tbl, return a list of equiv classes. *)
let filter_int_func one_class hash_tbl =
  let values_hash = Hashtbl.create 100 in
  let add_hash x = 
    (let y = Hashtbl.find hash_tbl x in 
    Hashtbl.add values_hash y x ;
      y ) in
  let all_values = 
    List.fold_right (fun x y -> (add_hash x)::y) one_class [] in
  let unique_values = unique_list all_values in
  let changed = (List.length unique_values ) > 1  in
    if changed then 
      let ret_lists = List.fold_right 
	(fun x y -> (Hashtbl.find_all values_hash x)::y) 
	unique_values [] in
	ret_lists, changed
    else [one_class], changed 

(* Given a counter model in hash_tbl, return a list of equiv classes. *)
let filter_int_func_with_history one_class counter_model extra_info_list =
  let values_hash = Hashtbl.create 100 in
  let add_hash x = 
    (let y = int_of_string (Hashtbl.find counter_model x) in 
       Hashtbl.add values_hash y x ;
      y ) in
  let all_values = 
    List.fold_right (fun x y -> (add_hash x)::y) one_class [] in
  let unique_values = unique_list all_values in
  let ret_lists = List.fold_right 
    (fun x y -> 
      let x_items = (Hashtbl.find_all values_hash x) in 
      let new_extra_info_list = extra_info_list@[x] in
	(x_items,new_extra_info_list) ::y) 
    unique_values [] in
    ret_lists


