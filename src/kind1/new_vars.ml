(*
This file is part of the Kind verifier

* Copyright (c) 2007-2011 by the Board of Trustees of the University of Iowa, 
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

(** 
@author Yeting Ge
@author Temesghen Kahsai

*)

open Util
open Expr_util
open Sub_exprs
open Types
open Exceptions
open Channels
open OldFlags
open Globals
open ExtString

let solver = Globals.my_solver

(* Given a sub_expr e,  *)
(* a nvr is a fresh new variable, say _NVRn_.  *)
(* a nvr_def is a function, say _NDEFn_(t).    *)
(* It is then asserted  _NDEFn_(t) = e for some t.   *)

let nvr_counter = new Counter.counter 

let nvr_prefix = "_NVR_" 
let mk_nvr_str id = nvr_prefix ^ (string_of_int id) 

let nvr_def_prefix = "_NDEF_"
let mk_nvr_def_str id = nvr_def_prefix ^ (string_of_int id)  

let nvr_prefix_interval = "_NVR_RG_" 
let mk_nvr_str_interval id = nvr_prefix_interval ^ (string_of_int id) 

let nvr_def_prefix_interval = "_NDEF_RG_"
let mk_nvr_def_str_interval id = nvr_def_prefix_interval ^ (string_of_int id)

let naive_prop = "_NP_"
let naive_prop_str id = naive_prop ^ (string_of_int id)


(*  Given a sub_expr e, maps nvr_str to   *)
(* (e, id, type, nvr_def_str, nvr_def_decl_body)  *)
let nvr_to_info_hash = 
  (Hashtbl.create 1000:
      (string,(il_expression*int*lustre_type*string*string)) Hashtbl.t)


(* Return a list of ids of mode vars*)
let get_interval_id_vars () = 
  Hashtbl.fold (fun i (n,v,t,c) acc  ->  
		match t with 
		    L_INT_RANGE (x,y) -> 
		      let internal_name = Tables.get_varinfo_name i in
			if (Tables.varid_lookup_interval internal_name = -1) then acc
			  else
			((Tables.varid_lookup_interval internal_name),x,y)::acc 
		  | _ -> acc
	     )(Tables.get_varinfo()) []
 

(* Return the list of internal name of mode vars*)
let get_interval_vars () =
let interval_list_id = get_interval_id_vars () in
  List.map( fun (v,x,y) -> ((Tables.get_varinfo_name v),x,y)) interval_list_id

(*Check that the range of the mode variables is not too big. If it is don't generate the canidates for mode vars.*)
let is_range_big () = 
  let gen_mode_candidates = ref true in (* a bool to check if we want to generate mode candidates*)
  let list_mode = get_interval_vars() in
    List.iter(fun (v,lb,ub) -> 
		( if ((ub - lb) < !OldFlags.range) then gen_mode_candidates:=true
		  else gen_mode_candidates:=false); print_to_user("RANGE TOO BIG\n")) list_mode; !gen_mode_candidates
		  
(* Create new candidate for mode type variables *)
let make_interval_candidate () =
  let list_interval =  get_interval_vars () in
  let positive_candidate_buf = Buffer.create 1000 in
  let negative_candidate_buf = Buffer.create 100 in
    List.map (fun (v,lb,ub) -> (
		List.iter (fun x ->
			     let nvr_id_pos = nvr_counter#next in
			     let nvr_str_pos = mk_nvr_str_interval nvr_id_pos in
			     let nvr_def_str_pos =  mk_nvr_def_str_interval nvr_id_pos in
			     let nvr_def_decl_body_pos = "(= ( "^v^ " _M)"^string_of_int(x)^")" in
			     let interval_nvr_decl_pos = "(define "^nvr_str_pos^" :: bool)\n" in
			     let interval_nvr_def_pos = "(define "^nvr_def_str_pos^" ::(-> _nat bool) (lambda ( _M::_nat) (= ( "^v^ " _M) "^string_of_int(x)^")))\n" in
			       Buffer.add_string positive_candidate_buf interval_nvr_decl_pos;
			       Buffer.add_string positive_candidate_buf interval_nvr_def_pos;
			 Hashtbl.add nvr_to_info_hash nvr_str_pos (REL(EQ,STRING(v),NUM(x)),nvr_id_pos,L_BOOL,nvr_def_str_pos,nvr_def_decl_body_pos);)
 (Util.interval_list lb ub);)) list_interval;

List.map (fun (v,lb,ub) -> (
	    List.iter (fun x ->
			     let nvr_id_neg = nvr_counter#next in
			     let nvr_str_neg = mk_nvr_str_interval nvr_id_neg in
			     let nvr_def_str_neg =  mk_nvr_def_str_interval nvr_id_neg in
			     let nvr_def_decl_body_neg = "(/= ( "^v^ " _M)"^string_of_int(x)^")" in
			     let interval_nvr_decl_neg = "(define "^nvr_str_neg^" :: bool)\n" in
			     let interval_nvr_def_neg = "(define "^nvr_def_str_neg^" ::(-> _nat bool) (lambda ( _M::_nat) (/= ( "^v^ " _M) "^string_of_int(x)^")))\n" in
			       Buffer.add_string negative_candidate_buf interval_nvr_decl_neg;
			       Buffer.add_string negative_candidate_buf interval_nvr_def_neg;
			       Hashtbl.replace nvr_to_info_hash nvr_str_neg (REL(NEQ,STRING(v),NUM(x)),nvr_id_neg,L_BOOL,nvr_def_str_neg,nvr_def_decl_body_neg);) 
	      (Util.interval_list lb ub);))list_interval;

   Buffer.add_buffer positive_candidate_buf negative_candidate_buf;
   Buffer.contents positive_candidate_buf


(** Make candidate for one mode variable *)
let mk_one_mode_candidate mode_var lb ub =
  let pos_can = 
    List.fold_right (fun x y ->
		 let nvr_id_pos = nvr_counter#next in
		 let nvr_str_pos = mk_nvr_str_interval nvr_id_pos in
		 let nvr_def_str_pos =  mk_nvr_def_str_interval nvr_id_pos in
		 let nvr_def_decl_body_pos = "(= ( "^mode_var^ " _M)"^string_of_int(x)^")" in
		 let interval_nvr_decl_pos = "(define "^nvr_str_pos^" :: bool)\n" in
		 let interval_nvr_def_pos = "(define "^nvr_def_str_pos^" ::(-> _nat bool) (lambda ( _M::_nat) (= ( "^mode_var^ " _M) "^string_of_int(x)^")))\n" in
		 let _ = Hashtbl.add nvr_to_info_hash nvr_str_pos (REL(EQ,STRING(mode_var),NUM(x)),nvr_id_pos,L_BOOL,nvr_def_str_pos,nvr_def_decl_body_pos) in
		   interval_nvr_decl_pos ^ interval_nvr_def_pos ^ y
		    )(Util.interval_list lb ub) "" in
  let neg_can = 
    List.fold_right (fun x y ->
		       let nvr_id_neg = nvr_counter#next in
		       let nvr_str_neg = mk_nvr_str_interval nvr_id_neg in
		       let nvr_def_str_neg =  mk_nvr_def_str_interval nvr_id_neg in
		       let nvr_def_decl_body_neg = "(/= ( "^mode_var^ " _M)"^string_of_int(x)^")" in
		       let interval_nvr_decl_neg = "(define "^nvr_str_neg^" :: bool)\n" in
		       let interval_nvr_def_neg = "(define "^nvr_def_str_neg^" ::(-> _nat bool) (lambda ( _M::_nat) (/= ( "^mode_var^ " _M) "^string_of_int(x)^")))\n" in
		       let _ = Hashtbl.replace nvr_to_info_hash nvr_str_neg (REL(NEQ,STRING(mode_var),NUM(x)),nvr_id_neg,L_BOOL,nvr_def_str_neg,nvr_def_decl_body_neg) in
			 interval_nvr_decl_neg ^ interval_nvr_def_neg ^ y
		    )(Util.interval_list lb ub) "" in
      pos_can, neg_can



let nvr_to_nvr_def_decl_body nvr_str = 
  let _,_,_,_,nvr_def_decl_str = Hashtbl.find nvr_to_info_hash nvr_str in
    nvr_def_decl_str

let nvr_to_expr nvr_str =
  let term,_,_,_,_ = Hashtbl.find nvr_to_info_hash nvr_str in
    term 

let nvr_to_nvr_def nvr_str = 
  let _,_,_,nvr_def,_ = Hashtbl.find nvr_to_info_hash nvr_str in
    nvr_def

let mk_nvr_decl_str nvr_id term ty =
  let m_ty = if ty = L_BOOL then M_BOOL else ty in
  let nvr_str = mk_nvr_str nvr_id in
  let nvr_decl = solver#get#define_const_string nvr_str ty in
  let buf = Buffer.create 100 in
  let term_buf = Lus_convert_yc.yc_expr_buffer GENERAL term in
  let nvr_def_str =  (mk_nvr_def_str nvr_id) in 
    solver#get#define_fun_buffer buf 
      nvr_def_str (M_FUNC[M_NAT;m_ty])
      [(solver#get#position_var1,M_NAT)] term_buf;
  let nvr_def_decl_body = Buffer.contents  term_buf in
  let nvr_def_decl = (Buffer.contents buf) in
    (nvr_decl, nvr_def_str, nvr_def_decl, nvr_def_decl_body )


(* Set up new variables for invariant candidates*)
let setup_nvr term ty =
  let nvr_id = nvr_counter#next in
  let nvr_str = mk_nvr_str nvr_id in
  let nvr_decl, nvr_def_str, nvr_def_decl, nvr_def_decl_body = 
    mk_nvr_decl_str nvr_id term ty in 

    Hashtbl.replace 
      nvr_to_info_hash 
      nvr_str 
      (term, nvr_id, ty, nvr_def_str, nvr_def_decl_body);
    (nvr_decl, nvr_def_decl) 


let get_bool_nvrs () = 
  Hashtbl.fold (fun x (_,_,ty,_,_) z -> 
    if ty = L_BOOL then x::z else z) nvr_to_info_hash [] 

let get_int_nvrs () = 
  Hashtbl.fold (fun x (_,_,ty,_,_) z -> 
    if ty = L_INT then x::z else z) nvr_to_info_hash [] 

let get_all_nvrs () =
  Hashtbl.fold (fun x y z -> x::z) nvr_to_info_hash [] 

let get_all_ndef () =
   Hashtbl.fold (fun x (_,_,_,y,_) z -> y::z) nvr_to_info_hash [] 


let mk_one_nvr_eq_cmd nvr_str nvr_def_str ty position  = 
  Lus_convert_yc.simple_command_string 
    (ASSERT (
      F_EQ (PRED(nvr_str,[]), PRED(nvr_def_str, [position]), ty))) 

let mk_nvr_eq_cmds position  = 
  Hashtbl.fold (fun x (_,_,ty,nvr_def_str,_) z -> 
    (mk_one_nvr_eq_cmd x nvr_def_str ty position) ^ z
  ) nvr_to_info_hash "" 


let bool_newvar_defs bool_sub_exprs = 
  let new_var_buf = Buffer.create 10000 in
      List.iter (fun x -> 
      let nvr_decl_str, nvr_def_decl_str = setup_nvr x L_BOOL in
	Buffer.add_string new_var_buf nvr_decl_str;
        Buffer.add_string new_var_buf nvr_def_decl_str;
    ) bool_sub_exprs;   
    Buffer.contents new_var_buf


let int_newvar_defs int_sub_exprs =  
  let new_var_buf = Buffer.create 10000 in
    List.iter (fun x -> 
      let nvr_decl_str, nvr_def_decl  = setup_nvr x L_INT in
	Buffer.add_string new_var_buf nvr_decl_str;
	Buffer.add_string new_var_buf nvr_def_decl;
    )int_sub_exprs;    

  if (!Globals.is_inter && !OldFlags.mode_inv) then (
    let interval_buf = make_interval_candidate() in
      Buffer.add_string new_var_buf interval_buf;
	   Buffer.contents new_var_buf)
  else
    Buffer.contents new_var_buf


let nvr_stepn_asserts equiv_class ty positions =   
  let nvr_defs = List.map (fun x -> nvr_to_nvr_def x) equiv_class in
  let mk_one_eq x y pos = F_EQ (PRED(x,[pos]), PRED(y, [pos]), ty)in
  let rec mk_eqs l pos =
    match l with 
	      [] -> []
      | hd::[] -> []
      | hd::(hd2::tl) ->
          (mk_one_eq hd hd2 pos)::(mk_eqs (hd2::tl) pos) in
  let eqs = List.map (fun x -> mk_eqs nvr_defs x) positions in 
    eqs 


let mk_not_ands fml_list = 
    if (List.length fml_list) < 1 
    then "" 
    else  
      let ands = List.fold_right (fun x y -> F_AND(x,y)) fml_list F_TRUE in
      let fml_assert = 
	         Lus_convert_yc.simple_command_string (ASSERT (F_NOT ands)) in
	     fml_assert







