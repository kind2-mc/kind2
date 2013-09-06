(*
This file is part of the Kind verifier

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

open Types
open Exceptions
open Lus_convert

(* first run scan_formula', then run sub_formula *)

let number_variables_inlined = ref 0

let get_number_variables_inlined () = !number_variables_inlined

let substitution_table = Hashtbl.create 10
let add_substitution nk c2 =
  incr number_variables_inlined;
  Hashtbl.replace substitution_table nk c2



(* returns the d,k,i tuple *)
let get_sub k =
  try
    let se = Hashtbl.find substitution_table k in
    Some (se)
  with Not_found -> None

let get_pos d pos d1 i =
  let i' =
    if d = 0 then 
      i
    else
      begin
        let pos_offset = Lus_convert.simplify_position_depth(pos) in
          PLUS(i,NUM(pos_offset))
      end
  in
  (d+d1, i')
 


(* il_expression -> string *)
(* if d = 0 then we keep the existing positions *)
let rec sub_term e d pos =
  begin
    match e with
      | PLUS(e1,e2) -> PLUS(sub_term e1 d pos,sub_term e2 d pos)
      | MINUS(e1,e2) -> MINUS(sub_term e1 d pos,sub_term e2 d pos) 
      | UMINUS(e1) -> UMINUS(sub_term e1 d pos)
      | MULT(e1,e2) -> MULT(sub_term e1 d pos,sub_term e2 d pos)
      | DIV(e1,e2) -> DIV(sub_term e1 d pos,sub_term e2 d pos)
      | INTDIV(e1,e2) -> INTDIV(sub_term e1 d pos,sub_term e2 d pos)
      | MOD(e1,e2) -> MOD(sub_term e1 d pos,sub_term e2 d pos)
      | REL(r1,e1,e2) -> REL(r1,sub_term e1 d pos,sub_term e2 d pos)
      | ITE(e1,e2,e3) -> 
          ITE(sub_term e1 d pos,sub_term e2 d pos,sub_term e3 d pos) 
      | STREAM_ITE(e1,e2,e3) -> 
          STREAM_ITE(sub_term e1 d pos,sub_term e2 d pos,sub_term e3 d pos)
      | B_AND(e1,e2) -> B_AND(sub_term e1 d pos,sub_term e2 d pos)
      | B_OR(e1,e2) -> B_OR(sub_term e1 d pos,sub_term e2 d pos)
      | B_IMPL(e1,e2) -> B_IMPL(sub_term e1 d pos,sub_term e2 d pos)
      | B_NOT(e1) -> B_NOT(sub_term e1 d pos)
      | B_IFF(e1,e2) -> B_IFF(sub_term e1 d pos,sub_term e2 d pos)
      | VAR_GET(s,d1,((NUM k) as k'),i) -> 
          let nk = Tables.resolve_substitution k in
          let (d',i') = get_pos d pos d1 i in
          begin
            match get_sub nk with
                None -> VAR_GET(s,d',k',i')
              | Some x -> sub_term x d' i'
          end
      | RECORD_LIT(el) -> 
         RECORD_LIT(List.map (fun (f1,e1) -> (f1,(sub_term e1 d pos)) ) el)
      | RECORDREF(e1,field) -> raise (Not_supported "inlining record")
      | TUPLE_LIT(el) -> 
         TUPLE_LIT(List.map (fun e1 -> (sub_term e1 d pos) ) el)
      | TUPLEREF(e1,index) -> raise (Not_supported "inlining tuple")
      | x -> x
  end

(* make sure the rhs contains no local or output variables behind pres *)
(* those can cause infinite recursion in substitution *)
(* we bound this both by the estimated size explosion of this term *)
(* returns true if safe to substitute *)
let rhs_check id e =
  let rhs_vars = ref [] in
  let terms = ref 0 in
  let rec rhs_check' e =
    incr terms;
    match e with
      | UMINUS(e1) -> rhs_check' e1
      | B_NOT(e1) -> rhs_check' e1
      | PLUS(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | MINUS(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | MULT(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | DIV(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | INTDIV(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | MOD(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | REL(r1,e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | B_AND(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | B_OR(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | B_IMPL(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | B_IFF(e1,e2) -> (rhs_check' e1) && (rhs_check' e2)
      | ITE(e1,e2,e3) -> (rhs_check' e1) && (rhs_check' e2) && (rhs_check' e3)
      | STREAM_ITE(e1,e2,e3) -> (rhs_check' e1) && (rhs_check' e2) && (rhs_check' e3)
      | VAR_GET(_,d,(NUM k),_) -> 
          let nk = Tables.resolve_substitution k in
          rhs_vars := nk::(!rhs_vars);
          d = 0 || (Tables.is_output_var nk)
      | RECORD_LIT(el) -> 
         List.fold_left (fun acc (_,e1) -> acc && (rhs_check' e1) ) true el
      | TUPLE_LIT(el) -> 
         List.fold_left (fun acc e1 -> acc && (rhs_check' e1) ) true el
      | x -> true
  in
  let result = rhs_check' e in
  let num = Tables.get_var_count (Tables.resolve_substitution id) in
  if result && (num * !terms) <= !OldFlags.aggressive_inlining then
    begin
      List.iter (fun x -> Tables.add_var_count x num) !rhs_vars;
      true
    end
  else
    false

(* store_defs is almost always true except for STATE VARS *)
(* returns (possibly truncated) version of formula *)
let scan_formula f' vrefs =
Coi.examine_assignments f';
let sub_var x c2 =
  not (List.mem x vrefs) && (rhs_check x c2)
in
let rec scan_formula' f =
  match f with
    | F_EQ(c1,c2,_) ->
      begin
        match c1 with
        | VAR_GET(_,_,(NUM k),_) ->
            let nk = Tables.resolve_substitution k in
            if sub_var nk c2 then
              begin
                add_substitution nk c2;
                F_TRUE
              end
            else
              f
        | _ -> f
      end
    | F_NOT(f1) -> F_NOT (scan_formula' f1)
    | F_AND(f1,f2) -> 
        Lus_convert.f_and (scan_formula' f1) (scan_formula' f2)
    | x -> x
in
scan_formula' f'

let rec sub_formula f =
  match f with
    | F_EQ(c1,c2,x) -> F_EQ(c1, sub_term c2 0 (NUM(0)),x)
    | F_NOT(f1) -> F_NOT (sub_formula f1)
    | F_AND(f1,f2) -> 
        Lus_convert.f_and (sub_formula f1) (sub_formula f2)
    | x -> x

let inlined_formula f vrefs =
  let f2 = scan_formula f vrefs in
  sub_formula f2
