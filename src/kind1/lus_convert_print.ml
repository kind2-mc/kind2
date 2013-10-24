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

(* print the ASTs *)
open Types
open Lus_convert
open Exceptions

let soi = string_of_int
let nl = "\n"
let cnl = ",\n"

let type_string ty = 
  match ty with 
      L_BOOL -> "B"
    | L_INT -> "I"
    | L_REAL -> "R"
    | L_TUPLE _ 
    | L_RECORD _ 
    | L_TYPEDEF _
    | L_INT_RANGE _ -> "RANGE"
    | L_UNDET _ 
	-> "ERROR L"
    | M_BOOL _ 
    | M_NAT  _
    | M_FUNC _ 
	-> "ERROR M"


let rec lustre_term_string (s,t) indent =
  match s with 
      S_TRUE -> indent^"TRUE"
    | S_FALSE -> indent^"FALSE"
    | S_INT(x) -> indent^"INT("^(soi x)^")"
    | S_REAL(i,n,d) -> indent^"REAL("^(soi i)^","^(soi n)^","^(soi d)^")"
    | S_VAR(sym,id) -> indent^"VAR("^sym^","^(soi id)^")"
    | S_AND(s1,s2) -> 
         indent^"AND(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_OR(s1,s2) ->
         indent^"OR(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_IMPL(s1,s2) ->
         indent^"IMPL(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_XOR(s1,s2) ->
         indent^"XOR(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_NOT(s1) -> 
         indent^"NOT(\n"^
         lustre_term_string s1 (indent^" ")^nl^
         indent^")"
    | S_PRE(s1) ->
         indent^"PRE(\n"^
         lustre_term_string s1 (indent^" ")^nl^
         indent^")"
    | S_FBY(s1,i,s2) ->
         indent^"OR(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         indent^" "^(soi i)^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_FOLLOWEDBY(s1,s2) ->
         indent^"->(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_CONDACT(s1,s2,s3,s4) ->
         indent^"CONDACT(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^cnl^
         lustre_term_string s3 (indent^" ")^cnl^
         lustre_term_string s4 (indent^" ")^nl^
         indent^")"
    | S_ITE(s1,s2,s3) ->
         indent^"ITE(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^cnl^
         lustre_term_string s3 (indent^" ")^nl^
         indent^")"
    | S_EQ(s1,s2) ->
         indent^"=(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_LT(s1,s2) ->
         indent^"<(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_GT(s1,s2) ->
         indent^">(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_LTE(s1,s2) ->
         indent^"<=(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_GTE(s1,s2) ->
         indent^">=(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_PLUS(s1,s2) ->
         indent^"+(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_MINUS(s1,s2) ->
         indent^"-(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_MULT(s1,s2) ->
         indent^"*(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_DIV(s1,s2) ->
         indent^"/(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_INTDIV(s1,s2) ->
         indent^"INTDIV(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_MOD(s1,s2) ->
         indent^"MOD(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_UMINUS(s1) ->
         indent^"-(\n"^
         lustre_term_string s1 (indent^" ")^nl^
         indent^")"
    | S_COERCE_TO_INT(s1) -> (* not applicable to cvcl? *)
         indent^"TO_INT(\n"^
         lustre_term_string s1 (indent^" ")^nl^
         indent^")"
    | S_COERCE_TO_REAL(s1) -> (* not applicable to cvcl? *)
         indent^"TO_REAL(\n"^
         lustre_term_string s1 (indent^" ")^nl^
         indent^")"
    | S_CURRENT(S_WHEN(s1,s2),_) -> (* different clock *)
         indent^"CURRENT(WHEN(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^"))"
    | S_RECORDLIT(s1) ->
        let rs =
          List.fold_left (fun s (field,e) -> 
              s^indent^" "^field^":\n"^
              (lustre_term_string e (indent^"  "))^nl
          ) "" s1 
        in
        indent^"RECORD_LIT(\n"^rs^indent^")"
    | S_TUPLELIT(s1) ->
        let rs =
          List.fold_left (fun s e -> 
              s^(lustre_term_string e (indent^"  "))^nl
          ) "" s1 
        in
        indent^"TUPLE_LIT(\n"^rs^indent^")"
    | S_RECORDREF(s1,fieldname) ->
        (lustre_term_string s1 indent)^"."^fieldname
    | S_TUPLEREF(s1,index) ->
        (lustre_term_string s1 indent)^"."^(soi index)
    | S_CURRENT(s1) -> (* if no clock change, does nothing *)
         indent^"CURRENT(\n"^
         lustre_term_string s1 (indent^" ")^nl^
         indent^")"
    | S_DEF(nid,s1,s2) -> (* this includes a "dummy" ONE expr *)
         indent^"DEF(\n"^
         lustre_term_string s1 (indent^" ")^cnl^
         lustre_term_string s2 (indent^" ")^nl^
         indent^")"
    | S_ASSERT(nid,s1) -> 
         indent^"ASSERT(\n"^
         lustre_term_string s1 (indent^" ")^nl^
         indent^")"
    | S_NODE(nid,lnum,pnum,params) -> (* flatten the node call *)
        let rs =
          List.fold_left (fun s e -> 
              s^(lustre_term_string e (indent^"  "))^nl
          ) "" params 
        in
        let name = Tables.get_nodename nid in
        indent^"NODE_"^name^"_"^(soi lnum)^"(\n"^rs^indent^")"
    | _ -> "{UNKNOWN TERM}"


(* il_expression -> string *)
let rec expr_term_string e indent =
    match e with
      (* we need to define constant arrays because, eg. pre(false) = nil *)
        ZERO -> indent^"ZERO"
      | ONE -> indent^"ONE"
      | STEP_BASE -> indent^"_base"
      | POSITION_VAR(s) -> indent^"POS("^s^")"
      | INT_CONST(e1) -> 
          indent^"INT(\n"^
          expr_term_string e1 (indent^" ")^nl^
          indent^")"
      | REAL_CONST(e1,_) -> 
          indent^"REAL(\n"^
          expr_term_string e1 (indent^" ")^nl^
          indent^")"
      | STRING x -> indent^"STRING("^x^")"
      | NUM(x) -> indent^"NUM("^(soi x)^")"
      | PLUS(e1,e2) -> 
          indent^"+(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | MINUS(e1,e2) -> 
          indent^"-(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | UMINUS(e1) -> 
          indent^"-(\n"^
          expr_term_string e1 (indent^" ")^nl^
          indent^")"
      | MULT(e1,e2) -> 
          indent^"*(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | DIV(e1,e2) -> 
          indent^"/(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | INTDIV(e1,e2) -> 
          indent^"INTDIV(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | MOD(e1,e2) -> 
          indent^"MOD(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | REL(EQ,e1,e2) ->
          indent^"=(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | REL(NEQ,e1,e2) ->
          indent^"~=(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | REL(LT,e1,e2) ->
          indent^"<(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | REL(GT,e1,e2) ->
          indent^">(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | REL(LTE,e1,e2) ->
          indent^"<=(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | REL(GTE,e1,e2) ->
          indent^">=(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | ITE(e1,e2,e3) -> 
          indent^"ITE(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^cnl^
          expr_term_string e3 (indent^" ")^nl^
          indent^")"
      | STREAM_ITE(e1,e2,e3) ->
          indent^"STREAM_ITE(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^cnl^
          expr_term_string e3 (indent^" ")^nl^
          indent^")"
      | B_AND(e1,e2) -> 
          indent^"AND(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | B_OR(e1,e2) -> 
          indent^"OR(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | B_IMPL(e1,e2) -> 
          indent^"IMPL(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | B_NOT(e1) -> 
          indent^"NOT(\n"^
          expr_term_string e1 (indent^" ")^nl^
          indent^")"
      | B_IFF(e1,e2) -> 
          indent^"IFF(\n"^
          expr_term_string e1 (indent^" ")^cnl^
          expr_term_string e2 (indent^" ")^nl^
          indent^")"
      | VAR_GET(s,d,(NUM nk'),i) -> 
                  let nk = Tables.resolve_substitution nk' in
          indent^"VAR_GET("^s.s^",depth "^(soi d)^",id "^(soi nk)^cnl^
          (expr_term_string i (indent^"  "))^nl^
          indent^")" ^

          indent^"ORIGINAL VAR_GET("^s.s^",depth "^(soi d)^",id "^(soi nk')^cnl^
          (expr_term_string i (indent^"  "))^nl^
          indent^")"


      | RECORD_LIT(el) -> 
          let rs =
            List.fold_left (fun s (field,e) -> 
                s^indent^" "^field^":\n"^
                (expr_term_string e (indent^"  "))^nl
            ) "" el 
          in
          indent^"RECORD_LIT(\n"^rs^indent^")"
      | RECORDREF(e1,field) -> 
          (expr_term_string e1 indent)^"."^field
      | TUPLE_LIT(el) -> 
          let rs =
            List.fold_left (fun s e -> 
                s^indent^(expr_term_string e (indent^"  "))^nl
            ) "" el 
          in
          indent^"TUPLE_LIT(\n"^rs^indent^")"
      | TUPLEREF(e1,index) -> 
          (expr_term_string e1 indent)^"."^(soi index)
      | x -> "{UNKNOWN EXPRESSION}"

let rec expr_formula_string f indent =
    match f with
        F_TRUE -> indent^"F_TRUE"
      | F_FALSE -> indent^"F_FALSE"
      | F_STR(s1) -> indent^"F_STRING("^s1^")"
      | F_EQ(c1,c2,_) -> 
          indent^"F_EQ(\n"^
          expr_term_string c1 (indent^" ")^cnl^
          expr_term_string c2 (indent^" ")^nl^
          indent^")"
      | F_NOT(f1) -> 
          indent^"F_NOT(\n"^
          expr_formula_string f1 (indent^" ")^nl^
          indent^")"
      | F_AND(f1,f2) -> 
          indent^"F_AND(\n"^
          expr_formula_string f1 (indent^" ")^cnl^
          expr_formula_string f2 (indent^" ")^nl^
          indent^")"
      | _ -> raise (ConversionError "expr_formula_string")

let print_lustre_term t =
  print_string ((lustre_term_string t "")^"\n")

let print_expr_term t =
  print_string ((expr_term_string t "")^"\n")

let expr_string t = expr_term_string t ""

let print_expr_formula t =
  print_string ((expr_formula_string t "")^"\n")


let print_node_def (id,list) =

  print_string "*** Node : ";
  print_int id;
  let internal_name = Tables.get_nodename id in 
  let original_name = Tables.resolve_var_name internal_name in
  print_string (" # " ^ internal_name ^ " ## " ^ original_name );
  print_string "\n----------------\n"  ;
  List.iter 
    (fun x -> print_lustre_term x;   
      print_string "\n==================\n" 
    ) 
    list;
  print_string "\n"

   
let print_node_defs () = 
  let node_list = Tables.fold_node_defs () in
    ignore (List.map (fun x -> print_node_def x) node_list )




let rec prop_term_string (s,t) indent =
  match s with 
      S_TRUE -> indent^"true"
    | S_FALSE -> indent^"false"
    | S_INT(x) -> indent^" "^(soi x)
    | S_REAL(i,n,d) -> indent^"REAL("^(soi i)^","^(soi n)^","^(soi d)^")"
    | S_VAR(sym,id) -> indent^Tables.varid_to_orginal_name id
    | S_AND(s1,s2) -> 
         prop_term_string s1 indent ^ prop_term_string s2 (indent^" and ")
    | S_OR(s1,s2) ->
	prop_term_string s1 indent ^ prop_term_string s2 (indent^" or ")
   
    | S_IMPL(s1,s2) ->
	prop_term_string s1 indent ^ prop_term_string s2 (indent^" => ")
		  
    | S_XOR(s1,s2) ->
	prop_term_string s1 indent ^ prop_term_string s2 (indent^" xor ")
    | S_NOT(s1) -> 
	  prop_term_string s1 (indent^"not ")
    | S_PRE(s1) ->
	 prop_term_string s1 (indent^"pre ")
    | S_FBY(s1,i,s2) ->
        ""
    | S_FOLLOWEDBY(s1,s2) ->
	prop_term_string s1 indent ^ prop_term_string s2 (indent^" -> ")
    | S_CONDACT(s1,s2,s3,s4) ->
	""
    | S_ITE(s1,s2,s3) ->
	"if " ^ prop_term_string s1 (indent^ "") ^ " then (" ^ prop_term_string s2 (indent^"") ^ ") else (" ^ prop_term_string s3 (indent^ "") ^ ")"
    | S_EQ(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" = ") ^ ")"
    | S_LT(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" < ") ^ ")"
    | S_GT(s1,s2) ->
    	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" > ") ^ ")"
    | S_LTE(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" <= ") ^ ")"
    | S_GTE(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" >= ") ^ ")"
    | S_PLUS(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" + ") ^ ")"
    | S_MINUS(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" - ") ^ ")"
    | S_MULT(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" * ") ^ ")"
    | S_DIV(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" / ") ^ ")"
    | S_INTDIV(s1,s2) ->
	""
    | S_MOD(s1,s2) ->
	prop_term_string s1 (indent ^ "(") ^ prop_term_string s2 (indent^" mod ") ^ ")"      
    | S_UMINUS(s1) ->
	 prop_term_string s1 (indent^"- ")
    | S_COERCE_TO_INT(s1) -> (* not applicable to cvcl? *)
	 prop_term_string s1 (indent^"to_int ")
    | S_COERCE_TO_REAL(s1) -> (* not applicable to cvcl? *)
	prop_term_string s1 (indent^"to_real ")
    | _ -> ""
   


let mk_property_string p = 
  prop_term_string p ""
  
