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

let is_true x =
  match x with ONE -> true | _ -> false 

let is_false x =
  match x with ZERO -> true | _ -> false 

let is_true_or_false x = 
  match x with 
      ZERO
    | ONE -> true
    | _ -> false 

let is_one_or_zero x = 
  match x with 
      INT_CONST (NUM i) -> if ( i= 0 || i = 1) then true else false  
    | NUM i -> if ( i= 0 || i = 1) then true else false  
    | _ -> false 

let pr_expr x =
  Lus_convert_print.print_expr_term x     

let pr = print_string

let rec contains_base t =
  match t with 
    ZERO 
  | ONE 
      -> false 
  | STEP_BASE
      -> (failwith "should not be here")
  | POSITION_VAR _
  | INT_CONST _
  | REAL_CONST( _, _)
  | STRING _
  | NUM _
  | FLOAT _
      -> false
  | VAR_GET (s,c,_,_)

    (*-> if (c != 0)
    then true
      else false *)

    -> false

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
    -> (contains_base l) || (contains_base r) 
  | B_NOT ex
  | UMINUS ex 
    -> (contains_base ex)
  | REL (_, l ,r ) 
    -> (contains_base l) || (contains_base r) 
  | ITE (a,b,c)
  | STREAM_ITE (a,b,c) 
    -> (contains_base a) || (contains_base b) || (contains_base c) 
  | RECORD_LIT record_list 
     -> List.fold_right 
	(fun (_,y) x -> (contains_base y) || x )  record_list false 
  | RECORDREF (l,_)
  | TUPLEREF  (l,_)
    ->  (contains_base l)
  | TUPLE_LIT tuple_list
    ->  List.fold_right 
	(fun y x -> (contains_base y ) || x )  tuple_list false 
  | PRED (_,il_list)
    ->  List.fold_right 
	(fun y x -> (contains_base y) || x )  il_list false 



let rec is_trivial_ite expr = 
  match expr with 
     ITE (a,b,c) -> 
       if (is_true_or_false b && is_true_or_false c)
       then true
       else false
    | B_NOT x -> is_trivial_ite x 
    | B_IFF (b, c) -> 
	  (is_true_or_false b) || (is_true_or_false c)
    | _ -> false
	
let filter_trivial_ite l = 
  List.filter (fun x -> not (is_trivial_ite x)) l 
 

let filter_base expr_list =
  List.filter (
    fun x -> 
    not (contains_base x ) && not (is_trivial_ite x) 
  )
    expr_list


(* get children with types *)
let rec il_expr_chld_type f =
  match f with 
    ZERO 
  | ONE 
    -> [(f,L_BOOL)]
  | STEP_BASE
    -> []
  | POSITION_VAR _
    -> []
  | INT_CONST _
    -> [(f,L_INT)]
  | REAL_CONST( _, _)
    -> [(f,L_REAL)]    
  | STRING _
    -> failwith "not sure about how to do this"
  | NUM _ 
    -> [(f,L_INT)]
  | FLOAT _
    -> [(f,L_REAL)]
  | VAR_GET (_,_,(NUM id),_)
    -> let id' = Tables.resolve_substitution id in
       let _,_,ty,_ = Tables.varid_to_info id' in
	   [(f,ty)]
  | PLUS (l,r)
  | MINUS (l,r)
  | MULT (l,r)
  | DIV (l,r)
  | INTDIV (l,r)
  | MOD (l,r)
      -> let l_chls = (il_expr_chld_type l) in
      let r_chls = (il_expr_chld_type r) in
      let _,ty = List.hd r_chls in
	[(f,ty)] @ l_chls @ r_chls 
  | B_AND (l,r)
  | B_OR (l,r)
  | B_IFF (l,r)
  | B_IMPL (l,r)
    -> [(f,L_BOOL)]@(il_expr_chld_type l)@(il_expr_chld_type r) 
  | B_NOT ex
    -> [(f,L_BOOL)]@(il_expr_chld_type ex) 
  | UMINUS ex 
    -> let ex_chls = (il_expr_chld_type ex) in
    let _,ty = List.hd ex_chls in
      [(f,ty)] @ ex_chls 
  | REL (_, l ,r ) 
    -> [(f,L_BOOL)]@(il_expr_chld_type l)@(il_expr_chld_type r) 
  | ITE (a,b,c)
(*    -> [(f,L_BOOL)]@
       (il_expr_chld_type a) @
       (il_expr_chld_type b) @
       (il_expr_chld_type c)
*)
  | STREAM_ITE (a,b,c) 
    -> let b_chls = (il_expr_chld_type b) in
    let _,ty = List.hd b_chls in
      [(f,ty)]@
       (il_expr_chld_type a) @
        b_chls @
       (il_expr_chld_type c)
  | RECORD_LIT _
  | RECORDREF _
  | TUPLEREF  _
  | TUPLE_LIT _
      -> failwith "what is the type of record?"
  | PRED (_,il_list)
     -> failwith "what is a pred in expr?"
  | _  -> failwith " Non exhaustive pattern matching"

(* all eqs in a formula *)
let rec il_formula_eqs f = 
  match f with 
    F_TRUE 
  | F_FALSE
  | F_STR _ 
    -> []
  | F_NOT ch 
    -> il_formula_eqs ch
  | F_EQ (l,r,t)
    -> [(l,r,t)]
  | F_AND (l,r) 
  | F_OR (l,r)
  | F_IMPL (l,r)
      -> (il_formula_eqs l) @ (il_formula_eqs r) 
  | F_PRED (_,il_list) 
    -> failwith "F_PRED in il_fromula_eqs"
  | _ -> failwith "Unknown il_formula type" 
      


let mk_eq x1 x2 ty = 
  match ty with 
      L_BOOL -> B_IFF(x1,x2) 
    | L_INT ->  REL(EQ,x1,x2)
    | L_REAL -> REL(EQ,x1,x2)
    | L_INT_RANGE(_,_) -> REL(EQ,x1,x2)
    | _ -> failwith "unknown eq type"


let print_expr_list l = 
  print_string "------ expr list ----- \n";
  List.iter (fun x ->
    pr "##\n";
    Lus_convert_print.print_expr_term x;
    print_string "\n") 
    l ;
  print_string "\n" 



let rec replace_stream_ite t =
  match t with 
    ZERO 
  | ONE 
      -> t
  | STEP_BASE -> failwith "shoul not be here"
  | POSITION_VAR _
  | INT_CONST _
  | REAL_CONST( _, _)
  | STRING _
  | NUM _
  | FLOAT _
      -> t
  | VAR_GET (a,b,(NUM c),d) ->  
      let c' = Tables.resolve_substitution c in
      VAR_GET (a,b,(NUM c'),d)
  | PLUS (l,r) 
    -> PLUS (replace_stream_ite l, replace_stream_ite r)
  | MINUS (l,r)
    -> MINUS (replace_stream_ite l, replace_stream_ite r)
  | MULT (l,r)
    -> MULT (replace_stream_ite l, replace_stream_ite r)
  | DIV (l,r)
    -> DIV (replace_stream_ite l, replace_stream_ite r)
  | INTDIV (l,r)
    -> INTDIV (replace_stream_ite l, replace_stream_ite r)
  | MOD (l,r)
    -> MOD (replace_stream_ite l, replace_stream_ite r)
  | B_AND (l,r)
    -> B_AND (replace_stream_ite l, replace_stream_ite r)
    | B_OR (l,r)
    -> B_OR (replace_stream_ite l, replace_stream_ite r)
  | B_IFF (l,r)
    -> B_IFF (replace_stream_ite l, replace_stream_ite r)
  | B_IMPL (l,r)
    -> B_IMPL (replace_stream_ite l, replace_stream_ite r)
  | B_NOT ex
    -> B_NOT (replace_stream_ite ex)
  | UMINUS ex 
    -> UMINUS (replace_stream_ite ex)
  | REL (rel, l ,r ) 
    -> REL (rel,(replace_stream_ite l),(replace_stream_ite r))
  | ITE (a,b,c)
    -> ITE (replace_stream_ite a,replace_stream_ite b,replace_stream_ite c)
  | STREAM_ITE (a,b,c) 
(*    -> STREAM_ITE (replace_stream_ite a,replace_stream_ite b,replace_stream_ite c) *)
    -> (replace_stream_ite c) 
  | RECORD_LIT record_list 
     -> RECORD_LIT (
       List.map  (fun (x,y) -> x, replace_stream_ite y )  record_list) 
  | RECORDREF (l,s)
      -> RECORDREF (replace_stream_ite l, s)
  | TUPLEREF  (l,s)
    ->  TUPLEREF (replace_stream_ite l, s)
  | TUPLE_LIT tuple_list
    ->  TUPLE_LIT (
      List.map (fun x -> replace_stream_ite x)   tuple_list ) 
  | PRED (s,il_list)
    ->  PRED (s, (List.map (fun x -> replace_stream_ite x) il_list))
 | _  -> failwith " Non exhaustive pattern matching"


let rec replace_var_get t =
  match t with 
    ZERO 
  | ONE 
  | STEP_BASE
  | POSITION_VAR _
  | INT_CONST _
  | REAL_CONST( _, _)
  | STRING _
  | NUM _
  | FLOAT _
      -> t
  | VAR_GET (a,b,(NUM c),d) ->  
      let c' = Tables.resolve_substitution c in
      VAR_GET (a,b,(NUM c'),d)
  | PLUS (l,r) 
    -> PLUS (replace_var_get l, replace_var_get r)
  | MINUS (l,r)
    -> MINUS (replace_var_get l, replace_var_get r)
  | MULT (l,r)
    -> MULT (replace_var_get l, replace_var_get r)
  | DIV (l,r)
    -> DIV (replace_var_get l, replace_var_get r)
  | INTDIV (l,r)
    -> INTDIV (replace_var_get l, replace_var_get r)
  | MOD (l,r)
    -> MOD (replace_var_get l, replace_var_get r)
  | B_AND (l,r)
    -> B_AND (replace_var_get l, replace_var_get r)
  | B_OR (l,r)
    -> B_OR (replace_var_get l, replace_var_get r)
  | B_IFF (l,r)
    -> B_IFF (replace_var_get l, replace_var_get r)
  | B_IMPL (l,r)
    -> B_IMPL (replace_var_get l, replace_var_get r)
  | B_NOT ex
    -> B_NOT (replace_var_get ex)
  | UMINUS ex 
    -> UMINUS (replace_var_get ex)
  | REL (rel, l ,r ) 
    -> REL (rel,(replace_var_get l),(replace_var_get r))
  | ITE (a,b,c)
    -> ITE (replace_var_get a,replace_var_get b,replace_var_get c)
  | STREAM_ITE (a,b,c) 
    -> STREAM_ITE (replace_var_get a,replace_var_get b,replace_var_get c)
  | RECORD_LIT record_list 
     -> RECORD_LIT (
       List.map  (fun (x,y) -> x, replace_var_get y )  record_list) 
  | RECORDREF (l,s)
      -> RECORDREF (replace_var_get l, s)
  | TUPLEREF  (l,s)
    ->  TUPLEREF (replace_var_get l, s)
  | TUPLE_LIT tuple_list
    ->  TUPLE_LIT (
      List.map (fun x -> replace_var_get x)   tuple_list ) 
  | PRED (s,il_list)
    ->  PRED (s, (List.map (fun x -> replace_var_get x) il_list))
 | _  -> failwith " Non exhaustive pattern matching"

open Tables



let rec map_org_il_expr t =
  let parent str = "(" ^ str ^ ")"  in
  let binary_op op_str l r = 
    let l_str = (map_org_il_expr l) in
    let r_str = (map_org_il_expr r) in
      parent ( l_str ^ " " ^ op_str ^ " " ^ r_str) in 
let binary_op_2 op_str l r = 
    let l_str = (map_org_il_expr l) in
    let r_str = (map_org_il_expr r) in
     parent ( "not "^ parent ( l_str ^ " " ^ op_str ^ " " ^ r_str)) in 
  let unary_op  op_str t = 
    let t_str = (map_org_il_expr t) in
      parent ( op_str ^ " " ^ t_str) in 

  match t with 
    ZERO -> "false"
  | ONE -> "true"
  | STEP_BASE -> failwith "step base" 
  | POSITION_VAR s -> failwith ("position var" ^ s)
  | INT_CONST i  ->  map_org_il_expr i
  | REAL_CONST( a,b) -> (
      let ret = map_org_il_expr a  in
	ret
    )

  | STRING str ->  Tables.internal_name_to_original_name str (* Added by Teme*)
  | NUM i -> string_of_int i 
  | FLOAT f  -> string_of_float f 
  | VAR_GET (name,depth,(NUM c),position) ->  
      let org_name = Tables.varid_to_orginal_name c in
(*	(org_name ^ " :: " ^ (string_of_int depth) ^ (map_org_il_expr position)) *)
	if (0 = depth) then org_name
	else (
	  assert (depth >= 1);
	  let l  = Util.n_to_m 1 depth in
	    List.fold_right (fun x y -> "(pre " ^ y ^ ")") l org_name   
	)
  | PLUS (l,r) 
    ->  binary_op "+" l r
  | MINUS (l,r)
    ->  binary_op "-" l r
  | MULT (l,r)
    ->  binary_op "*" l r 
  | DIV (l,r)
    ->  binary_op "/" l r 
  | INTDIV (l,r)
    ->  binary_op "div" l r 
  | MOD (l,r)
    ->  binary_op "mod" l r 
  | B_AND (l,r)
    ->  binary_op "and" l r 
  | B_OR (l,r)
    ->  binary_op "or" l r 
  | B_IFF (l,r)
    ->  binary_op "=" l r 
  | B_IMPL (l,r)
    ->  binary_op "=>" l r 
  | B_NOT ex
    ->  unary_op "not" ex
  | UMINUS ex 
    -> unary_op "-" ex
  | REL (rel, l ,r ) 
    -> (
      match rel with 
	  EQ -> binary_op "=" l r 
	| LT -> binary_op "<" l r 
	| GT -> binary_op ">" l r 
	| LTE -> binary_op "<=" l r 
	| GTE -> binary_op ">=" l r 
	| NEQ -> binary_op_2 "=" l r
    )
  | ITE (a,b,c)
    -> let str_a = map_org_il_expr a in
    let str_b = map_org_il_expr b in
    let str_c = map_org_il_expr c in
      parent ("if " ^ str_a ^ " then " ^ str_b ^ " else " ^ str_c) 
  | STREAM_ITE (a,b,c) 
    -> Lus_convert_print.print_expr_term (STREAM_ITE (a,b,c)); failwith "stream ite"
  | RECORD_LIT _
  | RECORDREF _
  | TUPLEREF  _
  | TUPLE_LIT _
  | PRED _
    ->  failwith "record or pred"
 | _  -> failwith " Non exhaustive pattern matching"

(* Teme : for invaraint *)

let rec invariant_map_org_il_expr t =
  let parent str = " (" ^ str ^ ") "  in
  let binary_op_2 op_str l r = 
    let l_str = (map_org_il_expr l) in
    let r_str = (map_org_il_expr r) in
     parent ( "not "^ parent ( l_str ^ " " ^ op_str ^ " " ^ r_str)) in 
  let binary_op op_str l r = 
    let l_str = (map_org_il_expr l) in
    let r_str = (map_org_il_expr r) in
      parent (" "^ op_str ^ " " ^ l_str ^ " " ^ r_str) in 
  let unary_op  op_str t = 
    let t_str = (map_org_il_expr t) in
      parent ( op_str ^ " " ^ t_str) in 
  match t with 
    ZERO -> "false"
  | ONE -> "true"
  | STEP_BASE -> failwith "step base" 
  | POSITION_VAR s -> failwith ("position var" ^ s)
  | INT_CONST i  ->  map_org_il_expr i
  | REAL_CONST( a,b) -> (
      let ret = map_org_il_expr a  in
	ret
    )
  | STRING str ->  str
  | NUM i -> string_of_int i 
  | FLOAT f  -> string_of_float f 
  | VAR_GET (name,depth,(NUM c),position) ->  
      let org_name = Tables.varid_to_orginal_name c in
(*	(org_name ^ " :: " ^ (string_of_int depth) ^ (map_org_il_expr position)) *)
	if (0 = depth) then org_name
	else (
	  assert (depth >= 1);
	  let l  = Util.n_to_m 1 depth in
	    List.fold_right (fun x y -> "(pre " ^ y ^ ")") l org_name   
	)
  | PLUS (l,r) 
    ->  binary_op "+" l r
  | MINUS (l,r)
    ->  binary_op "-" l r
  | MULT (l,r)
    ->  binary_op "*" l r 
  | DIV (l,r)
    ->  binary_op "/" l r 
  | INTDIV (l,r)
    ->  binary_op "div" l r 
  | MOD (l,r)
    ->  binary_op "mod" l r 
  | B_AND (l,r)
    ->  binary_op "and" l r 
  | B_OR (l,r)
    ->  binary_op "or" l r 
  | B_IFF (l,r)
    ->  binary_op "=" l r 
  | B_IMPL (l,r)
    ->  binary_op "=>" l r 
  | B_NOT ex
    ->  unary_op "not" ex
  | UMINUS ex 
    -> unary_op "-" ex
  | REL (rel, l ,r ) 
    -> (
      match rel with 
	  EQ -> binary_op "=" l r 
	| LT -> binary_op "<" l r 
	| GT -> binary_op ">" l r 
	| LTE -> binary_op "<=" l r 
	| GTE -> binary_op ">=" l r 
	| NEQ ->  binary_op_2 "=" l r 
    )
  | ITE (a,b,c)
    -> let str_a = map_org_il_expr a in
    let str_b = map_org_il_expr b in
    let str_c = map_org_il_expr c in
      parent ("if " ^ str_a ^ " then " ^ str_b ^ " else " ^ str_c) 
  | STREAM_ITE (a,b,c) 
    -> Lus_convert_print.print_expr_term (STREAM_ITE (a,b,c)); failwith "stream ite"
  | RECORD_LIT _
  | RECORDREF _
  | TUPLEREF  _
  | TUPLE_LIT _
  | PRED _
    ->  failwith "record or pred"
  | _  -> failwith " Non exhaustive pattern matching"


let filter_var_get l = 
  failwith "never call this";
  let is_var x =
    match x with Types.VAR_GET (_,_,_,_) -> true
      | _ -> false in
    List.filter (fun x -> not (is_var x)) l


let filter_sub_exprs l = 
  let l1 = filter_base l in
    l1

let mk_ands fls =  
  if (List.length fls) <= 0  
  then ""
  else let asserts_formula = 
    List.fold_right (fun x y -> F_AND(x,y)) fls F_TRUE  in
	 Lus_convert_yc.simple_command_string (ASSERT asserts_formula)
	   
let mk_not_ands fml_list = 
    if (List.length fml_list) < 1 
    then "" 
    else  
      let ands = List.fold_right (fun x y -> F_AND(x,y)) fml_list F_TRUE in
      let fml_assert = 
	Lus_convert_yc.simple_command_string (ASSERT (F_NOT ands)) in
	fml_assert ;;

let fold_list_with_op op l =
  let rec help_func l =
    match l with
       [] -> []
      | hd::[] -> []
      | hd::((hd2::tl) as tail) ->
         (op hd hd2)::(help_func tail)
  in
    help_func l
