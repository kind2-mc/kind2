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
open OldFlags
open Exceptions
open Channels

let solver = Globals.my_solver


let def_term_hash = Hashtbl.create 100 

let add_def_term_hash x y = Hashtbl.add def_term_hash  x y
 
let get_all_def_terms () =
  Hashtbl.fold (fun x y z -> y::z) def_term_hash [] 

(* the id is neg if this is a local variable *)
(* name, id, position offset *)
let current_vars = ref ([]:(string*int*int) list)
let add_current_var name id pos =
  current_vars := (name,id,pos)::(!current_vars)
let clear_current_vars () =
  current_vars := []
let get_current_vars () = !current_vars


(* also sets current_vars *)
(* pd is position depth (int) *)
(* keep here *)
let yc_simplify_var k pos alt mode pd solver =
   match k with
     NUM id ->
       begin
         try
           let (n,v,t,c) = Tables.safe_find_varinfo id "yc_simplify_var" in
             begin
               match mode,c with
                 (FRESH_INPUTS x),INPUT ->
                   let s = "_z_"^v^"__M" in
                   let fresh_varname = solver#get#fresh_varname_string s x in
                  add_current_var (fresh_varname) (-id) pd;
                    (fresh_varname),""
               | _,_ ->
                   add_current_var v id pd;
                   v,pos
           end
         with Not_found ->
           raise (IdNotFound (alt))
       end
    | _ -> raise (ConversionError "yc_simplify_var")


(* final translation to solver-radable format *)
(* also eliminates redundant variables and notes when they are used *)
(* il_expression -> string *)
(* keep here *)
let rec yc_expr_buffer mode e =
  let buf = Buffer.create 800 in
  begin
    match e with
      (* we need to define constant arrays because, eg. pre(false) = nil *)
        ZERO -> Buffer.add_string buf solver#get#zero_string
      | ONE -> Buffer.add_string buf solver#get#one_string
      | STEP_BASE -> Buffer.add_string buf solver#get#step_base_string
      | POSITION_VAR(s) -> 
              begin
                match mode with
                    GENERAL -> Buffer.add_string buf s
                  | STATE_VAR_GEN -> Buffer.add_string buf s
                  | FRESH_INPUTS x -> Buffer.add_string buf s
                  | N_STEP -> Buffer.add_string buf s
                  | DEPTH d -> 
                     let d' =
                       if !do_negative_index then
                         -d
                       else
                         d
                     in
                     Buffer.add_buffer buf (yc_expr_buffer mode (PLUS(STEP_BASE,NUM(d'))))
              end
      | INT_CONST(e1) -> 
                         Buffer.add_buffer buf (yc_expr_buffer mode e1)
                         
      | REAL_CONST(e1,_) -> 
                          Buffer.add_buffer buf (yc_expr_buffer mode e1)
                          
      | STRING x -> Buffer.add_string buf x
      | NUM(x) -> solver#get#buffer_of_num buf x
      (* can simplify these for negative numbers *)
      | PLUS(e1,NUM(n)) -> 
          let b1 = yc_expr_buffer mode e1 in
          if n < 0 then
            begin
              let b2 = yc_expr_buffer mode (NUM (-n)) in
              solver#get#buffer_of_binary buf solver#get#minus_string b1 b2
            end
          else
            begin
              let b2 = yc_expr_buffer mode (NUM n) in
              solver#get#buffer_of_binary buf solver#get#plus_string b1 b2
            end
      | PLUS(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#plus_string b1 b2
      | MINUS(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#minus_string b1 b2
      | UMINUS(e1) -> 
          if solver#get#supports_unary_minus then
            begin
              let b1 = yc_expr_buffer mode e1 in
              solver#get#buffer_of_unary buf solver#get#uminus_string b1
            end
          else
            begin
              let b1 = yc_expr_buffer mode (MINUS(NUM 0,e1)) in
              Buffer.add_buffer buf b1
            end
      | MULT(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#mult_string b1 b2
      | DIV(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#div_string b1 b2
      | INTDIV(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#intdiv_string b1 b2
      | MOD(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#mod_string b1 b2
      | REL(r1,e1,e2) ->
          begin
            match r1 with 
      (* the following convert cvcl BOOLEAN expressions into bool expressions *)
              | EQ -> 
                  let b1 = yc_expr_buffer mode e1 in
                  let b2 = yc_expr_buffer mode e2 in
                  solver#get#buffer_of_binary buf solver#get#eq_string b1 b2
              | LT -> 
                  let b1 = yc_expr_buffer mode e1 in
                  let b2 = yc_expr_buffer mode e2 in
                  solver#get#buffer_of_binary buf solver#get#lt_string b1 b2
              | GT -> 
                  let b1 = yc_expr_buffer mode e1 in
                  let b2 = yc_expr_buffer mode e2 in
                  solver#get#buffer_of_binary buf solver#get#gt_string b1 b2
              | LTE -> 
                  let b1 = yc_expr_buffer mode e1 in
                  let b2 = yc_expr_buffer mode e2 in
                  solver#get#buffer_of_binary buf solver#get#lte_string b1 b2
              | GTE -> 
                  let b1 = yc_expr_buffer mode e1 in
                  let b2 = yc_expr_buffer mode e2 in
                  solver#get#buffer_of_binary buf solver#get#gte_string b1 b2
	      | NEQ -> 
                  let b1 = yc_expr_buffer mode e1 in
                  let b2 = yc_expr_buffer mode e2 in
                  solver#get#buffer_of_binary buf solver#get#neq_string b1 b2
          end
      | ITE(e1,e2,e3) -> 
          begin
            let test_buf = yc_boolean_relation_buffer mode e1 solver#get#one_string in 
            let b1 = yc_expr_buffer mode e2 in
            let b2 = yc_expr_buffer mode e3 in
            solver#get#buffer_of_ite buf test_buf b1 b2
          end
      | STREAM_ITE(e1,e2,e3) ->
          begin
            match mode,e1 with
               (DEPTH d, REL(EQ,position,STEP_BASE)) ->
                 (* the one case we know about *)
                 let depth = Lus_convert.simplify_position_depth position in
                 if depth = d then
                   Buffer.add_buffer buf (yc_expr_buffer mode e2)
                 else
                   Buffer.add_buffer buf (yc_expr_buffer mode e3)
             | (N_STEP, REL(EQ,position,STEP_BASE)) ->
                 Buffer.add_buffer buf (yc_expr_buffer mode e3)
             | (_,_) ->
                 let test_buf = yc_boolean_relation_buffer mode e1 solver#get#one_string in 
                 let b1 = yc_expr_buffer mode e2 in
                 let b2 = yc_expr_buffer mode e3 in
                 solver#get#buffer_of_ite buf test_buf b1 b2
          end
      | B_AND(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#b_and_string b1 b2
      | B_OR(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#b_or_string b1 b2
      | B_IMPL(e1,e2) -> 
          if solver#get#term_impl_available then
            begin
              let b1 = yc_expr_buffer mode e1 in
              let b2 = yc_expr_buffer mode e2 in
              solver#get#buffer_of_binary buf solver#get#b_impl_string b1 b2
            end
          else
            Buffer.add_buffer buf (yc_expr_buffer mode (B_OR((B_NOT e1),e2)))
      | B_NOT(e1) -> 
          let b1 = yc_expr_buffer mode e1 in
          solver#get#buffer_of_unary buf solver#get#b_not_string b1
      | B_IFF(e1,e2) -> 
          let b1 = yc_expr_buffer mode e1 in
          let b2 = yc_expr_buffer mode e2 in
          solver#get#buffer_of_binary buf solver#get#b_iff_string b1 b2
      | VAR_GET(s,d,(NUM nk'),i) -> 
                  let nk = Tables.resolve_substitution nk' in
                  let k = (NUM nk) in
                  Tables.update_used_vars nk d e;
                  begin
                    match mode with
                        FRESH_INPUTS x ->
                             let pd = 
                               -(Lus_convert.simplify_position_depth (PLUS(i,NUM(x)))) 
                             in
                             let p =
                               Buffer.contents (yc_expr_buffer mode
                                 (MINUS(POSITION_VAR solver#get#position_var1,NUM(pd))))
                             in
                             let vs,_ = 
                               (yc_simplify_var k p "??" (FRESH_INPUTS pd) pd solver)
                             in
                             s.s <- vs;
                             Buffer.add_string buf vs
                      | _ -> let p =
                               Buffer.contents (yc_expr_buffer mode i)
                             in
                             let pd = -(Lus_convert.simplify_position_depth i) in
                             let vs,ps = yc_simplify_var k p "??" mode pd solver in
                             s.s <- vs;
                             Buffer.add_string buf (solver#get#string_of_var_ref vs ps)
                  end
      | RECORD_LIT(el) -> 
          let l1 = List.sort (compare) el in
          let l2 = List.map (fun (x,y) -> x,yc_expr_buffer mode y) l1 in
          solver#get#buffer_of_record buf l2
      | RECORDREF(e1,field) -> 
          let b1 = yc_expr_buffer mode e1 in
          solver#get#buffer_of_record_ref buf b1 field
      | TUPLE_LIT(el) -> 
          let l1 = List.map (fun x -> yc_expr_buffer mode x) el in
          solver#get#buffer_of_tuple buf l1
      | TUPLEREF(e1,index) -> 
          let b1 = yc_expr_buffer mode e1 in
          solver#get#buffer_of_tuple_ref buf b1 index
(* used during k-induction *)
      | PRED(s1,li) -> 
                      if List.length li > 0 then
                        begin
                          let li2 = 
                            List.map (fun x -> yc_expr_buffer mode x) li 
                          in
                          solver#get#buffer_of_pred buf s1 li2
                        end
                      else
                        Buffer.add_string buf s1

      | x ->   Lus_convert_print.print_expr_term x;  
	  raise (ConversionError "yc_expr_buffer")
  end;
  buf
and yc_boolean_relation_buffer mode e rh_string =
  let buf = Buffer.create 1600 in
  begin
    match e with
        REL(EQ,e4,e5) -> 
          let b1 = yc_expr_buffer mode e4 in
          let b2 = yc_expr_buffer mode e5 in
          solver#get#buffer_of_binary buf solver#get#eq_string b1 b2
      | REL(LT,e4,e5) -> 
          let b1 = yc_expr_buffer mode e4 in
          let b2 = yc_expr_buffer mode e5 in
          solver#get#buffer_of_binary buf solver#get#lt_string b1 b2
      | REL(GT,e4,e5) -> 
          let b1 = yc_expr_buffer mode e4 in
          let b2 = yc_expr_buffer mode e5 in
          solver#get#buffer_of_binary buf solver#get#gt_string b1 b2
      | REL(LTE,e4,e5) -> 
          let b1 = yc_expr_buffer mode e4 in
          let b2 = yc_expr_buffer mode e5 in
          solver#get#buffer_of_binary buf solver#get#lte_string b1 b2
      | REL(GTE,e4,e5) -> 
          let b1 = yc_expr_buffer mode e4 in
          let b2 = yc_expr_buffer mode e5 in
          solver#get#buffer_of_binary buf solver#get#gte_string b1 b2
      | _ -> 
          let b1 = yc_expr_buffer mode e in
          let b2 = Buffer.create 1600 in
          Buffer.add_string b2 rh_string;
          solver#get#buffer_of_binary buf solver#get#b_iff_string b1 b2
  end;
  buf


(* keep here *)
let yc_add_def solver lhs rhs s1 s2 = 
  let s = Buffer.create 1000 in
  solver#get#buffer_of_binary s solver#get#f_eq_string s1 s2;

(* PLEASE FIXME TEME - f_eq_string used here even for BOOL cases! *)
(*  let rhs_ids = List.map (fun (_,i)->i) rhs in*)
  let rhs_ids = List.fold_left (fun acc (_,i,pos)-> 
                  if not (List.mem (i,pos) acc) then
                    (i,pos)::acc
                  else
                    acc
                ) [] rhs 
  in
  match lhs with
    | [(_,x,_)] -> Deftable.def_add x s rhs_ids
    | (_,h,_)::t -> Deftable.def_add h s rhs_ids;
              List.iter (fun (_,x,_) ->
                Deftable.def_add_ref x h
              ) t
    | _ -> raise (ConversionError "yc_add_def")



(* il_formula -> string_buffer *)
(* store_defs is almost always true except for STATE VARS*)
(* stores variables definitions for later use (only those actually used) *)
(* keep here *)
let rec yc_formula_string_buffer mode coi_depth f =
  let buf = Buffer.create 6400 in
  begin
    match f with
        F_TRUE -> Buffer.add_string buf solver#get#true_string
      | F_FALSE -> Buffer.add_string buf solver#get#false_string
      | F_PRED (s1,li) -> 
                        if List.length li > 0 then
                          begin
                            let li2 = 
                              List.map (fun x -> yc_expr_buffer mode x) li 
                            in
                            solver#get#buffer_of_pred buf s1 li2
                          end
                        else
                          Buffer.add_string buf s1
      | F_STR(s1) -> Buffer.add_string buf s1
      | F_EQ(c1,c2,t) -> add_def_term_hash c1 c2;
	                 clear_current_vars ();
                         let s1 = (yc_expr_buffer mode c1) in
                         let lhs = get_current_vars () in
                         clear_current_vars ();
                         let s2 = (yc_expr_buffer mode c2) in
                         let rhs = get_current_vars () in
                         let eq_str = 
                           if t = L_BOOL then 
                             solver#get#f_iff_string
                           else
                             solver#get#f_eq_string
                         in
                         solver#get#buffer_of_binary buf eq_str s1 s2;
                         if mode != STATE_VAR_GEN then
                           yc_add_def solver lhs rhs s1 s2
      | F_NOT(f1) -> let s1 = yc_formula_string_buffer mode coi_depth f1 in
                     solver#get#buffer_of_unary buf solver#get#f_not_string s1
      | F_OR(f1,f2) -> let s1 = yc_formula_string_buffer mode coi_depth f1 in
                       let s2 = yc_formula_string_buffer mode coi_depth f2 in
                       solver#get#buffer_of_binary buf solver#get#f_or_string s1 s2
      | F_IMPL(f1,f2) -> let s1 = yc_formula_string_buffer mode coi_depth f1 in
                       let s2 = yc_formula_string_buffer mode coi_depth f2 in
                       solver#get#buffer_of_binary buf solver#get#f_impl_string s1 s2
      | F_AND(f1,f2) -> 
(* interestingly enough, the below (non-tail recursive) version is
slightly faster than a tail-recursive version *)
          let check_coi_f x =
            match x with
              | F_EQ(c1,_,_) -> Coi.check_coi c1 coi_depth
              | _ -> true
          in
          let rec getlist fas =
                match fas with
                  | F_AND((F_AND(_,_) as x),(F_AND(_,_) as y)) ->
                      (getlist x) @ (getlist y)
                  | F_AND((F_AND(_,_) as x),y) ->
                      if check_coi_f y then
                        y :: (getlist x)
                      else
                        (getlist x)
                  | F_AND(x,(F_AND(_,_) as y)) ->
                      if check_coi_f x then
                        x :: (getlist y)
                      else
                        (getlist y)
                  | F_AND(x,y) ->
                      let x1 = check_coi_f x in
                      let y1 = check_coi_f y in
                      begin
                        match x1,y1 with
                            true,true -> [x;y]
                          | true,_ -> [x]
                          | _,true -> [y]
                          | _ -> []
                      end
                  | _ -> raise (ConversionError "yc_formula_string_buffer")
          in
          let rebuild_conjunction form_list =
            if solver#get#boolean_connectives_strictly_binary then
              begin
                let rec remake_binary x = 
                  let buf2 = Buffer.create 800 in
                  match x with
                      [] -> Buffer.add_string buf2 solver#get#true_string; 
                            buf2
                    | [y] -> y
                    | y::ys -> 
                      let buf2 = Buffer.create 800 in
                      solver#get#buffer_of_binary buf2 solver#get#f_and_string y
                        (remake_binary ys);
                      buf2
                in
                Buffer.add_buffer buf (remake_binary form_list)
              end
            else
              solver#get#buffer_of_nary buf solver#get#f_and_string form_list
          in
          let fl = 
            List.map (fun x -> yc_formula_string_buffer mode coi_depth x) 
              (getlist f) 
          in
          rebuild_conjunction fl
  end;
  buf


(* il_formula -> string_buffer *)
(* does not do any bookkeepping, only translates the formula *)
(* used to generate formulas while interacting with solver *)
(* keep here *)
let rec simple_formula_buffer f =
  let buf = Buffer.create 6400 in
  begin
    match f with
        F_TRUE -> Buffer.add_string buf solver#get#true_string
      | F_FALSE -> Buffer.add_string buf solver#get#false_string
      | F_PRED (s1,li) -> 
                        if List.length li > 0 then
                          begin
                            let li2 = 
                              List.map (fun x -> yc_expr_buffer GENERAL x) li 
                            in
                            solver#get#buffer_of_pred buf s1 li2
                          end
                        else
                          Buffer.add_string buf s1
      | F_STR(s1) -> Buffer.add_string buf s1
      | F_EQ(c1,c2,t) -> let s1 = (yc_expr_buffer GENERAL c1) in
                         let s2 = (yc_expr_buffer GENERAL c2) in
                         let eq_str = 
                           if t = L_BOOL then 
                             solver#get#f_iff_string
                           else
                             solver#get#f_eq_string
                         in
                         solver#get#buffer_of_binary buf eq_str s1 s2;
      | F_NOT(f1) -> let s1 = simple_formula_buffer f1 in
                     solver#get#buffer_of_unary buf solver#get#f_not_string s1
      | F_OR(f1,f2) -> let s1 = simple_formula_buffer f1 in
                       let s2 = simple_formula_buffer f2 in
                       solver#get#buffer_of_binary buf solver#get#f_or_string s1 s2
      | F_IMPL(f1,f2) -> let s1 = simple_formula_buffer f1 in
                       let s2 = simple_formula_buffer f2 in
                       solver#get#buffer_of_binary buf solver#get#f_impl_string s1 s2
      | F_AND(f1,f2) -> let s1 = simple_formula_buffer f1 in
                       let s2 = simple_formula_buffer f2 in
                       solver#get#buffer_of_binary buf solver#get#f_and_string s1 s2
  end;
  buf

let simple_command_buffer e =
  let buf = Buffer.create 800 in
  begin
    match e with
        PUSH -> Buffer.add_string buf solver#get#push_string
      | POP -> Buffer.add_string buf solver#get#pop_string
      | DEFINE_VAR (n,t) ->
         Buffer.add_string buf (solver#get#define_var_string n t)
      | DEFINE_FUN (vn,paramlist,f) ->
         let n,t = vn in
         let f_buf = simple_formula_buffer f in
         solver#get#define_fun_buffer buf n t paramlist f_buf
      | QUERY f -> 
         let f_buf = simple_formula_buffer f in
         solver#get#query_buffer buf f_buf
      | ASSERT f -> 
         let f_buf = simple_formula_buffer f in
         solver#get#assert_buffer buf f_buf
      | ASSERT_PLUS f -> 
         let f_buf = simple_formula_buffer f in
         solver#get#assert_plus_buffer buf f_buf
  end;
  buf

let simple_command_string f = 
  Buffer.contents (simple_command_buffer f)






(* keep here *)
let yc_resolve_in_out c =
  let base = " "^(solver#get#cc) in
  match c with
      INPUT -> base^" INPUT"
    | OUTPUT -> base^" OUTPUT"
    | _ -> base^" LOCAL"



(* example definitions of input/output vars*)
(* keep here *)
let yc_var_shortcut_string () =
    let first = "" in (* for prettyprinting *)
    Hashtbl.fold (fun i (n,v,t,c) acc -> 
    try
      let uvd = Tables.find_used_var i in
        begin
          let s1 = solver#get#define_var_string v t in
          let s2 = Tables.resolve_var_name v in
          let s3 = if (compare v s2) = 0 then "" else s2 in
          let s4 = match uvd with
                     None -> ""
                   | Some r -> ",STATE("^(List.fold_left 
                      (fun acc x -> (string_of_int(x))^",")
                      "" r.depths)^")"
          in
          Tables.varid_name_add v i;
          acc^first^s1^first^"\t\t\t"^solver#get#cc^s3^(yc_resolve_in_out c)^s4
          ^"/"^(string_of_int i)^"\n"
        end
    with Not_found -> acc
  ) (Tables.get_varinfo()) ""


(* keep here *)
let yc_property_string_buf position p mode =
  let term,_ = Lus_convert.convert_term p position 0 0 None None in
  yc_expr_buffer mode term

(* position_string, position, lustre_expr, cvc_expr *)
(* keep here*)

let yc_property_header position_string position p =
  let fs = Buffer.contents (yc_property_string_buf position p GENERAL) in 
    Globals.prop_specified := fs;
  (* we need the guard implication for the step case with ite elim *)
  solver#get#property_header position_string fs

let yc_property_header_new position_string position p =
  let fs = Buffer.contents (yc_property_string_buf position p GENERAL) in 
  (* we need the guard implication for the step case with ite elim *)
  solver#get#property_header_new position_string fs

(* by Teme*)
(* To print a multiple properties as one string*)

(* let rec yc_multi_property_header position multi_p =
  match multi_p with
    |[x] -> Buffer.contents (yc_property_string_buf position x GENERAL)
    | y::ys ->  "\nand" ^(String.concat " "
        (List.map 
         (fun l-> 
           (Buffer.contents (yc_property_string_buf position l GENERAL)))
         (y::ys)))
*)


   let rec yc_multi_property_header position_string position multi_p =
  match multi_p with
     [] -> ""
    |[x] -> Buffer.contents (yc_property_string_buf position x GENERAL)
    | y::ys ->  "\n(define MULTI_PROPERTY ::(-> _nat bool) (lambda ("^position_string^"::_nat)"^"(and "^(String.concat " "
        (List.map 
         (fun l-> 
           (Buffer.contents (yc_property_string_buf position l GENERAL)))
         (y::ys)))^")))"
  
(* by Teme*)
(* To print a multiple properties as one string*)
let rec yc_multi_property_header_list position multi_p =
  match multi_p with
    | [] -> []
    |[x] -> [Buffer.contents (yc_property_string_buf position x GENERAL)]
    | y::ys ->  Buffer.contents (yc_property_string_buf position y GENERAL):: yc_multi_property_header_list position ys
  


let yc_assumption_string position_string position =
  match Lus_assertions.get_assertion_term() with
      None -> ""
    | Some x -> let formula = yc_expr_buffer GENERAL x in
                let buf = Buffer.create 6400 in
                solver#get#define_fun_buffer buf solver#get#assertions (M_FUNC[M_NAT;L_BOOL])
                  [(position_string,M_NAT)] formula;
                Buffer.contents buf

let yc_assumption_string_invariant position_string position file =
  match Lus_assertions.get_assertion_term() with
      None -> ""
    | Some x -> let formula = yc_expr_buffer GENERAL x in
                let buf = Buffer.create 6400 in
                solver#get#define_fun_buffer buf solver#get#assertions (M_FUNC[M_NAT;L_BOOL])
                  [(position_string,M_NAT)] formula;
                Buffer.contents buf

let state_vars_version = ref 0
let get_state_vars_r_version () = 
    if solver#get#can_redefine then
      solver#get#state_vars_r
    else
      solver#get#state_vars_r^(string_of_int !state_vars_version)


let build_state_var_exprs k e depth = 
assert (k >= 0);
assert (depth >=0);
  let nk = NUM k in
  let d = depth-1 in
  let p1 = if d > 0 then
             MINUS(POSITION_VAR solver#get#position_var1,NUM(d)) 
           else
             POSITION_VAR solver#get#position_var1
  in        
  let p2 = if d > 0 then
             MINUS(POSITION_VAR solver#get#position_var2,NUM(d))
           else
             POSITION_VAR solver#get#position_var2
  in            
  match e with      
      | VAR_GET(s,_,_,_) -> VAR_GET(s,d,nk,p1),VAR_GET(s,d,nk,p2)
      | _ -> raise (ConversionError "build_state_var_exprs")



(* this assumes the used_vars table has been populated *)
let state_vars_tuples_refined(index) =
Channels.debug_to_user "state_vars_tuples_refined";
(*  Buffer.contents (expr_string Node (TUPLE_LIT(!state_var_list)))*)
  let all_refined,l1,l2 = Hashtbl.fold (fun i e ((fnd,ls1,ls2) as acc) ->
    try
      match Deftable.get_def i ("get_def:state_vars_tuples_refined "^(string_of_int i)) with
          DEF_REF z -> acc
        | DEF_STR z ->
            if z.abstr.(index) = NOT_REFINED then
              (false,ls1,ls2)
            else
              match e with
                  None -> acc
                | Some r ->
                    List.fold_left (fun (tf,acc1,acc2) d ->
                      let e1,e2 = build_state_var_exprs i r.ex d in
                      (tf,e1::acc1,e2::acc2)
                    ) acc r.depths
    with IdNotFound _ -> acc
    ) (Tables.get_used_vars()) (true,[],[])
  in
  if List.length l1 > 0 then
    begin
      if all_refined then
        raise AllStatefulVarsRefined
      else
        F_NOT(F_EQ(TUPLE_LIT(l1),TUPLE_LIT(l2),L_UNDET))
    end
  else
    raise NoStatefulVars (* this turn *)

(*
(* second version of state_vars_tuples_refined, that keeps track of the 
 already caught variables with the stamp field *)
(* this assumes the used_vars table has been populated *)
let state_vars_tuples_refined2 (index) =
(*  Buffer.contents (expr_string Node (TUPLE_LIT(!state_var_list)))*)
  let all_refined,l1,l2 = Hashtbl.fold (fun i e ((fnd,ls1,ls2) as acc) ->
    try
      match Deftable.get_def i "get_def:state_vars_tuples_refined2" with
          DEF_REF z -> acc
        | DEF_STR z ->
            if z.abstr.(index) = NOT_REFINED then
              (false,ls1,ls2)
            else
              match e with
                  None -> acc
                | Some r ->
                    if z.stamp = 0 then
                      begin
                        z.stamp <- 1;
                        List.fold_left (fun (tf,acc1,acc2) d ->
                          let e1,e2 = build_state_var_exprs i r.ex d in
                          (tf,e1::acc1,e2::acc2)
                        ) acc r.depths
                      end
                    else
                      acc
    with Not_found -> acc
    ) (Tables.get_used_vars()) (true,[],[])
  in
  if List.length l1 > 0 then
    begin
      if all_refined then
        raise AllStatefulVarsRefined
      else
        F_NOT(F_EQ(TUPLE_LIT(l1),TUPLE_LIT(l2),L_UNDET))
    end
  else
    raise NoStatefulVars (* no new ones this turn *)
*)

(* this assumes the used_vars table has been populated *)
let state_vars_tuples () =
  let l1,l2 = Hashtbl.fold (fun i e acc ->
              match e with
                  None -> acc
                | Some r ->
                    List.fold_left (fun (acc1,acc2) d ->
                      let e1,e2 = build_state_var_exprs i r.ex d in
                      e1::acc1,e2::acc2
                    ) acc r.depths
    ) (Tables.get_used_vars()) ([],[])
  in
  if List.length l1 > 0 then
    F_NOT(F_EQ(TUPLE_LIT(l1),TUPLE_LIT(l2),L_UNDET))
  else
    raise NoStatefulVars (* there are none at all *)



(* raises NoStatefulVars *)
let yc_state_vars_string () = 
(* check against empty *)
  let buf = Buffer.create 6400 in
  let formula = 
    yc_formula_string_buffer STATE_VAR_GEN 0 (state_vars_tuples()) 
  in
  solver#get#define_fun_buffer buf solver#get#state_vars (M_FUNC[M_NAT;M_NAT;M_BOOL])
    [(solver#get#position_var1,M_NAT);(solver#get#position_var2,M_NAT)] formula;
  Buffer.contents buf

(* raises NoStatefulVarsRefined & AllStatefulVarsRefined *)
let yc_state_vars_string_refined index = 
  incr state_vars_version;
  let state_vars_string = get_state_vars_r_version () in
  let buf = Buffer.create 6400 in
  let formula = 
    yc_formula_string_buffer STATE_VAR_GEN 0 (state_vars_tuples_refined index) 
  in
  solver#get#define_fun_buffer buf state_vars_string (M_FUNC[M_NAT;M_NAT;M_BOOL])
    [(solver#get#position_var1,M_NAT);(solver#get#position_var2,M_NAT)] formula;
  Buffer.contents buf

(* not yet used *)
(*
let yc_state_vars_string_refined2 index = 
  let buf = Buffer.create 32 in
  let n = Lus_convert.get_state_vars_index() in
 (* NO! *)
  let subformula =
    if n = 0 then
      F_PRED (solver#get#state_vars_link, [STRING solver#get#position_var1;STRING solver#get#position_var2;NUM n])
    else
      F_OR(
        F_PRED (solver#get#state_vars_link, [STRING solver#get#position_var1;STRING solver#get#position_var2;NUM n]),
        F_NOT(F_PRED (solver#get#state_vars_link, [STRING solver#get#position_var1;STRING solver#get#position_var2;NUM (n-1)]))
      )
  in
  let formula_b = 
    (yc_formula_string_buffer STATE_VAR_GEN 0 
      (F_OR ((state_vars_tuples_refined2 index),subformula))) 
  in
  solver#get#define_fun_buffer buf (solver#get#state_vars^(string_of_int n)) 
    (M_FUNC[M_NAT;M_NAT;L_BOOL])
    [(solver#get#position_var1,M_NAT);(solver#get#position_var2,M_NAT)] formula_b;
  Buffer.contents buf
*)

