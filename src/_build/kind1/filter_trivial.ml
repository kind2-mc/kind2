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


(* Teme: Filter trivial invariants*)


let filter_non_empty classes =
  List.filter (fun x -> x != [] ) classes 

let pick_equs classes =
  let classes_rep = List.map (fun x -> List.hd x ) classes in
  let rec help_func l =
    match l with 
	hd1::(hd2::tl as tl1) -> (hd1,hd2)::(help_func tl1)
      | _::[] 
      | [] -> []
  in
    help_func classes_rep 

let mk_eq_bool (x, y) = 
  (Types.F_EQ(Types.PRED (x,[]), Types.PRED(y,[]), Types.L_BOOL))

let mk_imp_bool (expr_l, expr_r) =
  Types.F_IMPL (Types.F_PRED (expr_l,[]), Types.F_PRED(expr_r,[]))

let mk_eq_int (x, y)  = Types.F_EQ (Types.REL (Types.EQ, Types.PRED(x,[]), Types.PRED(y, [])), Types.ONE , Types.L_BOOL) 

let mk_eq_int_oneclass equiv_class  = 
  Partial_order.fold_list_with_op  
    (fun x y -> mk_eq_int (x, y) ) 
    equiv_class 

let mk_imp_int (x,y) = Types.F_EQ (Types.REL (Types.LTE, Types.PRED(x,[]), Types.PRED(y,[])), Types.ONE, Types.L_BOOL) 


(* The idea is as follow: 
   
   In the beginning, this data structure contains all equiv classes and
   implications found.  Then test if it is valid given the definition of
   the lustrue program at step/time n-k,n-k+1,...,n .

   If the it is valid, then this means the all equalities and implications
   are trivial and we are done.
   
   If not valid, we have a counter mode.  If an equiv class contains terms
   evaluated to several values, then split this equiv class into several
   equiv classes according to the values of its terms.  Suppose an equiv
   class is split into a set of equiv classes S, then a non-trivial
   equality can be obtained by chosing two terms that belong to two
   different equiv classes in S.  If S contains n equiv classes, then we
   need to keep n-1 equalities.  For a bool implication a ==> b if a is
   ture and b is false, then a==> is a non-trivial implication.  For an
   integer implicaiton a<=b, if the value of A is greater than b, then a<=b
   is a non-trivial interger impliation, and we keep it.
*)

class filter_trivial (bool_equiv_classes, (* a list of list of strings *) 
		     bool_imps, (* a list of (str,str) *)
		     int_equiv_classes, (* a list of list of string *)
		     int_imps) = (* a list of (str,str) *)
object (self)
  val mutable d_bool_equiv_classes_left = 
    (*    final_graph#fold_nodes (fun x y -> (x#equiv) ::y) []*)
    bool_equiv_classes
  val mutable d_bool_equ_picked = []
  val mutable d_bool_imps_left = bool_imps 
(*
    let fold_func (l,r) y =
      if final_graph#is_false_node l or final_graph#is_true_node r 
      then y
      else 
	let get_rep id = List.hd (final_graph#ith_node_info id)#equiv  in
	let rep_l = get_rep l in
	let rep_r = get_rep r in
	  (rep_l,rep_r)::y
    in
      final_graph#fold_edges fold_func []
*)
  val mutable d_bool_imps_picked = [] 
  val mutable d_int_equiv_classes_left = int_equiv_classes 
  val mutable d_int_equ_picked = []
  val mutable d_int_imps_left = int_imps
  val mutable d_int_imps_picked = []

  method filter hash_tbl =
    let changed = ref false in
    let bool_equiv_func one_class (equiv_classes, picked_equs) =
      let t_class, f_class = 
	List.partition (fun x -> 
	  Imp_graph.is_true (Hashtbl.find hash_tbl x)) one_class 
      in
      let split_equiv_classes = filter_non_empty [t_class;f_class] in
      let non_trivial_equs = pick_equs split_equiv_classes in 
	if (List.length split_equiv_classes) > 1 
	then changed:=true; 
	(split_equiv_classes@equiv_classes), (non_trivial_equs@picked_equs)
    in
    let 
	new_equiv_cls, new_picked_equalities = 
      List.fold_right bool_equiv_func d_bool_equiv_classes_left ([],d_bool_equ_picked) in
      d_bool_equiv_classes_left <- new_equiv_cls ;
      d_bool_equ_picked <- new_picked_equalities ; 
    
    let bool_imp_func ((l,r) as one_imp) (imps, picked_imps) =
      let l_v = Hashtbl.find hash_tbl l in
      let r_v = Hashtbl.find hash_tbl r in
	if (Imp_graph.is_true l_v && Imp_graph.is_false r_v) 
	then (changed:=true;(imps, one_imp::picked_imps))
	else (one_imp::imps, picked_imps) 
    in
    let bool_imps_left, picked_bool_imps = 
      List.fold_right bool_imp_func d_bool_imps_left ([],d_bool_imps_picked) in
      d_bool_imps_picked <- picked_bool_imps;
      d_bool_imps_left <- bool_imps_left;

    let int_equiv_func one_class (equiv_classes, picked_equs) =
      let split_equiv_classes, _ = Equiv_util.filter_int_func one_class hash_tbl in
      let non_trivial_equs = pick_equs split_equiv_classes in
      if (List.length split_equiv_classes) > 1 
      then changed:=true; 
	(split_equiv_classes@equiv_classes),(non_trivial_equs@picked_equs)
    in
    let new_equiv_cls, new_picked_equalities = 
      List.fold_right int_equiv_func d_int_equiv_classes_left ([],d_int_equ_picked) in
      d_int_equiv_classes_left <- new_equiv_cls ;
      d_int_equ_picked <- new_picked_equalities ; 

    let int_imp_func ((l,r) as one_imp) (imps, picked_imps) =
      let l_v = int_of_string (Hashtbl.find hash_tbl l) in
      let r_v = int_of_string (Hashtbl.find hash_tbl r) in
	if (l_v > r_v) 
	then (changed:=true;(imps, one_imp::picked_imps))
	else (one_imp::imps, picked_imps) 
    in
    let int_imps_left, picked_int_imps = 
      List.fold_right int_imp_func d_int_imps_left ([],d_int_imps_picked) in
      d_int_imps_picked <- picked_int_imps;
      d_int_imps_left <- int_imps_left;
      !changed
  method doc_of_bool_eqs_picked () =
    List.map mk_eq_bool d_bool_equ_picked
  method doc_of_bool_equiv_left () =
    List.fold_right (fun x y -> (Equiv_util.mk_eqs_one_class x Types.L_BOOL)@y ) d_bool_equiv_classes_left [] 
  method doc_of_bool_imps_picked () =
    List.map mk_imp_bool d_bool_imps_picked
  method doc_of_bool_imps_left () =
    List.map mk_imp_bool d_bool_imps_left

  method doc_of_int_eqs_picked () =
    List.map mk_eq_int  d_int_equ_picked
  method doc_of_int_equiv_left () =
    List.fold_right (fun x y -> (mk_eq_int_oneclass x )@y ) d_int_equiv_classes_left [] 
  method doc_of_int_imps_picked () =
    List.map mk_imp_int d_int_imps_picked
  method doc_of_int_imps_left () =
    List.map mk_imp_int d_int_imps_left

  method doc_of_asserts () =
    let bool_eqs =  self#doc_of_bool_equiv_left() in
    let bool_imps = self#doc_of_bool_imps_left ()  in
    let int_eqs =  self#doc_of_int_equiv_left() in
    let int_imps = self#doc_of_int_imps_left ()  in
      Expr_util.mk_not_ands (bool_eqs @ bool_imps @ int_eqs @ int_imps)    
  method doc_of_picked() =
    let bool_eqs =  self#doc_of_bool_eqs_picked () in
    let bool_imps = self#doc_of_bool_imps_picked () in
    let int_eqs =  self#doc_of_int_eqs_picked () in
    let int_imps = self#doc_of_int_imps_picked ()  in
      Expr_util.mk_not_ands (bool_eqs @ bool_imps @ int_eqs @ int_imps)    
  method picked_invs () =
    let bool_eqs =  self#doc_of_bool_eqs_picked () in
    let bool_imps = self#doc_of_bool_imps_picked () in
    let int_eqs =  self#doc_of_int_eqs_picked () in
    let int_imps = self#doc_of_int_imps_picked ()  in
      bool_eqs, bool_imps, int_eqs, int_imps
end

