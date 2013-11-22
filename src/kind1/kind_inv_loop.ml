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

(** Kind-Inv: Offline invariant generator for lustre programs. Main k-induction loop. *)

(** 
@author Yeting Ge 
@author Temesghen Kahsai

*)

open Types
open OldFlags
open Exceptions
open Channels
open Globals
open ExtList
open Util


let solver = Globals.my_solver
let toss x = () (* toss outputs *)


(** Function that prints the conjunction of the discovered invariants *)
let pr_func b_eqs b_imps i_eqs i_imps depth =
  pr "-- "; 
  print_int ((List.length b_imps) 
	      + 2*(List.length b_eqs) 
	      + 2*(List.length i_eqs) 
	      + (List.length i_imps) ) ;
  pr " implications. \n";
  pr "assert";
  let pos_l = Util.n_to_m 1 depth in
    List.iter (fun x-> pr " (true -> (") pos_l ; 
    List.map(fun x -> pr (Imp_graph.eq_org x); pr " \nand ";) b_eqs;
    List.map(fun x -> pr (Imp_graph.imp_org x); pr " \nand ";) b_imps;
    List.map(fun x -> pr (Imp_graph.int_eq_org x); pr " \nand ";) i_eqs;
    List.map(fun x -> pr (Imp_graph.int_imp_org x); pr " \nand ";) i_imps;
    pr " true ";
    List.iter (fun x-> pr "))") pos_l ; 
    pr ";\n" 

let pr_func_no_imp b_eqs b_imps i_eqs i_imps depth =
  pr "-- "; 
  print_int ((List.length b_imps) 
	      + 2*(List.length b_eqs) 
	      + 2*(List.length i_eqs) 
	      + (List.length i_imps) ) ;
  pr " implications. \n";
  pr "assert";
  let pos_l = Util.n_to_m 1 depth in
    List.iter (fun x-> pr " (true -> (") pos_l ; 
    List.map(fun x -> pr (Imp_graph.eq_org x); pr " \nand ";) b_eqs;
    List.map(fun x -> pr (Imp_graph.int_eq_org x); pr " \nand ";) i_eqs;
    List.map(fun x -> pr (Imp_graph.int_imp_org x); pr " \nand ";) i_imps;
    pr " true ";
    List.iter (fun x-> pr "))") pos_l ; 
    pr ";\n" 


(** Main k-induction loop for invariant generation*) 
let mainloop filename send_invariant =
  let defdoc,maxdepth,def_hash,no_stateful,pvars, _  = Defgen.start filename in

(* Check that at least one flag is activated.*)
  let _ =   
    if ( (not !OldFlags.invariant_bool) && (not !OldFlags.invariant_int)  && (not !OldFlags.mode_inv)) 
    then (pstr "Specify what type of invariants you want to generate.
             Integer type with -inv_int and/or Boolean type with -inv_bool and/or Mode invarirnat with -inv_mode\n"; 
          failwith "No invariants to generate.") in 



  (* Generate candidates in terms of new variables. *)
  let all_terms = Lus_convert_yc.get_all_def_terms () in
  let bool_sub_exprs, int_sub_exprs, float_sub_exprs = Sub_exprs.sub_exprs all_terms Expr_util.filter_sub_exprs in
  let _ = Kind_support.print_stat_headers() in
  let nvar = solver#get#k_position_string in
  let add = Kind_support.get_add() in
  let nstart = solver#get#step_base_string in
  let startdepth = maxdepth + 1 in
  let from_solver_ch, from_checker_ch, from_solver2_ch = Kind_support.setup_channels() in

  (* Print TS definitions *)
  let _ = Kind_support.print_to_both_limited from_solver_ch from_solver2_ch from_checker_ch (defdoc^"\n") in

  (* Print definitions of candidates .  *)
  let _ =   print_to_both solver#get#push_string in
  let _ = 
    if (!OldFlags.invariant_bool) then(
      let new_bool_var_doc = New_vars.bool_newvar_defs bool_sub_exprs in
	Kind_support.print_to_both_limited from_solver_ch from_solver2_ch from_checker_ch (new_bool_var_doc^"\n")) in
    
  let _ =
    if (!Globals.is_inter && !OldFlags.mode_inv) then (
      List.iter (fun (v,lb,ub) -> 
		   let p, n = New_vars.mk_one_mode_candidate v lb ub in
		     Kind_support.print_to_both_limited from_solver_ch from_solver2_ch from_checker_ch (p^n)
		)(New_vars.get_interval_vars())) in

  let _ = 
    if (!OldFlags.invariant_int) then (
      let new_int_var_doc =  New_vars.int_newvar_defs int_sub_exprs in
	Kind_support.print_to_both_limited from_solver_ch from_solver2_ch from_checker_ch (new_int_var_doc^"\n")) in
    

(* Setup equiv classes *)
  let bool_imp_graph =     
    new Imp_graph.bool_imp_graph (
      if (!OldFlags.invariant_bool or !OldFlags.mode_inv) then New_vars.get_bool_nvrs ()
      else []
    )
  in
  let ints_partial_order = 
    new Partial_order.partial_order (
      if (!OldFlags.invariant_int) then New_vars.get_int_nvrs ()
      else []
    ) 
  in

  let _ =  debug_proc INV_GEN_PROC None "Begin K-induction" in
  let _  =   print_to_both solver#get#push_string in
  let _ = Kind_support.print_initialization def_hash startdepth add from_checker_ch in
  let _ = print_to_both solver#get#push_string in
  let _ = print_to_solver (New_vars.mk_nvr_eq_cmds (NUM 0)) in
  let _ = Kind_support.set_last_level_asserted (startdepth-1) in

  let filter_final filter =
    let _ = print_to_solver solver#get#push_string in 
    let _ =  debug_proc INV_GEN_PROC None "Final filter" in
    let imp_equiv_doc = filter#doc_of_asserts () in
      if ("" = imp_equiv_doc) 
        then  false
      else (
	         print_to_solver imp_equiv_doc;
	         print_to_solver ( Lus_convert_yc.simple_command_string (QUERY(F_TRUE)));
	         print_to_solver solver#get#done_string;

    let out1 = solver#get#get_solver_output INV_GEN_PROC from_solver_ch in
      if (solver#get#result_is_unsat out1) 
      then(
        debug_proc INV_GEN_PROC None "UNSAT";
        print_to_solver solver#get#pop_string; (* PUSH 2 *)
        print_to_solver solver#get#pop_string;
	false
      )
    else if (solver#get#result_is_sat out1) 
    then (
      debug_proc INV_GEN_PROC None "SAT";
      let simulation_value_hash =  solver#get#get_simulation_cex INV_GEN_PROC out1 print_to_solver from_solver_ch  in
      let changed = filter#filter simulation_value_hash in
	if changed then ( true )
        else  (failwith "error in final stage")
    )
    else ( (* error *)
      if (solver#get#result_is_error out1) then
	print_to_user_final ((Str.matched_string out1)^"\n");
      debug_proc INV_GEN_PROC None ("SOLVER OUTPUT: "^out1);
      Globals.error := true;
      raise SOLVER_ERROR
    )
      )
  in

  let rec filter_imp_equiv_classes_one_round stepn_positions =
    let _ = debug_proc INV_GEN_PROC None  "Filter" in
    let _ = print_to_solver solver#get#push_string in 

    if (!OldFlags.invariant_bool || !OldFlags.mode_inv)
    then 
      List.iter 
	(fun x-> print_to_solver x; )
	(bool_imp_graph#doc_of_stepn_asserts stepn_positions);

    if (!OldFlags.invariant_int)
    then 
      List.iter  (fun x-> print_to_solver x; )
	(ints_partial_order#doc_of_stepn_asserts stepn_positions);
    let bool_imp_doc = 
      if (!OldFlags.invariant_bool || !OldFlags.mode_inv)
      then (bool_imp_graph#doc_of_asserts ())
      else [] 
    in
    let int_imp_doc = 
      if !OldFlags.invariant_int
      then (ints_partial_order#doc_of_asserts ())
      else []
    in
    let imp_equiv_doc = Expr_util.mk_not_ands (bool_imp_doc@int_imp_doc) in
      if ("" = imp_equiv_doc) then false
      else (
      print_to_solver imp_equiv_doc;
      print_to_solver (Lus_convert_yc.simple_command_string (QUERY(F_TRUE)));
      print_to_solver solver#get#done_string;

    let out1 = solver#get#get_solver_output INV_GEN_PROC from_solver_ch in
      if (solver#get#result_is_unsat out1) 
      then (
        print_to_solver solver#get#pop_string; (* PUSH 2 *)
	true)
      else if (solver#get#result_is_sat out1) 
    then(
  let simulation_value_hash = 
	     solver#get#get_simulation_cex INV_GEN_PROC out1 
	     print_to_solver from_solver_ch  in
  let changed = 
	 if (!OldFlags.invariant_int &&(!OldFlags.invariant_bool || !OldFlags.mode_inv))
	then (
	  let ra = bool_imp_graph#set_new_graph simulation_value_hash in
	  let rb = ints_partial_order#sort simulation_value_hash in
	    if (ra || rb) then true else false) 
	else if (!OldFlags.invariant_bool || !OldFlags.mode_inv)
	then (bool_imp_graph#set_new_graph simulation_value_hash)
	else if (!OldFlags.invariant_int)
	then (ints_partial_order#sort simulation_value_hash )
	else failwith "Error"
      in
	print_to_solver solver#get#pop_string;
	if (changed ) 
	then ( 
	  filter_imp_equiv_classes_one_round stepn_positions 
	)
        else  false 
    )
    else ( (* error *)
      if (solver#get#result_is_error out1) then
        print_to_user_final ((Str.matched_string out1)^"\n");
      debug_proc INV_GEN_PROC None ("SOLVER OUTPUT: "^out1);
      Globals.error := true;
      raise SOLVER_ERROR
    )
      )
  in
    (* Some vars to control loops*)
  let cur_depth = ref maxdepth  in
  let last_changed = ref !cur_depth in
  let local_stop = ref false in

(* Main loop for generation of invariants *)
  try 
    while not !local_stop do
      let _ = print_to_solver solver#get#push_string in
      let bool_imp_doc = if (!OldFlags.invariant_bool || !OldFlags.mode_inv) then  bool_imp_graph#doc_of_asserts() else [] in
      let int_imp_doc = if (!OldFlags.invariant_int) then ints_partial_order#doc_of_asserts() else [] in
      let equiv_imp_doc = Expr_util.mk_not_ands (bool_imp_doc@int_imp_doc) in
      let _ = print_to_solver equiv_imp_doc in
      let _ = if (equiv_imp_doc = "") then (pr_func [] [] [] [] 1; exit 0 ) in
      let base_num = !cur_depth * add in
      let assert_base = (F_EQ(POSITION_VAR(nstart),NUM(base_num),L_INT)) in
      let _ = print_to_solver  (Lus_convert_yc.simple_command_string (ASSERT assert_base)) in
      let _ = print_to_solver (Lus_convert_yc.simple_command_string (QUERY(F_TRUE))) in
      let _ = print_to_solver solver#get#done_string in
    
    let out1 = solver#get#get_solver_output INV_GEN_PROC from_solver_ch in
      if (solver#get#result_is_unsat out1) then
	begin (* base valid *)
          print_to_solver solver#get#pop_string; (* PUSH 2 *)
          if (!cur_depth ) > (!last_changed )  
	  then raise EQUIV_CLS_STABLE ;
          Kind_support.persistent_step_asserts_concrete def_hash startdepth add (!cur_depth+1) from_checker_ch;
	  cur_depth := !cur_depth + 1 ; 	
	end (* base valid *)
    else if (solver#get#result_is_sat out1) then
      begin (* base invlaid *)
	last_changed := !cur_depth;
        let simulation_value_hash = solver#get#get_simulation_cex INV_GEN_PROC out1 print_to_solver from_solver_ch  in
	let changed  = 
	  if (!OldFlags.invariant_int && (!OldFlags.invariant_bool || !OldFlags.mode_inv))
	  then (
	    let ra = bool_imp_graph#set_new_graph simulation_value_hash in
	    let rb = ints_partial_order#sort simulation_value_hash in
	      if (ra || rb ) then true else false )
	  else if (!OldFlags.invariant_bool || !OldFlags.mode_inv)
	  then (bool_imp_graph#set_new_graph simulation_value_hash)
	  else if (!OldFlags.invariant_int)
	  then (ints_partial_order#sort simulation_value_hash)
	  else failwith "Error"
	in
        let _ = print_to_solver solver#get#pop_string in
        let _ = print_to_solver solver#get#safe_pop in
	let _ = local_stop := not changed  in
	    if(!local_stop ) 
	    then (
	      pr (Expr_util.mk_not_ands (bool_imp_graph#doc_of_asserts() ));
	      pr "No changes while sat.\n";
	      failwith "global stop"; )
      end (* base invalid *)
    else
      begin
        if (solver#get#result_is_error out1) then
          print_to_user_final ((Str.matched_string out1)^"\n");
        debug_proc INV_GEN_PROC None ("SOLVER OUTPUT: "^out1);
        Globals.error := true;
        local_stop := true
      end;
 done (* main loop *)

 with EQUIV_CLS_STABLE -> 
   begin
     let _ =  debug_proc INV_GEN_PROC None "Induction Step" in
     let _ = print_to_solver solver#get#pop_string in
     let _ = print_to_solver solver#get#pop_string in 
     let _ = print_to_both solver#get#push_string in
     let _ = print_to_solver (New_vars.mk_nvr_eq_cmds (POSITION_VAR(nvar))) in
     let base_num = !cur_depth * add in
     let assert_base = (F_EQ(POSITION_VAR(nstart),NUM(base_num),L_INT)) in
     let _ =  print_to_solver 
       (Lus_convert_yc.simple_command_string (ASSERT assert_base)) in
     let stepn_positions =  
       List.map 
	 (fun x -> MINUS(POSITION_VAR(nvar),NUM(x))) 
	 (Util.n_to_m 1 (!cur_depth - 1))  in 
     let _ =  List.iter (fun x -> 
	Kind_support.def_assert_both1 def_hash "DEF" 
          [PLUS(POSITION_VAR(nvar),NUM(x*add))]
          !cur_depth from_checker_ch;) (Util.n_to_m 0 (!cur_depth - 1)) in

       if filter_imp_equiv_classes_one_round stepn_positions
       then ( 
 	 if (not !OldFlags.remove_trivial_invariants)
	 then (* NOT remove trivial invariants *)
	   (
	     let b_eqs,b_imps =
	      if (!OldFlags.invariant_bool || !OldFlags.mode_inv)
	      then bool_imp_graph#eq_imp_graph()
	      else [],[]
	     in
	     let int_eqs,int_imps =
	       if (!OldFlags.invariant_int)
	       then ints_partial_order#eq_imp()
	       else [],[]
	     in
	      let _= List.map(fun x -> send_invariant x) b_eqs in
	      let _= List.map(fun x -> send_invariant x) b_imps in
	      let _= List.map(fun x -> send_invariant x) int_eqs in
	      let _= List.map(fun x -> send_invariant x) int_imps in
	       ()

	   )
	else 
	  ( (* remove trivial invariants *)
	    let bool_equiv_classes, bool_imps  =
	      if (!OldFlags.invariant_bool || !OldFlags.mode_inv)
	      then bool_imp_graph#equiv_classes(), bool_imp_graph#imps()
	      else [],[] 
	    in
	    let int_equiv_classes,int_imps =
	      if (!OldFlags.invariant_int)
	      then ints_partial_order#equiv_classes(), ints_partial_order#imps()
	      else [],[]
	    in
	    let filter = 
	      new Filter_trivial.filter_trivial (
		bool_equiv_classes,
		bool_imps,
		int_equiv_classes,
		int_imps) 
	    in
	      while (filter_final filter) do 
		ignore();
	      done ;
	      let b_eqs, b_imps, i_eqs, i_imps = filter#picked_invs() in
	      let _= List.map(fun x -> send_invariant x) b_eqs in
	      let _= List.map(fun x -> send_invariant x) b_imps in
	      let _= List.map(fun x -> send_invariant x) i_eqs in
	      let _= List.map(fun x -> send_invariant x) i_imps in
		if !OldFlags.no_imp then
		   pr_func_no_imp  b_eqs b_imps i_eqs i_imps maxdepth
		else
		 pr_func b_eqs b_imps i_eqs i_imps maxdepth
	  );
       )
       else (
	 pr "assert true;\n";
       );
      
   end 
      
