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

(** A module that provides support function for the main KIND module *)

(** 
@author George Hagen
@author Temesghen Kahsai
*)

open Types
open OldFlags
open Exceptions
open Channels
open Globals

let solver = Globals.my_solver

let toss x = () (* toss outputs *)

(********************************************************************)
(* this inserts a delay into the command string and blocks until it has
  been processed.  Any "early" results are discarded as the buffer is
  cleared.  This may need to be changed if this is used for anything
  other than the initial definitions *)

(* this appears to be a linux pipe limitation? *)
(* it assumes that the command list ends with a '\n' *)

let rec output_string_limited in_ch out_ch str =
  let len = String.length str in
  if len > (!buffer_limit) then
    begin
      let nextpos = (String.index_from str (!buffer_limit) '\n')+1 in
      output_string in_ch (String.sub str 0 nextpos);
      output_string in_ch solver#get#done_string;
      flush in_ch;
      toss(solver#get#get_output out_ch); (* ignore this *)
      output_string_limited in_ch out_ch 
        (String.sub str nextpos (len - nextpos))
    end
  else
    output_string in_ch str
     

(********************************************************************)
(* This is a work-around for dealing with OS pipe buffer limitations *)
(* It inserts a wait-delay into the command string at certain intervals *)
(* Currently this only may be encountered on large var_def definition 
   generation, but on slower machines it may be encountered elsewhere 
   and so may need to be altered and called more often *)

let print_to_both_limited from_solver from_solver2 from_checker str =
  if !do_scratch then
    begin
      output_string !main_ch str;
      flush !main_ch
    end;
  output_string_limited !to_solver_ch from_solver str;
  flush !to_solver_ch;
  if !separate_solvers then
    begin
      if !do_scratch then
        begin
          output_string !main2_ch str;
          flush !main2_ch
        end;
      output_string_limited !to_solver2_ch from_solver2 str;
      flush !to_solver2_ch;
    end;
  if !checker_mode then
    begin
      if !do_scratch then
        begin
          output_string !check_ch str;
          flush !check_ch
        end;
      output_string_limited !to_checker_ch from_checker str;
      flush !to_checker_ch
    end;
  if !debug then
    begin
      output_string !debug_ch str;
      flush !debug_ch
    end


(********************************************************************)
(** Print all the defs in solver 1*)

let print_defs_to_solver1 from_solver from_checker str =
  if !do_scratch then
    begin
      output_string !base_ch str;
      flush !main_ch
    end;
  output_string_limited !to_solver_ch from_solver str;
  flush !to_solver_ch;
  if !checker_mode then
    begin
      if !do_scratch then
        begin
          output_string !check_ch str;
          flush !check_ch
        end;
      output_string_limited !to_checker_ch from_checker str;
      flush !to_checker_ch
    end;
  if !debug then
    begin
      output_string !debug_ch str;
      flush !debug_ch
    end
      

(** Print all the definitions in to solver 2 *)
let print_defs_to_solver2 from_solver2 from_checker str =
  if !do_scratch then
    begin
      output_string !induct_ch str;
      flush !induct_ch
    end;
  output_string_limited !to_solver2_ch from_solver2 str;
  flush !to_solver2_ch;
  if !checker_mode then
    begin
      if !do_scratch then
        begin
          output_string !check_ch str;
          flush !check_ch
        end;
      output_string_limited !to_checker_ch from_checker str;
      flush !to_checker_ch
    end;
  if !debug then
    begin
      output_string !debug_ch str;
      flush !debug_ch
    end
      

(** Print all the definitions in to solver 3 *)
let print_defs_to_solver3 from_solver3 from_checker str =
 if !do_scratch then
    begin
      output_string !inv_ch str;
      flush !inv_ch
    end;
  output_string_limited !to_solver3_ch from_solver3 str;
  flush !to_solver3_ch;
  if !checker_mode then
    begin
      if !do_scratch then
        begin
          output_string !check_ch str;
          flush !check_ch
        end;
      output_string_limited !to_checker_ch from_checker str;
      flush !to_checker_ch
    end;
  if !debug then
    begin
      output_string !debug_ch str;
      flush !debug_ch
    end


(** Print all defs to solver 4 *)
let print_defs_to_solver_bmc_checker solver_bmc_checker_ch str = 
  output_string_limited !to_solver4_ch solver_bmc_checker_ch str;
  flush !to_solver4_ch;
   if !do_scratch then ( output_string !base_ch str; flush !base_ch)
   

(** Print all defs to solver 5 *)
let print_defs_to_solver_induct_checker solver_induct_checker_ch str = 
  output_string_limited !to_solver5_ch solver_induct_checker_ch str;
  flush !to_solver5_ch;
   if !do_scratch then ( output_string !extra_ch str; flush !extra_ch)




(********************************************************************)
let print_countermodel foundvars minstep maxstep =
  let minstep',maxstep' =
    if !do_negative_index then
      -maxstep,-minstep
    else
      minstep,maxstep
  in
  let prev_loud = !OldFlags.loud in
  if !OldFlags.final_cex_loud then
    OldFlags.loud := true;
  print_to_user_final ("                      Instant\n");
  print_to_user_final ("variable             ");
  for i=minstep to maxstep do
    if abs(i) < 10 then print_to_user_final " ";
    print_to_user_final ("  "^(string_of_int i))
  done;
  print_to_user_final "\n\n";
  Hashtbl.iter (fun id _ -> 
    let (_,key',_,c) = 
      Tables.safe_find_varinfo id "print_countermodel"
    in
    if ((!print_all_vars || c = INPUT) && (c != ABSTRACT)) then
      begin
        let found = ref false in
        let key = Tables.resolve_var_name key' in
        let buf = Buffer.create 20 in
        Buffer.add_string buf (key^" ");
        for i=0 to 19 - (String.length key) do
          Buffer.add_string buf " ";
        done;
        for i=minstep' to maxstep' do
          try
            let tval = Hashtbl.find foundvars (id,i) in
            let reg3 = Str.regexp_string_case_fold "true" in
            let reg4 = Str.regexp_string_case_fold "false" in
            let reg5 = Str.regexp_string_case_fold "0bin0" in
            let reg6 = Str.regexp_string_case_fold "0bin1" in
            let keyval =
              if Str.string_match reg3 tval 0 then
                "1"
              else if Str.string_match reg4 tval 0 then
                "0"
              else if Str.string_match reg5 tval 0 then
                "0"
              else if Str.string_match reg6 tval 0 then
                "1"
              else 
                tval
            in
            if String.length keyval < 3 then
              Buffer.add_string buf " ";
            if String.length keyval < 2 then
              Buffer.add_string buf " ";
            found := true;
            Buffer.add_string buf (" "^keyval)
          with Not_found ->
            Buffer.add_string buf "   -"
        done;
        Buffer.add_string buf "\n";
        if !found then
          print_to_user_final (Buffer.contents buf)
      end
    ) (Tables.get_used_vars());
  OldFlags.loud := prev_loud



(********************************************************************)
let save_countermodel foundvars minstep maxstep =
  let buf = Buffer.create 1000 in
  let minstep',maxstep' =
    if !do_negative_index then
      -maxstep,-minstep
    else
      minstep,maxstep
  in
  let prev_loud = !OldFlags.loud in
  if !OldFlags.final_cex_loud then
    OldFlags.loud := true;

(*  print_to_user (solver#get#cc^"Counterexample trace:\n");*)
  Buffer.add_string buf "                          Instant\n";
  Buffer.add_string buf "variable               ";
  for i=minstep to maxstep do
    if abs(i) < 10 then Buffer.add_string buf  " ";
    let instant = "  "^(string_of_int i) in
    Buffer.add_string buf instant
  done; 
Buffer.add_string buf "\n";
  Hashtbl.iter (fun id _ -> 
    let (_,key',_,c) = 
      Tables.safe_find_varinfo id "print_countermodel"
    in
    if ((!print_all_vars || c = INPUT) && (c != ABSTRACT)) then
      begin
        let found = ref false in
        let key = Tables.resolve_var_name key' in
        Buffer.add_string buf (solver#get#cc^key^" ");
        for i=0 to 19 - (String.length key) do
          Buffer.add_string buf " ";
        done;
        for i=minstep' to maxstep' do
          try
            let tval = Hashtbl.find foundvars (id,i) in
            let reg3 = Str.regexp_string_case_fold "true" in
            let reg4 = Str.regexp_string_case_fold "false" in
            let reg5 = Str.regexp_string_case_fold "0bin0" in
            let reg6 = Str.regexp_string_case_fold "0bin1" in
            let keyval =
              if Str.string_match reg3 tval 0 then
                "1"
              else if Str.string_match reg4 tval 0 then
                "0"
              else if Str.string_match reg5 tval 0 then
                "0"
              else if Str.string_match reg6 tval 0 then
                "1"
              else 
                tval
            in
            if String.length keyval < 3 then
              Buffer.add_string buf " ";
            if String.length keyval < 2 then
              Buffer.add_string buf " ";
            found := true;
            Buffer.add_string buf (" "^keyval)
          with Not_found ->
            Buffer.add_string buf "   -"
        done;
        Buffer.add_string buf "\n";
      end
    ) (Tables.get_used_vars());
   OldFlags.loud := prev_loud;
   Buffer.contents buf



(** Print header for results in XML format*)
let print_header_xml fn =
  let buf = Buffer.create 100 in
  let _ = Buffer.add_string buf "<?xml version=\"1.0\"?>\n" in
  let _ = Buffer.add_string buf "<Results xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">\n" in
  let _  = Buffer.add_string buf ("  <File>"^(fn)^".xml"^"</File>\n") in 
    Buffer.contents buf




 let mk_cex_xml foundvars minstep maxstep name k time = 
   let buf = Buffer.create 1000 in
   let minstep', maxstep' = 
     if !do_negative_index then -maxstep,-minstep 
     else minstep,maxstep  in 
   let prev_loud = !OldFlags.loud in 
     if !OldFlags.final_cex_loud then 
       OldFlags.loud:=true; 
     let _ =  Buffer.add_string buf("  <Property name=\""^name^"\">\n") in
    let _ = Buffer.add_string buf"    <Date>" in
    let lt = Unix.localtime(Unix.time()) in 
    let time_st = Printf.sprintf "%04d-%02d-%02d"(1900+lt.Unix.tm_year)(1+lt.Unix.tm_mon)(lt.Unix.tm_mday) in 
    let _ = Buffer.add_string buf time_st in
    let _ = Buffer.add_string buf "</Date>\n" in
    let _  = Buffer.add_string buf ("    <Runtime unit=\"sec\" timeout=\"false\">"^time^"</Runtime>\n") in
    let _  = Buffer.add_string buf ("    <K>"^k^"</K>\n") in
    let _  = Buffer.add_string buf "    <Answer>falsifiable</Answer>\n" in
    let _ = Buffer.add_string buf "    <Counterexample>\n" in 
    let buf2 = Buffer.create 100 in
      Hashtbl.iter(fun id _-> 
		     let (ni,key',_,c)= 
		       Tables.safe_find_varinfo id"print_countermodel" 
		     in 
		       if((!print_all_vars||c=INPUT)&&(c!=ABSTRACT))then 
			 begin(* block 1 *) 
			   let found = ref false in 
			   let key = Tables.resolve_var_name key' in 
			   let buf3 = Buffer.create 20 in 
			   let ty = 
			     (match (Tables.get_varinfo_type id) with 
				| L_BOOL-> " type=\"bool\"" 
				| L_INT ->" type=\"int\""  
				| L_REAL->" type=\"real\""
        | L_INT_RANGE (x, y)  -> let lower = string_of_int(x) in
                                 let upper = string_of_int(y) in
                              " type=\" subrange [" ^lower^","^ upper^"]\""
				|_ -> "" ) in 
			     Buffer.add_string buf2 ("      <Signal name=\""^key^"\" node=\""^(Tables.nodeid_to_original_name 
										      ni)^"\""^ty^">\n"); 
			     Buffer.add_string buf3 (solver#get#cc^key^" ");
			     for i=0 to 19-(String.length key) do 
			       Buffer.add_string buf3 " "; 
			     done; 
			     for i=minstep' to maxstep' do 
			       try 
				  let tval = Hashtbl.find foundvars (id,i) in
            let reg3 = Str.regexp_string_case_fold "true" in
            let reg4 = Str.regexp_string_case_fold "false" in
            let reg5 = Str.regexp_string_case_fold "0bin0" in
            let reg6 = Str.regexp_string_case_fold "0bin1" in
            let keyval =
              if Str.string_match reg3 tval 0 then
                "1"
              else if Str.string_match reg4 tval 0 then
                "0"
              else if Str.string_match reg5 tval 0 then
                "0"
              else if Str.string_match reg6 tval 0 then
                "1"
              else 
                tval
	    in 
	      if String.length keyval < 3 then 
		Buffer.add_string buf3 " "; 
	      if String.length keyval < 2 then 
		Buffer.add_string buf3 " "; 
	      found:=true; 
	      Buffer.add_string buf3 (" "^keyval); 
	      Buffer.add_string buf2 ("        <Value time=\""^(string_of_int
						       (if !do_negative_index then i+maxstep else i))^"\">"^keyval^"</Value>\n"); 
			       with Not_found-> 
				 Buffer.add_string buf3"   -"; 
			     done; 
			     Buffer.add_string buf3"\n"; 
			     Buffer.add_string buf2 ("      </Signal>\n")
			 end(* block 1 *) 
		  )(Tables.get_used_vars()); 
      OldFlags.loud:=prev_loud; 
      Buffer.add_string buf (Buffer.contents buf2);
      Buffer.add_string buf "    </Counterexample>\n";
      Buffer.add_string buf "  </Property>\n";
      Buffer.contents buf


(** Print valid property for XML output *)
let mk_xml_result result k time name timeout=
  let buf = Buffer.create 100 in
  let _ =  Buffer.add_string buf("  <Property name=\""^name^"\">\n") in
  let _ = Buffer.add_string buf"    <Date>" in
  let lt = Unix.localtime(Unix.time()) in 
  let time_st = Printf.sprintf "%04d-%02d-%02d"(1900+lt.Unix.tm_year)(1+lt.Unix.tm_mon)(lt.Unix.tm_mday) in 
  let _ = Buffer.add_string buf time_st in
  let _ = Buffer.add_string buf "</Date>\n" in
  let _ = 
    if(timeout) then (
      Buffer.add_string buf ("    <Runtime unit=\"sec\" timeout=\"true\"></Runtime>\n")
    ) else (
    Buffer.add_string buf ("    <Runtime unit=\"sec\" timeout=\"false\">"^time^"</Runtime>\n")) in
  let _  = Buffer.add_string buf ("    <K>"^k^"</K>\n") in
  let _  = Buffer.add_string buf ("    <Answer>"^result^"</Answer>\n") in
  let _  = Buffer.add_string buf "  </Property>\n" in
    Buffer.contents buf



(** Printing the result in XML format *)
let print_resultProp_xml  xml_format =
  match xml_format.result with 
      VALID -> mk_xml_result "valid" xml_format.k xml_format.time xml_format.name false
    | UNKNOWN -> mk_xml_result "unknown" xml_format.k xml_format.time xml_format.name false
    | INVALID -> 
	begin
	  match 
	    xml_format.foundvars, 
	    xml_format.minstep, 
	    xml_format.maxstep with
		Some foundvars, Some minstep, Some maxstep -> mk_cex_xml foundvars minstep maxstep xml_format.name xml_format.k xml_format.time 
	      | _ -> assert false
		  
	end
    | TIMEOUT -> mk_xml_result "unknown" xml_format.k xml_format.time xml_format.name true
    | _ -> assert false


(********************************************************************)
(* this wraps the formula in a (assert+ ) command *)
let print_checker_assertion from_checker_ch f varid step =
debug_to_user "print_checker_assertion";
  if !checker_mode then
    begin
      let str = Lus_convert_yc.simple_command_string (ASSERT_PLUS(f)) in
          print_to_checker (str);
          print_to_checker (solver#get#done_string);

          let out = solver#get#get_output from_checker_ch in
          solver#get#get_assert_id out varid step
    end



  (*************************************************************)
  (* send a list of assignments from the model to the checker *)
  (* return true if unsat, false otherwise *)
let check_for_bad_assignments from_checker_ch foundvars varlist k =
    debug_to_user "check_for_bad_assignments";
    print_to_checker (solver#get#cc^"checking assignments\n");
    print_to_checker solver#get#push_string;
    for i= (-k) to 0 do
      List.iter (fun id ->
        try
          let value = Hashtbl.find foundvars (id,i) in

          let key = Tables.get_varinfo_name id in
          
          print_to_checker (
            Lus_convert_yc.simple_command_string (
(**)              ASSERT(F_EQ(PRED(key,[NUM i]),STRING value,L_INT)))
          );
        with Not_found -> ()
      ) varlist;
    done;
    print_to_checker (Lus_convert_yc.simple_command_string
                        (QUERY(F_TRUE)));
    print_to_checker solver#get#done_string;
    print_to_checker solver#get#pop_string;
    let out = solver#get#get_output from_checker_ch in
    solver#get#result_is_unsat out



(********************************************************************)
(* p_assert is a string describing the negated property *)
let query_checker from_checker_ch assignments base_step k1 =
try
debug_to_user "query_checker";
  let nstart = solver#get#step_base_string in
  let found_at_least_one = ref false in
  let maxindex = ref (-k1) in
  let k1_s = string_of_int k1 in
  print_to_checker solver#get#push_string;
  print_to_checker (solver#get#cc^"k1="^k1_s^"\n");
  Hashtbl.iter (fun (id,step) tval ->
    let name = Tables.get_varinfo_name id in
      begin
        found_at_least_one := true;
        if step > !maxindex then 
          maxindex := step;
        print_checker_assertion from_checker_ch (
            F_EQ(PRED(name,[NUM step]),STRING tval,L_INT)
          ) id step
      end
  ) assignments;
  if !found_at_least_one then
    begin (* found at least one *)
      begin
        match solver#get#get_current_n_value with
          Some x -> 
            print_to_checker (Lus_convert_yc.simple_command_string 
             (ASSERT(
               F_EQ(POSITION_VAR solver#get#k_position_string, NUM x,L_INT))))
          | None -> ()
      end;
      (* this is necessary to avoid unnecessary incompleteness *)

      if !do_negative_index then
        begin
          (* the following should be redundant *)
          let klist = (Array.to_list (Array.init (k1) (fun x -> x+1))) in
          let plist = 
            List.fold_left (fun acc x -> F_AND(F_PRED("P",[NUM x]),acc)) 
              (F_NOT(F_PRED("P",[NUM 0]))) klist 
          in
          let qbase = 
            F_AND(F_EQ(POSITION_VAR nstart, MINUS(NUM 0,NUM k1),L_INT),plist) 
          in
          print_to_checker (Lus_convert_yc.simple_command_string
            (QUERY(qbase)));
          end;


      print_to_checker solver#get#done_string;
      print_to_checker solver#get#pop_string;
      let out = solver#get#get_output from_checker_ch in
      if (solver#get#result_is_unsat out) then
        begin
          print_to_user (solver#get#cc^"Counterexample appears spurious\n");
          print_to_checker (solver#get#cc^"CEX spurious\n");
          let res = 
            solver#get#get_unsat_core out print_to_checker from_checker_ch
          in
          CHECK_INCORRECT res
        end (* found at least one *)
      else
        begin
          print_to_user (solver#get#cc^"Counterexample appears valid\n");
          print_to_checker (solver#get#cc^"CEX valid\n");
          CHECK_VALID
        end
    end
  else
    begin
      print_to_checker solver#get#pop_string;
      print_to_user (solver#get#cc^"Counterexample probably valid\n");
      print_to_checker (solver#get#cc^"CEX valid\n");
      CHECK_VALID
    end
with UNSAT_FOUND -> (* detects unsat early *)
  print_to_checker solver#get#pop_string;
  CHECK_INCORRECT []


(********************************************************************)
(* print def(0) to step solver if in loopfree mode *)
(* do this for all state vars? *)
let def_assert_initial def_hash def_base add id =
debug_to_user "def_assert_initial";
  let nstart = solver#get#step_base_string in
  (* initial in step *)
  if !separate_solvers  && !loopfree_mode && !initial_compression && 
     not !fully_define_initial_state 
  then
    begin
      let y = Tables.safe_find def_hash id "def_assert_initial" in
      let s = Lus_convert_yc.simple_command_string
        (ASSERT(
          F_PRED(def_base^"__"^(string_of_int id),[POSITION_VAR nstart])))
      in 
      match y with
          DEF_REF _ -> () (* skip *)
        | DEF_STR d ->
debug_to_user (string_of_int id);
          if !abs_mode then
            begin
              match d.abstr.(step_abstr) with
                  NOT_REFINED -> ()
                | REFINED_MORE (_,x) ->
                  Abs.set_refined id d step_abstr (REFINED(x));
                  print_to_solver2 s
                | _ -> (* only print refined vars *)
                  print_to_solver2 s
            end
          else (* print them all *)
            begin
              print_to_solver2 s
            end
    end

(********************************************************************)
(* only send to solver *)
(* print a single variable def *)
 let def_assert_single base_step print_to_dest defhash def_base params id =
debug_to_user "def_assert_single";
  let index = 
    if base_step = STEP then step_abstr
    else base_abstr
  in
  let y = Tables.safe_find defhash id "def_assert_single" in
    match y with
        DEF_REF _ -> () (* skip *)
      | DEF_STR d ->
        if !abs_mode then
          begin
            let printout () = 
                let s =
                  Lus_convert_yc.simple_command_string (
                    ASSERT(
                      F_PRED(def_base^"__"^(string_of_int id),params)
                      ))
                in
                print_to_dest s
            in
            match d.abstr.(index) with
                NOT_REFINED -> ()
              | REFINED_MORE (_,x) ->
                d.abstr.(index) <- REFINED(x);
                printout()
              | _ -> (* only print refined vars *)
                printout()
          end
        else (* print them all *)
          begin
            let s = 
                  Lus_convert_yc.simple_command_string (
                    ASSERT(
                      F_PRED(def_base^"__"^(string_of_int id),params)
                      ))
            in
            print_to_dest s
          end

(********************************************************************)
(* only send to solver *)
(* print a single variable def with level info *)
let def_assert_single_level print_to_dest defhash def_base params id level =
debug_to_user "def_assert_single_level";
  let y = Tables.safe_find defhash id "def_assert_single_level" in
    match y with
        DEF_REF _ -> () (* skip *)
      | DEF_STR d ->
        if !abs_mode then
          begin
                let s =
                  Lus_convert_yc.simple_command_string (
                    ASSERT(
                      F_PRED(def_base^"__"^(string_of_int id),params)
                      ))
                in
                print_to_dest s
          end
        else (* print them all *)
          begin
            let s = 
                  Lus_convert_yc.simple_command_string (
                    ASSERT(
                      F_PRED(def_base^"__"^(string_of_int id),params)
                      ))
            in
            print_to_dest s
          end


(********************************************************************)
(* coi requires more thought *)
let print_initialization_single def_hash startdepth add id =
debug_to_user "print_initialization";
  for i=0 to startdepth-1 do
      def_assert_single BASE print_to_solver def_hash "DEF" [NUM(add*i)] id
  done


(********************************************************************)
(* assume all defs referenced with inputs or props are inially refined *)
(* only send to solver *)
(* coi requires more thought *)
let def_assert base_step print_to_dest defhash def_base params =
debug_to_user "def_assert";
  let index = 
    if base_step = STEP then step_abstr
    else base_abstr
  in
  Hashtbl.iter (fun x y ->
    match y with
        DEF_REF _ -> () (* skip *)
      | DEF_STR d ->
        if !abs_mode then
          begin
            let printout () =
                let s =
                  Lus_convert_yc.simple_command_string (
                    ASSERT(
                      F_PRED(def_base^"__"^(string_of_int x),params)
                      ))
                in
                print_to_dest s
            in
            match d.abstr.(index) with
                NOT_REFINED -> ()
              | REFINED_MORE (_,x) ->
                d.abstr.(index) <- REFINED(x);
                printout()
              | _ -> (* only print refined vars *)
                printout()
          end
        else (* print them all *)
          begin
            let s = 
                  Lus_convert_yc.simple_command_string (
                    ASSERT(
                      F_PRED(def_base^"__"^(string_of_int x),params)
                      ))
            in
            print_to_dest s
          end
  ) defhash


(********************************************************************)
(* def_param should be None or Some "blah" *)
(* send to both solver and checker *)
(* assume all defs referenced with inputs or props are inially refined *)
(* coi requires more thought *)
let def_assert_both base_step print_to_dest defhash def_base params step from_checker_ch =
debug_to_user "def_assert_both";
  let index = 
    if base_step = STEP then step_abstr
    else base_abstr
  in
  Hashtbl.iter (fun x y ->
    match y with
        DEF_REF _ -> () (* skip *)
      | DEF_STR d ->
        if !abs_mode then
          begin
            let printout () =
              let s = F_PRED(def_base^"__"^(string_of_int x),params) in
              print_to_dest (Lus_convert_yc.simple_command_string (ASSERT(s)));
(**)          print_checker_assertion from_checker_ch s x step
            in
            match d.abstr.(index) with
                NOT_REFINED -> (* print all to checker *)
                  if !checker_mode then
                    begin
                      let s = F_PRED(def_base^"__"^(string_of_int x),params) in
(**)                  print_checker_assertion from_checker_ch s x step
                    end
              | REFINED_MORE (_,x) ->
                d.abstr.(index) <- REFINED(x);
                printout()
              | _ -> (* only print refined vars *)
                printout()
          end
        else (* print them all *)
          begin
            let s = F_PRED(def_base^"__"^(string_of_int x),params) in
            print_to_dest (Lus_convert_yc.simple_command_string (ASSERT(s)));
(**)        print_checker_assertion from_checker_ch s x step
          end
  ) defhash


(********************************************************************)
let def_assert_both1 defhash def_base def_param step from_checker_ch =
debug_to_user "def_assert_both1";
    def_assert_both BASE print_to_solver defhash def_base def_param step from_checker_ch

(********************************************************************)
let def_assert_both2 defhash def_base def_param step from_checker_ch =
debug_to_user "def_assert_both2";
    def_assert_both STEP print_to_solver2 defhash def_base def_param step from_checker_ch
 
(********************************************************************)
let def_assert_both3 defhash def_base def_param step from_checker_ch =
debug_to_user "def_assert_both3";
    def_assert_both BASE print_to_solver3 defhash def_base def_param step from_checker_ch

(********************************************************************)
let def_assert_both4 defhash def_base def_param step from_checker_ch =
debug_to_user "def_assert_both4";
    def_assert_both BASE print_to_solver4 defhash def_base def_param step from_checker_ch

(********************************************************************)
let def_assert_both5 defhash def_base def_param step from_checker_ch =
  debug_to_user "def_assert_both5";
  def_assert_both STEP print_to_solver5 defhash def_base def_param step from_checker_ch
    

(********************************************************************)
let last_level_asserted = ref 0

let set_last_level_asserted x = last_level_asserted := x

let checker_not_asserted k = 
  (* returns false if already asserted at this level *)
    if !last_level_asserted = k then
      false
    else
      begin
        last_level_asserted := k;
        true
      end


(********************************************************************)
let persistent_step_asserts_concrete def_hash startdepth add k from_checker_ch=
    if !OldFlags.var_defs_mode then
      begin
        if checker_not_asserted k then
          def_assert_both1 def_hash "DEF" [NUM(add*k)]
            k from_checker_ch
        else
          def_assert BASE print_to_solver def_hash "DEF" [NUM(add*k)]
      end
    else
      print_to_both
       (Lus_convert_yc.simple_command_string
                (ASSERT(F_PRED("DEF",[NUM(add*k)]))))

let persistent_assert_bmc def_hash startdepth add k from_checker_ch=
    if !OldFlags.var_defs_mode then
      begin
        if checker_not_asserted k then
          def_assert_both4 def_hash "DEF" [NUM(add*k)]
            k from_checker_ch
        else
          def_assert BASE print_to_solver def_hash "DEF" [NUM(add*k)]
      end
    else
      print_to_solver4
       (Lus_convert_yc.simple_command_string
                (ASSERT(F_PRED("DEF",[NUM(add*k)]))))


(********************************************************************)
let persistent_step_asserts_concrete_inv def_hash startdepth add k from_checker_ch=
    if !OldFlags.var_defs_mode then
      begin
        if checker_not_asserted k then
          def_assert_both3 def_hash "DEF" [NUM(add*k)] k from_checker_ch
          else
          def_assert BASE print_to_solver3 def_hash "DEF" [NUM(add*k)]
      end
    else
      print_to_solver3
       (Lus_convert_yc.simple_command_string
                (ASSERT(F_PRED("DEF",[NUM(add*k)]))))


(********************************************************************)
(* print out one instance of all asserts at step k *)
let persistent_step_asserts_symbolic def_hash startdepth add k from_checker_ch =
  let nvar = solver#get#k_position_string in
  let ksend = k-startdepth in
     if !OldFlags.var_defs_mode then
(**)    def_assert_both2 def_hash "DEF"
          [PLUS(POSITION_VAR(nvar),NUM(add*ksend))]
          k from_checker_ch
     else
       print_to_both2
        (Lus_convert_yc.simple_command_string
          (ASSERT(F_PRED("DEF",[PLUS(POSITION_VAR(nvar),NUM(add*ksend))]))))


(**  Print out one instance of all asserts at step k. Inductive process. *)
let asserts_inductive def_hash startdepth add k from_checker_ch =
  let nvar = solver#get#k_position_string in
  let ksend = k-startdepth in
     if !OldFlags.var_defs_mode then
       def_assert_both2 def_hash "DEF"
         [PLUS(POSITION_VAR(nvar),NUM(add*ksend))]
          k from_checker_ch
     else
       print_to_solver2
         (Lus_convert_yc.simple_command_string
            (ASSERT(F_PRED("DEF",[PLUS(POSITION_VAR(nvar),NUM(add*ksend))]))))
	 
(********************************************************************)
(* send k1 as k *)
(* print out one instance of only id assert at step k *)
let persistent_step_single_assert def_hash startdepth add base_step k id =
  let nvar = solver#get#k_position_string in
  let ksend = k-startdepth in
  def_assert_single base_step print_to_solver def_hash
    "DEF" [NUM(add*k)] id;
  if base_step = STEP then
    def_assert_single base_step print_to_solver2 def_hash
      "DEF" [PLUS(POSITION_VAR(nvar),NUM(add*ksend))] id

(********************************************************************)
(* send k1 as k *)
(* print out one instance of only id assert at step level *) 
let persistent_step_single_level_assert def_hash startdepth add base_step level id k =
  let nvar = solver#get#k_position_string in
  def_assert_single_level print_to_solver def_hash "DEF"
    [NUM(add*level)] id level;
                
  if base_step = STEP then
    def_assert_single_level print_to_solver2 def_hash "DEF"
      [PLUS(POSITION_VAR(nvar),NUM(add*level))] id level



(********************************************************************)
(* coi requires more thought *)
(* only the first time *)
let print_initialization def_hash startdepth add from_checker_ch =
debug_to_user "print_initialization";
  for i=0 to startdepth-1 do
    let i_s = string_of_int i in
    if !var_defs_mode then
      def_assert_both1 def_hash "DEF" [NUM(add*i)] i from_checker_ch
    else
      print_to_solver ("(assert (= (DEF (- 0 "^i_s^")) true))\n")
  done
  
 

(** Print initial TS given a solver *)
let print_init solver def_hash startdepth add from_checker_ch =
match solver with 
    1 -> 
      begin
	debug_to_user "print_initialization\n";
	for i=0 to startdepth-1 do
	  let i_s = string_of_int i in
	    if !var_defs_mode then
	      def_assert_both1 def_hash "DEF" [NUM(add*i)] i from_checker_ch
	    else
	      print_to_solver ("(assert (= (DEF (- 0 "^i_s^")) true))\n")
	done
      end	
  | 3 ->
       begin
	debug_to_user "print_initialization\n";
	for i=0 to startdepth-1 do
	  let i_s = string_of_int i in
	    if !var_defs_mode then
	      def_assert_both3 def_hash "DEF" [NUM(add*i)] i from_checker_ch
	    else
	      print_to_solver3 ("(assert (= (DEF (- 0 "^i_s^")) true))\n")
	done
       end
  | 4 -> begin
	for i=0 to startdepth-1 do
	  let i_s = string_of_int i in
	    if !var_defs_mode then
	      def_assert_both4 def_hash "DEF" [NUM(add*i)] i from_checker_ch
	    else
	      print_to_solver4 ("(assert (= (DEF (- 0 "^i_s^")) true))\n")
	done
       end
  | _  -> assert false


 
(********************************************************************)
let print_stat_headers () =
  if !do_k_induction then
    print_to_user (solver#get#cc^"MODE:K_INDUCTION_"^(string_of_int !k_step_size)^"\n")
  else
    print_to_user (solver#get#cc^"MODE:BMC\n");
  let is_static =
    if static_path_compression.(base_abstr) then
      "STATIC_"
    else
      ""
  in
  if !loopfree_mode then
    print_to_user(solver#get#cc^"MODE:"^is_static^"PATH_COMPRESSION\n");
  if !termination_check then
    print_to_user(solver#get#cc^"MODE:"^is_static^"TERMINATION_CHECK\n");
  if !separate_solvers then
    print_to_user(solver#get#cc^"MODE:SEPARATE_SOLVERS\n");
  if !abs_mode then
    print_to_user(solver#get#cc^"MODE:ABSTRACTION_REFINEMENT\n");
  if !force_refinement < max_int then
    print_to_user(solver#get#cc^"MODE:FORCE_REFINEMENT_"^(string_of_int !force_refinement)^"\n");
  if !debug then
    print_to_user(solver#get#cc^"MODE:DEBUG\n");
  if !inlining_mode then
    print_to_user(solver#get#cc^"MODE:BASIC_INLINING ("^(string_of_int (Tables.get_number_variables_inlined()))^" variables inlined)\n");
  if !aggressive_inlining > 0 then
    print_to_user(solver#get#cc^"MODE:AGGRESSIVE_INLINING_"^(string_of_int !OldFlags.aggressive_inlining)^" ("^(string_of_int (Inlining.get_number_variables_inlined()))^" variables inlined)\n")

(********************************************************************)
let get_add () = 
    if !do_negative_index then
      -1
    else
      1

(********************************************************************)
let setup_channels () =
  let solvercall = solver#get#solver_call !OldFlags.solverflags in
  let from_solver_ch,to_ch = Unix.open_process solvercall in
  to_solver_ch := to_ch;
  (* start a second checker process if necessary *)
  let from_checker_ch,to_chkr = 
    if !checker_mode then
      Unix.open_process solvercall 
    else
      stdin,stdout
  in
  to_checker_ch := to_chkr;
  let from_solver2_ch,to_ch2 = 
    if !separate_solvers then
      Unix.open_process solvercall
    else
      from_solver_ch,to_ch
  in
  to_solver2_ch := to_ch2;
  from_solver_ch,from_checker_ch,from_solver2_ch


(********************************************************************)
let setup_solver1 () =
  let solvercall = solver#get#solver_call !OldFlags.solverflags in
  (* start a second checker process if necessary *)
  let from_checker_ch,to_chkr = 
    if !checker_mode then
      Unix.open_process solvercall 
    else
      stdin,stdout
  in
    to_checker_ch := to_chkr;
    let from_solver_ch,to_ch = Unix.open_process solvercall in
      to_solver_ch := to_ch;
      from_checker_ch,from_solver_ch
	

(********************************************************************)
let setup_solver2 () =
  let solvercall = solver#get#solver_call !OldFlags.solverflags in
  (* start a second checker process if necessary *)
  let from_checker_ch,to_chkr = 
    if !checker_mode then
      Unix.open_process solvercall 
    else
      stdin,stdout
  in
  to_checker_ch := to_chkr;
  let from_solver2_ch,to_ch2 = Unix.open_process solvercall
  in
  to_solver2_ch := to_ch2;
  from_checker_ch,from_solver2_ch


(********************************************************************)
let setup_solver3 () =
  let solvercall = solver#get#solver_call !OldFlags.solverflags in
  (* start a second checker process if necessary *)
  let from_checker_ch,to_chkr = 
    if !checker_mode then
      Unix.open_process solvercall 
    else
      stdin,stdout
  in
  to_checker_ch := to_chkr;
  let from_solver3_ch,to_ch3 = Unix.open_process solvercall
  in
  to_solver3_ch := to_ch3;
  from_checker_ch,from_solver3_ch


(********************************************************************)
let setup_solver_bmc_checker () =
let solvercall = solver#get#solver_call !OldFlags.solverflags in
  let from_checker_ch,to_chkr = 
    if !checker_mode then
      Unix.open_process solvercall 
    else
      stdin,stdout
  in
    to_checker_ch := to_chkr;
    let from_solver4_ch,to_ch4 = Unix.open_process solvercall in
      to_solver4_ch := to_ch4;
      from_checker_ch, from_solver4_ch


(********************************************************************)
let setup_solver_induct_checker () =
  let solvercall = solver#get#solver_call !OldFlags.solverflags in
  let from_checker_ch,to_chkr = 
    if !checker_mode then
      Unix.open_process solvercall 
    else
      stdin,stdout
  in
    to_checker_ch := to_chkr;
    let from_solver5_ch,to_ch5 = Unix.open_process solvercall in
      to_solver5_ch := to_ch5;
      from_checker_ch, from_solver5_ch


(* To separate solvers for incremental invariant generation *)
(********************************************************************)
let setup_channels_inv () =
  let solvercall = solver#get#solver_call !OldFlags.solverflags in
  (* start a second checker process if necessary *)
  let from_checker_ch,to_chkr = 
    if !checker_mode then
      Unix.open_process solvercall 
    else
      stdin,stdout
  in
  to_checker_ch := to_chkr;
    let from_solver4_ch,to_ch4 = Unix.open_process solvercall in
      to_solver4_ch := to_ch4;
      let from_solver5_ch,to_ch5 =  Unix.open_process solvercall in
	to_solver5_ch := to_ch5;
	from_solver4_ch,from_checker_ch,from_solver5_ch





