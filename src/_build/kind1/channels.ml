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

(** Global declration of channnels *)

(** 
@author Jed Hagen
@author Temesghen Kahsai

*)

open Types

(* channels used, and basic printings *)

let main_ch = ref stdout (* sent to reference file used in sequential KIND*)
let main2_ch = ref stdout (* sent to reference file2 used in sequential KIND *)
let base_ch = ref stdout (* For the base process *)
let induct_ch = ref stdout (* For the inductive process *)
let extra_ch = ref stdout (* For the extra checks in the inductive process*)
let inv_ch = ref stdout (* For the invariant generator process *)
let check_ch = ref stdout (* sent to reference file *)
let to_solver_ch = ref stdout (* sent to solver *)
let to_checker_ch = ref stdout (* sent to checker *)
let to_solver2_ch = ref stdout (* sent to solver2 *)
let to_solver3_ch = ref stdout (* sent to solver3 *)
let to_solver4_ch = ref stdout (* sent to solver4 *)
let to_solver5_ch = ref stdout (* sent to solver5 *)
let dummy = stdin (* dummy *)
let debug_ch = ref stdout  (* what the user sees *)
let xml_ch = ref stdout (* for generation of XML document *)

(*  Invariant files *)
let inv_file = ref stdout (* invariant*)
let file_plus_invariant = ref stdout (* invariant*)

(********************************************************************)
let print_to_solver str =
  if !OldFlags.do_scratch then
    output_string !base_ch str;
  output_string !to_solver_ch str;
  if !OldFlags.debug then
    output_string !base_ch str;
  flush_all ()


(********************************************************************)
let print_to_solver2 str =
  if !OldFlags.do_scratch then
    output_string !induct_ch str;
  output_string !to_solver2_ch str;
  if !OldFlags.debug then
    output_string !induct_ch str;
  flush_all ()
    
(********************************************************************)
let print_to_solver3 str =
  if !OldFlags.do_scratch then
    output_string !inv_ch str;
  output_string !to_solver3_ch str;
  if !OldFlags.debug then
    output_string !inv_ch str;
  flush_all ()

let print_to_solver4 str =
  if !OldFlags.do_scratch then
    output_string !base_ch str;
  output_string !to_solver4_ch str;
  if !OldFlags.debug then
    output_string !debug_ch str;
  flush_all ()

let print_to_solver5 str =
  if !OldFlags.do_scratch then
    output_string !extra_ch str;
  output_string !to_solver5_ch str;
  if !OldFlags.debug then
    output_string !extra_ch str;
  flush_all ()


let send_to_solver solver str =
  match solver with
      BMC ->
	begin
	  if !OldFlags.do_scratch then output_string !base_ch str;
	  output_string !to_solver_ch str;
	  if !OldFlags.debug then output_string !debug_ch str; flush_all ()
	end
    | INDUCT ->
	begin
	  if !OldFlags.do_scratch then output_string !induct_ch str;
	  output_string !to_solver2_ch str;
	  if !OldFlags.debug then output_string !debug_ch str; flush_all ()
	end
    | INVR -> 
	begin
	   if !OldFlags.do_scratch then output_string !inv_ch str;
	  output_string !to_solver3_ch str;
	  if !OldFlags.debug then output_string !debug_ch str;flush_all ()
	  end
    | BASE_CHECK -> 
	begin
	  (*TODO change !base_ch*)
	   if !OldFlags.do_scratch then output_string !base_ch str;
	  output_string !to_solver4_ch str;
	  if !OldFlags.debug then output_string !debug_ch str;flush_all ()
	  end
    | INDUCT_CHECK -> 
	begin
	  (*TODO change !induct_ch*)
	  if !OldFlags.do_scratch then output_string !induct_ch str;
	  output_string !to_solver5_ch str;
	  if !OldFlags.debug then output_string !debug_ch str;flush_all ()
	end
    | _ -> assert false


(********************************************************************)
let print_to_checker str =
  if !OldFlags.do_scratch then
    output_string !check_ch str;
  output_string !to_checker_ch str;
  if !OldFlags.debug then
    output_string !debug_ch (!OldFlags.commentchar^"CHECK>"^str);
  flush_all ()

(********************************************************************)
let print_to_both str =
  if !OldFlags.do_scratch then
    begin
      output_string !main_ch str;
      flush !main_ch
    end;
  output_string !to_solver_ch str;
  flush !to_solver_ch;
  if !OldFlags.checker_mode then
    begin
      if !OldFlags.do_scratch then
        begin
          output_string !check_ch str;
          flush !check_ch
        end;
      output_string !to_checker_ch str;
      flush !to_checker_ch
    end;
  if !OldFlags.debug then
    begin
      output_string !debug_ch str;
      flush !debug_ch
    end



(********************************************************************)
let print_to_both2 str =
      if !OldFlags.do_scratch then
        begin
          output_string !main2_ch str;
          flush !main2_ch
        end;
      output_string !to_solver2_ch str;
      flush !to_solver2_ch;
      if !OldFlags.checker_mode then
        begin
          if !OldFlags.do_scratch then
            begin
              output_string !check_ch str;
              flush !check_ch
            end;
          output_string !to_checker_ch str;
          flush !to_checker_ch
        end;
      if !OldFlags.debug then
        begin
          output_string !debug_ch str;
          flush !debug_ch
        end


let print_to_user str =
  if !OldFlags.do_scratch then
    begin
      output_string !main2_ch str;
    end;
  if !OldFlags.loud then
    output_string !debug_ch str;
  flush_all ()


(********************************************************************)
(* used for status notifications *)
let print_to_user_final str =
  output_string !debug_ch str;
  flush_all ()


(********************************************************************)
(* used for OldFlags.debugging. adds OldFlags.commentchar & \n to string *)
let debug_to_user str =
  if (!OldFlags.debug) then
    begin
      let s = (!OldFlags.commentchar)^str^"\n" in
      if !OldFlags.do_scratch then
        output_string !main_ch s;
	output_string !debug_ch s;
	flush_all ()
    end
      
(* Debug each processes *)
let debug_proc proc verbose str = 
 
  if !OldFlags.loud then
    (
    match proc, verbose with 
	BASE_PROC, Some true->
	  begin
	    let s = !OldFlags.commentchar^"BMC PROC : "^str^"\n" in
	      output_string !debug_ch s;
	      flush_all ()
	  end
      | INDUCT_PROC, Some true->
	  begin
	    let s = !OldFlags.commentchar^"INDUCTIVE PROC : "^str^"\n" in
	      output_string !debug_ch s;
	      flush_all ()
	  end
      | INV_GEN_PROC, Some true->
	  begin
	    let s = !OldFlags.commentchar^"INVARIANT GENERATION : "^str^"\n" in
	      output_string !debug_ch s;
	      flush_all ()
	  end
    | EXTRA_PROC, Some true->
    begin
      let s = !OldFlags.commentchar^"EXTRA CHECK : "^str^"\n" in
        output_string !debug_ch s;
        flush_all ()
    end
      | _ , None -> flush_all ()
    ); 
  if !OldFlags.do_scratch then
    (
    match proc with 
	BASE_PROC ->
	  begin
	    let s = !OldFlags.commentchar^"BASE : "^str^"\n" in
	      output_string !base_ch s;
	      flush_all ()
	  end
      | INDUCT_PROC ->
	  begin
	    let s = !OldFlags.commentchar^"INDUCT : "^str^"\n" in
	      output_string !induct_ch s;
	      flush_all ()
	  end
      | INV_GEN_PROC ->
	  begin
	    let s = !OldFlags.commentchar^"INV GEN : "^str^"\n" in
	      output_string !inv_ch s;
	      flush_all ()
	  end
    | EXTRA_PROC ->
    begin
      let s = !OldFlags.commentchar^"EXTRA CHECK : "^str^"\n" in
        output_string !extra_ch s;
        flush_all ()
    end
      | _ -> flush_all ()
    )	  

(* Debugging lists of properties *)
let rec mk_string list_props = 
  match list_props with 
      [] -> ""
    | [a] -> a
    | h::l -> h ^ " " ^ mk_string l

let rec mk_id list_props = 
  match list_props with 
      [] -> ""
    | [a] -> string_of_int(a)
    | h::l -> string_of_int(h) ^ " " ^ mk_id l

let debug_prop_var proc l = 
  let st_list = mk_string l in
    debug_proc proc None st_list

let debug_prop_id proc l = 
  let st_list = mk_id l in
    debug_proc proc None st_list

(* Print XML document*)
let print_xml str =
  output_string !xml_ch str;
  flush_all ()
