(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
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

(** YICES Module *)

(**
@author Jed Hagen
@author Temesghen Kahsai

*)
open Types
open OldFlags
open Channels
open Exceptions

(* solver interface for yices stand-alone executable *)
(* primarily inherited from the wrapper interface *)
(* note there is an input buffer limitation that large formulas may run 
  afoul of (promarily in the definition phase of Kind) *)

class solver_yices_cmdline = object (self)
  inherit Solver_yices.solver_yices

  (*************************************************************)
  (* command line string to call the solver *)
  method solver_call flags = 
    if not !OldFlags.gui then 
      Solvers_path.yices_path ^ " -i " ^ flags
    else
      !OldFlags.solver_path^" -i " ^ flags

  (*************************************************************)
  (* returns a string of the output from channel in_ch, terminated by __DONE__ *)
  method get_output in_ch =
    debug_to_user "get_output";
    let buf = Buffer.create 1 in
    let pos = 8 in
    try 
      while true do 
        let line = input_line in_ch in
        let long_enough = (String.length line) > pos in
        debug_to_user (line);

        let reg1 = Str.regexp_string "__DONE__" in
        let reg2 = Str.regexp_string_case_fold "error" in
        if long_enough && (Str.string_match reg1 line pos) then (* only if in position *)
          raise End_of_file
        else if (try Str.search_forward reg2 line 0 >= 0 with Not_found -> false)
          then
          raise (SolverError line)
        else
          Buffer.add_string buf (line^"\n")
      done;
    debug_to_user "get_output_done";
      ""
    with End_of_file ->
      Buffer.contents buf


 method get_solver_output solver in_ch =
   let buf = Buffer.create 1 in
   let pos = 8 in
     try 
       while true do 
         let line = input_line in_ch in
         let long_enough = (String.length line) > pos in
	   let _ = match solver with 
	       BASE_PROC -> debug_proc BASE_PROC  None (line)
		  | INDUCT_PROC -> debug_proc INDUCT_PROC None (line)
      | EXTRA_PROC -> debug_proc EXTRA_PROC None (line)
		  | INV_GEN_PROC ->  debug_proc INV_GEN_PROC None (line) in
        let reg1 = Str.regexp_string "__DONE__" in
        let reg2 = Str.regexp_string_case_fold "error" in
        if long_enough && (Str.string_match reg1 line pos) then (* only if in position *)
          raise End_of_file
        else if (try Str.search_forward reg2 line 0 >= 0 with Not_found -> false)
          then
          raise (SolverError line)
        else
          Buffer.add_string buf (line^"\n")
      done;
      ""
     with End_of_file ->
       Buffer.contents buf
end
