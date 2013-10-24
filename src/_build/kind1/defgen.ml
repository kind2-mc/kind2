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


(** Formula generator *)

(**
@author Jed Hagen 
@author Temesghen Kahsai

*)

open Types
open Exceptions
open Channels
open Printf



let solver = Globals.my_solver


(********************************************************************)
(* returns string buffer *)
(* ite_maxdepth should be > 0 for ite elim mode 'n' only *)
(* ite_maxdepth should be < 0 for ite elim mode 'i' only *)
let generate_var_defs_yc defhash def_base_name ite_maxdepth =
  let buf = Buffer.create 100 in
  Hashtbl.iter (fun x y ->
    match y with
        DEF_REF _ -> ()
      | DEF_STR dhe ->
          if ite_maxdepth >= 0 then
              solver#get#define_fun_buffer buf 
               (def_base_name^"__"^(string_of_int x)) (M_FUNC[M_NAT;M_BOOL])
               [(solver#get#position_var1,M_NAT)] dhe.def
          else
              solver#get#define_fun_buffer buf 
               (def_base_name^"__"^(string_of_int x)) M_BOOL [] dhe.def
    
  ) defhash;
  buf


(** Used in Z3 (incomplete) *)
let generate_trans_def defhash def_base_name =
  let buf = Buffer.create 500 in
    solver#get#define_trans buf (Hashtbl.fold (fun x _ rest -> ((def_base_name^"__"^(string_of_int x))::rest)) defhash []); 
    buf



(** Generate formulas.*)
 let start filename =   
  let use_file = open_in filename in
  let in_ch = use_file in
  let lexbuf = Lexing.from_channel in_ch in
  let outdoc = Buffer.create 1000 in
  let def_hash = Deftable.get_defhash() in
  let no_stateful = ref false in

  try
    let (cp, p, list_p, target_node) = Lustre_parser.main Lustre_lexer.token lexbuf in
      
(* cp is not currently used *)
    let position = POSITION_VAR (solver#get#position_var1) in
     
    let _ = if (!OldFlags.abstr_bool || !OldFlags.abstr_ite || !OldFlags.abstr_pre) then 
      Lus_flatten.flatten_all_node_defs () in

    let fd = Lus_convert.convert_def_list position target_node in
    let maxdepth = Lus_convert.get_max_depth() in
    let _ = if maxdepth > Lus_convert.get_max_adepth() then
      raise Unguarded_PRE in
	
    let fd' =
      if !OldFlags.aggressive_inlining > 0 then
        Inlining.inlined_formula fd (Coi.property_id_list p) 
      else
        fd
    in
   
    (* verfs lists the initial set of variables -- properties, basically *)
    let _ =  Coi.examine_assignments fd' in
    let vrefs1 = Coi.property_id_list p in
    let vrefs = 
      if !OldFlags.pre_refine_state_vars then
        List.rev_append vrefs1 (Lus_convert.state_vars_list())
      else
        vrefs1
    in
      Coi.calculate_all_dependencies vrefs 0 maxdepth;

     
      begin (*formula generation for yices *)
        let form_str_buf = Lus_convert_yc.yc_formula_string_buffer GENERAL maxdepth fd' in
        (* the above determin which variables are actually used *)
        let property =  Lus_convert_yc.yc_property_header solver#get#position_var1 position p in
        let assertions = Lus_convert_yc.yc_assumption_string solver#get#position_var1 position in
        let vdef = Lus_convert_yc.yc_var_shortcut_string () in
          Buffer.add_string outdoc (solver#get#header_string^"\n");
            Buffer.add_string outdoc (solver#get#cc^"maxdepth = "^(string_of_int maxdepth)^"\n");
            Buffer.add_string outdoc (vdef^"\n\n");
	  Buffer.add_string outdoc (solver#get#cc^"Generic definitions\n");
          (* print out generic def *)
        if (!OldFlags.var_defs_mode) then (
          Deftable.initialize_defs def_hash vrefs; 
          Buffer.add_buffer outdoc (generate_var_defs_yc def_hash "DEF" 0);
        )else(
            solver#get#aggdef_header outdoc form_str_buf;
        );
	
	if (!OldFlags.enabled_z3) then (
	Buffer.add_buffer outdoc (generate_trans_def def_hash "DEF"));
       
	 Buffer.add_string outdoc (solver#get#cc^"Property(ies)\n");
        (* print out property & state limitations *)
	if !OldFlags.no_multi then (
	   Buffer.add_string outdoc (property^"\n");
	   Buffer.add_string outdoc (solver#get#cc^"SINGLE PROP - NO MULTI\n")
	) else (
	  if (List.length list_p == 1) then (
	    Buffer.add_string outdoc (property^"\n");
	  )else(
	    Buffer.add_string outdoc (solver#get#cc^"NO SINGLE PROP\n")
	  )
	);
	      
        Buffer.add_string outdoc (assertions^"\n");
        if (!OldFlags.loopfree_mode || !OldFlags.termination_check) then
          begin
            Coi.clean_used_vars maxdepth;
            try
              Buffer.add_string outdoc 
                ((Lus_convert_yc.yc_state_vars_string())^"\n");
            with NoStatefulVars ->
              no_stateful := true;
          end;
      end; (* end yices formula generation *)
    (* return values *)
      (Buffer.contents outdoc),
    maxdepth,
    def_hash,
    !no_stateful,
    vrefs,
    list_p
  with TypeMismatch(s,x,y) ->
    Printf.printf "\nType Mismatch %s:\n%s\n!=\n%s\n at line %d (col %d)\n" s
      (solver#get#type_string x) (solver#get#type_string y) 
      (!Lus_convert.linenum) 
      ((Lexing.lexeme_start lexbuf) - !Lus_convert.linepos);
    raise Lus_convert_error
    | Parsing.Parse_error ->
	Printf.printf "\nParse error at line %d (col %d): '%s'\n" 
	  (!Lus_convert.linenum) 
	  ((Lexing.lexeme_start lexbuf) - !Lus_convert.linepos)
	  (Lexing.lexeme lexbuf);
	raise Lus_convert_error
	  

(** Formula generator for the invariant genartor process *)
let start_invariant_generator lus_file =
  let use_file = open_in lus_file in
  let in_ch = use_file in
  let lexbuf = Lexing.from_channel in_ch in
  let outdoc = Buffer.create 1000 in
  let def_hash = Deftable.get_defhash() in
 
  try
    let (cp,p,list_p,target_node) = Lustre_parser.main Lustre_lexer.token lexbuf in
    let position = POSITION_VAR (solver#get#position_var1) in

    if (!OldFlags.abstr_bool || !OldFlags.abstr_ite || !OldFlags.abstr_pre) then 
      Lus_flatten.flatten_all_node_defs ();

    let fd = Lus_convert.convert_def_list position target_node in
    let maxdepth = Lus_convert.get_max_depth() in
    if maxdepth > Lus_convert.get_max_adepth() then
      raise Unguarded_PRE;


    let fd' = 
      if !OldFlags.aggressive_inlining > 0 then
	Inlining.inlined_formula fd (Coi.property_id_list p) 
      else
	fd
    in
    

    (* verfs lists the initial set of variables -- properties, basically *)
    let _ = Coi.examine_assignments fd' in
    let vrefs1 = Coi.property_id_list p in
    let vrefs = 
      if !OldFlags.pre_refine_state_vars then
        List.rev_append vrefs1 (Lus_convert.state_vars_list())
      else
        vrefs1
    in
    Coi.calculate_all_dependencies vrefs 0 maxdepth;

      begin(*formula generation for yices *)
        let form_str_buf =  Lus_convert_yc.yc_formula_string_buffer GENERAL maxdepth fd'  in
        let vdef = Lus_convert_yc.yc_var_shortcut_string () in
          Buffer.add_string outdoc (solver#get#header_string^"\n");
          Buffer.add_string outdoc (solver#get#cc^"maxdepth = "^(string_of_int maxdepth)^"\n");
          Buffer.add_string outdoc (vdef^"\n\n");
          Buffer.add_string outdoc (solver#get#cc^"Generic definitions:\n");
        (* print out generic def *)
        if (!OldFlags.var_defs_mode) then (
          Deftable.initialize_defs def_hash vrefs; 
          Buffer.add_buffer outdoc (generate_var_defs_yc def_hash "DEF" 0))
        else(
            solver#get#aggdef_header outdoc form_str_buf);
      end; (* end yices formula generation *)
    (* return values *)
      (Buffer.contents outdoc),
      maxdepth,
      def_hash,
      vrefs
  with TypeMismatch(s,x,y) ->
    Printf.printf "\nType Mismatch %s:\n%s\n!=\n%s\n at line %d (col %d)\n" s
      (solver#get#type_string x) (solver#get#type_string y) 
      (!Lus_convert.linenum) 
      ((Lexing.lexeme_start lexbuf) - !Lus_convert.linepos);
    raise Lus_convert_error
  | Parsing.Parse_error ->
    Printf.printf "\nParse error at line %d (col %d): '%s'\n" 
      (!Lus_convert.linenum) 
      ((Lexing.lexeme_start lexbuf) - !Lus_convert.linepos)
      (Lexing.lexeme lexbuf);
    raise Lus_convert_error








