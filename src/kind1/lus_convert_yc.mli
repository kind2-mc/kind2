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

(** Translate from IL format into sover-specific formulas *)

(** {6 Formulas} *)

val yc_expr_buffer : 
  Types.modetype -> Types.il_expression -> Buffer.t

(** Translate a {!Types.il_formula} into a stringbuffer.  Also perform some bookkeeping for later use. Used for the main program translation. *)
val yc_formula_string_buffer : 
  Types.modetype -> int -> Types.il_formula -> Buffer.t

val simple_formula_buffer : Types.il_formula -> Buffer.t

(** Translate a {!Types.il_formula} into a string.  Do not do any further processing. Used for translation of predetermined formulas (mostly asserts and queries) into solver-specific format.  *)
val simple_command_string : Types.solver_command -> string

(** Returns a string of the program variable definitions.  Also performs some bookkeeping *)
val yc_var_shortcut_string : unit -> string

(** Returns a string of the formula describing the property predicate P() *)
val yc_property_header : 
  string -> Types.il_expression -> Types.typed_stream -> string

(** Returns a string of the formula describing multiple properties *)
val yc_multi_property_header : 
   string -> Types.il_expression -> Types.typed_stream list -> string

val yc_property_header_new : 
   string -> Types.il_expression -> Types.typed_stream -> string

(** Returns a list of strings of the formula describing the properties *)
val yc_multi_property_header_list : 
   Types.il_expression -> Types.typed_stream list -> string list

(** Returns a string of a formula defining all assumptions (lustre asserts) in the program.  *)
val yc_assumption_string : string -> Types.il_expression -> string

(** Returns a string describing a unique state, based on all variables *)
val yc_state_vars_string : unit -> string 

(** Returns a string describing a unique state based on currently refined variables *)
val yc_state_vars_string_refined : int -> string 

(** Returns the current name of the state_vars definition.  *)
val get_state_vars_r_version : unit -> string

val get_all_def_terms: unit -> Types.il_expression list
