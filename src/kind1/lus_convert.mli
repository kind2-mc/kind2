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

(** First Pass Translation.  This translates from a stream formal into an "IL"-like format. *)

(** A counter to ensure all variable ids are unique. *)
val idcounter : Counter.counter

(** Current line number and position of the last newline.  Used by parser. *)
val linenum : int ref
(** Current line number and position of the last newline.  Used by parser. *)
val linepos : int ref


(** Create a conjunction of two formulas *)
val f_and : Types.il_formula -> Types.il_formula -> Types.il_formula

(** Translate position into an integer *)
val simplify_position_depth : Types.il_expression -> int

(** Convert a {!Types.typed_stream} into a set of {!Types.il_formula}s.  
Any subnode calls are transformed into inlined definitions.  A basic simplification is done to unify obviously redundant variables (of the type a=b). *)
val convert_term : Types.typed_stream -> Types.il_expression -> int -> int ->  (string * Types.transtable) option -> Types.typed_stream option -> (Types.il_expression * Types.il_formula)

(** Returns the maximun depth of pres in the program *)
val get_max_depth : unit -> int

(** Returns the maximum depth of followdbys in the program *)
val get_max_adepth : unit -> int


(** Returns a list of stateful variables (for use when we refine them as a preprocessing step) *)
val state_vars_list : unit -> Types.idtype list

val convert_def_list : Types.il_expression -> Types.node_id_t -> Types.il_formula

val convert_equation : Types.typed_stream ->  Types.il_expression -> Types.il_formula


