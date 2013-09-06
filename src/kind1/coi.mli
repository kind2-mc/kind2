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

(** Cone of influence and (static) slicing *)

(** {6 Functions} *)

(** Given an expression, return true if any variables mentioned should
be in the COI at the given depth.  First call [calculate_all_dependencies]. *)
val check_coi : Types.il_expression -> int -> bool

(** Initialize a table keeping track of variable dependencies *)
val examine_assignments : Types.il_formula -> unit

(** Returns a list of the ids in the input property. *)
val property_id_list : Types.typed_stream -> Types.idtype list

(** Calculate the COI based on the input list of variables and the given min/max depth range. *)
val calculate_all_dependencies : Types.idtype list -> int -> int -> unit

(** Removes redundant entries from [Tables.used_vars] based on a call to
[examine_assignments] for a certain formula and given maximum depth *)
val clean_used_vars : int -> unit
