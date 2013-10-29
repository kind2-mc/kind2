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


(** Global variables & functions *)

(**
@author Jed Hagen
@author Temesghen Kahsai

*)




(** Strings denoting version information *)
val version : string 
val build : string

(** The [current_solver] class is used to store the actual solver interface.*)
class current_solver :
object
  val mutable s : Solver_base.solver_base
  method set : Solver_base.solver_base -> unit (** Store a solver interface *)
  method get : Solver_base.solver_base (** The currently stored solver interface *)
end

val my_solver : current_solver


val firsttime : bool ref (** True if first time through main loop *)
val stop : bool ref  (** Set to true if main loop is done *)
val error : bool ref (** Set to true if error encountered in main loop *)

val base_abstr : int (** The index for the base abstraction *)
val step_abstr : int (** The index for the step abstraction *)

val max_num_digits: int (** The max number of digits allowed **)


(** For generation of invariants of type intervals*)
val is_inter : bool ref

(*
(** Parallel processes *)
val proc_size : int  
val proc_rank : int
val base_proc : int
val step_proc : int
val inv_gen_proc : int ref
val kind_ai_proc: int ref
val base_stop : bool ref
val stop_inv_gen : bool ref
*)

(** Wall time *)
val base_time_start : float ref
val base_time_stop : float ref
val step_time_start : float ref
val step_time_stop : float ref
val inv_gen_time_start : float ref
val inv_gen_time_stop : float ref 
val bool_inv_gen_time_start  : float ref
val bool_inv_gen_time_stop  : float ref
val int_inv_gen_time_start  : float ref
val int_inv_gen_time_stop  : float ref
val kind_ai_time_start  : float ref
val kind_ai_time_stop  : float ref


(** Generation of xml document *)
val xml : bool ref

(** Storing the specified property. This is needed for single property verification.*)
val prop_specified : string ref


val prop_typed_stream : Types.typed_stream ref
