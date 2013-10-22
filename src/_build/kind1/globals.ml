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
@author Jed Hagen\
@author Temesghen Kahsai

*)

open Types
open Exceptions
(* open Mpi *)

let version = "1.8"
let build = "2012/01/09"

class current_solver =
object
  val mutable s = new Solver_base.solver_base
  method set s1 = s <- s1
  method get = (s :> Solver_base.solver_base)
end

let my_solver = new current_solver

let firsttime = ref true (* true if fist time through main loop *)
let stop = ref false  (* set to true if main loop is done *)
let error = ref false (* set to true if error encountered in solver *)
(*let counter_stop = ref false   set to true when in parallel you find a counterexample*)

let base_abstr = 0
let step_abstr = 1

let max_num_digits = 9


(** For generation of invariants of type intervals*)
let is_inter = ref false

(*
(** Parallel processes *)
let proc_size = comm_size comm_world  (* comm_size, comm_rank *)
let proc_rank = comm_rank comm_world
let base_proc = 0
let step_proc = 1
let inv_gen_proc = ref 2
let kind_ai_proc = ref 3
let base_stop = ref false
let stop_inv_gen = ref false
*)

(** Wall time *)
let master_time_start  =  ref 0.0
let master_time_stop  =  ref 0.0
let base_time_start  = ref 0.0
let base_time_stop  = ref 0.0
let step_time_start  = ref 0.0
let step_time_stop  = ref 0.0
let inv_gen_time_start  = ref 0.0
let inv_gen_time_stop  = ref 0.0
let bool_inv_gen_time_start  = ref 0.0
let bool_inv_gen_time_stop  = ref 0.0
let int_inv_gen_time_start  = ref 0.0
let int_inv_gen_time_stop  = ref 0.0
let kind_ai_time_start = ref 0.0
let kind_ai_time_stop  = ref 0.0

(** Generation of xml document *)
let xml = ref false

(** Storing the specified property. This is needed for single property verification.*)
let prop_specified = ref ""

let prop_typed_stream = ref (S_TRUE,L_BOOL)

