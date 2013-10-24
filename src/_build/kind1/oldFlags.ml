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


(** Global flags mostly set from the command line *)


(** 
@author Jed Hagen 
@author Temesghen Kahsai

*)

open Types

let inlining_mode = ref true (* use standard inlining *)
let aggressive_inlining = ref 0 (* the complexity of aggressive inlining, <1 is none *)
let rename_long_vars = ref true (* reduce size of formulas sent to solvers *)
let long_vars_length = 0 (* this depends on the hashtable precision *)
let do_negative_index = ref true (* does the loop start at zero or end at zero? *)
let loopfree_mode = ref false (* turn off internally if no state vars *)
let termination_check = ref false (* turn off internally if no state vars *)
let pre_refine_state_vars = ref false (* preprocess refine state variables *)
let bv_mode = ref false (* treat booleans as bitvectors (used for cvc3) *)
let define_mod_div = ref false (* add definitions of mod & div to headers *)
let debug = ref false
let do_k_induction = ref true (* false = bmc only *)
let k_step_size = ref 1 (* interval between induction checks *)
let more_steps = ref false (* will be true if k_step_size > 1*)
let incr_k_step_size = ref false (* increase induction step size as we go *)
let abs_mode = ref false (* refine one var / step *)
let core_mode = ref false (* refine 1 var/core var/step *)
let full_subtree_mode = ref false (* refine subtree of cores *)
let hybrid_core_mode = ref false (* refine 1 var/core var/step, but not backwards ITE does not yet work *)
let fine_core_mode = ref false (* refine 1 var/core var/step, but not backwards,or forwards  ITE does not yet work *)
let incr_mode = ref false (* refine 1 var/core var/step *)
let path_mode = ref false (* refine 1 var path/step *)
let hpath_mode = ref false (* refine 1 var path/step, with ordering heuristic *)
let separate_solvers = ref true (* separate solvers for symbolic formulas *)
let var_defs_mode = ref true (* define each variable separately *)
let checker_mode = ref false (* check for spurious counterexamples *)
let no_inductive_check_mode = ref false (**)
let print_all_vars = ref true (* output all variables or just inputs? *)
let hpath_mode1 = ref false (* used for heuristic refinement *)
let hpath_mode2 = ref false (* used for heuristic refinement *)
let rev_heuristic_mode = ref false (* used for heuristic refinement *)
let best_first_path_mode = ref false (* used for heuristic refinement *)
let print_dot_one = ref false (* print graphs *)
let print_dot_all = ref false (* print graphs *)
let force_refinement = ref max_int (* how often we force refinement *)
let compression_in_checker = ref false (* add compression formulas to checker -- does not seem helpful *)
let initial_compression = ref false (* compress against initial position *)
let check_compression = ref true (* verify compression is correct *)
let interleave_termination_checks = ref false (* only do term check after a step check *)
let static_path_compression = [| false;false |] (* do not base path compression on abstraction *)
let fully_define_initial_state = ref false
let w1 = ref 1 (* used for heuristic refinement *)
let w2 = ref 1 (* used for heuristic refinement *)
let user_specified_main_node_name = ref "" (* main node specified by user *) 
let maxloops = ref 200 (* limit to prevent running forever *)
let loud = ref false (* printout status to user? *)
let final_cex_loud = ref true (* printout final counterexample if invalid? *)
let do_scratch = ref false (* save work? *)
let buffer_limit = ref 200000 (* unix pipe limit? *)
let commentchar = ref ";"
let set_my_solver = ref YICES_WRAPPER (* which solver are we using? *)
let solverflags = ref "" (* send to solver *)
let only_1_abstraction = ref true (* one or 2 abstractions? *)
let abstr_bool = ref false (* flatten booleans *)
let abstr_ite = ref false (* flatten ites *)
let abstr_pre = ref false (* flatten pres *)
let abstr_non_var_pre = ref false (* flatten pres s.t. only variables occur under it *)
let abstr_non_var_pre_dist = ref false (* distribute pres over non-variable terms *)
let use_x = ref false  (* if variable _x was used in a meta-property *)
let set_use_x () =  use_x := true
let naive = ref false
let no_imp = ref false

(** Produce XML format of the counterexample *)
let xml = ref false

(** Generation of results for the GUI*)
let gui = ref false 

(** Invariant generation global flags*)
let invariant_bool = ref false
let invariant_int = ref false
let remove_trivial_invariants = ref false
let range = ref 10

(** For incremental invariant generation *)
let k_incremental = ref 10
let incremental = ref true

(** For mpi implementation *)
let mpi_abort = ref false
let stop_invariant = ref false

(** Related to z3 *)
let enabled_z3 = ref false

(** Multiple properties*)
let no_multi = ref false 
let prop_as_invariant = ref true

(** Print the inductive counterexample *)
let inductive_cs = ref false

(** Generate invariant for mode variables *) 
let mode_inv = ref true

(** Generate invariant for mode variables *) 
let select_mv = ref false

(** Used for Kind GUI to specify the solver path*)
let solver_path = ref ""

(** KIND GUI *)
let gui = ref false


(** Timeout *)
let timeout = ref 100.0


