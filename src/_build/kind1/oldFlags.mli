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




val inlining_mode : bool ref (** use standard inlining *)
val aggressive_inlining :int ref (** the complexity of aggressive inlining, <1 is none *)
val rename_long_vars : bool ref (** reduce size of formulas sent to solvers *)
val long_vars_length : int (** What is considered a "long" variable name (to be renamed) -- set to 0 to ensure there are no name conflicts with Kind's reserved names *)
val do_negative_index : bool ref (** does the loop start at zero or end at zero? *)

val loopfree_mode : bool ref (** turn off internally if no state vars *)
val termination_check : bool ref (** turn off internally if no state vars *)

val pre_refine_state_vars : bool ref (** preprocess refine state variables *)

val bv_mode : bool ref (** treat booleans as bitvectors (used for cvc3) *)

val define_mod_div : bool ref (** add definitions of mod & div to headers *)

val debug : bool ref
val do_k_induction : bool ref (** false = bmc only *)
val k_step_size : int ref (** interval between induction checks *)
val more_steps : bool ref (* will be true if k_step_size > 1*)
val incr_k_step_size : bool ref (** increase induction step size as we go *)
val abs_mode : bool ref (** refine one var / step *)
val core_mode : bool ref (** refine 1 var/core var/step *)
val full_subtree_mode : bool ref (** refine subtree of cores *)
val hybrid_core_mode : bool ref (** refine 1 var/core var/step, but not backwards ITE does not yet work *)
val fine_core_mode : bool ref (** refine 1 var/core var/step, but not backwards,or forwards  ITE does not yet work *)
val incr_mode : bool ref (** refine 1 var/core var/step *)
val path_mode : bool ref (** refine 1 var path/step *)
val hpath_mode : bool ref (** refine 1 var path/step, with ordering heuristic *)
val separate_solvers : bool ref (** separate solvers for symbolic formulas *)
val var_defs_mode : bool ref (** define each variable separately *)
val checker_mode : bool ref (** check for spurious counterexamples *)
val no_inductive_check_mode : bool ref (**)
val print_all_vars : bool ref (** output all variables or just inputs? *)
val hpath_mode1 : bool ref (** used for heuristic refinement *)
val hpath_mode2 : bool ref (** used for heuristic refinement *)
val rev_heuristic_mode : bool ref (** used for heuristic refinement *)
val best_first_path_mode : bool ref (** used for heuristic refinement *)
val print_dot_one : bool ref (** print graphs *)
val print_dot_all : bool ref (** print graphs *)
val force_refinement : int ref (** how often we force refinement *)
val compression_in_checker : bool ref (** add compression formulas to checker -- does not seem helpful *)
val initial_compression : bool ref (** compress against initial position *)
val check_compression : bool ref (** verify compression is correct *)
val interleave_termination_checks : bool ref (** only do term check after a step check *)
val static_path_compression : bool array (** do not base path compression on abstraction *)
val fully_define_initial_state : bool ref
(** this can be set via flag or internally *)
val w1 : int ref (** used for heuristic refinement *)
val w2 : int ref (** used for heuristic refinement *)

val user_specified_main_node_name : string ref (** main node specified by user **)

val invariant_bool: bool ref (** Generate boolean implicaiton invariants **)
val invariant_int:  bool ref (** Generate integer less_or_equal invariants **)
val remove_trivial_invariants: bool ref (** Whether remove trivial invariants in the end **)

val maxloops : int ref (** limit to prevent running forever *)
val loud : bool ref (** printout status to user? *)
val final_cex_loud : bool ref (** printout final counterexample if invalid? *)
val do_scratch : bool ref (** save work? *)
val naive : bool ref (** naive algorithm*)
val no_imp : bool ref (** no implication *)

val buffer_limit : int ref (** unix pipe limit? *)

val commentchar : string ref (** Solver-specific comment character *)

val set_my_solver : Types.solvertype ref (** which solver are we using? *)
val solverflags : string ref (** send to solver *)


val only_1_abstraction : bool ref (** one or 2 abstractions? *)


val abstr_bool : bool ref (** flatten booleans *)
val abstr_ite : bool ref (** flatten ites *)
val abstr_pre : bool ref (** flatten pres *)
val abstr_non_var_pre : bool ref (** flatten pres *)
val abstr_non_var_pre_dist : bool ref (** distribute pres when flattening *)


(** if variable [_x] was used in a meta-property *)
val use_x : bool ref
(** Indicate that [_x] was used in a meta-property *)
val set_use_x : unit -> unit 


(** Produce XML format of the counterexample *)
val xml : bool ref 

(** Generation of results for the GUI*)
val gui : bool ref

(** For incremental invariant generation *)
val k_incremental : int ref
val incremental : bool ref
val range : int ref


(** For mpi implementation *)
val mpi_abort : bool ref
val stop_invariant : bool ref


(** Enable z3 *)
val enabled_z3 : bool ref

(** Multiple properties *)
val no_multi : bool ref
val prop_as_invariant : bool ref

(** Print the inductive counterexample *)
val inductive_cs : bool ref 

(** Generate invariant for mode variables *) 
val mode_inv : bool ref 

(** Select intresting mode variables *) 
val select_mv : bool ref

(** Used for Kind GUI to specify the solver path*)
val solver_path : string ref 


(** KIND GUI *)
val gui : bool ref


(** Timeout *)
val timeout : float ref
