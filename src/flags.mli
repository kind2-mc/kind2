(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

(** Command-line flags 

    Use the OCaml module [Arg] to parse the command-line and store the
    value in a record type.
    
    @author Christoph Sticksel *)

(** {1 Accessors for flags} *)

(** Wallclock timeout *)
val timeout_wall : unit -> float

(** CPU timeout *)
val timeout_virtual : unit -> float

(** SMT Solver to use *)
type smtsolver = 
  [ `Z3_SMTLIB
  | `CVC4_SMTLIB
  | `MathSat5_SMTLIB
  | `Yices_SMTLIB
  | `Yices_native
  | `detect ]

(** Return SMT solver *)
val smtsolver : unit -> smtsolver 

(** Set SMT solver and executable *)
val set_smtsolver : smtsolver -> string -> unit

(* (\** Return SMT solver to use with IC3 *\) *)
(* val ic3_smtsolver : unit -> smtsolver  *)

(* (\** Return SMT solver to use with Quantifier Elimination *\) *)
(* val qe_smtsolver : unit -> smtsolver  *)

(** detect logic to send SMT solver *)
type smtlogic = [ `None | `detect | `Logic of string ]
val smtlogic : unit -> smtlogic 

(** Executable of Z3 solver *)
type z3_bin = string
val z3_bin : unit -> z3_bin

(** Use check-sat with assumptions, or simulate with push/pop *)
type smt_check_sat_assume = bool
val smt_check_sat_assume : unit -> smt_check_sat_assume

(** Send short names to SMT solver *)
type smt_short_names = bool
val smt_short_names : unit -> smt_short_names

(** Executable of CVC4 solver *)
type cvc4_bin = string
val cvc4_bin : unit -> cvc4_bin

(** Executable of MathSAT5 solver *)
type mathsat5_bin = string
val mathsat5_bin : unit -> mathsat5_bin

(** Executable of Yices solver *)
type yices_bin = string
val yices_bin : unit -> yices_bin

(** Executable of Yices2 SMT2 solver *)
type yices2smt2_bin = string
val yices2smt2_bin : unit -> yices2smt2_bin

(** Write all SMT commands to files *)
type smt_trace = bool
val smt_trace : unit -> smt_trace

(** Directory for trace logs of SMT commands *)
type smt_trace_dir = string 
val smt_trace_dir : unit -> smt_trace_dir

(** Enabled Kind modules *)
type enable = Lib.kind_module list
val enable : unit -> enable

(** Maximal number of iterations in BMC *)
type bmc_max = int
val bmc_max : unit -> bmc_max

(** Check that the unrolling of the system alone is satisfiable. *)
type bmc_check_unroll = bool
val bmc_check_unroll : unit -> bmc_check_unroll

(** Print counterexamples to induction. *)
type ind_print_cex = bool
val ind_print_cex : unit -> ind_print_cex

(** Output version information and exit *)
type check_version = bool
val check_version : unit -> check_version

(** Compress inductive counterexample *)
type ind_compress = bool
val ind_compress : unit -> ind_compress

(** Compress inductive counterexample when states are equal modulo
    inputs *)
type ind_compress_equal = bool
val ind_compress_equal : unit -> ind_compress_equal

(** Compress inductive counterexample when states have same successors *)
type ind_compress_same_succ = bool
val ind_compress_same_succ : unit -> ind_compress_same_succ

(** Compress inductive counterexample when states have same predecessors *)
type ind_compress_same_pred = bool
val ind_compress_same_pred : unit -> ind_compress_same_pred

(** Lazy assertion of invariants. *)
type ind_lazy_invariants = bool
val ind_lazy_invariants : unit -> ind_lazy_invariants

(** Strict Lustre mode *)
type strict = bool
val strict : unit -> strict

(** Algorithm for quantifier elimination in IC3 *)
type ic3_qe = [ `Z3 | `Z3_impl | `Z3_impl2 | `Cooper ]
val ic3_qe : unit -> ic3_qe
val set_ic3_qe : ic3_qe -> unit

(** Heuristics for extraction of implicant *)
type ic3_extract = [ `First | `Vars ]
val ic3_extract : unit -> ic3_extract

(** Check inductiveness of blocking clauses *)
type ic3_check_inductive = bool
val ic3_check_inductive : unit -> ic3_check_inductive

(** File for inductive blocking clauses *)
type ic3_print_to_file = string option 
val ic3_print_to_file : unit -> ic3_print_to_file

(** Tighten blocking clauses to an unsatisfiable core *)
type ic3_inductively_generalize = int
val ic3_inductively_generalize : unit -> ic3_inductively_generalize

(** Block counterexample in future frames *)
type ic3_block_in_future = bool
val ic3_block_in_future : unit -> ic3_block_in_future
  
(** Block counterexample in future frames first before returning to frame *)
type ic3_block_in_future_first = bool
val ic3_block_in_future_first : unit -> ic3_block_in_future_first  

(** Also propagate clauses before generalization *)
type ic3_fwd_prop_non_gen = bool
val ic3_fwd_prop_non_gen : unit -> ic3_fwd_prop_non_gen

(** Inductively generalize all clauses after forward propagation *)
type ic3_fwd_prop_ind_gen = bool
val ic3_fwd_prop_ind_gen : unit -> ic3_fwd_prop_ind_gen

(** Subsumption in forward propagation *)
type ic3_fwd_prop_subsume = bool
val ic3_fwd_prop_subsume : unit -> ic3_fwd_prop_subsume

(** Use invariants from invariant generators *)
type ic3_use_invgen = bool
val ic3_use_invgen : unit -> ic3_use_invgen

(** Abstraction mechanism to use in IC3 *)
type ic3_abstr = [ `None | `IA ]
val ic3_abstr : unit -> ic3_abstr

(** Debug sections to enable *)
val debug : unit -> string list

(** Logfile for debug output  *)
val debug_log : unit -> string option

(** Verbosity level *)
val log_level : unit -> Lib.log_level

(** Output in XML format *)
val log_format_xml : unit -> bool

(** Modular analysis. *)
type modular = bool
val modular : unit -> modular

(** Compositional analysis. *)
type compositional = bool
val compositional : unit -> compositional

(** Check modes. *)
type check_modes = bool
val check_modes : unit -> check_modes

(** Check modes. *)
type check_implem = bool
val check_implem : unit -> check_implem

(** Order variables in polynomials by order of elimination **)
type cooper_order_var_by_elim = bool
val cooper_order_var_by_elim : unit -> cooper_order_var_by_elim

(** Choose lower bounds containing variables **)
type cooper_general_lbound = bool
val cooper_general_lbound : unit -> cooper_general_lbound

(** Activates test generation. *)
type testgen_active = bool
val testgen_active : unit -> testgen_active

(** Only generate graph of reachable modes, do not log testcases. *)
type testgen_graph_only = bool
val testgen_graph_only : unit -> testgen_graph_only

(** Command for lustrec. *)
type testgen_lustrec = string option
val testgen_lustrec : unit -> testgen_lustrec

(** Output directory for test generation. *)
type testgen_out_dir = string
val testgen_out_dir : unit -> testgen_out_dir

(** Length of the test case generated. *)
type testgen_len = int
val testgen_len : unit -> testgen_len

(** InvGen will remove trivial invariants, i.e. invariants implied by
    the transition relation.. **)
type invgengraph_prune_trivial = bool
val invgengraph_prune_trivial : unit -> invgengraph_prune_trivial
type invgengraph_max_succ = int
val invgengraph_max_succ : unit -> invgengraph_max_succ
(** InvGen will lift candidate terms from subsystems.. **)
type invgengraph_lift_candidates = bool
val invgengraph_lift_candidates : unit -> invgengraph_lift_candidates
(** InvGen will generate invariants only for top level. **)
type invgengraph_top_only = bool
val invgengraph_top_only : unit -> invgengraph_top_only
(** InvGen will look for candidate terms in the transition
    predicate. *)
type invgengraph_mine_trans = bool
val invgengraph_mine_trans : unit -> invgengraph_mine_trans

(** Renice invariant generation process *)
type invgengraph_renice = int
val invgengraph_renice : unit -> invgengraph_renice

(** Number of disjuncts in the DNF constructed by C2I. *)
type c2i_dnf_size = int
val c2i_dnf_size : unit -> c2i_dnf_size

(** Number of int cubes in the DNF constructed by C2I. *)
type c2i_int_cube_size = int
val c2i_int_cube_size : unit -> c2i_int_cube_size

(** Number of real cubes in the DNF constructed by C2I. *)
type c2i_real_cube_size = int
val c2i_real_cube_size : unit -> c2i_real_cube_size

(** Whether mode sub candidate is activated in c2i. *)
type c2i_modes = bool
val c2i_modes : unit -> c2i_modes

(** Read input from file **)
type interpreter_input_file = string
val interpreter_input_file : unit -> interpreter_input_file

(** Run number of steps, override the number of steps given in the
    input file **)
type interpreter_steps = int
val interpreter_steps : unit -> interpreter_steps

(** Format of input file *)
type input_format = [ `Lustre | `Horn | `Native ]
val input_format : unit -> input_format 

(** Input file *)
val input_file : unit -> string 

(** Main node in Lustre file *)
val lustre_main : unit -> string option

(** Flatten arrays to one stream per element *)
type lustre_flatten_arrays = bool
val lustre_flatten_arrays : unit -> lustre_flatten_arrays

(** {1 Parsing of the command line} *)

(** Parse the command line *)
val parse_argv : unit -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
