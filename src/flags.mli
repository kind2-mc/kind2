(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

(* (\** Return SMT solver to use with PDR *\) *)
(* val pdr_smtsolver : unit -> smtsolver  *)

(* (\** Return SMT solver to use with Quantifier Elimination *\) *)
(* val qe_smtsolver : unit -> smtsolver  *)

(** SMT Logic to use *)
type smtlogic = [ `QF_LIA | `QF_LRA | `QF_LIRA |`QF_UFLIA | `QF_UFLRA | `detect ]
val smtlogic : unit -> smtlogic 

(** Executable of Z3 solver *)
type z3_bin = string
val z3_bin : unit -> z3_bin

(** Executable of CVC4 solver *)
type cvc4_bin = string
val cvc4_bin : unit -> cvc4_bin

(** Executable of MathSAT5 solver *)
type mathsat5_bin = string
val mathsat5_bin : unit -> mathsat5_bin

(** Executable of Yices solver *)
type yices_bin = string
val yices_bin : unit -> yices_bin

(** Executable of Yices solver *)
type yices_arith_only = bool
val yices_arith_only : unit -> yices_arith_only

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

(** Output version information and exit *)
type check_version = bool
val check_version : unit -> check_version

(** Compresss inductive counterexample *)
type ind_compress = bool
val ind_compress : unit -> ind_compress

(** Compresss inductive counterexample when states are equal modulo
    inputs *)
type ind_compress_equal = bool
val ind_compress_equal : unit -> ind_compress_equal

(** Compresss inductive counterexample when states have same successors *)
type ind_compress_same_succ = bool
val ind_compress_same_succ : unit -> ind_compress_same_succ

(** Compresss inductive counterexample when states have same predecessors *)
type ind_compress_same_pred = bool
val ind_compress_same_pred : unit -> ind_compress_same_pred

(** Lazy assertion of invariants. *)
type ind_lazy_invariants = bool
val ind_lazy_invariants : unit -> ind_lazy_invariants

(** Output inductive counterexample *)
type ind_print_inductive_cex = bool
val ind_print_inductive_cex : unit -> ind_print_inductive_cex

(** Algorithm for quantifier elimination in PDR *)
type pdr_qe = [ `Z3 | `Z3_impl | `Z3_impl2 | `Cooper ]
val pdr_qe : unit -> pdr_qe
val set_pdr_qe : pdr_qe -> unit

(** Heuristics for extraction of implicant *)
type pdr_extract = [ `First | `Vars ]
val pdr_extract : unit -> pdr_extract

(** Check inductiveness of blocking clauses *)
type pdr_check_inductive = bool
val pdr_check_inductive : unit -> pdr_check_inductive

(** Simultaneous check for propagation *)
type pdr_fwd_prop_check_multi = bool
val pdr_fwd_prop_check_multi : unit -> pdr_fwd_prop_check_multi

(** Output inductive blocking clauses *)
type pdr_print_inductive_assertions = bool
val pdr_print_inductive_assertions : unit -> pdr_print_inductive_assertions

(** Output all blocking clauses *)
type pdr_print_blocking_clauses = bool
val pdr_print_blocking_clauses : unit -> pdr_print_blocking_clauses

(** File for inductive blocking clauses *)
type pdr_print_to_file = string option 
val pdr_print_to_file : unit -> pdr_print_to_file

(** Tighten blocking clauses to an unsatisfiable core *)
type pdr_tighten_to_unsat_core = bool
val pdr_tighten_to_unsat_core : unit -> pdr_tighten_to_unsat_core

(** Tighten blocking clauses to an unsatisfiable core *)
type pdr_inductively_generalize = int
val pdr_inductively_generalize : unit -> pdr_inductively_generalize

(** Block counterexample in future frames *)
type pdr_block_in_future = bool
val pdr_block_in_future : unit -> pdr_block_in_future

(** Print inductive invariant if property proved *)
type pdr_print_inductive_invariant = bool
val pdr_print_inductive_invariant : unit -> pdr_print_inductive_invariant

(** Check inductive invariant if property proved *)
type pdr_check_inductive_invariant = bool
val pdr_check_inductive_invariant : unit -> pdr_check_inductive_invariant

(** Debug sections to enable *)
val debug : unit -> string list

(** Logfile for debug output  *)
val debug_log : unit -> string option

(** Verbosity level *)
val log_level : unit -> Lib.log_level

(** Output in XML format *)
val log_format_xml : unit -> bool

(** Order variables in polynomials by order of elimination **)
type cooper_order_var_by_elim = bool
val cooper_order_var_by_elim : unit -> cooper_order_var_by_elim

(** Choose lower bounds containing variables **)
type cooper_general_lbound = bool
val cooper_general_lbound : unit -> cooper_general_lbound

(** InvGen will remove trivial invariants, i.e. invariants implied by
    the transition relation.. **)
type invgengraph_prune_trivial = bool
val invgengraph_prune_trivial : unit -> invgengraph_prune_trivial
type invgengraph_max_succ = int
val invgengraph_max_succ : unit -> invgengraph_max_succ
(** InvGen will lift candidate terms from subsystems.. **)
type invgengraph_lift_candidates = bool
val invgengraph_lift_candidates : unit -> invgengraph_lift_candidates
(** InvGen will look for candidate terms in the transition
    predicate. *)
type invgengraph_mine_trans = bool
val invgengraph_mine_trans : unit -> invgengraph_mine_trans

(** Renice invariant generation process *)
type invgengraph_renice = int
val invgengraph_renice : unit -> invgengraph_renice

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
