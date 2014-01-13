(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
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
type smtsolver = [ `Z3_SMTLIB | `Z3_API | `CVC4_SMTLIB | `CVC4_API | `Yices ]
val smtsolver : unit -> smtsolver 

(** SMT Logic to use *)
type smtlogic = [ `QF_LIA | `QF_LRA | `detect ]
val smtlogic : unit -> smtlogic 

(** Executable of Z3 solver *)
type z3_bin = string
val z3_bin : unit -> z3_bin

(** Executable of CVC4 solver *)
type cvc4_bin = string
val cvc4_bin : unit -> cvc4_bin

(** Enabled Kind modules *)
type enable = Lib.kind_module list
val enable : unit -> enable 

(** Algorithm for quantifier elimination in PDR *)
type pdr_qe = [ `Z3 | `Cooper ]
val pdr_qe : unit -> pdr_qe

(** Timeout in ms for subsumption check in frames *)
type pdr_subs_timeout = int
val pdr_subs_timeout : unit -> pdr_subs_timeout

(** Check inductiveness of blocking clauses *)
type pdr_check_inductive = bool
val pdr_check_inductive : unit -> pdr_check_inductive

(** Simultaneous check for propagation *)
type pdr_fwd_prop_check_multi = bool
val pdr_fwd_prop_check_multi : unit -> pdr_fwd_prop_check_multi

(** Output inductive blocking clauses *)
type pdr_dump_inductive_assertions = bool
val pdr_dump_inductive_assertions : unit -> pdr_dump_inductive_assertions

(** File for inductive blocking clauses *)
type pdr_inductive_assertions_file = string option 
val pdr_inductive_assertions_file : unit -> pdr_inductive_assertions_file

(** Minimize counterexamples *)
type pdr_minimize_cex = bool
val pdr_minimize_cex : unit -> pdr_minimize_cex

(** Tighten blocking clauses to an unsatisfiable core *)
type pdr_tighten_to_unsat_core = bool
val pdr_tighten_to_unsat_core : unit -> pdr_tighten_to_unsat_core

(** Block counterexample in future frames *)
type pdr_block_in_future = bool
val pdr_block_in_future : unit -> pdr_block_in_future

(** Last frame contains property (Bradley vs. Een et al.) *)
type pdr_prop_in_last_frame = bool
val pdr_prop_in_last_frame : unit -> pdr_prop_in_last_frame

(** Debug sections to enable *)
val debug : unit -> string list

(** Logfile for debug output  *)
val debug_log : unit -> string option

(** Verbosity level *)
val log_level : unit -> Event.log_level

(** Output in XML format *)
val log_format_xml : unit -> bool

(** Order variables in polynomials by order of elimination **)
type cooper_order_var_by_elim = bool
val cooper_order_var_by_elim : unit -> cooper_order_var_by_elim

(** Choose lower bounds containing variables **)
type cooper_general_lbound = bool
val cooper_general_lbound : unit -> cooper_general_lbound

(** Read input from file **)
type interpreter_input_file = string
val interpreter_input_file : unit -> interpreter_input_file

(** Run number of steps, override the number of steps given in the
    input file **)
type interpreter_steps = int
val interpreter_steps : unit -> interpreter_steps

(** Input file *)
val input_file : unit -> string 

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
