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



(**

Parsing of command line arguments

{1 Workflow}

Flags are separated based on the technique(s) they impact. {e Global flags} are
the ones that don't impact any technique, or impact all of them. Log flags,
help flags, timeout flags... are global flags.

{e NB:} when adding a boolean flag, make sure to parse its value with the
[bool_of_string] function.

{2 Adding a new (non-global) flag to an existing module}

Adding a new flag impacts three pieces of code. The first is the body of the
module you're adding the flag to. Generally speaking, adding a flag looks like

{[
(* Default value of the flag. *)
let my_flag_default = ...
(* Reference storing the value of the flag. *)
let my_flag = ref my_flag_default
(* Add flag specification to module specs. *)
let _ = add_spec (
  (* The actual flag. *)
  "--my_flag",
  (* What to do with the value given to the flag, see other flags. *)
  ...,
  (* Flag description. *)
  fun fmt ->
    Format.fprintf fmt
      "@[<v>Description of my flag.@ Default: %a@]"
      pp_print_default_value_of_my_flag my_flag_default
)
(* Flag value accessor. *)
let my_flag () = !my_flag
]}

At this point your flag is integrated in the Kind 2 flags.

To make it available to the rest of Kind 2, you need to modify the signature of
the module you added the flag to
- in this file, where the module is declared, and
- in [flags.mli].

The update to the signature is typically

{[
  val my_flag : unit -> type_of_my_flag
]}


{b Adding a new flag module}

The template to add a new module is

{[
module MyModule : sig
  include FlagModule
end = struct

  (* Identifier of the module. No space or special characters. *)
  let id = "..."
  (* Short description of the module. *)
  let desc = "..."
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      ...\
    @]"

  (* All the flag specification of this module. *)
  let all_specs = ref []
  let add_specs specs = all_specs := !all_specs @ specs
  let add_spec spec = add_specs [spec]

  (* Returns all the flag specification of this module. *)
  let all_specs () = !all_specs

end
]}

Don't forget to update `flags.mli`:

{[
module MyModule : sig
  include FlagModule
end
]}

You then need to add your module to the [module_map], the association map
between module identifiers and modules. Make sure the identifier for your
module is not used yet.

You can now add modules following the instructions in the previous section.

@author Christoph Sticksel, Adrien Champion *)


(** {1 Accessors for flags} *)


(** {2 Meta flags} *)


(** {2 Generic flags} *)

(** Input file *)
val input_file : unit -> string

(** All lustre files in the cone of influence of the input file. *)
val all_input_files : unit -> string list

(** Clears the lustre files in the cone of influence of the input file. *)
val clear_input_files : unit -> unit

(** Adds a lustre file in the cone of influence of the input file.

    Returns false if the cone of influence already contains the file *)
val add_input_file : string -> bool

(** Main node in Lustre file *)
val lus_main : unit -> string option

(** Format of input file *)
type input_format = [ `Lustre | `Horn | `Native ]
val input_format : unit -> input_format

(** Output directory for the files Kind 2 generates. *)
val output_dir : unit -> string

val include_dirs : unit -> string list

type real_precision = [`Rational | `Float]
val real_precision : unit -> real_precision

(** Minimizes and logs invariants as contracts. *)
val log_invs : unit -> bool

(** Prints invariants **)
val print_invs : unit -> bool

(** Debug sections to enable *)
val debug : unit -> string list

(** Logfile for debug output  *)
val debug_log : unit -> string option

(** Verbosity level *)
val log_level : unit -> Lib.log_level

(** Output in XML format *)
val log_format_xml : unit -> bool

(** Output in XML format *)
val log_format_json : unit -> bool

(** Wallclock timeout. *)
val timeout_wall : unit -> float

(** Per-run wallclock timeout. *)
val timeout_analysis : unit -> float

(** The Kind modules enabled is a list of [kind_module]s. *)
type enable = Lib.kind_module list

(** Only parse the Lustre program. No analysis is performed. *)
val only_parse : unit -> bool

(** Stop after Parsing and type checking the Lustre program. No analysis is performed. *)
val only_tc : unit -> bool

(** Skip the type checking phase for the lustre program. *)
val no_tc : unit -> bool
  
(** The modules enabled. *)
val enabled : unit -> enable

(** Returns the invariant generation techniques currently enabled. *)
val invgen_enabled : unit -> enable

(** Manually disables a module. *)
val disable : Lib.kind_module -> unit

(** Modular analysis. *)
val modular : unit -> bool

(** Node slicing *)
val slice_nodes : unit -> bool

(** Check properties of subnodes *)
val check_subproperties : unit -> bool

(** Strict Lustre mode. *)
val lus_strict : unit -> bool

(** Activates compilation to Rust. *)
val lus_compile : unit -> bool

(** Colored output. *)
val color : unit -> bool

(** Use weak hash-consing. *)
val weakhcons : unit -> bool

(** {2 SMT solver flags} *)
module Smt : sig

  (** Logic sendable to the SMT solver. *)
  type logic = [
    `None | `detect | `Logic of string
  ]

  (** Logic to send to the SMT solver *)
  val logic : unit -> logic

  (** Legal SMT solvers. *)
  type solver = [
    | `MathSAT_SMTLIB
    | `Boolector_SMTLIB
    | `Z3_SMTLIB
    | `CVC4_SMTLIB
    | `Yices_SMTLIB
    | `Yices_native
    | `detect
  ]

  (** Set SMT solver and executable *)
  val set_solver : solver -> unit

  (** Which SMT solver to use. *)
  val solver : unit -> solver

  (** Use check-sat with assumptions, or simulate with push/pop *)
  val check_sat_assume : unit -> bool

  val set_check_sat_assume : bool -> unit

  (** Send short names to SMT solver *)
  val short_names : unit -> bool

  (** Change sending of short names to SMT solver *)
  val set_short_names : bool -> unit

  (** Executable of MathSAT solver *)
  val mathsat_bin : unit -> string

  (** Executable of Boolector solver *)
  val boolector_bin : unit -> string

  (** Executable of Z3 solver *)
  val z3_bin : unit -> string

  (** Executable of CVC4 solver *)
  val cvc4_bin : unit -> string

  (** CVC4 binary requires --rewrite-divk flag *)
  val cvc4_rewrite_divk : unit -> bool

  val set_cvc4_rewrite_divk : bool -> unit

  (** CVC4 binary requires --bv-print-consts-in-binary flag *)
  val cvc4_bv_consts_in_binary : unit -> bool

  val set_cvc4_bv_consts_in_binary : bool -> unit

  (** Executable of Yices solver *)
  val yices_bin : unit -> string

  (** Executable of Yices2 SMT2 solver *)
  val yices2smt2_bin : unit -> string

  (** Yices 2 binary supports models in SMT2 format **)
  val yices2_smt2models : unit -> bool

  val set_yices2_smt2models : bool -> unit

  (** Forces SMT traces. *)
  val set_trace: bool -> unit
  
  (** Write all SMT commands to files *)
  val trace : unit -> bool

  (** Path to the smt trace directory. *)
  val trace_dir : unit -> string
end


(** {2 BMC / k-induction flags} *)
module BmcKind : sig

  (** Maximal number of iterations in BMC. *)
  val max : unit -> int

  (** Check that the unrolling of the system alone is satisfiable. *)
  val check_unroll : unit -> bool

  (** Print counterexamples to induction. *)
  val print_cex : unit -> bool

  (** Compress inductive counterexample. *)
  val compress : unit -> bool

  (** Compress inductive counterexample when states are equal modulo inputs. *)
  val compress_equal : unit -> bool

  (** Compress inductive counterexample when states have same successors. *)
  val compress_same_succ : unit -> bool

  (** Compress inductive counterexample when states have same predecessors. *)
  val compress_same_pred : unit -> bool

  (** Lazy assertion of invariants. *)
  val lazy_invariants : unit -> bool
end


(** {2 IC3 flags} *)
module IC3 : sig

  (** Check inductiveness of blocking clauses. *)
  val check_inductive : unit -> bool

  (** File for inductive blocking clauses. *)
  val print_to_file : unit -> string option

  (** Tighten blocking clauses to an unsatisfiable core. *)
  val inductively_generalize : unit -> int

  (** Block counterexample in future frames. *)
  val block_in_future : unit -> bool

  (** Block counterexample in future frames first before returning to frame. *)
  val block_in_future_first : unit -> bool

  (** Also propagate clauses before generalization. *)
  val fwd_prop_non_gen : unit -> bool

  (** Inductively generalize all clauses after forward propagation. *)
  val fwd_prop_ind_gen : unit -> bool

  (** Subsumption in forward propagation. *)
  val fwd_prop_subsume : unit -> bool

  (** Use invariants from invariant generators. *)
  val use_invgen : unit -> bool

  (** Legal abstraction mechanisms for in IC3. *)
  type abstr = [ `None | `IA ]

  (** Abstraction mechanism IC3 should use. *)
  val abstr : unit -> abstr
end

(** {2 QE flags} *)
module QE : sig
  (** Methods available for quantifier elimination. *)
  type qe_method = [
    `Precise | `Impl | `Impl2 | `Cooper
  ]

  (** The QE method used. *)
  val qe_method : unit -> qe_method

  (** Set [qe_method]. *)
  val set_qe_method : qe_method -> unit

  (** Supported heuristics for extraction of implicants. *)
  type extract = [ `First | `Vars ]

  (** Heuristic for extraction of implicants. *)
  val extract : unit -> extract

  (** Order variables in polynomials by order of elimination **)
  val order_var_by_elim : unit -> bool

  (** Choose lower bounds containing variables **)
  val general_lbound : unit -> bool
end


(** {2 Contracts flags} *)
module Contracts : sig

  (** Compositional analysis. *)
  val compositional : unit -> bool

  (** Translate contracts. *)
  val translate_contracts : unit -> string option

  (** Check modes. *)
  val check_modes : unit -> bool

  (** Check modes. *)
  val check_implem : unit -> bool


  (** Contract generation. *)
  val contract_gen : unit -> bool

  (** Contract generation: max depth. *)
  val contract_gen_depth : unit -> int

  (** Activate refinement. *)
  val refinement : unit -> bool
end


(** {2 Certificates and Proofs} *)
module Certif : sig

  (** Minimization stragegy for k *)
  type mink = [ `No | `Fwd | `Bwd | `Dicho | `FrontierDicho | `Auto]

  (** Minimization stragegy for invariants *)
  type mininvs = [ `Easy | `Medium | `MediumOnly | `Hard | `HardOnly ]

  (** Certification only. *)
  val certif : unit -> bool

  (** Proof production. *)
  val proof : unit -> bool

  (** Use abstract type indexes in certificates/proofs. *)
  val abstr : unit -> bool

  (** Log trusted parts of proofs. *)
  val log_trust : unit -> bool

  (** Minimization stragegy for k *)
  val mink : unit -> mink

  (** Minimization stragegy for invariants *)
  val mininvs : unit -> mininvs

  (** Binary for JKind *)
  val jkind_bin : unit -> string

  val only_user_candidates : unit -> bool

end

(** {2 Inductive Validity Cores} *)
module IVC : sig

  type minimize_mode = [ `DO_NOT_MINIMIZE | `VALID_LUSTRE | `CONCISE ]
  type ivc_element =
    [ `NODE_CALL | `CONTRACT_ITEM | `EQUATION | `ASSERTION | `ANNOTATIONS ]

  (** Enable computation of Inductive Validity Cores *)
  val compute_ivc : unit -> bool

  val ivc_all : unit -> bool

  (** Specify on which elements we want to minimize *)
  val ivc_category : unit -> ivc_element list

  (** Print the model elements of the computed IVC *)
  val print_ivc : unit -> bool

  (** Print the model elements NOT in the computed IVC *)
  val print_ivc_compl : unit -> bool

  (** If true, compute an approximation of a MIVC *)
  val ivc_approximate : unit -> bool

  (** If true, compute the MUST set first and compute the IVCs starting from it *)
  val ivc_must_set : unit -> bool

  (** If true, compute a smallest IVC first *)
  val ivc_smallest_first : unit -> bool

  (** If true, compute IVC over elements of the main node only *)
  val ivc_only_main_node : unit -> bool

  (** Parameter k of the UMIVC algorithm.
  Correspond to the parameter 'k' of the implementation UMIVC.
  In particular, the value 0 implements the MARCO algorithm,
  and the value -1 (infinity) implements the CAMUS algorithm.
  *)
  val ivc_precomputed_mcs: unit -> int

  (** If true, IVCs will be computed for each properties separately *)
  val ivc_per_property : unit -> bool

  (** Generate a minimize lustre program *)
  val minimize_program : unit -> minimize_mode

  (** The directory where minimized programs should be saved *)
  val minimized_program_dir : unit -> string

  (** Timeout for unsat core computation *)
  val ivc_uc_timeout : unit -> int

  (** DEBUG flag: disable the must-set optimisation (ignored if ivc_must_set is true) *)
  val ivc_disable_must_opt : unit -> bool

end

(** {2 Minimal Cut Sets} *)
module MCS : sig

  type mcs_element =
    [ `NODE_CALL | `CONTRACT_ITEM | `EQUATION | `ASSERTION | `ANNOTATIONS ]

  (** Enable computation of Minimal Cut Sets *)
  val compute_mcs : unit -> bool

  (** Specify whether all the Minimal Cut Sets must be computed or just one *)
  val mcs_all : unit -> bool

  (** If true, compute an approximation of a MCS *)
  val mcs_approximate : unit -> bool

  (** Specify on which elements we want to minimize *)
  val mcs_category : unit -> mcs_element list

  (** Only search for MCSs of cardinality lower or equal to this parameter *)
  val mcs_max_cardinality : unit -> int

  (** Print the model elements of the computed MCS *)
  val print_mcs : unit -> bool

  (** Print the model elements NOT in the computed MCS *)
  val print_mcs_compl : unit -> bool

  (** Print the MCS using the legacy format *)
  val print_mcs_legacy : unit -> bool

  (** Print the counterexample found for each MCS *)
  val print_mcs_counterexample : unit -> bool

  (** If true, compute MCS over elements of the main node only *)
  val mcs_only_main_node : unit -> bool

  (** If true, MCSs will be computed for each properties separately *)
  val mcs_per_property : unit -> bool

end

(** {2 Arrays flags} *)
module Arrays : sig

  (** Use builtin theory of arrays in SMT solver *)
  val smt : unit -> bool

  (** Inline arrays with fixed bounds *)
  val inline : unit -> bool

  (** Define recursive functions for arrays *)
  val recdef : unit -> bool

  (** Allow non constant array sizes  *)
  val var_size : unit -> bool
end

(** {2 Testgen flags} *)

module Testgen : sig

  (** Activates test generation. *)
  val active : unit -> bool

  (** Only generate graph of reachable modes, do not log testcases. *)
  val graph_only : unit -> bool

  (** Length of the test case generated. *)
  val len : unit -> int
end


(** {2 Invgen flags} *)
module Invgen : sig

  (** InvGen will remove trivial invariants, i.e. invariants implied by the
      transition relation. *)
  val prune_trivial : unit -> bool

  (** Sets the max depth for invariant generation. *)
  val set_max_depth : int option -> unit
  
  (** Gets the max depth for invariant generation. *)
  val max_depth : unit -> int option

  (** Number of unrollings invariant generation should perform between
    switching to a different systems. *)
  val max_succ : unit -> int

  (** InvGen will lift candidate terms from subsystems. **)
  val lift_candidates : unit -> bool

  (** InvGen will generate invariants only for top level. **)
  val top_only : unit -> bool

  (** Forces invgen to consider a huge number of candidates. *)
  val all_out : unit -> bool

  (** InvGen will look for candidate terms in the transition predicate. *)
  val mine_trans : unit -> bool

  (** InvGen will run in two state mode. *)
  val two_state : unit -> bool

  (** Forces bool invgen to look for equalities only. *)
  val bool_eq_only : unit -> bool

  (** Forces arith invgen to look for equalities only. *)
  val arith_eq_only : unit -> bool

  (** Renice invariant generation process. *)
  val renice : unit -> int
end


(** {2 C2I flags} *)
module C2I : sig

  (** Number of disjuncts in the DNF constructed by C2I. *)
  val dnf_size : unit -> int

  (** Number of int cubes in the DNF constructed by C2I. *)
  val int_cube_size : unit -> int

  (** Number of real cubes in the DNF constructed by C2I. *)
  val real_cube_size : unit -> int

  (** Whether mode sub candidate is activated in c2i. *)
  val modes : unit -> bool
end


(** {2 Interpreter flags} *)
module Interpreter : sig

  (** Read input from file. *)
  val input_file : unit -> string

  (** Run number of steps, override the number of steps given in the input
    file. *)
  val steps : unit -> int
end


(** {1 Convenience functions} *)

(** Path to subdirectory for a system (in the output directory). *)
val subdir_for : string list -> string


(** {1 Parsing of the command line} 

    Parsing of the command line arguments is performed when loading this
    module.
*)

(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
